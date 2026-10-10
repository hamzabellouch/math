import OAI.Analysis.MutuallyUnbiased.Bases.CompleteFamily
import OAI.Analysis.MutuallyUnbiased.Matrix.Equivalence
import OAI.Analysis.MutuallyUnbiased.Cubic.CubicPositivity
import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def commonRowTransform (H : CMatrix) (r : Equiv.Perm Coord) (u : Coord → ℂ) : CMatrix :=
  fun i j => u i * H (r i) j

theorem commonRowTransform_isHadamard {H : CMatrix} (hH : IsHadamard H)
    (r : Equiv.Perm Coord) (u : Coord → ℂ) (hu : ∀ i, Complex.normSq (u i) = 1) :
    IsHadamard (commonRowTransform H r u) := by
  have hh := (hH.permutations r (Equiv.refl Coord)).phaseTransform u (fun _ => 1) hu (by simp)
  change IsHadamard (fun i j => u i * H (r i) j * 1) at hh
  change IsHadamard (fun i j => u i * H (r i) j)
  simpa only [mul_one] using hh

theorem g_commonRowTransform (H : CMatrix) (r : Equiv.Perm Coord)
    (u : Coord → ℂ) (a : Charge) :
    g (commonRowTransform H r u) a = character u a * g H (permuteCharge r.symm a) := by
  calc
    _ = character u a * g (fun i j => H (r i) j) a :=
      g_row_phase (fun i j => H (r i) j) u a
    _ = _ := by rw [g_row_permutation H r a]

theorem balanced_permute (r : Equiv.Perm Coord) {a : Charge} (ha : Balanced a) :
    Balanced (permuteCharge r a) := by
  simpa only [Balanced, permuteCharge, Function.comp_apply, Equiv.sum_comp] using ha

theorem order_permute (r : Equiv.Perm Coord) (a : Charge) :
    order (permuteCharge r a) = order a := by
  exact Equiv.sum_comp r (fun i => (a i).toNat)

theorem commonRowTransform_cross (H K : CMatrix) (r : Equiv.Perm Coord)
    (u : Coord → ℂ) (hu : ∀ i, Complex.normSq (u i) = 1) (k l : Coord) :
    (∑ i, commonRowTransform H r u i k * conj (commonRowTransform K r u i l)) =
      ∑ i, H i k * conj (K i l) := by
  calc
    _ = ∑ i, H (r i) k * conj (K (r i) l) := by
      apply Finset.sum_congr rfl
      intro i _
      have hunit : u i * conj (u i) = 1 := by rw [Complex.mul_conj, hu]; rfl
      simp only [commonRowTransform, map_mul]
      calc
        _ = (u i * conj (u i)) * (H (r i) k * conj (K (r i) l)) := by ring
        _ = _ := by rw [hunit, one_mul]
    _ = _ := Equiv.sum_comp r (fun i => H i k * conj (K i l))

theorem columnTransform_cross (H K : CMatrix) (c : Equiv.Perm Coord)
    (v : Coord → ℂ) (hv : ∀ j, Complex.normSq (v j) = 1) (k l : Coord) :
    Complex.normSq (∑ i, H i k * conj (K i (c l) * v l)) =
      Complex.normSq (∑ i, H i k * conj (K i (c l))) := by
  have he : (∑ i, H i k * conj (K i (c l) * v l)) =
      (∑ i, H i k * conj (K i (c l))) * conj (v l) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_mul, mul_assoc]
  rw [he, map_mul, Complex.normSq_conj, hv, mul_one]

def averageOtherFourier (U : Coord → CMatrix) (s : Coord) (a : Charge) : ℂ :=
  (5 : ℂ)⁻¹ * ∑ t : Fin 5, g (U (s.succAbove t)) a

theorem averageOtherFourier_order_two (U : Coord → CMatrix) (s : Coord)
    (hs : ∀ a, Balanced a → g (U s) a = g tao a)
    (horder : ∀ a, Balanced a → order a = 2 → ∑ t, g (U t) a = 0) :
    TaoArithmetic.OrderTwoValues (averageOtherFourier U s) := by
  intro a ha ho
  have hsum := horder a ha ho
  rw [Fin.sum_univ_succAbove _ s, hs a ha] at hsum
  have he : (∑ t : Fin 5, g (U (s.succAbove t)) a) = -g tao a := by
    linear_combination hsum
  rw [averageOtherFourier, he]
  ring

theorem averageOtherFourier_positive (U : Coord → CMatrix) (s : Coord)
    (hU : ∀ t, IsHadamard (U t)) :
    0 ≤ 6 + offDiagSum (fun i j =>
      (averageOtherFourier U s ((3 : ℤ) • difference i j)).re) := by
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun t _ =>
    cubic_fourier_nonnegative (hU (s.succAbove t)))
  have havg (a : Charge) : (averageOtherFourier U s a).re =
      (5 : ℝ)⁻¹ * ∑ t : Fin 5, (g (U (s.succAbove t)) a).re := by
    simp [averageOtherFourier, Complex.mul_re]
  have he : offDiagSum (fun i j =>
      (averageOtherFourier U s ((3 : ℤ) • difference i j)).re) =
      (5 : ℝ)⁻¹ * ∑ t : Fin 5, offDiagSum (fun i j =>
        (g (U (s.succAbove t)) ((3 : ℤ) • difference i j)).re) := by
    simp_rw [havg]
    calc
      _ = (5 : ℝ)⁻¹ * offDiagSum (fun i j => ∑ t : Fin 5,
          (g (U (s.succAbove t)) ((3 : ℤ) • difference i j)).re) := by
        simp only [offDiagSum, Finset.mul_sum]
      _ = _ := by rw [offDiagSum_sum]
  rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  norm_num at hsum ⊢
  linarith

theorem different_matrices_conjugated {H K : CMatrix} (hH : IsHadamard H)
    (hK : IsHadamard K)
    (hc : ∀ k l, Complex.normSq (∑ i, H i k * conj (K i l)) = 6) (a c : Charge) :
    offDiagSum (fun i j => g H (a + difference i j) * conj (g K (c + difference i j))) = 0 := by
  have h := different_matrices_identity hH hK hc a (-c)
  have he (i j : Coord) : -c + difference j i = -(c + difference i j) := by
    rw [difference_reverse j i]
    abel
  simpa only [he, g_neg hK] using h

theorem averageOtherFourier_cross (U : Coord → CMatrix) (s : Coord)
    (hU : ∀ t, IsHadamard (U t))
    (hc : ∀ t : Fin 5, ∀ k l,
      Complex.normSq (∑ i, U (s.succAbove t) i k * conj (tao i l)) = 6)
    (a c : Charge) :
    offDiagSum (fun i j => averageOtherFourier U s (a + difference i j) *
      conj (g tao (c + difference i j))) = 0 := by
  have he (i j : Coord) :
      averageOtherFourier U s (a + difference i j) * conj (g tao (c + difference i j)) =
      (5 : ℂ)⁻¹ * ∑ t : Fin 5,
        g (U (s.succAbove t)) (a + difference i j) * conj (g tao (c + difference i j)) := by
    rw [averageOtherFourier, mul_assoc, Finset.sum_mul]
  simp_rw [he]
  rw [offDiagSum_mul, offDiagSum_sum]
  have hz : (∑ t : Fin 5, offDiagSum (fun i j =>
      g (U (s.succAbove t)) (a + difference i j) * conj (g tao (c + difference i j)))) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    exact different_matrices_conjugated (hU _) tao_isHadamard (hc t) a c
  rw [hz, mul_zero]

/-- A full-equivalence copy of Tao in six candidate Hadamards supplies exactly
    the three hypotheses of the checked Tao certificate. -/
theorem equivalent_tao_average (H : Coord → CMatrix)
    (hH : ∀ t, IsHadamard (H t))
    (hcross : ∀ t s, t ≠ s → ∀ k l,
      Complex.normSq (∑ i, H t i k * conj (H s i l)) = 6)
    (horder : ∀ a, Balanced a → order a = 2 → ∑ t, g (H t) a = 0)
    (s : Coord) (heq : Equivalent (H s) tao) :
    ∃ f : Charge → ℂ,
      (∀ a c, Balanced a → Balanced c →
        offDiagSum (fun i j => f (a + difference i j) *
          star (g tao (c + difference i j))) = 0) ∧
      TaoArithmetic.OrderTwoValues f ∧
      0 ≤ 6 + offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) := by
  rcases heq with ⟨r, c, u, v, hu, hv, heq⟩
  let U : Coord → CMatrix := fun t => commonRowTransform (H t) r u
  have hU (t : Coord) : IsHadamard (U t) := commonRowTransform_isHadamard (hH t) r u hu
  have htao : tao = fun i j => U s i (c j) * v j := by
    funext i j
    exact heq i j
  have hs (a : Charge) (ha : Balanced a) : g (U s) a = g tao a := by
    calc
      _ = g (fun i j => U s i (c j)) a := (g_column_permutation (U s) c a).symm
      _ = g (fun i j => U s i (c j) * v j) a :=
        (g_column_phase (fun i j => U s i (c j)) v (fun j => unit_ne_zero (hv j)) a ha).symm
      _ = _ := by rw [htao]
  have hUorder (a : Charge) (ha : Balanced a) (ho : order a = 2) : ∑ t, g (U t) a = 0 := by
    change (∑ t, g (commonRowTransform (H t) r u) a) = 0
    simp_rw [g_commonRowTransform]
    rw [← Finset.mul_sum, horder _ (balanced_permute r.symm ha)
      (by rw [order_permute]; exact ho), mul_zero]
  have hUcross (t : Fin 5) (k l : Coord) :
      Complex.normSq (∑ i, U (s.succAbove t) i k * conj (tao i l)) = 6 := by
    calc
      _ = Complex.normSq (∑ i, U (s.succAbove t) i k * conj (U s i (c l) * v l)) := by
        rw [htao]
      _ = Complex.normSq (∑ i, U (s.succAbove t) i k * conj (U s i (c l))) :=
        columnTransform_cross (U (s.succAbove t)) (U s) c v hv k l
      _ = Complex.normSq (∑ i, H (s.succAbove t) i k * conj (H s i (c l))) := by
        rw [commonRowTransform_cross _ _ r u hu]
      _ = 6 := hcross _ _ (s.ne_succAbove t).symm k (c l)
  refine ⟨averageOtherFourier U s, ?_, averageOtherFourier_order_two U s hs hUorder,
    averageOtherFourier_positive U s hU⟩
  intro a c _ _
  exact averageOtherFourier_cross U s hU hUcross a c

end MUB6

end

end OAI
