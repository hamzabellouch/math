import OAI.Geometry.NodalSets.Coefficients.JetCoefficient

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def polynomialEikonal (g : Fin 4 → Fin 4 → CPoly) (p : CPoly) : CPoly :=
  (∑ i, ∑ j, g i j * (pderiv i p * pderiv j p)) + C 4

lemma gradientJet_polynomial (v : Fin 4 → ℂ) (p : CPoly)
    (hfirst : ∀ i, pderiv i (homogeneousComponent 1 p) = C (v i)) (k : ℕ) (i : Fin 4) :
    gradientJet v (polynomialJet p) k i = homogeneousComponent k (pderiv i p) := by
  rw [homogeneousComponent_pderiv]
  unfold gradientJet polynomialJet
  split_ifs with hk
  · subst k; exact (hfirst i).symm
  · rfl

lemma eikonal_convolution (g : Fin 4 → Fin 4 → CPoly) (p : CPoly) (d : ℕ) :
    (∑ r ∈ Finset.range (d + 1), ∑ t ∈ Finset.range (d - r + 1), ∑ i, ∑ j,
      homogeneousComponent r (g i j) * homogeneousComponent t (pderiv i p) *
        homogeneousComponent (d - r - t) (pderiv j p)) =
    homogeneousComponent d (∑ i, ∑ j, g i j * (pderiv i p * pderiv j p)) := by
  simp only [map_sum, homogeneousComponent_mul, Finset.mul_sum]
  simp only [mul_assoc]
  calc
    _ = ∑ r ∈ Finset.range (d + 1), ∑ i : Fin 4, ∑ j : Fin 4,
        ∑ t ∈ Finset.range (d - r + 1),
          homogeneousComponent r (g i j) * homogeneousComponent t (pderiv i p) *
            homogeneousComponent (d - r - t) (pderiv j p) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [mul_assoc]

theorem eikonalCoefficient_eq (v : Fin 4 → ℂ) (g : Fin 4 → Fin 4 → CPoly)
    (hmetric : ∀ i j, homogeneousComponent 0 (g i j) = if i = j then 1 else 0)
    (p : CPoly) (hfirst : ∀ i, pderiv i (homogeneousComponent 1 p) = C (v i)) (n : ℕ) :
    eikonalCoefficient v (fun r i j ↦ homogeneousComponent r (g i j)) n (polynomialJet p) =
      homogeneousComponent (n + 1) (polynomialEikonal g p) := by
  have he := eikonal_convolution g p (n + 1)
  rw [Finset.sum_range_succ'] at he
  simp only [Nat.sub_zero, hmetric] at he
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at he
  have hs : (∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1 - (r + 1) + 1), ∑ i, ∑ j,
      homogeneousComponent (r + 1) (g i j) * homogeneousComponent t (pderiv i p) *
        homogeneousComponent (n + 1 - (r + 1) - t) (pderiv j p)) =
      ∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1 - r), ∑ i, ∑ j,
        homogeneousComponent (r + 1) (g i j) * homogeneousComponent t (pderiv i p) *
          homogeneousComponent (n - r - t) (pderiv j p) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hnr : n + 1 - (r + 1) + 1 = n + 1 - r := by
      have := Finset.mem_range.mp hr
      omega
    rw [hnr, Nat.add_sub_add_right]
  rw [hs] at he
  unfold eikonalCoefficient
  simp_rw [gradientJet_polynomial v p hfirst]
  rw [show n + 1 + 1 = n + 2 by omega] at he
  rw [add_comm (G := CPoly)] at he
  rw [he, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _)]
  unfold polynomialEikonal
  rw [map_add, homogeneousComponent_of_mem (isHomogeneous_C (Fin 4) (4 : ℂ))]
  simp

theorem polynomial_eikonal_jets (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (g : Fin 4 → Fin 4 → CPoly)
    (hmetric : ∀ i j, homogeneousComponent 0 (g i j) = if i = j then 1 else 0)
    (initial : Jet) (hi : ∀ k, (initial k).IsHomogeneous k)
    (hfirst : ∀ i, pderiv i (initial 1) = C (v i))
    (hcenter : (∑ i, v i * v i) + 4 = 0)
    (hsecond : eikonalCoefficient v (fun r i j ↦ homogeneousComponent r (g i j)) 0 initial = 0)
    (steps : ℕ) :
    ∃ p : CPoly, (∀ k, k ≤ 2 → polynomialJet p k = initial k) ∧
      (∀ d, steps + 2 < d → homogeneousComponent d p = 0) ∧
      ∀ d, d ≤ steps + 1 → homogeneousComponent d (polynomialEikonal g p) = 0 := by
  obtain ⟨p, hkeep, hdegree, hsolve⟩ := finite_eikonal_polynomial v hv
    (fun r i j ↦ homogeneousComponent r (g i j)) initial hi hsecond steps
  have hpfirst : ∀ i, pderiv i (homogeneousComponent 1 p) = C (v i) := by
    intro i
    rw [show homogeneousComponent 1 p = initial 1 from hkeep 1 (by omega), hfirst]
  refine ⟨p, hkeep, hdegree, ?_⟩
  intro d hd
  cases d with
  | zero =>
    unfold polynomialEikonal
    have hc0 (a b : CPoly) : homogeneousComponent 0 (a * b) =
        homogeneousComponent 0 a * homogeneousComponent 0 b := by
      simpa using homogeneousComponent_mul a b 0
    simp only [map_add, map_sum, hc0, homogeneousComponent_pderiv, Nat.zero_add, hpfirst, hmetric]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [homogeneousComponent_eq_self (isHomogeneous_C (Fin 4) (4 : ℂ))]
    have he : (∑ i : Fin 4, C (v i) * C (v i)) + C 4 = (0 : CPoly) := by
      simpa only [map_add, map_sum, map_mul, map_zero] using congrArg C hcenter
    exact he
  | succ n =>
    rw [← eikonalCoefficient_eq v g hmetric p hpfirst n]
    exact hsolve n (by omega)

end
end Yau.Jets

end OAI
