import OAI.Geometry.CylinderCovering.Angular.CubicFamily

namespace OAI

noncomputable section
namespace CylinderCovering.Cubic
open Set TriangularCovering

def scaledLowerFamily (ε : ℝ) (hε : 0 < ε) (j : Fin (n ε)) : TriCylinder :=
  TriangularCovering.lowerCylinder
    (family_node_strict (ceil_count_pos hε) j)
    (div_pos (family_cap_pos hε.le (node (n ε) j) (node (n ε) (j + 1))) (by norm_num : (0 : ℝ) < 2)) ε
    (alpha (node (n ε) j) (node (n ε) (j + 1)))
    (beta (node (n ε) j) (node (n ε) (j + 1)))

def scaledUpperFamily (ε : ℝ) (hε : 0 < ε) (j : Fin (n ε)) : TriCylinder :=
  TriangularCovering.upperCylinder
    (family_node_strict (ceil_count_pos hε) j)
    (div_pos (family_cap_pos hε.le (node (n ε) j) (node (n ε) (j + 1))) (by norm_num : (0 : ℝ) < 2)) ε
    (alpha (node (n ε) j) (node (n ε) (j + 1)))
    (beta (node (n ε) j) (node (n ε) (j + 1)))

def scaledFiniteFamily (ε : ℝ) (hε : 0 < ε) : Fin (2 * n ε) → TriCylinder :=
  (Fin.append (scaledLowerFamily ε hε) (scaledUpperFamily ε hε)) ∘ Fin.cast (two_mul (n ε))

lemma scaledFiniteFamily_covers {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 2) :
    Covers (scaledFiniteFamily ε hε) := by
  rintro p ⟨x, y, t, _ht0, _ht1, hx, hy, rfl⟩
  have hx4 : |2 * x| ≤ 1 - (2 * t - 1) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hy4 : |2 * y| ≤ 1 + (2 * t - 1) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  rcases finite_coordinate_cover_ceil hε hsmall hx4 hy4 with
    ⟨j, hj, hl⟩ | ⟨j, hj, hu⟩
  · refine ⟨Fin.cast (two_mul (n ε)).symm
      (Fin.castAdd (n ε) (⟨j, hj⟩ : Fin (n ε))), ?_⟩
    simp only [scaledFiniteFamily, Function.comp_apply, Fin.cast_cast,
      Fin.cast_eq_self, Fin.append_left]
    apply TriangularCovering.lowerCylinder_hit
    · have := hl.1.1
      dsimp only [n] at this ⊢
      nlinarith only [this]
    · have := hl.2
      dsimp only [n] at this ⊢
      nlinarith only [this]
    · have := hl.1.2.1
      dsimp only [n] at this ⊢
      nlinarith only [this]
    · have := hl.1.2.2
      dsimp only [n] at this ⊢
      nlinarith only [this]
  · refine ⟨Fin.cast (two_mul (n ε)).symm
      (Fin.natAdd (n ε) (⟨j, hj⟩ : Fin (n ε))), ?_⟩
    simp only [scaledFiniteFamily, Function.comp_apply, Fin.cast_cast,
      Fin.cast_eq_self, Fin.append_right]
    apply TriangularCovering.upperCylinder_hit
    · have := hu.1.1
      dsimp only [n] at this ⊢
      nlinarith only [this]
    · have := hu.2
      dsimp only [n] at this ⊢
      nlinarith only [this]
    · have := hu.1.2.1
      dsimp only [n] at this ⊢
      nlinarith only [this]
    · have := hu.1.2.2
      dsimp only [n] at this ⊢
      nlinarith only [this]

lemma scaledFiniteFamily_total (ε : ℝ) (hε : 0 < ε) :
    totalArea (scaledFiniteFamily ε hε) = cubicCost ε / 4 := by
  have hs : totalArea (scaledFiniteFamily ε hε) =
      (∑ j : Fin (n ε), area (scaledLowerFamily ε hε j).base) +
      (∑ j : Fin (n ε), area (scaledUpperFamily ε hε j).base) := by
    change (∑ i : Fin (2 * n ε),
      (fun k : Fin (n ε + n ε) =>
        area (Fin.append (scaledLowerFamily ε hε) (scaledUpperFamily ε hε) k).base)
        ((finCongr (two_mul (n ε))) i)) = _
    rw [Equiv.sum_comp (finCongr (two_mul (n ε)))
      (fun k => area (Fin.append (scaledLowerFamily ε hε) (scaledUpperFamily ε hε) k).base)]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hs, ← Finset.sum_add_distrib, cubicCost, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [scaledLowerFamily, scaledUpperFamily, TriangularCovering.lowerCylinder_area,
    TriangularCovering.upperCylinder_area, node_succ]
  dsimp only [n]
  ring

lemma scaled_count_eq (τ : ℝ) : n (τ / 2) = ⌈8 / τ ^ 2⌉₊ := by
  unfold n
  congr 1
  ring

lemma scaled_cap_eq (τ a b : ℝ) :
    cap (τ / 2) a b / 2 =
      1 / 2 + τ ^ 2 * (profileMax a b / 8 + (25 / 4 : ℝ) * τ) := by
  unfold cap
  ring

lemma scaledFiniteFamily_prescribed (ε : ℝ) (hε : 0 < ε) :
    ScaledPrescribedFamily ε (n ε) (scaledFiniteFamily ε hε) := by
  intro j
  simp only [lowerIndexN, upperIndexN, scaledFiniteFamily, Function.comp_apply,
    Fin.cast_cast, Fin.cast_eq_self, Fin.append_left, Fin.append_right]
  exact ⟨rfl, rfl, rfl, rfl⟩

lemma scaledLowerInterceptVertices_contraction (ε a b : ℝ) (i : Fin 3) :
    scaledLowerInterceptVertices ε a b i =
      point 0 0 (1 / 2) + (1 / 2 : ℝ) • lowerInterceptVertices ε a b i := by
  ext k
  fin_cases i <;> fin_cases k <;>
    dsimp [scaledLowerInterceptVertices, lowerInterceptVertices, point] <;> ring

lemma scaledUpperInterceptVertices_contraction (ε a b : ℝ) (i : Fin 3) :
    scaledUpperInterceptVertices ε a b i =
      point 0 0 (1 / 2) + (1 / 2 : ℝ) • upperInterceptVertices ε a b i := by
  ext k
  fin_cases i <;> fin_cases k <;>
    dsimp [scaledUpperInterceptVertices, upperInterceptVertices, point] <;> ring

theorem scaledFiniteCover_proof : ScaledFiniteCoverStatement := by
  intro τ hτ hsmall
  have hε : 0 < τ / 2 := by linarith
  have hεsmall : τ / 2 ≤ 1 / 2 := by linarith
  have h : ∃ c : Fin (2 * n (τ / 2)) → TriCylinder,
      Covers c ∧ totalArea c = cubicCost (τ / 2) / 4 ∧
      ScaledPrescribedFamily (τ / 2) (n (τ / 2)) c :=
    ⟨scaledFiniteFamily (τ / 2) hε, scaledFiniteFamily_covers hε hεsmall,
      scaledFiniteFamily_total (τ / 2) hε, scaledFiniteFamily_prescribed (τ / 2) hε⟩
  rw [scaled_count_eq] at h
  exact h

end CylinderCovering.Cubic

end

end OAI
