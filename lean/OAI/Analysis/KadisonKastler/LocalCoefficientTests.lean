import OAI.Analysis.KadisonKastler.ReducingRestriction
import OAI.Analysis.FactorGeneration.Bicommutant

namespace OAI

/-! # Original-space coefficients from a reducing corner

Strong density of the restricted algebra gives finite coefficient
approximants in the original algebra. This step needs neither faithful
restriction nor norm bounds on the chosen coefficient approximants.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem exists_strong_coefficient_approx
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (V : Finset H) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : S, ∀ ξ ∈ V, ∀ η ∈ V,
      ‖inner ℂ η (((b : H →L[ℂ] H) - T) ξ)‖ < ε := by
  classical
  let C : ℝ := 1 + ∑ η ∈ V, ‖η‖
  have hC : 0 < C := by dsimp [C]; positivity
  have hηC (η : H) (hη : η ∈ V) : ‖η‖ ≤ C := by
    have h : ‖η‖ ≤ ∑ ζ ∈ V, ‖ζ‖ :=
      Finset.single_le_sum (fun ζ (_ : ζ ∈ V) => norm_nonneg ζ) hη
    dsimp [C]
    linarith only [h]
  obtain ⟨b, hb⟩ := Generator.bicommutant_finite_strong_approximation
    S T hT V (ε / C) (div_pos hε hC)
  refine ⟨b, ?_⟩
  intro ξ hξ η hη
  have hnorm : ‖((b : H →L[ℂ] H) - T) ξ‖ < ε / C := by
    simpa only [sub_apply, norm_sub_rev] using hb ξ hξ
  calc
    _ ≤ ‖η‖ * ‖((b : H →L[ℂ] H) - T) ξ‖ := norm_inner_le_norm _ _
    _ ≤ C * ‖((b : H →L[ℂ] H) - T) ξ‖ :=
      mul_le_mul_of_nonneg_right (hηC η hη) (norm_nonneg _)
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hnorm hC
    _ = ε := mul_div_cancel₀ ε hC.ne'

variable (K : Submodule ℂ H) [CompleteSpace K]
  (A B : StarSubalgebra ℂ (H →L[ℂ] H))
  (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
  (hB : ∀ b : B, ∀ x ∈ K, (b : H →L[ℂ] H) x ∈ K)

theorem exists_original_coefficient_approx
    (v : unitary (K →L[ℂ] K)) (a : A)
    (ha : unitaryConj v (reducingRestriction K A hA a) ∈
      Set.centralizer (Set.centralizer (Set.range (reducingRestriction K B hB))))
    (V : Finset H) (hV : ∀ ξ ∈ V, ξ ∈ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : B, ∀ ξ ∈ V, ∀ η ∈ V,
      ‖inner ℂ η (((b : H →L[ℂ] H) -
        unitaryConj (cornerUnitary K v) a.val) ξ)‖ < ε := by
  classical
  let W : Finset K := V.attach.image (fun ξ => ⟨ξ.val, hV ξ.val ξ.property⟩)
  let T := unitaryConj v (reducingRestriction K A hA a)
  let S : StarSubalgebra ℂ (K →L[ℂ] K) := (reducingRestriction K B hB).range
  have hS : (S : Set (K →L[ℂ] K)) = Set.range (reducingRestriction K B hB) := rfl
  have ha' : T ∈ Set.centralizer (Set.centralizer (S : Set (K →L[ℂ] K))) := by
    rw [hS]
    exact ha
  obtain ⟨c, hc⟩ := exists_strong_coefficient_approx (H := K) S T ha' W hε
  obtain ⟨b, hb⟩ := c.property
  change reducingRestriction K B hB b = (c : K →L[ℂ] K) at hb
  refine ⟨b, ?_⟩
  intro ξ hξ η hη
  let ξK : K := ⟨ξ, hV ξ hξ⟩
  let ηK : K := ⟨η, hV η hη⟩
  have hξW : ξK ∈ W := Finset.mem_image.mpr ⟨⟨ξ, hξ⟩, by simp, rfl⟩
  have hηW : ηK ∈ W := Finset.mem_image.mpr ⟨⟨η, hη⟩, by simp, rfl⟩
  have heq : inner ℂ η (((b : H →L[ℂ] H) -
      unitaryConj (cornerUnitary K v) a.val) ξ) =
      inner ℂ ηK (((c : K →L[ℂ] K) - T) ξK) := by
    rw [sub_apply, inner_sub_right]
    rw [show ξ = (ξK : H) from rfl,
      unitaryConj_cornerUnitary_apply K A hA v a ξK,
      ← reducingRestriction_coe_apply K B hB b ξK]
    rw [hb]
    simp only [sub_apply, inner_sub_right]
    rfl
  rw [heq]
  exact hc ξK hξW ηK hηW

end

end KadisonKastler

end OAI
