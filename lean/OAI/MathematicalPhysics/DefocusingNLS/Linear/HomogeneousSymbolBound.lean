import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDyadicSeries
import Mathlib.Analysis.LocallyConvex.WithSeminorms

namespace OAI

/-! # Finite Schwartz-jet control for normalized profile pieces

Continuity of the actual Schwartz-to-Y embedding reduces the remaining
annular estimate to finitely many weighted physical derivatives.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_homogeneousSymbolJet_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : 𝓢(E, ℂ)) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ x : E, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ψ x‖ ≤ D) →
      ‖homogeneousSchwartzEmbedding a k ha ha1 hk ψ‖ ≤ C * D := by
  let T := (homogeneousSchwartzEmbedding a k ha ha1 hk).restrictScalars ℝ
  let q : Seminorm ℝ 𝓢(E, ℂ) := (normSeminorm ℝ (HomogeneousY a k)).comp T.toLinearMap
  have hq : Continuous q := T.continuous.norm
  obtain ⟨S, C, _, hC⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ E ℂ) q hq
  let N := S.sup (fun p : ℕ × ℕ => max p.1 p.2)
  refine ⟨N, C, C.coe_nonneg, ?_⟩
  intro ψ D hD hjet
  have hsemi : ∀ p ∈ S, schwartzSeminormFamily ℝ E ℂ p ψ ≤ D := by
    intro p hp
    have hpN : max p.1 p.2 ≤ N := Finset.le_sup (f := fun q : ℕ × ℕ => max q.1 q.2) hp
    have hi : p.1 ≤ N := (le_max_left _ _).trans hpN
    have hn : p.2 ≤ N := (le_max_right _ _).trans hpN
    apply SchwartzMap.seminorm_le_bound ℝ p.1 p.2 ψ hD
    intro x
    have hweight : ‖x‖ ^ p.1 ≤ (1 + ‖x‖) ^ N := by
      calc
        _ ≤ (1 + ‖x‖) ^ p.1 := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        _ ≤ _ := pow_le_pow_right₀ (by linarith [norm_nonneg x]) hi
    exact (mul_le_mul_of_nonneg_right hweight (norm_nonneg _)).trans (hjet p.2 hn x)
  have hsup : S.sup (schwartzSeminormFamily ℝ E ℂ) ψ ≤ D := by
    exact Seminorm.finset_sup_apply_le hD hsemi
  have hb := hC ψ
  change ‖homogeneousSchwartzEmbedding a k ha ha1 hk ψ‖ ≤ (C : ℝ) * _ at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hsup C.coe_nonneg)

/-- Uniform jets of the normalized annuli suffice for the dyadic Y reconstruction. -/
theorem exists_homogeneous_from_schwartz_annuli (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : ℕ → 𝓢(E, ℂ)) (D : ℝ), 0 ≤ D →
      (∀ j n, n ≤ N → ∀ x : E,
        (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (ψ j) x‖ ≤ D) →
      ∃ q : HomogeneousY a k,
        (∀ y : E, homogeneousPhysicalCLM a k ha ha1 hk q y =
          ∑' j, (((2 : ℝ) ^ j) ^ (-2 * a) : ℝ) * ψ j (((2 : ℝ) ^ j)⁻¹ • y)) ∧
        ‖q‖ ≤ C * D / (1 - 2 ^ (-a)) := by
  obtain ⟨N, C, hC, hCb⟩ := exists_homogeneousSymbolJet_bound a k ha ha1 hk
  refine ⟨N, C, hC, ?_⟩
  intro ψ D hD hjet
  let v : ℕ → HomogeneousY a k := fun j => homogeneousSchwartzEmbedding a k ha ha1 hk (ψ j)
  have hv : ∀ j, ‖v j‖ ≤ C * D := fun j => hCb (ψ j) D hD (hjet j)
  refine ⟨∑' j, homogeneousDyadicPiece a k ha ha1 hk v j, ?_,
    homogeneousDyadicSeries_norm_le a k ha ha1 hk v (C * D) hv⟩
  intro y
  rw [homogeneousDyadicSeries_physical a k ha ha1 hk v (C * D) hv]
  apply tsum_congr
  intro j
  rw [show v j = homogeneousSchwartzEmbedding a k ha ha1 hk (ψ j) from rfl,
    homogeneousPhysicalCLM_Schwartz]

end DefocusingNLS

end OAI
