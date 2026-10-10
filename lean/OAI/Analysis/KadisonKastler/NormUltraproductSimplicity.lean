import OAI.Analysis.KadisonKastler.NormUltraproduct
import OAI.Analysis.KadisonKastler.PublishedSimpleDerivation

namespace OAI

/-! # A concrete uniform-fullness criterion for the norm ultraproduct

A coordinate compression estimate implies simplicity of the norm
ultraproduct. For type III factors, this estimate follows from projection
comparison.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

theorem exists_eventually_norm_lower_bound (ω : Ultrafilter ℕ)
    (X : VaryingBoundedSequence B) (hX : normUltraproductMap B ω X ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ j in (ω : Filter ℕ), ε ≤ ‖X j‖ := by
  by_contra h
  have hsmall (ε : ℝ) (hε : 0 < ε) : ∀ᶠ j in (ω : Filter ℕ), ‖X j‖ < ε := by
    have hn : ¬∀ᶠ j in (ω : Filter ℕ), ε ≤ ‖X j‖ := fun hj => h ⟨ε, hε, hj⟩
    simpa only [not_le] using (Ultrafilter.eventually_not.mpr hn)
  apply hX
  apply (normUltraproductMap_eq_zero_iff B ω X).mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  simpa only [dist_zero_right, norm_norm] using hsmall ε hε

/-- Uniform coordinate compression to `1` makes every nonzero ideal of
the norm ultraproduct contain `1`. This proves even algebraic simplicity. -/
theorem normUltraproduct_simple_of_uniform_fullness
    (hfull : ∀ ε R : ℝ, 0 < ε → 0 ≤ R → ∃ K : ℝ, 0 ≤ K ∧
      ∀ j (x : B j), ε ≤ ‖x‖ → ‖x‖ ≤ R → ∃ b c : B j,
        ‖b‖ ≤ K ∧ ‖c‖ ≤ K ∧ b * x * c = 1)
    (ω : Ultrafilter ℕ) : CStarSimple (NormUltraproduct B ω) := by
  intro I _
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hex : ∃ a : NormUltraproduct B ω, a ∈ I ∧ a ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hI
    apply le_antisymm _ bot_le
    intro a ha
    simpa only [TwoSidedIdeal.mem_bot] using hn a ha
  obtain ⟨a, ha, hane⟩ := hex
  obtain ⟨X, hX⟩ := normUltraproductMap_surjective B ω a
  obtain ⟨ε, hε, hlarge⟩ := exists_eventually_norm_lower_bound ω X (hX ▸ hane)
  obtain ⟨K, hK, hcompress⟩ := hfull ε ‖X‖ hε (norm_nonneg X)
  have hchoices : ∀ j, ∃ b c : B j, ‖b‖ ≤ K ∧ ‖c‖ ≤ K ∧
      (ε ≤ ‖X j‖ → b * X j * c = 1) := by
    intro j
    by_cases hj : ε ≤ ‖X j‖
    · obtain ⟨b, c, hb, hc, heq⟩ := hcompress j (X j) hj (varyingSequence_norm_apply_le X j)
      exact ⟨b, c, hb, hc, fun _ => heq⟩
    · exact ⟨0, 0, by simpa using hK, by simpa using hK, fun h => (hj h).elim⟩
  choose b c hb hc hbc using hchoices
  let bSeq : VaryingBoundedSequence B :=
    ⟨b, memℓp_infty ⟨K, by rintro _ ⟨j, rfl⟩; exact hb j⟩⟩
  let cSeq : VaryingBoundedSequence B :=
    ⟨c, memℓp_infty ⟨K, by rintro _ ⟨j, rfl⟩; exact hc j⟩⟩
  have hnull : NormNullSequence B ω (bSeq * X * cSeq - 1) := by
    have heq : (fun j => ‖(bSeq * X * cSeq - 1) j‖) =ᶠ[(ω : Filter ℕ)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hlarge] with j hj
      change ‖b j * X j * c j - 1‖ = 0
      rw [hbc j hj, sub_self, norm_zero]
    exact tendsto_const_nhds.congr' heq.symm
  have hone : normUltraproductMap B ω bSeq * a * normUltraproductMap B ω cSeq = 1 := by
    have hz := (normUltraproductMap_eq_zero_iff B ω _).mpr hnull
    rw [map_sub, map_mul, map_mul, map_one, hX] at hz
    exact sub_eq_zero.mp hz
  apply I.eq_top
  rw [← hone]
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)

end

end KadisonKastler

end OAI
