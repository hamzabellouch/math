import OAI.Analysis.SeparableQuotients.Positive.SeparatedFamilies

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal
universe u

namespace SeparableQuotient.Positive.Family
open Set MeasureTheory TopologicalSpace Function
open scoped Cardinal
universe v
attribute [local instance] realSpaceRatSpace realSpaceRatTower




theorem continuum_large_density_family {Y : Type v} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (D : Set Y) (hne : D.Nonempty)
    (hcard : Cardinal.mk D ≤ Cardinal.continuum.{v})
    (hdense : ∀ A : Set D, Dense A → Cardinal.continuum.{v} ≤ Cardinal.mk A)
    (μ : Measure ContinuumIndex) [IsProbabilityMeasure μ]
    (hadd : ContinuumAdditive μ) (hsingle : ∀ i, μ {i} = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ h : ContinuumIndex → StrongDual ℝ Y,
      (∀ α, ‖h α‖ = 1) ∧
      (∀ α, ∃ y ∈ D, ε < |h α y|) ∧
      ∀ y ∈ D, μ {α | h α y ≠ 0} = 0 := by
  classical
  let : Nonempty D := hne.to_subtype
  have hreg : Cardinal.IsRegular Cardinal.continuum.{v} := by
    simpa using (continuum_regular μ hadd hsingle).lift.{v}
  obtain ⟨δ, hδ, S₀, hsep₀, hS₀⟩ := exists_large_separated_of_density hreg
    Cardinal.aleph0_lt_continuum hdense
  let S : Set Y := Subtype.val '' S₀
  have hsep : S.Pairwise (fun x y => δ < dist x y) := by
    rintro x ⟨x', hx, rfl⟩ y ⟨y', hy, rfl⟩ hxy
    exact hsep₀ hx hy (by intro h; exact hxy (congrArg Subtype.val h))
  have hS : Cardinal.continuum.{v} ≤ Cardinal.mk S := by
    have heq : Cardinal.mk S = Cardinal.mk S₀ :=
      Cardinal.mk_congr (Equiv.Set.image _ _ Subtype.val_injective).symm
    rw [heq]
    exact hS₀
  obtain ⟨e⟩ : Nonempty (D ↪ ContinuumIndex) := Cardinal.lift_mk_le'.mp (by
    simpa [ContinuumIndex] using hcard)
  let z : ContinuumIndex → D := Function.invFun e
  have hz : Function.Surjective z := (Function.leftInverse_invFun e.injective).surjective
  let y : ContinuumIndex → Y := fun α => z α
  let P : ContinuumIndex → Set Y := fun α => y '' Set.Iio α
  let M : ContinuumIndex → Submodule ℝ Y := fun α => (Submodule.span ℝ (P α)).topologicalClosure
  have hP (α : ContinuumIndex) : Cardinal.mk (P α) < Cardinal.continuum.{v} := by
    have hc : Cardinal.mk (Set.Iio α) < Cardinal.continuum.{0} := by
      simpa [ContinuumIndex] using Cardinal.mk_Iio_lt α (by simp [ContinuumIndex])
    have him : Cardinal.mk (P α) ≤ Cardinal.lift.{v} (Cardinal.mk (Set.Iio α)) := by
      simpa [P] using (Cardinal.mk_image_le_lift (f := y) (s := Set.Iio α))
    exact him.trans_lt (Cardinal.lift_lt_continuum.mpr hc)
  have hc (α : ContinuumIndex) :
      ∃ h : StrongDual ℝ Y, ‖h‖ = 1 ∧ (∀ m ∈ M α, h m = 0) ∧
        ∃ y ∈ D, δ / 4 < |h y| := by
    let A : Set Y := Submodule.span ℚ (P α)
    have hA : Cardinal.mk A < Cardinal.continuum.{v} :=
      (card_rat_span_le (P α)).trans_lt (max_lt (hP α) Cardinal.aleph0_lt_continuum)
    have hAne : A.Nonempty := ⟨0, Submodule.zero_mem _⟩
    obtain ⟨x, hx, hdist⟩ := large_separated_away_small_closure hδ hsep hS hA hAne
    have hdist' : δ / 4 < Metric.infDist x (M α : Set Y) := by
      simpa only [A, closure_rat_span_eq_real, M, Submodule.topologicalClosure_coe] using hdist
    obtain ⟨h, hh, hann, hval⟩ := exists_unit_dual_annihilating (M α) x (by positivity) hdist'
    refine ⟨h, hh, hann, x, ?_, hval⟩
    rcases hx with ⟨x', _, rfl⟩
    exact x'.property
  choose h hnorm hann hval using hc
  refine ⟨δ / 4, by positivity, h, hnorm, hval, ?_⟩
  intro w hw
  obtain ⟨β, hβ⟩ := hz ⟨w, hw⟩
  have hsubset : {α | h α w ≠ 0} ⊆ Set.Iic β := by
    intro α hα
    by_contra hn
    have hβα : β < α := lt_of_not_ge hn
    apply hα
    apply hann α
    apply (Submodule.span ℝ (P α)).le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨β, hβα, congrArg Subtype.val hβ⟩
  apply measure_mono_null hsubset
  rw [← Set.Iio_union_right]
  exact measure_union_null
    (small_set_null μ hadd hsingle _ (by simpa [ContinuumIndex] using Cardinal.mk_Iio_lt β (by simp [ContinuumIndex])))
    (hsingle β)
end SeparableQuotient.Positive.Family

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal
universe u

namespace SeparableQuotient.Positive.Family
open Set TopologicalSpace MeasureTheory
open scoped Cardinal

lemma real_dual_cardinal_le {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SeparableSpace E] :
    Cardinal.mk (StrongDual ℝ E) ≤ Cardinal.continuum.{u} := by
  obtain ⟨d, hd⟩ := exists_dense_seq E
  let j : StrongDual ℝ E → ULift.{u} (ℕ → ℝ) := fun f => ULift.up (fun n => f (d n))
  have hj : Function.Injective j := by
    intro f g hfg
    have he : ∀ n, f (d n) = g (d n) := fun n => congrFun (congrArg ULift.down hfg) n
    exact DFunLike.ext' (hd.equalizer f.continuous g.continuous (funext he))
  exact (Cardinal.mk_le_of_injective hj).trans_eq (by simp [Cardinal.mk_real])

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
local instance dualSubmoduleNormedGroup (E : Submodule ℝ (StrongDual ℝ X)) :
    NormedAddCommGroup E := Submodule.normedAddCommGroup E
local instance dualSubmoduleNormedSpace (E : Submodule ℝ (StrongDual ℝ X)) :
    NormedSpace ℝ E := Submodule.normedSpace E

def evaluation (E : Submodule ℝ (StrongDual ℝ X)) : X →L[ℝ] StrongDual ℝ E :=
  E.subtypeL.flip

lemma norm_evaluation_le (E : Submodule ℝ (StrongDual ℝ X)) : ‖evaluation E‖ ≤ 1 := by
  rw [evaluation, ContinuousLinearMap.opNorm_flip]
  exact Submodule.norm_subtypeL_le E



theorem evaluation_family_of_density (E : Submodule ℝ (StrongDual ℝ X))
    [SeparableSpace E]
    (μ : Measure ContinuumIndex) [IsProbabilityMeasure μ]
    (hadd : ContinuumAdditive μ) (hsingle : ∀ i, μ {i} = 0)
    (hdense : ∀ A : Set (evaluation E '' {x : X | ‖x‖ ≤ 1}), Dense A →
      Cardinal.continuum.{u} ≤ Cardinal.mk A) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ h : ContinuumIndex → StrongDual ℝ (StrongDual ℝ E),
      (∀ α, ‖h α‖ = 1) ∧
      (∀ α, ε < ‖(h α).comp (evaluation E)‖ ∧ ‖(h α).comp (evaluation E)‖ ≤ 1) ∧
      ∀ x : X, ‖x‖ ≤ 1 → μ {α | h α (evaluation E x) ≠ 0} = 0 := by
  let D := evaluation E '' {x : X | ‖x‖ ≤ 1}
  have hne : D.Nonempty := ⟨0, 0, by simp, by simp⟩
  have hc : Cardinal.mk D ≤ Cardinal.continuum.{u} :=
    (Cardinal.mk_set_le D).trans real_dual_cardinal_le
  obtain ⟨ε, hε, h, hn, hv, hz⟩ :=
    continuum_large_density_family D hne hc hdense μ hadd hsingle
  refine ⟨ε, hε, h, hn, fun α => ?_, fun x hx => hz _ ⟨x, hx, rfl⟩⟩
  constructor
  · obtain ⟨y, ⟨x, hx, rfl⟩, hval⟩ := hv α
    exact hval.trans_le (by
      simpa only [Real.norm_eq_abs, mul_one, ContinuousLinearMap.comp_apply] using
        ((h α).comp (evaluation E)).le_opNorm_of_le hx)
  · exact ((h α).opNorm_comp_le (evaluation E)).trans (by
      simpa only [hn α, one_mul] using norm_evaluation_le E)

end SeparableQuotient.Positive.Family

end

end

end OAI
