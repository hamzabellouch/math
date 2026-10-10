import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetNormalize
import OAI.Probability.Ballisticity.Estimates.SingleThreat

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeBudgetEndpointLaw_rows {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (x : Fin k → Lattice d) (S : Set (Lattice d))
    (hx : ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω => relativeBudgetEndpointLaw e f H r ω x) := by
  exact (Measure.measurable_map _ (measurable_of_countable _)).comp
    (relativeBudgetWordLaw_rows e f H r x S hx)

lemma budgetEndpointMixture_joint_rows {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (C : Set (Fin k → Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S) :
    @Measurable (SupportedTupleMeasures C × Environment d) (Measure (Fin k → Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => budgetEndpointMixture e f H r p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [budgetEndpointMixture_apply,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ C
  · exact (((Measure.measurable_coe hA).comp
      (relativeBudgetEndpointLaw_rows e f H r x S (hC x hx))).comp measurable_snd).mul
      ((Measure.measurable_coe (measurableSet_singleton x)).comp
        (measurable_subtype_coe.comp measurable_fst))
  · have he : (fun p : SupportedTupleMeasures C × Environment d =>
        relativeBudgetEndpointLaw e f H r p.2 x A*p.1.val {x}) = fun _ => 0 := by
      funext p
      rw [supportedTupleMeasures_singleton C p.1 hx,mul_zero]
    rw [he]
    exact measurable_const

lemma budgetProfileMass_joint_rows {d k : ℕ} (e f : Direction d) (a G : ℝ)
    (H : ℕ) (r : ℝ) (S : Set (Lattice d))
    (hS : ∀ x ∈ TupleAtHeight (k:=k) (realPosition (step e)) a,
      ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S) :
    @Measurable (BudgetProfile (k:=k) e f a G × Environment d) ℝ
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => relativeBudgetMass e f H r p.1.val p.2) := by
  have hm := (relativeBudgetMassENN_joint_rows e f H r _ S hS).comp
    (((BudgetProfile.measurable_toSupported e f a G).comp measurable_fst).prodMk measurable_snd)
  have he : (fun p : BudgetProfile (k:=k) e f a G × Environment d =>
      relativeBudgetMass e f H r p.1.val p.2) =
      fun p => (relativeBudgetMassENN e f H r p.1.val p.2).toReal := by
    funext p; exact (relativeBudgetMassENN_toReal e f H r _ _).symm
  rw [he]
  exact hm.ennreal_toReal

lemma nextBudgetProfile_measurable_rows {d k : ℕ} (e f : Direction d) (a G r : ℝ)
    (hr : 0 ≤ r) (H : ℕ) (S : Set (Lattice d))
    (hS : ∀ x ∈ TupleAtHeight (k:=k) (realPosition (step e)) a,
      ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma S) _ π) :
    @Measurable _ _ (rowSigma S) _ (fun ω => nextBudgetProfile e f H a G r hr (π ω) ω) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  have hm := (budgetEndpointMixture_joint_rows e f H r _ S hS).comp
    (((BudgetProfile.measurable_toSupported e f a G).comp hπ).prodMk measurable_id)
  have hρ := (Measure.measurable_map (tupleShiftUp e H) (measurable_of_countable _)).comp
    (measurable_subtype_coe.comp hπ)
  exact (measurable_normalizeOr _ _ hm hρ).subtype_mk

lemma nextBudgetProfile_measurable_below {d k : ℕ} (e f : Direction d) (a G r : ℝ)
    (hr : 0 ≤ r) (H : ℕ)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+H))) _
      (fun ω => nextBudgetProfile e f H a G r hr (π ω) ω) := by
  apply nextBudgetProfile_measurable_rows
  · intro x hx j y hy
    change dot (realPosition y) (realPosition (step e)) < a+H
    simpa only [hx j] using hy.2
  · exact hπ.mono (rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < a+H
      have hn : (0:ℝ) ≤ H := Nat.cast_nonneg H
      exact lt_of_lt_of_le hx (le_add_of_nonneg_right hn))) le_rfl

lemma measurableSet_profileBudgetThreat_upper {d k : ℕ} (e f : Direction d)
    (a G r s : ℝ) (H : ℕ) :
    @MeasurableSet (BudgetProfile (k:=k) e f a G × Environment d)
      (MeasurableSpace.prod inferInstance (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}))
      {p | p.2 ∈ budgetThreatEvent e f H r p.1.val s} := by
  let : MeasurableSpace (Environment d) := rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}
  change MeasurableSet {p : BudgetProfile (k:=k) e f a G × Environment d |
    ∃ h ≤ H, relativeBudgetMass e f h r p.1.val p.2 < s}
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion; intro h
  by_cases hh : h ≤ H
  · simp only [hh,true_and]
    apply measurableSet_lt _ measurable_const
    apply budgetProfileMass_joint_rows
    intro x hx j y hy
    change a ≤ dot (realPosition y) (realPosition (step e))
    simpa only [hx j] using hy.1
  · simp only [hh,false_and,Set.ofPred_false]
    exact MeasurableSet.empty

lemma fresh_random_budget_threat {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a G r s : ℝ) (H : ℕ)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (c : ℝ≥0∞)
    (hbound : ∀ η ∈ A, environmentLaw ν (budgetThreatEvent e f H r (π η).val s) ≤ c) :
    environmentLaw ν {ω | ω ∈ A ∧ ω ∈ budgetThreatEvent e f H r (π ω).val s} ≤
      c*environmentLaw ν A := by
  let S := BelowHeight (realPosition (step e)) a
  let T : Set (Lattice d) := {y | a ≤ dot (realPosition y) (realPosition (step e))}
  let B : Set (Environment d × Environment d) := {p | p.2 ∈ budgetThreatEvent e f H r (π p.1).val s}
  have hB : @MeasurableSet (Environment d × Environment d)
      (MeasurableSpace.prod (rowSigma S) (rowSigma T)) B :=
    (measurableSet_profileBudgetThreat_upper e f a G r s H).preimage
      ((hπ.comp measurable_fst).prodMk measurable_snd)
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb (η : Environment d) (hη : η ∈ A) :
      (@Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν))
        {ω | (η,ω) ∈ B} ≤ c := by
    rw [show {ω | (η,ω) ∈ B}=Prod.mk η ⁻¹' B from rfl,
      Measure.map_apply hV (hB.preimage measurable_prodMk_left)]
    exact hbound η hη
  apply @fresh_rows_random_test_bound d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
    ν _ S T _ id id measurable_id measurable_id A hA B hB c hb
  exact Set.disjoint_left.mpr fun x hx hy =>
    (not_lt.mpr (show a ≤ dot (realPosition x) (realPosition (step e)) from hy))
      (show dot (realPosition x) (realPosition (step e)) < a from hx)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma rawTupleEndpointLaw_rows {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (x : Fin k → Lattice d) (S : Set (Lattice d)) (hS : ∀ j, Strip ℓ (x j) H⊆S) :
    @Measurable _ _ (rowSigma S) _ (fun ω => rawTupleEndpointLaw ℓ H ω x) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply TupleKernel.measurable_countable_measure
  intro y
  simp only [rawTupleEndpointLaw_singleton]
  apply Finset.measurable_prod
  intro j _
  have he : (fun ω => variableHitKernel ℓ H (ω,x j)) = fun ω =>
      (rawWordLaw ℓ H ω (x j)).map (fun w => wordPath (x j) w w.length) := by
    funext ω; exact (rawWordLaw_endpoint ℓ H ω (x j)).symm
  have hm : Measurable (fun ω => variableHitKernel ℓ H (ω,x j)) := by
    rw [he]
    exact (Measure.measurable_map _ (measurable_of_countable _)).comp
      ((measurable_rawWordLaw_rows ℓ H (x j)).mono (rowSigma_mono (hS j)) le_rfl)
  exact (Measure.measurable_coe (measurableSet_singleton _)).comp hm

lemma rawTupleMixture_joint_rows {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (C : Set (Fin k → Lattice d)) (S : Set (Lattice d))
    (hS : ∀ x∈C, ∀ j, Strip ℓ (x j) H⊆S) :
    @Measurable (SupportedTupleMeasures C×Environment d) (Measure (Fin k → Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => rawTupleMixture ℓ H p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply Measure.measurable_of_measurable_coe
  intro U _
  simp only [rawTupleMixture_apply,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x∈C
  · exact (((Measure.measurable_coe (Set.to_countable _).measurableSet).comp
      (rawTupleEndpointLaw_rows ℓ H x S (hS x hx))).comp measurable_snd).mul
        ((Measure.measurable_coe (measurableSet_singleton x)).comp (measurable_subtype_coe.comp measurable_fst))
  · simp only [supportedTupleMeasures_singleton C _ hx,mul_zero]
    exact measurable_const

lemma rawTupleEndpointLaw_support {d k : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) (a : ℝ)
    (hx : x∈TupleAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂rawTupleEndpointLaw (realPosition (step e)) H ω x,
      y∈TupleAtHeight (realPosition (step e)) (a+H) := by
  apply ae_all_iff.mpr
  intro j
  have hs := (Measure.tendsto_eval_ae_ae (μ:=fun j : Fin k => variableHitKernel (realPosition (step e)) H (ω,x j)) (i:=j)).eventually (coordinate_hitKernel_supported e (x j) H ω)
  apply hs.mono
  intro y hy
  rw [signedHeight_projection,hy,Int.cast_add,Int.cast_natCast,← signedHeight_projection,hx j]

lemma rawTupleMixture_support {d k : ℕ} (e : Direction d) (H : ℕ) (a : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d)
    (hπ : ∀ᵐ x ∂π, x∈TupleAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂rawTupleMixture (realPosition (step e)) H π ω,
      y∈TupleAtHeight (realPosition (step e)) (a+H) := by
  apply TupleKernel.countable_bind_ae
  exact hπ.mono fun x hx => rawTupleEndpointLaw_support e H ω x a hx

lemma rawTupleMixture_univ_le {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    rawTupleMixture ℓ H π ω Set.univ≤π Set.univ := by
  rw [rawTupleMixture_apply]
  exact (lintegral_mono fun x => rawTupleEndpointLaw_le_one ℓ H ω x).trans_eq (by simp)

instance rawTupleMixture_finite {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] (ω : Environment d) :
    IsFiniteMeasure (rawTupleMixture ℓ H π ω) :=
  ⟨lt_of_le_of_lt (rawTupleMixture_univ_le ℓ H π ω) (measure_lt_top _ _)⟩

abbrev LayerTupleProfile {d k : ℕ} (e : Direction d) (a : ℝ) :=
  {π : Measure (Fin k → Lattice d) // IsProbabilityMeasure π ∧
    ∀ᵐ x ∂π, x∈TupleAtHeight (realPosition (step e)) a}

instance layerTupleProfile_probability {d k : ℕ} (e : Direction d) (a : ℝ)
    (π : LayerTupleProfile (k:=k) e a) : IsProbabilityMeasure π.val := π.property.1

def LayerTupleProfile.toSupported {d k : ℕ} {e : Direction d} {a : ℝ}
    (π : LayerTupleProfile (k:=k) e a) : SupportedTupleMeasures (TupleAtHeight (k:=k) (realPosition (step e)) a) :=
  ⟨π.val,ae_iff.mp π.property.2⟩

lemma LayerTupleProfile.measurable_toSupported {d k : ℕ} (e : Direction d) (a : ℝ) :
    Measurable (LayerTupleProfile.toSupported (k:=k) (e:=e) (a:=a)) := measurable_subtype_coe.subtype_mk

def BudgetProfile.toLayerProfile {d k : ℕ} {e f : Direction d} {a G : ℝ}
    (π : BudgetProfile (k:=k) e f a G) : LayerTupleProfile (k:=k) e a :=
  ⟨π.val,π.property.1,π.property.2.mono fun _ h => h.1⟩

noncomputable def fullTupleProfile {d k : ℕ} (e : Direction d) (a : ℝ) (H : ℕ)
    (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) : LayerTupleProfile (k:=k) e (a+H) := by
  let μ := rawTupleMixture (realPosition (step e)) H π.val ω
  let ρ := π.val.map (tupleShiftUp e H)
  let : IsProbabilityMeasure ρ := inferInstance
  refine ⟨normalizeOr μ ρ,normalizeOr_probability μ ρ,?_⟩
  apply normalizeOr_ae
  · exact rawTupleMixture_support e H a π.val ω π.property.2
  · rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
    apply π.property.2.mono
    intro x hx
    have hg : TupleSeparated e 0 x := fun _ _ _ => abs_nonneg _
    exact (tupleShiftUp_support e e H a 0 x ⟨hx,hg⟩).1

lemma fullTupleProfile_mass {d k : ℕ} (e : Direction d) (a : ℝ) (H : ℕ)
    (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    rawTupleMixture (realPosition (step e)) H π.val ω Set.univ •
      (fullTupleProfile e a H π ω).val=rawTupleMixture (realPosition (step e)) H π.val ω :=
  normalizeOr_mass _ _

lemma fullTupleProfile_measurable {d k : ℕ} (e : Direction d) (a : ℝ) (H : ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+H))) _
      (fun ω => fullTupleProfile e a H (π ω) ω) := by
  have hle : rowSigma (BelowHeight (realPosition (step e)) a)≤rowSigma (BelowHeight (realPosition (step e)) (a+H)) :=
    rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < a+H
      exact lt_of_lt_of_le hx (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) (a+H))
  apply Measurable.subtype_mk
  apply measurable_normalizeOr
  · apply (rawTupleMixture_joint_rows (realPosition (step e)) H _ _ ?_).comp
      (((LayerTupleProfile.measurable_toSupported e a).comp (hπ.mono hle le_rfl)).prodMk measurable_id)
    intro x hx j y hy
    change dot (realPosition y) (realPosition (step e))<a+H
    simpa only [hx j] using hy.2
  · exact (Measure.measurable_map _ (measurable_of_countable _)).comp (measurable_subtype_coe.comp (hπ.mono hle le_rfl))

end DirectionalTransience

end

end OAI
