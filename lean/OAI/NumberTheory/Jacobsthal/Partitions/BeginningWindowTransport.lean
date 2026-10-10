import OAI.NumberTheory.Jacobsthal.Renewal.ClockWindowPassage

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.KernelPotential

section Projection
variable {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f)
include hf

lemma costProjection_comp {K B : Kernel α α} {L C : Kernel ℝ ℝ}
    (hK : ∀ z, (K z).map f = L (f z)) (hB : ∀ z, (B z).map f = C (f z)) (z : α) :
    ((B ∘ₖ K) z).map f = (C ∘ₖ L) (f z) := by
  ext S hS
  rw [Measure.map_apply hf hS,Kernel.comp_apply' _ _ _ (hf hS),Kernel.comp_apply' _ _ _ hS]
  have hi (y : α) : B y (f ⁻¹' S) = C (f y) S := by
    rw [← Measure.map_apply hf hS,hB y]
  simp_rw [hi]
  rw [← lintegral_map (g := f) (C.measurable_coe hS) hf,hK z]

lemma costProjection_power {K : Kernel α α} {L : Kernel ℝ ℝ}
    (hK : ∀ z, (K z).map f = L (f z)) (n : ℕ) (z : α) :
    ((K ^ n) z).map f = (L ^ n) (f z) := by
  induction n generalizing z with
  | zero =>
    change (Measure.dirac z).map f = Measure.dirac (f z)
    exact Measure.map_dirac' hf z
  | succ n ih =>
    rw [pow_succ',pow_succ']
    exact costProjection_comp hf (fun z => ih z) hK z

lemma costProjection_potential {K B : Kernel α α} {L C : Kernel ℝ ℝ}
    (hK : ∀ z, (K z).map f = L (f z)) (hB : ∀ z, (B z).map f = C (f z)) (z : α) :
    ((potential B K) z).map f = (potential C L) (f z) := by
  rw [potential,Kernel.sum_apply,Measure.map_sum (f := f) hf.aemeasurable,
    potential,Kernel.sum_apply]
  apply congrArg Measure.sum
  funext n
  exact costProjection_comp hf (costProjection_power hf hK n) hB z

lemma costProjection_restrict {K : Kernel α α} {L : Kernel ℝ ℝ}
    (hK : ∀ z, (K z).map f = L (f z)) {S : Set ℝ} (hS : MeasurableSet S) (z : α) :
    ((K.restrict (s := f ⁻¹' S) (hf hS)) z).map f = (L.restrict hS) (f z) := by
  rw [Kernel.restrict_apply,Kernel.restrict_apply,← Measure.restrict_map hf hS,hK z]
end Projection

def relativeBeginningCost (t : ℝ) (z : RegCost) : ℝ := beginningCost z-t

lemma relativeBeginningCost_measurable (t : ℝ) : Measurable (relativeBeginningCost t) :=
  beginningCost_measurable.sub measurable_const

lemma beginning_relative_cost_projection (t : ℝ) (z : RegCost) :
    (markedBeginningKernel z).map (relativeBeginningCost t) =
      markedClockKernel (relativeBeginningCost t z) := by
  rw [markedClockKernel_apply]
  calc
    _ = ((markedBeginningKernel z).map (fun y => beginningCost y-beginningCost z)).map
        (fun G => relativeBeginningCost t z+G) := by
      rw [Measure.map_map (f := fun y : RegCost => beginningCost y-beginningCost z)
        (g := fun G : ℝ => relativeBeginningCost t z+G) (measurable_const.add measurable_id)
        (beginningCost_measurable.sub measurable_const)]
      congr 1
      funext y
      dsimp [Function.comp_def,relativeBeginningCost]
      ring
    _ = _ := by rw [markedBeginning_increment_law]

noncomputable def beginningBelow (t v : ℝ) : Kernel RegCost RegCost :=
  markedBeginningKernel.restrict (s := relativeBeginningCost t ⁻¹' Iio v)
    ((relativeBeginningCost_measurable t) measurableSet_Iio)

noncomputable def beginningWindow (t v H : ℝ) : Kernel RegCost RegCost :=
  markedBeginningKernel.restrict (s := relativeBeginningCost t ⁻¹' Icc v (v+H))
    ((relativeBeginningCost_measurable t) measurableSet_Icc)

noncomputable def beginningOver (t v H : ℝ) : Kernel RegCost RegCost :=
  markedBeginningKernel.restrict (s := relativeBeginningCost t ⁻¹' Ioi (v+H))
    ((relativeBeginningCost_measurable t) measurableSet_Ioi)

lemma beginningBelow_projection (t v : ℝ) (z : RegCost) :
    (beginningBelow t v z).map (relativeBeginningCost t) =
      clockBelow v (relativeBeginningCost t z) :=
  costProjection_restrict (relativeBeginningCost_measurable t)
    (beginning_relative_cost_projection t) measurableSet_Iio z

lemma beginningWindow_projection (t v H : ℝ) (z : RegCost) :
    (beginningWindow t v H z).map (relativeBeginningCost t) =
      clockWindow v H (relativeBeginningCost t z) :=
  costProjection_restrict (relativeBeginningCost_measurable t)
    (beginning_relative_cost_projection t) measurableSet_Icc z

lemma beginningOver_projection (t v H : ℝ) (z : RegCost) :
    (beginningOver t v H z).map (relativeBeginningCost t) =
      clockOver v H (relativeBeginningCost t z) :=
  costProjection_restrict (relativeBeginningCost_measurable t)
    (beginning_relative_cost_projection t) measurableSet_Ioi z

noncomputable def beginningWindowHit (z : RegCost) (v H : ℝ) : ℝ≥0∞ :=
  (potential (beginningWindow (beginningCost z) v H) (beginningBelow (beginningCost z) v)) z univ

noncomputable def beginningOvershoot (z : RegCost) (v H : ℝ) : ℝ≥0∞ :=
  (potential (beginningOver (beginningCost z) v H) (beginningBelow (beginningCost z) v)) z univ

lemma beginningWindowHit_eq_clock (z : RegCost) (v H : ℝ) :
    beginningWindowHit z v H = clockWindowHit v H := by
  have he := costProjection_potential (relativeBeginningCost_measurable (beginningCost z))
    (beginningBelow_projection (beginningCost z) v) (beginningWindow_projection (beginningCost z) v H) z
  apply_fun (fun μ : Measure ℝ => μ univ) at he
  rw [Measure.map_apply (relativeBeginningCost_measurable _) MeasurableSet.univ,preimage_univ] at he
  simpa only [relativeBeginningCost,sub_self,beginningWindowHit,clockWindowHit] using he

lemma beginningOvershoot_eq_clock (z : RegCost) (v H : ℝ) :
    beginningOvershoot z v H = clockOvershoot v H := by
  have he := costProjection_potential (relativeBeginningCost_measurable (beginningCost z))
    (beginningBelow_projection (beginningCost z) v) (beginningOver_projection (beginningCost z) v H) z
  apply_fun (fun μ : Measure ℝ => μ univ) at he
  rw [Measure.map_apply (relativeBeginningCost_measurable _) MeasurableSet.univ,preimage_univ] at he
  simpa only [relativeBeginningCost,sub_self,beginningOvershoot,clockOvershoot] using he

theorem beginningWindow_partition (z : RegCost) {v H : ℝ} (hv : 0 < v) (hH : 0 ≤ H) :
    beginningWindowHit z v H+beginningOvershoot z v H = 1 := by
  rw [beginningWindowHit_eq_clock,beginningOvershoot_eq_clock]
  exact clockWindowHit_add_overshoot hv hH

theorem beginningWindow_exponential : ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧ ∀ z : RegCost, ∀ v H : ℝ,
    0 < v → 0 ≤ H → beginningOvershoot z v H ≤ ENNReal.ofReal (C*Real.exp (-eta*H)) ∧
      1-ENNReal.ofReal (C*Real.exp (-eta*H)) ≤ beginningWindowHit z v H := by
  obtain ⟨eta,C,heta,hC,hTail⟩ := clockOvershoot_exponential
  refine ⟨eta,C,heta,hC,?_⟩
  intro z v H hv hH
  rw [beginningWindowHit_eq_clock,beginningOvershoot_eq_clock]
  refine ⟨hTail v H hv hH,?_⟩
  apply tsub_le_iff_right.mpr
  have he := clockWindowHit_add_overshoot hv hH
  calc
    1 = clockWindowHit v H+clockOvershoot v H := he.symm
    _ ≤ _ := add_le_add le_rfl (hTail v H hv hH)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
