import Mathlib
import OAI.Analysis.HardSphere.Conditioning.ProductNormalize
import OAI.Analysis.HardSphere.Geometry.FrozenChecks

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma freezeOutside_update_self (U : Finset I) (x : ∀i,X i) (u : ∀i:U,X i) :
    freezeOutside U x (Function.updateFinset x U u)=Function.updateFinset x U u := by
  funext i
  by_cases hi : i∈U <;> simp [freezeOutside,Function.updateFinset,hi]

omit [Fintype C] in
lemma frozen_local_mean (checks : C→LocalCheck X) (μ : ∀i,Measure (X i))
    (U : Finset I) (x : ∀i,X i) (hx : x∈retainedEvent checks (Finset.univ\U))
    (F : (∀i,X i)→ℝ≥0∞) :
    lmarginal μ U (fun y ↦ checkWeight (frozenChecks checks U x) U y*F (freezeOutside U x y)) x /
      checkNormalizer (frozenChecks checks U x) μ U x=
    lmarginal μ U (fun y ↦ checkWeight checks Finset.univ y*F y) x /
      lmarginal μ U (checkWeight checks Finset.univ) x := by
  have hU : U∪(Finset.univ\U)=Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
  unfold checkNormalizer lmarginal
  congr 1 <;> apply lintegral_congr <;> intro u <;> (try dsimp only) <;>
    rw [frozen_checkWeight checks U U _ _ hx,hU,freezeOutside_update_self]

lemma local_mean_integrates (checks : C→LocalCheck X) (μ : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] (U : Finset I) (F : (∀i,X i)→ℝ≥0∞)
    (hF : Measurable F) (A : ℝ≥0∞) (hA : A≠⊤)
    (hlocal : ∀x,x∈retainedEvent checks (Finset.univ\U) →
      lmarginal μ U (fun y ↦ checkWeight checks Finset.univ y*F y) x /
        lmarginal μ U (checkWeight checks Finset.univ) x≤A) :
    (∫⁻x,F x ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ))≤A := by
  let w := checkWeight checks Finset.univ
  have hw : Measurable w := measurable_checkWeight checks _
  have hraw : (∫⁻x,w x*F x ∂Measure.pi μ)≤A*∫⁻x,w x ∂Measure.pi μ := by
    rw [←lintegral_const_mul _ hw]
    apply lintegral_le_of_lmarginal_le U (f:=fun y ↦ w y*F y) (g:=fun y ↦ A*w y) (hw.mul hF) (measurable_const.mul hw)
    intro x
    have hden : lmarginal μ U w x≠⊤ := by
      have hd : lmarginal μ U w x≤1 := by
        calc
          _≤lmarginal μ U (fun _ ↦ 1) x := lmarginal_mono (checkWeight_le_one checks _) x
          _=1 := by simp [lmarginal]
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hd
    by_cases hx : x∈retainedEvent checks (Finset.univ\U)
    · have h := (ENNReal.div_le_iff_le_mul (Or.inr hA) (Or.inl hden)).mp (hlocal x hx)
      change _≤∫⁻u,A*w (Function.updateFinset x U u) ∂Measure.pi (fun i:U ↦ μ i)
      rw [lintegral_const_mul _ (show Measurable (fun u : ∀i:U,X i ↦ w (Function.updateFinset x U u)) from hw.comp measurable_updateFinset)]
      exact h
    · have hz : lmarginal μ U (fun y ↦ w y*F y) x=0 := by
        unfold lmarginal
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro u
        dsimp only
        have hout : checkWeight checks (Finset.univ\U) (Function.updateFinset x U u)=0 := by
          rw [checkWeight_depends checks (Finset.univ\U) (x:=Function.updateFinset x U u) (y:=x)
            (fun i hi ↦ by simp [Function.updateFinset,(Finset.mem_sdiff.mp hi).2])]
          exact Set.indicator_of_notMem hx _
        have hfull : w (Function.updateFinset x U u)=0 := le_antisymm
          ((checkWeight_antitone checks (Finset.subset_univ (Finset.univ\U)) _).trans_eq hout) bot_le
        simp only [hfull,zero_mul,Pi.zero_apply]
      rw [hz]
      exact bot_le
  let Z := (Measure.pi μ) (retainedEvent checks Finset.univ)
  have hZ : (∫⁻x,w x ∂Measure.pi μ)=Z := by
    exact (lintegral_indicator_const (measurableSet_retainedEvent checks _) (1:ℝ≥0∞)).trans (one_mul _)
  have hint : (∫⁻x,F x ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ))=
      Z⁻¹*∫⁻x,w x*F x ∂Measure.pi μ := by
    rw [conditionedMeasure,lintegral_smul_measure,←lintegral_indicator (measurableSet_retainedEvent checks _)]
    congr 1
    apply lintegral_congr
    intro x
    by_cases hx : x∈retainedEvent checks Finset.univ <;> simp [w,checkWeight,hx]
  rw [hint]
  calc
    _≤Z⁻¹*(A*Z) := mul_le_mul' (le_refl _) (hraw.trans_eq (congrArg (A*·) hZ))
    _≤A := by
      by_cases hz : Z=0
      · simp [hz]
      · have ht : Z≠⊤ := measure_ne_top _ _
        calc
          _=A*(Z⁻¹*Z) := by ac_rfl
          _≤A := by rw [ENNReal.inv_mul_cancel hz ht,mul_one]

end HardSphere.Comparison

end
end

end

end OAI
