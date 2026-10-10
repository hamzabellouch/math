import OAI.Analysis.RotationWeights.Transport

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace

open Filter Set
open scoped Topology

def fractionB (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x) : RealBorel where
  f x := (1+a x)⁻¹
  measurable := (measurable_const.add ha).inv
  bound := 1
  norm_le x := by
    have h : (1:ℝ)≤1+a x := by linarith [hp x]
    simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by linarith [hp x] : 0<1+a x)),one_div_one,one_div,inv_one,NNReal.coe_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) h

def fractionC (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x) : RealBorel where
  f x := a x/(1+a x)
  measurable := ha.div (measurable_const.add ha)
  bound := 1
  norm_le x := by
    rw [Real.norm_eq_abs,abs_of_pos (div_pos (hp x) (by linarith [hp x]))]
    exact (div_le_one (by linarith [hp x])).mpr (by linarith)

lemma fractionB_pos (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x) (x : CircleX) :
    0<fractionB a ha hp x := inv_pos.mpr (by linarith [hp x])
lemma fractionC_pos (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x) (x : CircleX) :
    0<fractionC a ha hp x := div_pos (hp x) (by linarith [hp x])

lemma fractionB_relation (θ : CircleX) (f F : RealBorel) (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x)
    (he : ∀ᵐ x ∂AddCircle.haarAddCircle,f x*a (x+θ)=F x*a x) :
    realPi θ (f.mul (fractionB a ha hp)) =
      realPi θ (((fractionB a ha hp).shift θ).mul ((f.mul (fractionB a ha hp)).add (F.mul (fractionC a ha hp)))) := by
  apply realPi_congr
  filter_upwards [he] with x hx
  change f x*(1+a x)⁻¹=(1+a (x+θ))⁻¹*(f x*(1+a x)⁻¹+F x*(a x/(1+a x)))
  have h1 : 1+a x≠0 := ne_of_gt (by linarith [hp x])
  have h2 : 1+a (x+θ)≠0 := ne_of_gt (by linarith [hp (x+θ)])
  field_simp
  nlinarith [hx]

lemma fractionC_relation (θ : CircleX) (f F : RealBorel) (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x)
    (he : ∀ᵐ x ∂AddCircle.haarAddCircle,f x*a (x+θ)=F x*a x) :
    realPi θ (F.mul (fractionC a ha hp)) =
      realPi θ (((fractionC a ha hp).shift θ).mul ((f.mul (fractionB a ha hp)).add (F.mul (fractionC a ha hp)))) := by
  apply realPi_congr
  filter_upwards [he] with x hx
  change F x*(a x/(1+a x))=(a (x+θ)/(1+a (x+θ)))*(f x*(1+a x)⁻¹+F x*(a x/(1+a x)))
  have h1 : 1+a x≠0 := ne_of_gt (by linarith [hp x])
  have h2 : 1+a (x+θ)≠0 := ne_of_gt (by linarith [hp (x+θ)])
  field_simp
  nlinarith [hx]

lemma fraction_operator_relations (θ : CircleX) (f F : RealBorel) (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x)
    (he : ∀ᵐ x ∂AddCircle.haarAddCircle,f x*a (x+θ)=F x*a x) :
    let b := realPi θ (fractionB a ha hp)
    let c := realPi θ (fractionC a ha hp)
    let L := fiberShiftL2 1 * realPi θ ((f.mul (fractionB a ha hp)).add (F.mul (fractionC a ha hp)))
    (fiberShiftL2 1*realPi θ f)*b=b*L ∧ (fiberShiftL2 1*realPi θ F)*c=c*L := by
  dsimp only
  constructor
  · rw [mul_assoc,←realPi_mul,fractionB_relation θ f F a ha hp he,realPi_mul]
    rw [←mul_assoc,←realPi_shift,mul_assoc]
  · rw [mul_assoc,←realPi_mul,fractionC_relation θ f F a ha hp he,realPi_mul]
    rw [←mul_assoc,←realPi_shift,mul_assoc]

theorem borel_weight_transport (θ : ℝ) (f F : RealBorel) (a : CircleX → ℝ)
    (ha : Measurable a) (hp : ∀ x,0<a x)
    (he : ∀ᵐ x ∂AddCircle.haarAddCircle,f x*a (x+(θ:CircleX))=F x*a x)
    (p : CircleFiberOperator) (hproj : IsStarProjection p)
    (hpc : ∀ B∈fiberCommutant θ,Commute p B) (hp0 : p≠0) (hp1 : p≠1)
    (hinv : (1-p)*(fiberShiftL2 1*realPi (θ:CircleX) f)*p=0) :
    ∃ q : CircleFiberOperator,IsStarProjection q ∧ (∀ B∈fiberCommutant θ,Commute q B) ∧
      q≠0 ∧ q≠1 ∧ (1-q)*(fiberShiftL2 1*realPi (θ:CircleX) F)*q=0 := by
  let b := fractionB a ha hp
  let c := fractionC a ha hp
  let P := p.range
  let : CompleteSpace P := (ContinuousLinearMap.IsIdempotentElem.isClosed_range hproj.isIdempotentElem).completeSpace_coe
  have hP : P.starProjection=p := by
    obtain ⟨_,h⟩ := isStarProjection_iff_eq_starProjection_range.mp hproj
    exact h.symm
  have hP0 : P≠⊥ := by
    intro h
    apply hp0
    simpa only [h, Submodule.starProjection_bot] using hP.symm
  have hP1 : P≠⊤ := by
    intro h
    apply hp1
    simpa only [h, Submodule.starProjection_top,ContinuousLinearMap.one_def] using hP.symm
  have hTP : ∀ x∈P,(fiberShiftL2 1*realPi (θ:CircleX) f) x∈P := by
    rintro x ⟨y,rfl⟩
    have hh := DFunLike.congr_fun hinv y
    change (fiberShiftL2 1*realPi (θ:CircleX) f) (p y)-p ((fiberShiftL2 1*realPi (θ:CircleX) f) (p y))=0 at hh
    exact ⟨_,(sub_eq_zero.mp hh).symm⟩
  have hrel := fraction_operator_relations (θ:CircleX) f F a ha hp he
  apply CircleTransport.bounded_fraction_transport (fiberCommutant θ) fiberVacuum
    (fiber_vacuum_trace θ) (fiber_vacuum_faithful θ)
    (realPi (θ:CircleX) b) (realPi (θ:CircleX) c)
    (realPi_injective _ b (fun x => ne_of_gt (fractionB_pos a ha hp x)))
    (realPi_injective _ c (fun x => ne_of_gt (fractionC_pos a ha hp x)))
    (realPi_selfAdjoint _ b) (realPi_selfAdjoint _ c) (realPi_commute _ b c)
    (realPi_fiberCommutant θ b) (realPi_fiberCommutant θ c)
    (realCutoffRange (θ:CircleX) b) (realCutoffRange (θ:CircleX) c)
    (fun n B hB => by rw [realCutoffRange_projection]; exact realPi_fiberCommutant θ _ B hB)
    (fun n B hB => by rw [realCutoffRange_projection]; exact realPi_fiberCommutant θ _ B hB)
    (realCutoffRange_le _ b) (realCutoffRange_le _ c)
    (realCutoffRange_tendsto _ b (fractionB_pos a ha hp) fiberVacuum)
    (realCutoffRange_tendsto _ c (fractionC_pos a ha hp) fiberVacuum)
    P (by simpa only [hP] using hpc) hP0 hP1
    (fiberShiftL2 1*realPi (θ:CircleX) f) (fiberShiftL2 1*realPi (θ:CircleX) F) _ hTP hrel.1 hrel.2


end ContinuousCircleWeight

end

end OAI
