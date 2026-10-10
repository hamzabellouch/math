import Mathlib
import OAI.Probability.Ballisticity.Estimates.JointMeshPhase

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def linearPhaseTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) : E →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => charPhase (L x),
    charPhase_continuous.comp L.continuous⟩ 2 (by
      intro x y
      rw [dist_eq_norm]
      calc
        _ ≤ ‖charPhase (L x)‖+‖charPhase (L y)‖ := norm_sub_le _ _
        _ = 2 := by rw [charPhase_norm,charPhase_norm]; norm_num)

lemma real_linear_apply (L : ℝ →L[ℝ] ℝ) (x : ℝ) : L x=L 1*x := by
  have h := L.map_smul x (1:ℝ)
  simpa [smul_eq_mul,mul_comm] using h

lemma charFunDual_gaussianReal (v : ℝ≥0) (L : ℝ →L[ℝ] ℝ) :
    charFunDual (gaussianReal 0 v) L=Complex.exp ((-(v:ℝ)*(L 1)^2/2:ℝ):ℂ) := by
  have hid : charFunDual (gaussianReal 0 v) L=charFun (gaussianReal 0 v) (L 1) := by
    rw [charFunDual_apply,charFun_apply_real]
    congr 1
    funext x
    rw [real_linear_apply L x,Complex.ofReal_mul]
  rw [hid,charFun_gaussianReal]
  congr 1
  push_cast
  ring

lemma product_linear_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E × (ℝ × ℝ) →L[ℝ] ℝ) (z : E) (x y : ℝ) :
    L (z,(x,y))=L (z,0)+L (0,(1,0))*x+L (0,(0,1))*y := by
  have hid : (z,(x,y))=(z,0)+x • (0,(1,0))+y • (0,(0,1)) := by ext <;> simp
  rw [hid,map_add,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  ring

lemma product_normal_law_of_characteristics {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (v : ℝ≥0)
    (Z : Ω → E) (X Y : Ω → ℝ) (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ (F : E →ᵇ ℂ) (a b : ℝ),
       (∫ ω, F (Z ω)*charPhase (a*X ω+b*Y ω) ∂μ)=
       Complex.exp ((-(v:ℝ)*(a^2+b^2)/2:ℝ):ℂ)*(∫ ω, F (Z ω) ∂μ)) :
    μ.map (fun ω => (Z ω,(X ω,Y ω)))=(μ.map Z).prod ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
  have hm := hZ.prodMk (hX.prodMk hY)
  have : IsProbabilityMeasure (μ.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (μ.map (fun ω => (Z ω,(X ω,Y ω)))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_prod,charFunDual_prod,charFunDual_gaussianReal,charFunDual_gaussianReal]
  let L0 : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E (ℝ × ℝ))
  let a := L (0,(1,0))
  let b := L (0,(0,1))
  have hleft : charFunDual (μ.map (fun ω => (Z ω,(X ω,Y ω)))) L=
      ∫ ω, linearPhaseTest L0 (Z ω)*charPhase (a*X ω+b*Y ω) ∂μ := by
    rw [charFunDual_apply,integral_map hm.aemeasurable (by fun_prop)]
    congr 1
    funext ω
    rw [product_linear_split,show L (0,(1,0))=a from rfl,show L (0,(0,1))=b from rfl]
    change charPhase (L (Z ω,0)+a*X ω+b*Y ω)=charPhase (L (Z ω,0))*charPhase (a*X ω+b*Y ω)
    rw [add_assoc,charPhase_add]
  rw [hleft,h]
  have hi : charFunDual (μ.map Z) L0=∫ ω, linearPhaseTest L0 (Z ω) ∂μ := by
    rw [charFunDual_apply,integral_map hZ.aemeasurable (by fun_prop)]
    rfl
  change _=charFunDual (μ.map Z) L0*(Complex.exp ((-(v:ℝ)*a^2/2:ℝ):ℂ)*
    Complex.exp ((-(v:ℝ)*b^2/2:ℝ):ℂ))
  rw [hi,← Complex.exp_add]
  have hex : ((-(v:ℝ)*a^2/2:ℝ):ℂ)+((-(v:ℝ)*b^2/2:ℝ):ℂ)=
      ((-(v:ℝ)*(a^2+b^2)/2:ℝ):ℂ) := by push_cast; ring
  rw [hex,mul_comm]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

def FullNormalJointPast (μ : Measure RealPathPair) (c : ℝ≥0) : Prop :=
  ∀ (q : ℕ) (v : Fin q → unitInterval) (s t : unitInterval),
    (∀ z, v z ≤ s) → s < t → (t:ℝ) < 1 →
    μ.map (fun P => (pairPastCoordinates v P,(pairPathIncrement false s t P,pairPathIncrement true s t P))) =
      (μ.map (pairPastCoordinates v)).prod
        ((gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))).prod
         (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))))

lemma fullNormalJointPast_of_cross (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hcross : SeparatedCrossBound μ A K)
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0) :
    FullNormalJointPast μ c := by
  intro q v s t hv hst ht
  apply product_normal_law_of_characteristics μ _ (pairPastCoordinates v)
    (pairPathIncrement false s t) (pairPathIncrement true s t) (by fun_prop) (by fun_prop) (by fun_prop)
  intro F a b
  have hh := normalJointPast_joint_characteristic μ c h hA hK hcross hz v s t hv hst ht F a b
  change (∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)=_
  rw [hh]
  congr 2
  rw [NNReal.coe_mul,Real.toNNReal_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le))]
  congr 1
  simp only [NNReal.coe_mk]
  ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DirectionalTransience

lemma measure_prod_shuffle {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology E] [SecondCountableTopology F]
    [SecondCountableTopology G] [SecondCountableTopology H]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure E) (ν : Measure F) (γ : Measure G) (δ : Measure H)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure γ] [IsFiniteMeasure δ] :
    ((μ.prod ν).prod (γ.prod δ)).map (fun z => ((z.1.1,z.2.1),(z.1.2,z.2.2)))=
      (μ.prod γ).prod (ν.prod δ) := by
  let S := (ContinuousLinearEquiv.prodProdProdComm ℝ E F G H).toContinuousLinearMap
  change (((μ.prod ν).prod (γ.prod δ)).map S)=(μ.prod γ).prod (ν.prod δ)
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map]
  simp only [charFunDual_prod]
  have hE : ((L.comp S).comp (ContinuousLinearMap.inl ℝ (E × F) (G × H))).comp
      (ContinuousLinearMap.inl ℝ E F)=
      (L.comp (ContinuousLinearMap.inl ℝ (E × G) (F × H))).comp (ContinuousLinearMap.inl ℝ E G) := by ext x; rfl
  have hF : ((L.comp S).comp (ContinuousLinearMap.inl ℝ (E × F) (G × H))).comp
      (ContinuousLinearMap.inr ℝ E F)=
      (L.comp (ContinuousLinearMap.inr ℝ (E × G) (F × H))).comp (ContinuousLinearMap.inl ℝ F H) := by ext x; rfl
  have hG : ((L.comp S).comp (ContinuousLinearMap.inr ℝ (E × F) (G × H))).comp
      (ContinuousLinearMap.inl ℝ G H)=
      (L.comp (ContinuousLinearMap.inl ℝ (E × G) (F × H))).comp (ContinuousLinearMap.inr ℝ E G) := by ext x; rfl
  have hH : ((L.comp S).comp (ContinuousLinearMap.inr ℝ (E × F) (G × H))).comp
      (ContinuousLinearMap.inr ℝ G H)=
      (L.comp (ContinuousLinearMap.inr ℝ (E × G) (F × H))).comp (ContinuousLinearMap.inr ℝ F H) := by ext x; rfl
  rw [hE,hF,hG,hH]
  ring

end DirectionalTransience

end

end

end OAI
