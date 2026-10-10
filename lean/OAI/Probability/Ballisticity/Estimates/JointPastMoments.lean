import Mathlib
import OAI.Probability.Ballisticity.Estimates.ConditionalLawTests

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def pairPastCoordinates {q : ℕ} (v : Fin q → unitInterval) :
    C(RealPathPair,Fin q → ℝ × ℝ) :=
  ⟨fun P z => (P.1 (v z),P.2 (v z)),by fun_prop⟩

noncomputable def pairPathIncrement (b : Bool) (s t : unitInterval) : C(RealPathPair,ℝ) :=
  ⟨fun P => if b then P.2 t-P.2 s else P.1 t-P.1 s,by cases b <;> simp <;> fun_prop⟩

lemma jointPastIncrementMap_eq {q : ℕ} (b : Bool) (P : RealPathPair)
    (v : Fin q → unitInterval) (s t : unitInterval) :
    jointPastIncrementMap b (P,(v,s,t))=(pairPastCoordinates v P,pairPathIncrement b s t P) := rfl

def NormalJointPast (μ : Measure RealPathPair) (c : ℝ≥0) : Prop :=
  ∀ (q : ℕ) (v : Fin q → unitInterval) (s t : unitInterval),
    (∀ z, v z ≤ s) → s < t → (t:ℝ) < 1 → ∀ b : Bool,
    μ.map (fun P => (pairPastCoordinates v P,pairPathIncrement b s t P)) =
      (μ.map (pairPastCoordinates v)).prod (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)))

lemma normal_past_of_uc_tests (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0)
    (h : ∀ (q : ℕ) (v : Fin q → unitInterval) (s t : unitInterval),
      (∀ z, v z ≤ s) → s < t → (t:ℝ) < 1 → ∀ (b : Bool)
      (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G : ℝ →ᵇ ℝ), UniformContinuous G →
      (∫ P, jointPastProductTest F G (∫ z, G z ∂gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)))
        (jointPastIncrementMap b (P,(v,s,t))) ∂μ)=0) : NormalJointPast μ c := by
  intro q v s t hv hst ht b
  apply product_law_of_uc_decorrelation μ _ (pairPastCoordinates v) (pairPathIncrement b s t)
    (pairPastCoordinates v).continuous.measurable (pairPathIncrement b s t).continuous.measurable
  intro F G hG
  exact h q v s t hv hst ht b F G hG

lemma product_law_integral_mul {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : Type*} [RCLike K] (μ : Measure Ω) [IsFiniteMeasure μ] (γ : Measure ℝ) [SFinite γ]
    (Z : Ω → E) (X : Ω → ℝ) (hZ : Measurable Z) (hX : Measurable X)
    (hlaw : μ.map (fun ω => (Z ω,X ω))=(μ.map Z).prod γ)
    (F : E → K) (G : ℝ → K) (hF : Measurable F) (hG : Measurable G) :
    (∫ ω, F (Z ω)*G (X ω) ∂μ)=(∫ ω, F (Z ω) ∂μ)*(∫ z, G z ∂γ) := by
  have hi := integral_map (μ := μ) (hZ.prodMk hX).aemeasurable
    ((hF.comp measurable_fst).mul (hG.comp measurable_snd)).aestronglyMeasurable
  change (∫ z : E × ℝ, F z.1*G z.2 ∂μ.map (fun ω => (Z ω,X ω)))=
    (∫ ω, F (Z ω)*G (X ω) ∂μ) at hi
  rw [← hi,hlaw,integral_prod_mul,integral_map hZ.aemeasurable hF.aestronglyMeasurable]

lemma product_law_integrable_mul {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : Type*} [RCLike K] (μ : Measure Ω) [IsFiniteMeasure μ] (γ : Measure ℝ) [SFinite γ]
    (Z : Ω → E) (X : Ω → ℝ) (hZ : Measurable Z) (hX : Measurable X)
    (hlaw : μ.map (fun ω => (Z ω,X ω))=(μ.map Z).prod γ)
    (F : E → K) (G : ℝ → K) (hF : Measurable F) (hG : Measurable G)
    (hIF : Integrable F (μ.map Z)) (hIG : Integrable G γ) :
    Integrable (fun ω => F (Z ω)*G (X ω)) μ := by
  have hi : Integrable (fun z : E × ℝ => F z.1*G z.2) ((μ.map Z).prod γ) := hIF.mul_prod hIG
  rw [← hlaw] at hi
  exact (integrable_map_measure ((hF.comp measurable_fst).mul (hG.comp measurable_snd)).aestronglyMeasurable
    (hZ.prodMk hX).aemeasurable).mp hi

lemma normalJointPast_moment {q k : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) :
    (∫ P, F (pairPastCoordinates v P)*(pairPathIncrement b s t P)^k ∂μ)=
      (∫ P, F (pairPastCoordinates v P) ∂μ)*(∫ z : ℝ, z^k ∂gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))) := by
  exact product_law_integral_mul μ _ _ _ (pairPastCoordinates v).continuous.measurable
    (pairPathIncrement b s t).continuous.measurable (h q v s t hv hst ht b) F (fun z => z^k)
    F.continuous.measurable (by fun_prop)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma gaussianReal_second_moment (v : ℝ≥0) :
    (∫ z : ℝ, z^2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

lemma normalJointPast_hasLaw {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) :
    HasLaw (pairPathIncrement b s t) (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))) μ := by
  have hp := h q v s t hv hst ht b
  have he := congrArg (fun ξ : Measure ((Fin q → ℝ × ℝ) × ℝ) => ξ.map Prod.snd) hp
  rw [Measure.map_map measurable_snd ((pairPastCoordinates v).continuous.measurable.prodMk
    (pairPathIncrement b s t).continuous.measurable)] at he
  refine ⟨(pairPathIncrement b s t).continuous.measurable.aemeasurable,?_⟩
  simpa [Measure.map_apply (pairPastCoordinates v).continuous.measurable,Function.comp_def] using he

lemma normalJointPast_integrable_abs_pow (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (k : ℕ) :
    Integrable (fun P => |pairPathIncrement b s t P|^k) μ := by
  have hl := normalJointPast_hasLaw μ c h (fun _ : Fin 0 => s) s t (by simp) hst ht b
  have hi := gaussian_absolute_moment_integrable (c*Real.toNNReal ((t:ℝ)-s)) k
  rw [← hl.map_eq] at hi
  exact (integrable_map_measure (by fun_prop : Measurable (fun z : ℝ => |z|^k)).aestronglyMeasurable
    hl.aemeasurable).mp hi

lemma normalJointPast_absolute_third_moment (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) :
    (∫ P, |pairPathIncrement b s t P|^3 ∂μ)=
      (Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment := by
  have hl := normalJointPast_hasLaw μ c h (fun _ : Fin 0 => s) s t (by simp) hst ht b
  have hi := hl.integral_comp (by fun_prop : Measurable (fun z : ℝ => |z|^3)).aestronglyMeasurable
  change (∫ P, |pairPathIncrement b s t P|^3 ∂μ) = _ at hi
  rw [hi,gaussian_absolute_third_moment]
  rw [NNReal.coe_mul,Real.toNNReal_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le))]
  rfl

lemma normalJointPast_mean {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) :
    (∫ P, F (pairPastCoordinates v P)*pairPathIncrement b s t P ∂μ)=0 := by
  simpa using normalJointPast_moment (k := 1) μ c h v s t hv hst ht b F

lemma normalJointPast_second {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) :
    (∫ P, F (pairPastCoordinates v P)*(pairPathIncrement b s t P)^2 ∂μ)=
      (∫ P, F (pairPastCoordinates v P) ∂μ)*((c:ℝ)*((t:ℝ)-s)) := by
  rw [normalJointPast_moment μ c h v s t hv hst ht b F,gaussianReal_second_moment,
    NNReal.coe_mul,Real.toNNReal_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le))]
  rfl

end DirectionalTransience

end

end

end OAI
