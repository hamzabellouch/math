import OAI.Analysis.LpDimension.CoordinateLaws

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE uI uV uΩ

namespace SubpolynomialLp

lemma integrated_power_perturbation {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p ε C b : ℝ)
    (hp : 0 < p) (hScalar : ∀ a t : ℝ, abs (|a+t|^p-|a|^p) ≤ ε*|a|^p+C*|t|^p)
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, |X x| ≤ B ∧ |Y x| ≤ B)
    (hYb : (∫ x, |Y x|^p ∂μ)=b) :
    |(∫ x, |X x|^p ∂μ)-b| ≤ ε*b+C*(∫ x, |X x-Y x|^p ∂μ) := by
  have hXi := bounded_power_integrable μ X hX p B hp hB0 (fun x => (hB x).1)
  have hYi := bounded_power_integrable μ Y hY p B hp hB0 (fun x => (hB x).2)
  have hDi := bounded_power_integrable μ (fun x => X x-Y x) (hX.sub hY) p (2*B) hp
    (by positivity) (fun x => (abs_sub _ _).trans (by linarith [(hB x).1,(hB x).2]))
  calc
    _ = |∫ x, |X x|^p-|Y x|^p ∂μ| := by rw [integral_sub hXi hYi,hYb]
    _ ≤ ∫ x, abs (|X x|^p-|Y x|^p) ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ε*|Y x|^p+C*|X x-Y x|^p ∂μ := by
      apply integral_mono (hXi.sub hYi).abs ((hYi.const_mul ε).add (hDi.const_mul C))
      intro x
      simpa only [Pi.sub_apply,Pi.add_apply,add_sub_cancel_left,add_sub_cancel_right,add_sub_cancel] using hScalar (Y x) (X x-Y x)
    _ = _ := by rw [integral_add (hYi.const_mul ε) (hDi.const_mul C),integral_const_mul,integral_const_mul,hYb]

variable {E : Type uE} [Fintype E]

def projectedRampLaw (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ) : Measure (E → ℝ) :=
  symmetricLaw (μ.map (fun v => P.mulVec (fun e => dyadicRamp ℓ (v e))))

instance projectedRampLaw_probability (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (P : Matrix E E ℝ) (ℓ : ℕ) : IsProbabilityMeasure (projectedRampLaw μ P ℓ) := by
  have : IsProbabilityMeasure (μ.map (fun v => P.mulVec (fun e => dyadicRamp ℓ (v e)))) :=
    inferInstance
  unfold projectedRampLaw
  infer_instance

lemma projectedRampLaw_symmetry (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ) :
    (projectedRampLaw μ P ℓ).map (fun v => -v)=projectedRampLaw μ P ℓ := symmetricLaw_symmetry _

lemma projectedRampLaw_bounded (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ)
    (H : ℝ) (hr : ∀ e, matrixRowNorm P e ≤ H) :
    ∀ᵐ z ∂projectedRampLaw μ P ℓ, ∀ e, |z e| ≤ H*2^(2*ℓ) := by
  apply ae_all_iff.mpr
  intro e
  apply symmetricLaw_ae
  · apply (ae_map_iff (show Measurable (fun v : E → ℝ => P.mulVec (fun a => dyadicRamp ℓ (v a))) by change Measurable (fun v : E → ℝ => fun e => ∑ a, P e a*dyadicRamp ℓ (v a)); fun_prop).aemeasurable
      (measurableSet_le (show Measurable (fun z : E → ℝ => |z e|) by fun_prop) measurable_const)).mpr
    apply ae_of_all
    intro v
    exact (matrix_mulVec_bound P _ _ (fun a => abs_dyadicRamp_le ℓ (v a)) e).trans
      (mul_le_mul_of_nonneg_right (hr e) (by positivity))
  · intro z hz
    simpa only [Pi.neg_apply,abs_neg] using hz

lemma projectedRampLaw_range {V : Type uV} [Fintype V]
    (μ : Measure (E → ℝ)) (P : Matrix E E ℝ) (ℓ : ℕ) (A : Matrix E V ℝ)
    (hP : P ∈ retractions A) :
    ∀ᵐ z ∂projectedRampLaw μ P ℓ, ∃ x, A.mulVec x=z := by
  classical
  have hm : MeasurableSet {z : E → ℝ | ∃ x, A.mulVec x=z} :=
    (LinearMap.range (Matrix.toLin' A)).closed_of_finiteDimensional.measurableSet
  apply symmetricLaw_ae
  · apply (ae_map_iff (show Measurable (fun v : E → ℝ => P.mulVec (fun a => dyadicRamp ℓ (v a))) by change Measurable (fun v : E → ℝ => fun e => ∑ a, P e a*dyadicRamp ℓ (v a)); fun_prop).aemeasurable hm).mpr
    exact ae_of_all _ (fun v => retraction_range A P hP _)
  · rintro z ⟨x,hx⟩
    exact ⟨-x,by rw [Matrix.mulVec_neg,hx]⟩

lemma projectedRampLaw_moment (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (P : Matrix E E ℝ) (ℓ : ℕ) (q : ℝ) (hq : 0 < q) (e : E) :
    (∫ z, |z e|^q ∂projectedRampLaw μ P ℓ) =
      ∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e|^q ∂μ := by
  let F := fun v : E → ℝ => P.mulVec (fun a => dyadicRamp ℓ (v a))
  have hF : Measurable F := by dsimp [F,Matrix.mulVec,dotProduct]; fun_prop
  have hi : Integrable (fun z : E → ℝ => |z e|^q) (μ.map F) := by
    rw [integrable_map_measure (show Measurable (fun z : E → ℝ => |z e|^q) by fun_prop).aestronglyMeasurable hF.aemeasurable]
    exact bounded_power_integrable μ (fun v => F v e) (by fun_prop) q
      (matrixRowNorm P e*2^(2*ℓ)) hq (by positivity [matrixRowNorm_nonneg P e])
      (fun v => matrix_mulVec_bound P _ _ (fun a => abs_dyadicRamp_le ℓ (v a)) e)
  rw [projectedRampLaw,symmetricLaw_even_integral _ _ (by fun_prop) hi
    (fun z => by simp only [Pi.neg_apply,abs_neg]),integral_map hF.aemeasurable (show Measurable (fun z : E → ℝ => |z e|^q) by fun_prop).aestronglyMeasurable]

lemma ramp_jump_law (p ε : ℝ) (hp : 2 < p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Type uE) (V : Type uV) (I : Type uI) [Fintype E] [Fintype V] [Fintype I]
      [DecidableEq E] [DecidableEq V] [Nonempty E] [Nonempty I]
      (src dst : E → V) (δ w : E → ℝ) (_hδ : ∀ e, 0 < δ e)
      (_hw : ∀ e, 0 < w e) (_hws : ∑ e, w e=1)
      (_hcard : 2 ≤ Fintype.card V)
      (_hinc : ∀ i : V, ∃ e, src e=i ∨ dst e=i)
      (_hconn : ∀ i j : V, i ≠ j → ∃ e,
        (src e=i ∧ dst e=j) ∨ (src e=j ∧ dst e=i))
      (g : I → E → ℝ) (_hg : ∀ e, ∑ i, |g i e|^p=1)
      (_hgr : ∀ i, ∃ x, (normalizedGradient src dst δ).mulVec x=g i)
      (ℓ : ℕ),
      let H := 4*Real.log (Fintype.card V : ℝ)
      let N := (Fintype.card I : ℝ)
      let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
      ∃ ν : Measure (E → ℝ), IsProbabilityMeasure ν ∧ ν.map (fun v => -v)=ν ∧
        (∀ᵐ z ∂ν, ∃ x, (normalizedGradient src dst δ).mulVec x=z) ∧
        (∀ᵐ z ∂ν, ∀ e, |z e| ≤ H*2^(2*ℓ)) ∧
        (∑ e, w e*|N*(∫ z, |z e|^p ∂ν)-b|) ≤ ε*b+C*H^(p-2)*(ℓ:ℝ) ∧
        (∑ e, w e*(N*(∫ z, (z e)^2 ∂ν))) ≤ 4*aboveVariance p ∧
        (∀ e, N*(∫ z, (z e)^2 ∂ν) ≤ H^2*aboveVariance p) := by
  obtain ⟨C₁,hC₁,hScalar⟩ := power_difference_epsilon p ε (by linarith) hε
  obtain ⟨C₂,hC₂,hRet⟩ := ramp_retraction p hp
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro E V I _ _ _ _ _ _ _ src dst δ w hδ hw hws hcard hinc hconn g hg hgr ℓ
  dsimp only
  let μ := paretoVectorLaw p g
  let H := 4*Real.log (Fintype.card V : ℝ)
  let N := (Fintype.card I : ℝ)
  let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hH : 1 ≤ H := by have ht := log_nat_lower (Fintype.card V) hcard; dsimp [H]; linarith
  let : IsProbabilityMeasure μ := paretoVectorLaw_probability p (by linarith) g
  obtain ⟨P,hP,hr,hErr,hVar,hVarE⟩ := hRet E V I src dst δ w hδ hw hws hcard hinc hconn g hg hgr ℓ
  change _ ≤ C₂*H^(p-2)*(ℓ:ℝ)/N at hErr
  change _ ≤ 4*aboveVariance p/N at hVar
  change ∀ e, _ ≤ H^2*aboveVariance p/N at hVarE
  let ν := projectedRampLaw μ P ℓ
  have hMoment (q : ℝ) (hq : 0 < q) (e : E) := projectedRampLaw_moment μ P ℓ q hq e
  have hSq (e : E) : (∫ z, (z e)^2 ∂ν)=∫ v, (P.mulVec (fun a => dyadicRamp ℓ (v a)) e)^2 ∂μ := by
    simpa only [Real.rpow_two,sq_abs] using hMoment 2 (by norm_num) e
  refine ⟨ν,inferInstance,projectedRampLaw_symmetry _ _ _,projectedRampLaw_range _ _ _ _ hP,
    projectedRampLaw_bounded _ _ _ H hr,?_,?_,?_⟩
  · have hPert (e : E) : |(∫ z, |z e|^p ∂ν)-b/N| ≤ ε*(b/N)+
        C₁*(∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e)|^p ∂μ) := by
      rw [hMoment p (by linarith) e]
      apply integrated_power_perturbation μ p ε C₁ (b/N) (by linarith) hScalar
        (fun v => P.mulVec (fun a => dyadicRamp ℓ (v a)) e) (fun v => dyadicRamp ℓ (v e))
        (by dsimp [Matrix.mulVec,dotProduct]; fun_prop) (by fun_prop) (H*2^(2*ℓ)) (by positivity)
      · intro v
        constructor
        · exact (matrix_mulVec_bound P _ _ (fun a => abs_dyadicRamp_le ℓ (v a)) e).trans
            (mul_le_mul_of_nonneg_right (hr e) (by positivity))
        · exact (abs_dyadicRamp_le ℓ (v e)).trans (by nlinarith [show (0:ℝ) ≤ 2^(2*ℓ) by positivity])
      · exact paretoVectorLaw_ramp_moment p p (by linarith) (by linarith) g hg ℓ e
    have hSum : (∑ e, w e*|(∫ z, |z e|^p ∂ν)-b/N|) ≤
        ε*(b/N)+C₁*(C₂*H^(p-2)*(ℓ:ℝ)/N) := by
      calc
        _ ≤ ∑ e, w e*(ε*(b/N)+C₁*(∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e)|^p ∂μ)) :=
          Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hPert e) (hw e).le)
        _ = ε*(b/N)+C₁*(∑ e, w e*(∫ v, |P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e)|^p ∂μ)) := by
          simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,Finset.mul_sum,hws,one_mul]
          congr 1; apply Finset.sum_congr rfl; intros; ring
        _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hErr hC₁.le) _
    have hh := mul_le_mul_of_nonneg_left hSum hN.le
    have he (e : E) : |N*(∫ z, |z e|^p ∂ν)-b|=N*|(∫ z, |z e|^p ∂ν)-b/N| := by
      rw [show N*(∫ z, |z e|^p ∂ν)-b = N*((∫ z, |z e|^p ∂ν)-b/N) by field_simp,abs_mul,abs_of_pos hN]
    change (∑ e, w e*|N*(∫ z, |z e|^p ∂ν)-b|) ≤ ε*b+(C₁*C₂)*H^(p-2)*(ℓ:ℝ)
    simp_rw [he]
    calc
      _ = N*(∑ e, w e*|(∫ z, |z e|^p ∂ν)-b/N|) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ _ := hh.trans_eq (by field_simp)
  · simp_rw [hSq]
    have hh := mul_le_mul_of_nonneg_left hVar hN.le
    calc
      _ = N*(∑ e, w e*(∫ v, (P.mulVec (fun a => dyadicRamp ℓ (v a)) e)^2 ∂μ)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ N*(4*aboveVariance p/N) := hh
      _ = _ := by field_simp
  · intro e
    rw [hSq]
    exact (mul_le_mul_of_nonneg_left (hVarE e) hN.le).trans_eq (by dsimp [H]; field_simp)

end SubpolynomialLp

end

end OAI
