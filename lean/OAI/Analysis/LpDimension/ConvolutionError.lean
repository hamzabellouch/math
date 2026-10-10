import OAI.Analysis.LpDimension.ProjectedRamps

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE

namespace SubpolynomialLp

lemma interval_moment_error (a M b α T : ℝ) (hb : 0 ≤ b) (hα : 1 ≤ α)
    (hT : 0 ≤ T) (hlo : a ≤ M) (hhi : M ≤ α*a+T) :
    |M-b| ≤ α*|a-b|+(α-1)*b+T := by
  have ha := abs_le.mp (le_refl |a-b|)
  have he : 0 ≤ (α-1)*|a-b| := mul_nonneg (by linarith) (abs_nonneg _)
  have he' : 0 ≤ (α-1)*b := mul_nonneg (by linarith) hb
  apply abs_le.mpr
  constructor <;> nlinarith

lemma weighted_variance_power {E : Type uE} [Fintype E] (w a : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (ha : ∀ e, 0 ≤ a e) (r B T : ℝ)
    (hr : 1 < r) (hB0 : 0 ≤ B) (hB : ∀ e, a e ≤ B) (hT : ∑ e, w e*a e ≤ T) :
    (∑ e, w e*(a e)^r) ≤ B^(r-1)*T := by
  have he (e : E) : (a e)^r ≤ B^(r-1)*a e := by
    calc
      _ = (a e)^(r-1)*a e := by rw [← Real.rpow_add_one' (ha e) (by linarith : r-1+1 ≠ 0)]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (ha e) (hB e) (by linarith)) (ha e)
  calc
    _ ≤ ∑ e, w e*(B^(r-1)*a e) := Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (he e) (hw e))
    _ = B^(r-1)*(∑ e, w e*a e) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hT (Real.rpow_nonneg hB0 _)

lemma variance_power_algebra (p H U : ℝ) (hH : 0 < H) (hU : 0 < U) :
    (H^2*U)^(p/2-1)*(4*U) = (4*U^(p/2))*H^(p-2) := by
  rw [Real.mul_rpow (sq_nonneg H) hU.le]
  have hHpow : (H^2)^(p/2-1)=H^(p-2) := by
    rw [← Real.rpow_natCast_mul hH.le]
    congr 1
    norm_num
    ring
  have hUpow : U^(p/2-1)*U=U^(p/2) := by
    rw [← Real.rpow_add_one hU.ne']
    congr 1
    ring
  rw [hHpow]
  calc
    _ = 4*(U^(p/2-1)*U)*H^(p-2) := by ring
    _ = _ := by rw [hUpow]

lemma convolutionLaw_weighted_error (p ε U : ℝ) (hp : 2 < p) (hε : 0 < ε) (hU : 0 < U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type uE) [Fintype E]
      (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
      (_hs : ν.map (fun v => -v)=ν) (w : E → ℝ) (_hw : ∀ e, 0 ≤ w e) (_hws : ∑ e, w e=1)
      (B H b err : ℝ) (_hH : 0 < H) (_hb : 0 ≤ b) (N : ℕ)
      (_hB : ∀ᵐ z ∂ν, ∀ e, |z e| ≤ B)
      (_hErr : (∑ e, w e*|(N:ℝ)*(∫ z, |z e|^p ∂ν)-b|) ≤ err)
      (_hVar : (∑ e, w e*((N:ℝ)*(∫ z, (z e)^2 ∂ν))) ≤ 4*U)
      (_hVarE : ∀ e, (N:ℝ)*(∫ z, (z e)^2 ∂ν) ≤ H^2*U),
      (∑ e, w e*|(∫ z, |z e|^p ∂convolutionPower ν N)-b|) ≤
        (1+ε)^2*err+((1+ε)^2-1)*b+C*H^(p-2) := by
  obtain ⟨C,hC,hMoment⟩ := convolutionPower_near_moment p ε hp hε
  refine ⟨C*(4*U^(p/2)),by positivity,?_⟩
  intro E _ ν _ hs w hw hws B H b err hH hb N hB hErr hVar hVarE
  let a : E → ℝ := fun e => (N:ℝ)*(∫ z, (z e)^2 ∂ν)
  have ha (e : E) : 0 ≤ a e := mul_nonneg (by positivity) (integral_nonneg (fun z => sq_nonneg _))
  have hMomentE (e : E) :
      |(∫ z, |z e|^p ∂convolutionPower ν N)-b| ≤
        (1+ε)^2*|(N:ℝ)*(∫ z, |z e|^p ∂ν)-b|+((1+ε)^2-1)*b+C*(a e)^(p/2) := by
    have hbnd : ∀ᵐ x ∂coordinateLaw ν e, |x| ≤ B :=
      (coordinateLaw_ae ν e _ (measurableSet_le (by fun_prop) measurable_const)).mpr (hB.mono (fun z hz => hz e))
    have hh := hMoment (coordinateLaw ν e) B hbnd (coordinateLaw_symmetric ν hs e) N
    rw [← coordinateLaw_convolutionPower] at hh
    simp only [coordinateLaw_abs_moment,coordinateLaw_sq_moment] at hh
    exact interval_moment_error _ _ b ((1+ε)^2) (C*(a e)^(p/2)) hb (by nlinarith)
      (by positivity) hh.1 (by simpa only [a,mul_assoc] using hh.2)
  have hVP := weighted_variance_power w a hw ha (p/2) (H^2*U) (4*U) (by linarith) (by positivity) hVarE hVar
  rw [variance_power_algebra p H U hH hU] at hVP
  calc
    _ ≤ ∑ e, w e*((1+ε)^2*|(N:ℝ)*(∫ z, |z e|^p ∂ν)-b|+((1+ε)^2-1)*b+C*(a e)^(p/2)) :=
      Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hMomentE e) (hw e))
    _ = (1+ε)^2*(∑ e, w e*|(N:ℝ)*(∫ z, |z e|^p ∂ν)-b|)+((1+ε)^2-1)*b+
        C*(∑ e, w e*(a e)^(p/2)) := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,Finset.mul_sum,hws,one_mul]
      congr 1
      · congr 1; apply Finset.sum_congr rfl; intros; ring
      · apply Finset.sum_congr rfl; intros; ring
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hErr (sq_nonneg (1+ε))
      have h₂ := mul_le_mul_of_nonneg_left hVP hC
      nlinarith

lemma convolutionLaw_exp_bound {E : Type uE} [Fintype E]
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (hs : ν.map (fun v => -v)=ν) (J : ℝ) (hJ : 0 < J) (N : ℕ)
    (hB : ∀ᵐ z ∂ν, ∀ e, |z e| ≤ J)
    (hVar : ∀ e, (N:ℝ)*(∫ z, (z e)^2 ∂ν) ≤ J^2) :
    ∀ e (s : ℝ), |s|=1 →
      Integrable (fun z => Real.exp (s*z e/J)) (convolutionPower ν N) ∧
      (∫ z, Real.exp (s*z e/J) ∂convolutionPower ν N) ≤ Real.exp 1 := by
  intro e s hs1
  obtain ⟨hi,hInt⟩ := bounded_symmetric_coordinate_exp ν hs e J hJ (hB.mono (fun z hz => hz e)) s hs1
  have hefun : (fun x : ℝ => Real.exp ((s/J)*x))=fun x => Real.exp (s*x/J) := by funext x; congr 1; ring
  have hi' : Integrable (fun x : ℝ => Real.exp ((s/J)*x)) (coordinateLaw ν e) := by
    rw [hefun,coordinateLaw_integrable _ _ _ (by fun_prop)]
    exact hi
  obtain ⟨hI,hEq⟩ := exp_convolutionPower (coordinateLaw ν e) (s/J) hi' N
  rw [← coordinateLaw_convolutionPower] at hI hEq
  rw [hefun,coordinateLaw_integrable _ _ _ (by fun_prop)] at hI
  simp only [hefun,coordinateLaw_exp_moment] at hEq
  refine ⟨hI,?_⟩
  rw [hEq]
  have hvar0 : 0 ≤ (∫ z, (z e)^2 ∂ν)/J^2 := by positivity
  have hex : 1+(∫ z, (z e)^2 ∂ν)/J^2 ≤ Real.exp ((∫ z, (z e)^2 ∂ν)/J^2) := by
    linarith [Real.add_one_le_exp ((∫ z, (z e)^2 ∂ν)/J^2)]
  have hp : (∫ z, Real.exp (s*z e/J) ∂ν)^N ≤ (Real.exp ((∫ z, (z e)^2 ∂ν)/J^2))^N :=
    pow_le_pow_left₀ (integral_nonneg (fun z => (Real.exp_pos _).le)) (hInt.trans hex) N
  rw [← Real.exp_nat_mul] at hp
  apply hp.trans (Real.exp_le_exp.mpr _)
  rw [← mul_div_assoc]
  exact (div_le_one (sq_pos_of_pos hJ)).mpr (hVar e)

end SubpolynomialLp

end

end OAI
