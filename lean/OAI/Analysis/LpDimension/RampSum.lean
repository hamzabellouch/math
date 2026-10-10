import OAI.Analysis.LpDimension.GradientLaws

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE uI uV

namespace SubpolynomialLp

lemma ramp_sum_bounded_law (p ε : ℝ) (hp : 2 < p) (hε : 0 < ε) :
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
      (ℓ : ℕ) (T : ℝ) (_hT : 0 ≤ T),
      let H := 4*Real.log (Fintype.card V : ℝ)
      let J := (aboveVariance p+1)*H*2^(2*ℓ)
      let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
      ∃ μ : Measure (E → ℝ), IsProbabilityMeasure μ ∧
        (∀ᵐ z ∂μ, ∃ x, (normalizedGradient src dst δ).mulVec x=z) ∧
        (∀ᵐ z ∂μ, ∀ e, |z e| ≤ T) ∧
        (∑ e, w e*|(∫ z, |z e|^p ∂μ)-b|) ≤
          ((1+ε)^3-1)*b+C*H^(p-2)*((ℓ:ℝ)+1)+
            C*J^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) := by
  classical
  let U := aboveVariance p
  have hU : 0 < U := aboveVariance_pos p hp
  obtain ⟨C₁,hC₁,hJump⟩ := ramp_jump_law p ε hp hε
  obtain ⟨C₂,hC₂,hSum⟩ := convolutionLaw_weighted_error p ε U hp hε hU
  obtain ⟨C₃,hC₃,hCut⟩ := globalCut_moments p (by linarith only [hp])
  let C := (1+ε)^2*C₁+C₂+C₃*2^p+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₁' : (1+ε)^2*C₁ ≤ C := by
    dsimp [C]
    have hh : 0 ≤ C₃*2^p := by positivity
    linarith only [hC₂,hh]
  have hC₂' : C₂ ≤ C := by
    dsimp [C]
    have hh : 0 ≤ (1+ε)^2*C₁+C₃*2^p := by positivity
    linarith only [hh]
  have hC₃' : C₃*2^p ≤ C := by
    dsimp [C]
    have hh : 0 ≤ (1+ε)^2*C₁ := by positivity
    linarith only [hC₂,hh]
  refine ⟨C,hC,?_⟩
  intro E V I _ _ _ _ _ _ _ src dst δ w hδ hw hws hcard hinc hconn g hg hgr ℓ T hT
  dsimp only
  let H := 4*Real.log (Fintype.card V : ℝ)
  let J := (U+1)*H*2^(2*ℓ)
  let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
  have hH : 1 ≤ H := by have hh := log_nat_lower (Fintype.card V) hcard; dsimp [H]; linarith only [hh]
  have hH0 : 0 < H := by linarith only [hH]
  have hJ : 0 < J := by dsimp [J]; positivity
  have hL : (1:ℝ) ≤ 2^(2*ℓ) := one_le_pow₀ (by norm_num)
  have hB : H*2^(2*ℓ) ≤ J := by
    calc
      _ ≤ (U+1)*(H*2^(2*ℓ)) := le_mul_of_one_le_left (by positivity) (by linarith only [hU])
      _ = _ := by dsimp [J]; ring
  have hVarB : H^2*U ≤ J^2 := by
    have hj : (U+1)*H ≤ J := by dsimp [J]; exact le_mul_of_one_le_right (by positivity) hL
    have hj0 : 0 ≤ (U+1)*H := by positivity
    have hsq := (sq_le_sq₀ hj0 hJ.le).mpr hj
    have hu : U ≤ (U+1)^2 := by nlinarith [sq_nonneg U]
    have hh := mul_le_mul_of_nonneg_left hu (sq_nonneg H)
    nlinarith only [hsq,hh]
  obtain ⟨ν,hν,hs,hRange,hBound,hErr,hVar,hVarE⟩ :=
    hJump E V I src dst δ w hδ hw hws hcard hinc hconn g hg hgr ℓ
  let : IsProbabilityMeasure ν := hν
  let N := Fintype.card I
  let W := convolutionPower ν N
  have hBoundJ : ∀ᵐ z ∂ν, ∀ e, |z e| ≤ J := hBound.mono (fun z hz e => (hz e).trans hB)
  have hExp := convolutionLaw_exp_bound ν hs J hJ N hBoundJ (fun e => (hVarE e).trans hVarB)
  have hWi (e : E) : Integrable (fun z => |z e|^p) W :=
    convolutionPower_coordinate_integrable ν J p (by linarith only [hp]) hBoundJ N e
  have hWErr := hSum E ν hs w (fun e => (hw e).le) hws (H*2^(2*ℓ)) H b
    (ε*b+C₁*H^(p-2)*(ℓ:ℝ)) hH0 (integral_nonneg (fun r => Real.rpow_nonneg (abs_nonneg _) _))
    N hBound hErr hVar hVarE
  let μ := globalCutLaw W T
  have hRangeW : ∀ᵐ z ∂W, z ∈ LinearMap.range (Matrix.toLin' (normalizedGradient src dst δ)) :=
    convolutionPower_submodule ν _ hRange N
  have hRangeμ := globalCutLaw_submodule W T _ hRangeW
  refine ⟨μ,inferInstance,hRangeμ,globalCutLaw_bound W T hT,?_⟩
  have hCutE (e : E) : |(∫ z, |z e|^p ∂μ)-(∫ z, |z e|^p ∂W)| ≤
      C₃*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) := by
    rw [globalCutLaw_moment]
    exact hCut E W J T hJ hT hWi hExp e
  have hCutSum : (∑ e, w e*|(∫ z, |z e|^p ∂μ)-b|) ≤
      (∑ e, w e*|(∫ z, |z e|^p ∂W)-b|)+C₃*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) := by
    calc
      _ ≤ ∑ e, w e*(|(∫ z, |z e|^p ∂W)-b|+
          C₃*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ)) := by
        apply Finset.sum_le_sum
        intro e _
        apply mul_le_mul_of_nonneg_left _ (hw e).le
        exact (abs_sub_le _ _ _).trans (by
          calc
            _ ≤ C₃*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ)+
                |(∫ z, |z e|^p ∂W)-b| := add_le_add (hCutE e) le_rfl
            _ = _ := add_comm _ _)
      _ = _ := by simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hws,one_mul]
  have hCGe : (1+ε)^2*C₁*(ℓ:ℝ)+C₂ ≤ C*((ℓ:ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_right hC₁' (show (0:ℝ) ≤ ℓ by positivity)
    nlinarith only [hh,hC₂']
  have hCore := mul_le_mul_of_nonneg_right hCGe (Real.rpow_nonneg hH0.le (p-2))
  have hTail : C₃*(2*J)^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) ≤
      C*J^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hJ.le]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by nlinarith only [hC₃',Real.rpow_nonneg hJ.le p] : C₃*(2^p*J^p) ≤ C*J^p)
        (Real.exp_pos _).le) (by positivity)
  change _ ≤ ((1+ε)^3-1)*b+C*H^(p-2)*((ℓ:ℝ)+1)+C*J^p*Real.exp (-T/(2*J))*(Fintype.card E : ℝ)
  nlinarith only [hWErr,hCutSum,hCore,hTail]

end SubpolynomialLp

end

end OAI
