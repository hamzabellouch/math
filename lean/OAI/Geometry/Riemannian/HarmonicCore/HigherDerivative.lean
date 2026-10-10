import OAI.Geometry.Riemannian.HarmonicCore.DirectionLimits

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma coefficientCLM_coe (B : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hB : AEStronglyMeasurable B (volume : Measure E3)) (hC : ∀ x, ‖B x‖ ≤ C) (v : DerivativeL2) :
    (coefficientCLM B C hB hC v : E3 → E3) =ᵐ[volume] (fun x ↦ B x (v x)) :=
  (coefficient_memLp B C hB hC v).coeFn_toLp

lemma coefficient_component_vectorize (B : E3 → E3 →L[ℝ] E3) (hB : Continuous B)
    (C : ℝ) (hC : ∀ x, ‖B x‖ ≤ C) (a b : E3)
    (θ : E3 → ℝ) (hθ : Continuous θ) (K : ℝ) (hK : ∀ x, ‖θ x‖ ≤ K)
    (he : ∀ x, θ x = ⟪a,B x b⟫_ℝ) (v : ValueL2) :
    componentL2 a (coefficientCLM B C hB.aestronglyMeasurable hC (vectorizeL2 b v)) =
      scalarFieldCLM θ hθ K hK v := by
  apply Lp.ext
  filter_upwards [componentL2_coe a (coefficientCLM B C hB.aestronglyMeasurable hC (vectorizeL2 b v)),
    coefficientCLM_coe B C hB.aestronglyMeasurable hC (vectorizeL2 b v),vectorizeL2_coe b v,
    scalarFieldCLM_coe θ hθ K hK v] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4,map_smul,inner_smul_right,he]
  simp only [smul_eq_mul]
  exact mul_comm _ _

lemma matrix_component_support (B : E3 → E3 →L[ℝ] E3) (a b : E3) :
    Function.support (fun x ↦ ⟪a,B x b⟫_ℝ) ⊆ Function.support B := by
  intro x hx
  change B x ≠ 0
  intro hb
  exact hx (by simp [hb])

theorem coefficient_H1_component {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E3)
    (B : E3 → E3 →L[ℝ] E3) (hB : ContDiff ℝ ∞ B) (hcompact : HasCompactSupport B)
    (C : ℝ) (hC : ∀ x, ‖B x‖ ≤ C) (N : ℝ) (F : DerivativeL2)
    (w : ι → ZeroSobolev N) (hw : ∀ i, sobolevValue N (w i) = componentL2 (b i) F) :
    ∃ R : ℝ, ∀ a : E3, ∃ q : ZeroSobolev R,
      sobolevValue R q = componentL2 a (coefficientCLM B C hB.continuous.aestronglyMeasurable hC F) := by
  classical
  obtain ⟨R,hR,hRs⟩ := hcompact.isBounded.subset_ball_lt (0:ℝ) (0:E3)
  refine ⟨R,fun a ↦ ?_⟩
  let θ : ι → E3 → ℝ := fun i x ↦ ⟪a,B x (b i)⟫_ℝ
  have hθ (i) : ContDiff ℝ ∞ (θ i) := ContDiff.inner ℝ contDiff_const (hB.clm_apply contDiff_const)
  have hcθ (i) : HasCompactSupport (θ i) := hcompact.mono (matrix_component_support B a (b i))
  have hsθ (i) : tsupport (θ i) ⊆ Metric.ball 0 R :=
    (closure_mono (matrix_component_support B a (b i))).trans hRs
  choose K hK using fun i ↦ continuous_compact_bound (θ i) (hθ i).continuous (hcθ i)
  choose D hD using fun i ↦ continuous_compact_bound (gradient (θ i))
    (gradient_continuous (hθ i)) (gradient_compact (hcθ i))
  let q : ι → ZeroSobolev R := fun i ↦ cutoffSobolev R N (θ i) (hθ i) (hsθ i) (K i) (D i) (hK i) (hD i) (w i)
  have hq (i) : sobolevValue R (q i) = scalarFieldCLM (θ i) (hθ i).continuous (K i) (hK i)
      (componentL2 (b i) F) := by rw [←hw]; rfl
  refine ⟨∑ i,q i,?_⟩
  rw [map_sum]
  simp only [hq]
  have hf := vectorize_component_sum b F
  conv_rhs => rw [←hf,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (coefficient_component_vectorize B hB.continuous C hC a (b i) (θ i) (hθ i).continuous
    (K i) (hK i) (fun _ ↦ rfl) (componentL2 (b i) F)).symm



theorem weak_forced_cutoff_H2 {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E3) (R S T N : ℝ) (hRS : R < S)
    (A : E3 → E3 →L[ℝ] E3) (C L c : ℝ) (hc : 0 < c) (_hL0 : 0 ≤ L)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev T) (F : DerivativeL2) (wF : ι → ZeroSobolev N)
    (hwF : ∀ i, sobolevValue N (wF i) = componentL2 (b i) F)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = ⟪F,sobolevDerivative S v⟫_ℝ)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) :
    ∃ w : ZeroSobolev R, sobolevValue R w = componentL2 a
      (sobolevDerivative R (cutoffSobolev R T χ hχ hsupp K D hK hD u)) := by
  obtain ⟨w1,_,hw1⟩ := weak_forced_interior_derivative b R S T N hRS A C L c hc hA hC hL hpos
    u F wF hwF hu χ hχ hsupp K D hK hD a
  let θ : E3 → ℝ := fun x ↦ fderiv ℝ χ x a
  have hθ : ContDiff ℝ ∞ θ := (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hsθ : tsupport θ ⊆ Metric.ball 0 R := (tsupport_fderiv_apply_subset ℝ a).trans hsupp
  have hcompact : HasCompactSupport θ :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport θ,Metric.isBounded_ball.subset hsθ⟩
  obtain ⟨Kθ,hKθ⟩ := continuous_compact_bound θ hθ.continuous hcompact
  obtain ⟨Dθ,hDθ⟩ := continuous_compact_bound (gradient θ) (gradient_continuous hθ) (gradient_compact hcompact)
  let w2 := cutoffSobolev R T θ hθ hsθ Kθ Dθ hKθ hDθ u
  refine ⟨w1+w2,?_⟩
  rw [map_add,hw1]
  change scalarFieldCLM χ hχ.continuous K hK (componentL2 a (sobolevDerivative T u)) +
    scalarFieldCLM θ hθ.continuous Kθ hKθ (sobolevValue T u) =
    componentL2 a (scalarFieldCLM χ hχ.continuous K hK (sobolevDerivative T u) +
      gradientFieldCLM χ hχ D hD (sobolevValue T u))
  rw [map_add,componentL2_scalar]
  congr 1
  apply Lp.ext
  filter_upwards [scalarFieldCLM_coe θ hθ.continuous Kθ hKθ (sobolevValue T u),
    componentL2_coe a (gradientFieldCLM χ hχ D hD (sobolevValue T u)),
    gradientFieldCLM_coe χ hχ D hD (sobolevValue T u)] with x h1 h2 h3
  rw [h1,h2,h3,inner_smul_right,inner_gradient_right]
  simp only [conj_trivial,smul_eq_mul,θ,mul_comm]



theorem weak_direction_H2 {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E3)
    (r R S T N : ℝ) (hrR : r < R) (hRS : R < S)
    (A : E3 → E3 →L[ℝ] E3) (hA : ContDiff ℝ ∞ A) (C L Q c : ℝ)
    (hc : 0 < c) (hC : ∀ x, ‖A x‖ ≤ C) (hL0 : 0 ≤ L) (hQ : 0 ≤ Q)
    (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hQbound : ∀ x y, ‖fderiv ℝ A y-fderiv ℝ A x‖ ≤ Q*‖y-x‖)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0)
    (w : ι → ZeroSobolev N)
    (hw : ∀ i, sobolevValue N (w i) = componentL2 (b i) (sobolevDerivative T u))
    (a : E3) (hcompact : HasCompactSupport (fun x ↦ fderiv ℝ A x a))
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 r)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D) :
    ∃ q : ZeroSobolev (T+1),
      sobolevValue (T+1) q = componentL2 a (sobolevDerivative T u) ∧
      ∀ d : E3, ∃ z : ZeroSobolev r,
        sobolevValue r z = componentL2 d
          (sobolevDerivative r (cutoffSobolev r (T+1) χ hχ hsupp K D hK hD q)) := by
  classical
  have hzero (i : ι) : sobolevValue N (0 : ZeroSobolev N) = componentL2 (b i) (0 : DerivativeL2) := by simp
  have hu' (v : ZeroSobolev S) :
      ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ =
        ⟪(0 : DerivativeL2),sobolevDerivative S v⟫_ℝ := by rw [hu,inner_zero_left]
  obtain ⟨q,hq,hqe⟩ := weak_direction_equation b b R S T N N hRS A hA C L Q hC hL0 hQ hL hQbound
    u 0 hu' w hw (fun _ ↦ 0) hzero a
  let B : E3 → E3 →L[ℝ] E3 := fun x ↦ fderiv ℝ A x a
  have hB : ContDiff ℝ ∞ B := (hA.fderiv_right (by simp)).clm_apply contDiff_const
  have hCb : ∀ x, ‖B x‖ ≤ L*‖a‖ := coefficientDirection_bound A L hL0 hL a
  obtain ⟨M,hM⟩ := coefficient_H1_component b B hB hcompact (L*‖a‖) hCb N (sobolevDerivative T u) w hw
  choose v hv using fun i ↦ hM (b i)
  let F : DerivativeL2 := -coefficientDirectionCLM A hA L hL0 hL a (sobolevDerivative T u)
  have hv' (i) : sobolevValue M (-v i) = componentL2 (b i) F := by
    rw [map_neg,hv]
    exact (map_neg _ _).symm
  have hqe' (v : ZeroSobolev R) :
      ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative (T+1) q),sobolevDerivative R v⟫_ℝ =
        ⟪F,sobolevDerivative R v⟫_ℝ := by
    simpa only [map_zero,Finset.sum_const_zero,zero_sub] using hqe v
  refine ⟨q,hq,fun d ↦ ?_⟩
  exact weak_forced_cutoff_H2 b r R (T+1) M hrR A C L c hc hL0 hA.continuous hC hL hpos q F
    (fun i ↦ -v i) hv' hqe' χ hχ hsupp K D hK hD d

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
