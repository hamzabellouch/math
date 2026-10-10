import OAI.Geometry.Riemannian.HarmonicCore.Distributions
import OAI.Geometry.Riemannian.HarmonicCore.Fourier

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction

namespace HarmonicCounterexample.Main.SmoothMetric3
section
open HarmonicCounterexample.Analytic
open scoped BoundedContinuousFunction

theorem weak_cutoff_sup_H1 (R S T : ℝ) (hRS : R < S)
    (C L c : ℝ) (hc : 0 < c) (hL0 : 0 ≤ L)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (A : E3 → E3 →L[ℝ] E3) (hA : Continuous A)
      (hC : ∀ x, ‖A x‖ ≤ C) (_hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖),
      (∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ) → ∀ u : ZeroSobolev T,
      (∀ v : ZeroSobolev S,
        ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0) →
      ∃ U : E3 →ᵇ ℝ, (U : E3 → ℝ) =ᵐ[volume] (fun x ↦ χ x*(sobolevValue T u) x) ∧
        ‖U‖ ≤ B*(‖sobolevValue T u‖+‖sobolevDerivative T u‖) := by
  classical
  let b := stdOrthonormalBasis ℝ E3
  have hh := fun i ↦ weak_cutoff_H2_bound R S T hRS C L c hc hL0 χ hχ hsupp K D hK hD (b i)
  choose B hB hBspec using hh
  obtain ⟨F,hF,hFspec⟩ := laplacianL2_continuous_estimate (E:=E3) (by norm_num [E3])
  have hK0 : 0 ≤ K := (norm_nonneg (χ 0)).trans (hK 0)
  let H : ℝ := K+∑ i,B i
  have hH : 0 ≤ H := add_nonneg hK0 (Finset.sum_nonneg (fun i _ ↦ hB i))
  refine ⟨F*‖complexifyL2‖*H,by positivity,fun A hA hC hL hpos u hu ↦ ?_⟩
  let v := cutoffSobolev R T χ hχ hsupp K D hK hD u
  choose w hw hn using (fun i ↦ hBspec i A hA hC hL hpos u hu)
  let z := ∑ i,componentL2 (b i) (sobolevDerivative R (w i))
  have hzn : ‖z‖ ≤ (∑ i,B i)*(‖sobolevValue T u‖+‖sobolevDerivative T u‖) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have h := componentL2_norm (b i) (sobolevDerivative R (w i))
    rw [b.norm_eq_one i,one_mul] at h
    exact h.trans (hn i)
  have hvn : ‖sobolevValue R v‖ ≤ K*‖sobolevValue T u‖ := scalarFieldCLM_norm χ hχ.continuous K hK _
  obtain ⟨U,hU,hUn⟩ := hFspec (complexifyL2 (sobolevValue R v)) (complexifyL2 z)
    (graph_laplacian b R R v w hw)
  let V : E3 →ᵇ ℝ := BoundedContinuousFunction.comp Complex.re Complex.reCLM.lipschitzWith U
  refine ⟨V,?_,?_⟩
  · filter_upwards [hU,complexifyL2_coe (sobolevValue R v),
      scalarFieldCLM_coe χ hχ.continuous K hK (sobolevValue T u)] with x h1 h2 h3
    change (U x).re = χ x*(sobolevValue T u) x
    rw [h1,h2,Complex.ofReal_re]
    exact h3
  · have hV : ‖V‖ ≤ ‖U‖ := (BoundedContinuousFunction.norm_le (norm_nonneg U)).mpr (fun x ↦
      (Complex.abs_re_le_norm (U x)).trans (U.norm_coe_le_norm x))
    apply hV.trans (hUn.trans _)
    have h1 := complexifyL2.le_opNorm (sobolevValue R v)
    have h2 := complexifyL2.le_opNorm z
    have h3 := mul_le_mul_of_nonneg_left hvn (norm_nonneg complexifyL2)
    have h4 := mul_le_mul_of_nonneg_left hzn (norm_nonneg complexifyL2)
    have h5 := mul_nonneg hK0 (norm_nonneg (sobolevDerivative T u))
    have h6 : ‖sobolevValue R v‖+‖z‖ ≤ H*(‖sobolevValue T u‖+‖sobolevDerivative T u‖) := by
      dsimp [H]
      nlinarith only [hvn,hzn,h5]
    have h7 := mul_le_mul_of_nonneg_left h6 (norm_nonneg complexifyL2)
    have h8 : ‖complexifyL2 (sobolevValue R v)‖+‖complexifyL2 z‖ ≤
        ‖complexifyL2‖*(H*(‖sobolevValue T u‖+‖sobolevDerivative T u‖)) := by
      nlinarith only [h1,h2,h7]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h8 hF



lemma cutoffSobolev_derivative_coe (R T : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ Metric.ball 0 R) (K D : ℝ)
    (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D) (u : ZeroSobolev T) :
    (sobolevDerivative R (cutoffSobolev R T χ hχ hsupp K D hK hD u) : E3 → E3) =ᵐ[volume]
      fun x ↦ χ x • (sobolevDerivative T u) x+(sobolevValue T u) x • gradient χ x := by
  change ((scalarFieldCLM χ hχ.continuous K hK (sobolevDerivative T u) +
    gradientFieldCLM χ hχ D hD (sobolevValue T u):DerivativeL2) : E3 → E3) =ᵐ[volume] _
  exact (Lp.coeFn_add _ _).trans ((scalarFieldCLM_coe χ hχ.continuous K hK _).add
    (gradientFieldCLM_coe χ hχ D hD _))

lemma coefficient_inner_integral (A : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3)) (hC : ∀ x, ‖A x‖ ≤ C)
    (u v : DerivativeL2) :
    ⟪coefficientCLM A C hA hC u,v⟫_ℝ = ∫ x, ⟪A x (u x),v x⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(coefficient_memLp A C hA hC u).coeFn_toLp] with x hx
  change ⟪((coefficient_memLp A C hA hC u).toLp _) x,v x⟫_ℝ = _
  rw [hx]

lemma weak_cutoff_restrict (R S T : ℝ) (hRS : R ≤ S)
    (A : E3 → E3 →L[ℝ] E3) (C : ℝ) (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hC : ∀ x, ‖A x‖ ≤ C) (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0)
    (ψ : E3 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsupp : tsupport ψ ⊆ Metric.ball 0 S)
    (K D : ℝ) (hK : ∀ x, ‖ψ x‖ ≤ K) (hD : ∀ x, ‖gradient ψ x‖ ≤ D)
    (hψ1 : ∀ x ∈ Metric.closedBall (0:E3) R, ψ x = 1)
    (hdψ : ∀ x ∈ Metric.closedBall (0:E3) R, gradient ψ x = 0) :
    ∀ v : ZeroSobolev R,
      ⟪coefficientCLM A C hA hC (sobolevDerivative S (cutoffSobolev S T ψ hψ hsupp K D hK hD u)),
        sobolevDerivative R v⟫_ℝ = 0 := by
  intro v
  have he := hu (includeSobolev hRS v)
  change ⟪coefficientCLM A C hA hC (sobolevDerivative T u),sobolevDerivative R v⟫_ℝ = 0 at he
  rw [←he,coefficient_inner_integral,coefficient_inner_integral]
  apply integral_congr_ae
  filter_upwards [cutoffSobolev_derivative_coe S T ψ hψ hsupp K D hK hD u,
    sobolevDerivative_supported R v] with x h3 h4
  rw [h3]
  by_cases hx : x ∈ Metric.closedBall (0:E3) R
  · rw [hψ1 x hx,hdψ x hx,one_smul,smul_zero,add_zero]
  · rw [h4 hx]
    simp

lemma cutoff_H1_L2_bound (R T : ℝ) (A : E3 → E3 →L[ℝ] E3)
    (C c : ℝ) (hc : 0 < c) (hC0 : 0 ≤ C)
    (hA : AEStronglyMeasurable A (volume : Measure E3)) (hC : ∀ x, ‖A x‖ ≤ C)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ) (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev R,
      ⟪coefficientCLM A C hA hC (sobolevDerivative T u),sobolevDerivative R v⟫_ℝ = 0)
    (ψ : E3 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsupp : tsupport ψ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖ψ x‖ ≤ K) (hD : ∀ x, ‖gradient ψ x‖ ≤ D) :
    ‖sobolevValue R (cutoffSobolev R T ψ hψ hsupp K D hK hD u)‖ +
    ‖sobolevDerivative R (cutoffSobolev R T ψ hψ hsupp K D hK hD u)‖ ≤
      (K+(2*C/c+1)*D)*‖sobolevValue T u‖ := by
  have hn := weak_caccioppoli R T A C c hc hA hC hpos u hu ψ hψ hsupp K D hK hD
  have hv := scalarFieldCLM_norm ψ hψ.continuous K hK (sobolevValue T u)
  have hg := gradientFieldCLM_norm ψ hψ D hD (sobolevValue T u)
  have hq := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*C/c by positivity)
  change ‖scalarFieldCLM ψ hψ.continuous K hK (sobolevValue T u)‖+
    ‖scalarFieldCLM ψ hψ.continuous K hK (sobolevDerivative T u)+
      gradientFieldCLM ψ hψ D hD (sobolevValue T u)‖ ≤ _
  have hsum := norm_add_le (scalarFieldCLM ψ hψ.continuous K hK (sobolevDerivative T u))
    (gradientFieldCLM ψ hψ D hD (sobolevValue T u))
  nlinarith only [hn,hv,hg,hq,hsum]

theorem weak_cutoff_sup_L2 (R R' S T : ℝ) (hRR' : R < R') (hR'S : R' ≤ S)
    (C L c : ℝ) (hc : 0 < c) (hC0 : 0 ≤ C) (hL0 : 0 ≤ L)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (ψ : E3 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : tsupport ψ ⊆ Metric.ball 0 S)
    (Kψ Dψ : ℝ) (hKψ : ∀ x, ‖ψ x‖ ≤ Kψ) (hDψ : ∀ x, ‖gradient ψ x‖ ≤ Dψ)
    (hψ1 : ∀ x ∈ Metric.closedBall (0:E3) R', ψ x = 1)
    (hdψ : ∀ x ∈ Metric.closedBall (0:E3) R', gradient ψ x = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (A : E3 → E3 →L[ℝ] E3) (hA : Continuous A)
      (hC : ∀ x, ‖A x‖ ≤ C) (_hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖),
      (∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ) → ∀ u : ZeroSobolev T,
      (∀ v : ZeroSobolev S,
        ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0) →
      ∃ U : E3 →ᵇ ℝ, (U : E3 → ℝ) =ᵐ[volume] (fun x ↦ χ x*(sobolevValue T u) x) ∧
        ‖U‖ ≤ B*‖sobolevValue T u‖ := by
  obtain ⟨B,hB,hBspec⟩ := weak_cutoff_sup_H1 R R' S hRR' C L c hc hL0 χ hχ hsχ K D hK hD
  have hKψ0 : 0 ≤ Kψ := (norm_nonneg (ψ 0)).trans (hKψ 0)
  have hDψ0 : 0 ≤ Dψ := (norm_nonneg (gradient ψ 0)).trans (hDψ 0)
  refine ⟨B*(Kψ+(2*C/c+1)*Dψ),by positivity,fun A hA hC hL hpos u hu ↦ ?_⟩
  let w := cutoffSobolev S T ψ hψ hsψ Kψ Dψ hKψ hDψ u
  obtain ⟨U,hU,hUn⟩ := hBspec A hA hC hL hpos w
    (weak_cutoff_restrict R' S T hR'S A C hA.aestronglyMeasurable hC u hu ψ hψ hsψ Kψ Dψ hKψ hDψ hψ1 hdψ)
  refine ⟨U,?_,hUn.trans ?_⟩
  · filter_upwards [hU,scalarFieldCLM_coe ψ hψ.continuous Kψ hKψ (sobolevValue T u)] with x h1 h2
    rw [h1]
    change χ x*(scalarFieldCLM ψ hψ.continuous Kψ hKψ (sobolevValue T u)) x = _
    rw [h2,smul_eq_mul]
    by_cases hx : χ x = 0
    · simp [hx]
    · have hs : x ∈ Metric.closedBall (0:E3) R' :=
        (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hRR'.le))
          (hsχ (subset_tsupport χ (by exact hx)))
      rw [hψ1 x hs,one_mul]
  · have hn := cutoff_H1_L2_bound S T A C c hc hC0 hA.aestronglyMeasurable hC hpos u hu
      ψ hψ hsψ Kψ Dψ hKψ hDψ
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn hB

end

section
open scoped BoundedContinuousFunction

lemma smooth_ball_cutoff (r s : ℝ) (hr : 0 < r) (hrs : r < s) :
    ∃ (χ : E3 → ℝ) (D : ℝ), ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Metric.ball 0 s ∧ (∀ x, ‖χ x‖ ≤ 1) ∧
      (∀ x, ‖gradient χ x‖ ≤ D) ∧
      (∀ x ∈ Metric.closedBall (0:E3) r, χ x = 1) ∧
      (∀ x ∈ Metric.closedBall (0:E3) r, gradient χ x = 0) := by
  let χ : ContDiffBump (0:E3) := ⟨(r+s)/2,(r+3*s)/4,by linarith,by linarith⟩
  obtain ⟨D,hD⟩ := continuous_compact_bound (gradient (χ:E3 → ℝ))
    (gradient_continuous χ.contDiff) (gradient_compact χ.hasCompactSupport)
  refine ⟨χ,D,χ.contDiff,?_,?_,hD,?_,?_⟩
  · rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [χ]; linarith)
  · intro x
    rw [Real.norm_eq_abs,abs_of_nonneg χ.nonneg]
    exact χ.le_one
  · intro x hx
    exact χ.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (by dsimp [χ]; linarith) hx)
  · intro x hx
    have he := χ.eventuallyEq_one_of_mem_ball
      (Metric.closedBall_subset_ball (show r < χ.rIn by dsimp [χ]; linarith) hx)
    rw [he.gradient_eq]
    exact gradient_const x (1:ℝ)

theorem weak_interior_sup_L2 (r s T : ℝ) (hr : 0 < r) (hrs : r < s)
    (C L c : ℝ) (hc : 0 < c) (hC0 : 0 ≤ C) (hL0 : 0 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (A : E3 → E3 →L[ℝ] E3) (hA : Continuous A)
      (hC : ∀ x, ‖A x‖ ≤ C) (_hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖),
      (∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ) → ∀ u : ZeroSobolev T,
      (∀ v : ZeroSobolev s,
        ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative s v⟫_ℝ = 0) →
      ∃ U : E3 →ᵇ ℝ, (U : E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)] (sobolevValue T u) ∧
        ‖U‖ ≤ B*‖sobolevValue T u‖ := by
  let R := (2*r+s)/3
  let R' := (r+2*s)/3
  have hrR : r < R := by dsimp [R]; linarith
  have hRR' : R < R' := by dsimp [R,R']; linarith
  have hR's : R' < s := by dsimp [R']; linarith
  obtain ⟨χ,D,hχ,hsχ,hK,hD,hχ1,_⟩ := smooth_ball_cutoff r R hr hrR
  obtain ⟨ψ,Dψ,hψ,hsψ,hKψ,hDψ,hψ1,hdψ⟩ := smooth_ball_cutoff R' s (hr.trans (hrR.trans hRR')) hR's
  obtain ⟨B,hB,hBspec⟩ := weak_cutoff_sup_L2 R R' s T hRR' hR's.le C L c hc hC0 hL0
    χ hχ hsχ 1 D hK hD ψ hψ hsψ 1 Dψ hKψ hDψ hψ1 hdψ
  refine ⟨B,hB,fun A hA hC hL hpos u hu ↦ ?_⟩
  obtain ⟨U,hU,hUn⟩ := hBspec A hA hC hL hpos u hu
  refine ⟨U,?_,hUn⟩
  rw [Filter.EventuallyEq,ae_restrict_iff' Metric.isOpen_ball.measurableSet]
  filter_upwards [hU] with x hx
  intro hxr
  rw [hx,hχ1 x (Metric.ball_subset_closedBall hxr),one_mul]

end


lemma energyOperator_contDiff (g : SmoothMetric3) : ContDiff ℝ ∞ g.energyOperator := by
  apply matrixOperator.contDiff.comp
  exact ((determinant_contDiff g.smooth).sqrt (fun x ↦ (g.positive x).det_pos.ne')).smul
    (contDiff_pi.mpr (fun i ↦ contDiff_pi.mpr (fun j ↦ g.inverse_contDiff i j)))

lemma compact_coefficient_bounds (δ : E3 → E3 →L[ℝ] E3)
    (hδ : ContDiff ℝ ∞ δ) (hsδ : HasCompactSupport δ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ (∀ x, ‖δ x‖ ≤ K) ∧
      (∀ x y, ‖δ y-δ x‖ ≤ L*‖y-x‖) := by
  obtain ⟨K,hK⟩ := continuous_compact_bound δ hδ.continuous hsδ
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsδ hδ (by simp)
  exact ⟨K,L,(norm_nonneg (δ 0)).trans (hK 0),L.coe_nonneg,hK,
    fun x y ↦ hL.norm_sub_le y x⟩

lemma convex_coefficient_coercive (B : E3 →L[ℝ] E3) (t c : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hB : ∀ v, c*‖v‖^2 ≤ ⟪B v,v⟫_ℝ) :
    ∀ v, min c 1*‖v‖^2 ≤ ⟪(ContinuousLinearMap.id ℝ E3+t • (B-ContinuousLinearMap.id ℝ E3)) v,v⟫_ℝ := by
  intro v
  have hAv : (ContinuousLinearMap.id ℝ E3+t • (B-ContinuousLinearMap.id ℝ E3)) v =
      t • B v+(1-t) • v := by
    simp only [add_apply,smul_apply,sub_apply,ContinuousLinearMap.id_apply]
    module
  have h1 : min c 1*‖v‖^2 ≤ ⟪B v,v⟫_ℝ :=
    (mul_le_mul_of_nonneg_right (min_le_left c 1) (sq_nonneg ‖v‖)).trans (hB v)
  have h2 : min c 1*‖v‖^2 ≤ ‖v‖^2 := mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _)
  rw [hAv,inner_add_left,inner_smul_left,inner_smul_left,real_inner_self_eq_norm_sq]
  simp only [conj_trivial]
  calc
    _ = t*(min c 1*‖v‖^2)+(1-t)*(min c 1*‖v‖^2) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 ht)
      (mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr ht1))

lemma bump_coefficient_coercive (B : E3 → E3 →L[ℝ] E3) (ψ : ContDiffBump (0:E3))
    (c : ℝ) (hB : ∀ x ∈ Metric.closedBall (0:E3) ψ.rOut, ∀ v, c*‖v‖^2 ≤ ⟪B x v,v⟫_ℝ) :
    ∀ x v, min c 1*‖v‖^2 ≤
      ⟪(ContinuousLinearMap.id ℝ E3+ψ x • (B x-ContinuousLinearMap.id ℝ E3)) v,v⟫_ℝ := by
  intro x v
  by_cases hx : x ∈ Metric.closedBall (0:E3) ψ.rOut
  · exact convex_coefficient_coercive (B x) (ψ x) c ψ.nonneg ψ.le_one (hB x hx) v
  · have hz : ψ x = 0 := ψ.zero_of_le_dist
      (le_of_lt (by simpa only [Metric.mem_closedBall,not_le] using hx))
    rw [hz]
    simp only [add_apply,smul_apply,
      ContinuousLinearMap.id_apply,zero_smul,add_zero,real_inner_self_eq_norm_sq]
    exact mul_le_of_le_one_left (sq_nonneg ‖v‖) (min_le_right c (1:ℝ))

theorem smooth_energy_extension (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (A : E3 → E3 →L[ℝ] E3) (C L c : ℝ), ContDiff ℝ ∞ A ∧ 0 ≤ C ∧ 0 ≤ L ∧ 0 < c ∧
      (∀ x, ‖A x‖ ≤ C) ∧ (∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖) ∧
      (∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ) ∧
      (∀ x ∈ Metric.closedBall (0:E3) R, A x = g.energyOperator x) := by
  let ψ : ContDiffBump (0:E3) := ⟨R+1,R+2,by linarith,by linarith⟩
  let I := ContinuousLinearMap.id ℝ E3
  let δ : E3 → E3 →L[ℝ] E3 := fun x ↦ ψ x • (g.energyOperator x-I)
  let A : E3 → E3 →L[ℝ] E3 := fun x ↦ I+δ x
  have hδ : ContDiff ℝ ∞ δ := ψ.contDiff.smul (g.energyOperator_contDiff.sub contDiff_const)
  have hsδ : HasCompactSupport δ := ψ.hasCompactSupport.smul_right (f':=fun x ↦ g.energyOperator x-I)
  obtain ⟨K,L,hK0,hL0,hK,hL⟩ := compact_coefficient_bounds δ hδ hsδ
  obtain ⟨c,C,hc,hC,hbound,hpos⟩ := g.energyOperator_uniform (R+2) (by linarith)
  refine ⟨A,1+K,L,min c 1,contDiff_const.add hδ,by positivity,hL0,lt_min hc zero_lt_one,?_,?_,?_,?_⟩
  · intro x
    exact (norm_add_le I (δ x)).trans (add_le_add ContinuousLinearMap.norm_id_le (hK x))
  · intro x y
    simpa only [A,add_sub_add_left_eq_sub] using hL x y
  · exact bump_coefficient_coercive g.energyOperator ψ c hpos
  · intro x hx
    have h1 : ψ x = 1 := ψ.one_of_mem_closedBall
      (Metric.closedBall_subset_closedBall (show R ≤ ψ.rIn by dsimp [ψ]; linarith) hx)
    simp only [A,δ,h1,one_smul]
    rw [←add_sub_assoc,add_sub_cancel_left]



lemma coefficient_ball_energy_eq (g : SmoothMetric3) (s : ℝ)
    (A : E3 → E3 →L[ℝ] E3) (C : ℝ) (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hC : ∀ x, ‖A x‖ ≤ C) (hAg : ∀ x ∈ Metric.closedBall (0:E3) s, A x = g.energyOperator x)
    (U : DerivativeL2) (v : ZeroSobolev s) :
    ⟪coefficientCLM A C hA hC U,sobolevDerivative s v⟫_ℝ =
      ∫ x, ⟪g.energyOperator x (U x),(sobolevDerivative s v) x⟫_ℝ := by
  rw [coefficient_inner_integral]
  apply integral_congr_ae
  filter_upwards [sobolevDerivative_supported s v] with x hx
  by_cases hxs : x ∈ Metric.closedBall (0:E3) s
  · rw [hAg x hxs]
  · rw [hx hxs]
    simp

theorem metric_weak_interior_sup_L2 (g : SmoothMetric3) (r s T : ℝ)
    (hr : 0 < r) (hrs : r < s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ZeroSobolev T,
      (∀ v : ZeroSobolev s,
        (∫ x, ⟪g.energyOperator x ((sobolevDerivative T u) x),
          (sobolevDerivative s v) x⟫_ℝ) = 0) →
      ∃ U : E3 →ᵇ ℝ, (U : E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)] (sobolevValue T u) ∧
        ‖U‖ ≤ B*‖sobolevValue T u‖ := by
  obtain ⟨A,C,L,c,hA,hC0,hL0,hc,hC,hL,hpos,hAg⟩ := g.smooth_energy_extension s (hr.trans hrs).le
  obtain ⟨B,hB,hBs⟩ := weak_interior_sup_L2 r s T hr hrs C L c hc hC0 hL0
  refine ⟨B,hB,fun u hu ↦ hBs A hA.continuous hC hL hpos u ?_⟩
  intro v
  rw [coefficient_ball_energy_eq g s A C hA.continuous.aestronglyMeasurable hC hAg]
  exact hu v

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
