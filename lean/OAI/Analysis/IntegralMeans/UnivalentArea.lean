import OAI.Analysis.IntegralMeans.Degree

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma exists_smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, χ =ᶠ[𝓝 z] fun _ => 1) ∧ ∀ z, χ z ∈ Icc 0 1 := by
  obtain ⟨L,hL,hLc,hKL,hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,ℂ) hK.isClosed hKL (n := 2)
  have hs : tsupport (χ : ℂ → ℝ) ⊆ L := by
    apply closure_minimal _ hLc
    intro z hz
    by_contra hn
    exact hz (hχ0 z hn)
  refine ⟨χ,contMDiff_iff_contDiff.mp χ.contMDiff,
    hL.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans hLU,?_,hχrange⟩
  intro z hz
  exact hχ1.filter_mono (nhds_le_nhdsSet hz)

lemma det_fderiv_complex {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℂ f z) :
    LinearMap.det (fderiv ℝ f z).toLinearMap = ‖deriv f z‖^2 := by
  rw [(hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv,determinant_complex_real,
    ← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul,
    Complex.I_mul, Complex.normSq_apply]
  ring

lemma smooth_extension_near_compact {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {x : ℂ → ℂ}
    (hx : ∀ z ∈ U, ContDiffAt ℝ 2 x z) :
    ∃ X : ℂ → ℂ, ContDiff ℝ 2 X ∧ ∀ z ∈ K, X =ᶠ[𝓝 z] x := by
  obtain ⟨χ,hχc,_hχK,hχU,hχ1,_hχrange⟩ := exists_smooth_cutoff hK hU hKU
  let X := fun z => (χ z : ℂ)*x z
  have hX : ContDiff ℝ 2 X := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hχc.contDiffAt).mul (hx z (hχU hz))
    · have he : X =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
        have hzero : χ w = 0 := notMem_support.mp (fun h => hw (subset_tsupport χ h))
        simp only [X,hzero,Complex.ofReal_zero,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨X,hX,?_⟩
  intro z hz
  filter_upwards [hχ1 z hz] with w hw
  simp only [X,hw,Complex.ofReal_one,one_mul]

lemma meromorphic_boundary_winding_le_zero {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹+h z)
    (hHd : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0}, deriv H z ≠ 0)
    (hHi : InjOn H (Metric.ball 0 1 \ {0}))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (ξ : ℂ)
    (hξ : ξ ∉ H '' Metric.sphere 0 r) :
    windingNumber (⟨fun t => H ((r : ℂ)*circleLoop t)-ξ, by
      refine Continuous.sub ?_ continuous_const
      apply hH.continuousOn.comp_continuous (by fun_prop)
      intro t
      have he : ‖(r : ℂ)*circleLoop t‖ = r := by simp [abs_of_pos hr]
      constructor
      · rw [Metric.mem_ball,dist_zero_right,he]
        exact hr1
      · change (r : ℂ)*circleLoop t ≠ 0
        exact norm_pos_iff.mp (by rw [he]; exact hr)⟩) ≤ 0 := by
  classical
  let U : Set ℂ := Metric.ball 0 1
  let K : Set ℂ := Metric.closedBall 0 r
  have hKU : K ⊆ U := Metric.closedBall_subset_ball hr1
  let x : ℂ → ℂ := fun z => 1+z*(h z-ξ)
  have hx (z) (hz : z ∈ U) : AnalyticAt ℂ x z := by
    exact analyticAt_const.add (analyticAt_id.mul ((hh.analyticOnNhd Metric.isOpen_ball z hz).sub analyticAt_const))
  obtain ⟨X,hXc,hX⟩ := smooth_extension_near_compact (isCompact_closedBall 0 r)
    Metric.isOpen_ball hKU (fun z hz => (hx z hz).contDiffAt.restrict_scalars ℝ)
  have hXval (z) (hz : z ∈ K) : X z = x z := (hX z hz).self_of_nhds
  have hxzero {z} (hz : z ∈ U) : x z = 0 ↔ z ≠ 0 ∧ H z = ξ := by
    by_cases hz0 : z = 0
    · simp [x,hz0]
    · rw [hdef z hz hz0]
      dsimp [x]
      field_simp
      constructor <;> intro he
      · exact ⟨hz0,by linear_combination he⟩
      · linear_combination he.2
  have hss : {z | z ∈ K ∧ X z = 0}.Subsingleton := by
    intro z hz w hw
    obtain ⟨hz0,hzξ⟩ := (hxzero (hKU hz.1)).mp ((hXval z hz.1) ▸ hz.2)
    obtain ⟨hw0,hwξ⟩ := (hxzero (hKU hw.1)).mp ((hXval w hw.1) ▸ hw.2)
    exact hHi ⟨hKU hz.1,hz0⟩ ⟨hKU hw.1,hw0⟩ (hzξ.trans hwξ.symm)
  let s := hss.finite.toFinset
  have hs (z) : z ∈ s ↔ z ∈ K ∧ X z = 0 := by simp [s]
  have hder (z) (hz : z ∈ s) : DifferentiableAt ℂ X z ∧ deriv X z ≠ 0 := by
    have hzK := ((hs z).mp hz).1
    have hzero := ((hs z).mp hz).2
    obtain ⟨hz0,hzξ⟩ := (hxzero (hKU hzK)).mp (by rwa [hXval z hzK] at hzero)
    have hUz : z ∈ Metric.ball (0 : ℂ) 1 \ {0} := ⟨hKU hzK,hz0⟩
    have hHd' := (hH z hUz).differentiableAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hUz)
    have heq : x =ᶠ[𝓝 z] fun w => w*(H w-ξ) := by
      filter_upwards [(Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hUz] with w hw
      have hw0 : w ≠ 0 := hw.2
      rw [hdef w hw.1 hw0]
      dsimp [x]
      field_simp [hw0]
      ring
    have hD : HasDerivAt X (z*deriv H z) z := by
      have hD := (hasDerivAt_id z).mul (hHd'.hasDerivAt.sub_const ξ)
      simp only [hzξ,sub_self,mul_zero,zero_add] at hD
      exact hD.congr_of_eventuallyEq ((hX z hzK).trans heq)
    exact ⟨hD.differentiableAt,hD.deriv ▸ mul_ne_zero hz0 (hHd z hUz)⟩
  let γ : C(unitInterval,ℂ) := (r : ℂ) • circleLoop
  have hγnorm (t) : ‖γ t‖ = r := by simp [γ,abs_of_pos hr]
  have hγK (t) : γ t ∈ K := by simpa [K] using (hγnorm t).le
  have hγU (t) : γ t ∈ U := hKU (hγK t)
  have hγ0 (t) : γ t ≠ 0 := norm_pos_iff.mp (by rw [hγnorm]; exact hr)
  have hγξ (t) : H (γ t) ≠ ξ := fun he => hξ ⟨γ t,by simpa using hγnorm t,he⟩
  let Y : C(ℂ,ℂ) := ⟨X,hXc.continuous⟩
  have hXY (t) : Y (γ t) = γ t*(H (γ t)-ξ) := by
    rw [show Y (γ t) = X (γ t) from rfl,hXval _ (hγK t),hdef _ (hγU t) (hγ0 t)]
    dsimp only [x]
    field_simp [hγ0 t]
    ring
  have hγnonzero (t) : Y (γ t) ≠ 0 := by rw [hXY]; exact mul_ne_zero (hγ0 t) (sub_ne_zero.mpr (hγξ t))
  have hi := windingNumber_finite_regular_zeros (convex_closedBall (0 : ℂ) r) s Y
    (fun z => fderiv ℝ X z) (fun z hz => ((hs z).mp hz).1)
    (fun z hz => by simp [hs,show z ∈ K from hz,Y])
    (fun z hz => ⟨((hder z hz).1.restrictScalars ℝ).hasFDerivAt,by
      rw [det_fderiv_complex (hder z hz).1]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hder z hz).2)⟩)
    γ (by simp [γ]) hγK hγnonzero
  have hins (z) (hz : z ∈ s) : ‖z‖ < r := by
    have hzK := ((hs z).mp hz).1
    have hle : ‖z‖ ≤ r := by simpa [K] using hzK
    refine lt_of_le_of_ne hle ?_
    intro he
    have hzero := ((hs z).mp hz).2
    have hzξ := ((hxzero (hKU hzK)).mp (by rwa [hXval z hzK] at hzero)).2
    exact hξ ⟨z,by simpa using he,hzξ⟩
  have hi' : windingNumber (Y.comp γ) = (s.card : ℤ) := by
    rw [hi]
    calc
      _ = ∑ _z ∈ s, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [loopIndex_circle_inside hr (hins z hz),mul_one]
        simp only [planeIndex,det_fderiv_complex (hder z hz).1,
          sq_pos_of_pos (norm_pos_iff.mpr (hder z hz).2),ite_true]
      _ = ↑s.card := by simp
  have hcard : s.card ≤ 1 := Finset.card_le_one.mpr (by
    intro z hz w hw
    exact hss ((hs z).mp hz) ((hs w).mp hw))
  let η : C(unitInterval,ℂ) := ⟨fun t => H (γ t)-ξ,by
    refine Continuous.sub ?_ continuous_const
    apply hH.continuousOn.comp_continuous γ.continuous
    exact fun t => ⟨hγU t,hγ0 t⟩⟩
  have he : Y.comp γ = γ*η := by ext t; exact hXY t
  have hwγ : windingNumber γ = 1 := by
    apply windingNumber_eq_of_logIncrement (by simp [γ])
    simpa [γ] using circleLoop_logIncrement (r : ℂ) (by exact_mod_cast hr.ne')
  rw [he,windingNumber_mul γ η (by simp [γ]) (by simp [η,γ]) hγ0
    (fun t => sub_ne_zero.mpr (hγξ t)),hwγ] at hi'
  change windingNumber η ≤ 0
  have hc : (s.card : ℤ) ≤ 1 := by exact_mod_cast hcard
  omega

lemma det_holomorphic_plus_conjugate {h : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z) (a : ℝ) :
    LinearMap.det (fderiv ℝ (fun w => a • conj w+h w) z).toLinearMap =
      ‖deriv h z‖^2-a^2 := by
  have hD := (Complex.conjCLE.hasFDerivAt.const_smul a).add
    (hh.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  change HasFDerivAt (fun w => a • conj w+h w) _ z at hD
  rw [hD.fderiv,determinant_complex_real,← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe,add_apply,
    smul_apply,ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,one_mul,Complex.real_smul,Complex.normSq_apply]
  simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
  ring

lemma meromorphic_univalent_area {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹+h z)
    (hHd : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0}, deriv H z ≠ 0)
    (hHi : InjOn H (Metric.ball 0 1 \ {0}))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∫ z in Metric.closedBall 0 r, ‖deriv h z‖^2 ∂volume ≤
      volume.real (Metric.closedBall (0 : ℂ) r) * (r^2)⁻¹^2 := by
  let K : Set ℂ := Metric.closedBall 0 r
  let x : ℂ → ℂ := fun z => (r^2)⁻¹ • conj z+h z
  have hKU : K ⊆ Metric.ball 0 1 := Metric.closedBall_subset_ball hr1
  have hx (z) (hz : z ∈ Metric.ball (0 : ℂ) 1) : ContDiffAt ℝ 2 x z := by
    exact (Complex.conjCLE.contDiff.contDiffAt.const_smul (r^2)⁻¹).add
      ((hh.analyticOnNhd Metric.isOpen_ball z hz).contDiffAt.restrict_scalars ℝ)
  obtain ⟨X,hXc,hX⟩ := smooth_extension_near_compact (isCompact_closedBall 0 r)
    Metric.isOpen_ball hKU hx
  have hXval (z) (hz : z ∈ K) : X z = x z := (hX z hz).self_of_nhds
  have hb (z) (hz : z ∈ Metric.sphere (0 : ℂ) r) : X z = H z := by
    have hn : ‖z‖ = r := by simpa using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by rw [hn];exact hr)
    rw [hXval z (Metric.sphere_subset_closedBall hz),hdef z (hKU (Metric.sphere_subset_closedBall hz)) hz0]
    dsimp [x]
    rw [Complex.inv_def,Complex.normSq_eq_norm_sq,hn]
    congr 1
    simp [mul_comm]
  have hw (ξ) (hξ : ξ ∉ X '' Metric.sphere 0 r) :
      windingNumber (⟨fun t => X ((r : ℂ)*circleLoop t)-ξ,by fun_prop⟩) ≤ 0 := by
    have hξ' : ξ ∉ H '' Metric.sphere 0 r := by
      rintro ⟨z,hz,hzξ⟩
      exact hξ ⟨z,hz,(hb z hz).trans hzξ⟩
    have hw := meromorphic_boundary_winding_le_zero hh hH hdef hHd hHi hr hr1 ξ hξ'
    convert hw using 2
    ext t
    change X ((r : ℂ)*circleLoop t)-ξ = H ((r : ℂ)*circleLoop t)-ξ
    rw [hb _ (by simp [abs_of_pos hr])]
  have hi := integral_jacobian_nonpos_of_boundary_winding
    (hXc.of_le (by norm_num)) hr hw
  have hdet (z) (hz : z ∈ K) :
      LinearMap.det (fderiv ℝ X z).toLinearMap = ‖deriv h z‖^2-(r^2)⁻¹^2 := by
    rw [(hX z hz).fderiv_eq]
    exact det_holomorphic_plus_conjugate
      ((hh z (hKU hz)).differentiableAt (Metric.isOpen_ball.mem_nhds (hKU hz))) _
  have hdcont : ContinuousOn (deriv h) K :=
    (hh.deriv Metric.isOpen_ball).continuousOn.mono hKU
  have hint : IntegrableOn (fun z => ‖deriv h z‖^2) K :=
    (hdcont.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 r)
  have hconst : IntegrableOn (fun _ : ℂ => (r^2)⁻¹^2) K :=
    integrableOn_const (isCompact_closedBall 0 r).measure_ne_top
  have he : (∫ z in K, LinearMap.det (fderiv ℝ X z).toLinearMap) =
      (∫ z in K, ‖deriv h z‖^2) - volume.real K * (r^2)⁻¹^2 := by
    rw [setIntegral_congr_fun measurableSet_closedBall hdet,
      integral_sub hint hconst]
    simp
  rw [he] at hi
  exact sub_nonpos.mp hi

end Brennan

end

end OAI
