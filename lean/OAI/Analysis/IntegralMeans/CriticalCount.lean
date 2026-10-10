import OAI.Analysis.IntegralMeans.LevelIndex

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

def squaredReciprocalPotential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ :=
  ‖f z-ξ‖^2 * z.im^(-2*k)

lemma squaredReciprocalPotential_eq_sq {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ halfPlane) :
    squaredReciprocalPotential f k ξ z = (reciprocalPotential f k ξ z)^2 := by
  rw [squaredReciprocalPotential,reciprocalPotential,div_pow]
  have he : z.im^(-2*k) = ((z.im^k)^2)⁻¹ := by
    rw [show -2*k = -(k*2) by ring, Real.rpow_neg hz.le, Real.rpow_mul hz.le,
      Real.rpow_two]
  rw [he,div_eq_mul_inv]

lemma squaredReciprocalPotential_nonneg {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ halfPlane) : 0 ≤ squaredReciprocalPotential f k ξ z := by
  rw [squaredReciprocalPotential_eq_sq hz]
  exact sq_nonneg _

lemma contDiffAt_squaredReciprocalPotential {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (ξ : ℂ) :
    ContDiffAt ℝ 2 (squaredReciprocalPotential f k ξ) z := by
  have hc : ContDiffAt ℝ 2 f z :=
    (hf.1.analyticOnNhd isOpen_halfPlane z hz).contDiffAt.restrict_scalars ℝ
  exact ((hc.sub contDiffAt_const).norm_sq ℂ).mul
    (Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne (ne_of_gt hz))

lemma potential_ge_iff_reciprocalPotential_le {f : ℂ → ℂ} {k h : ℝ}
    (hk : 0 ≤ k) (hh : 0 < h) {ξ z : ℂ} (hz : z ∈ halfPlane) :
    ENNReal.ofReal h ≤ potential f k ξ z ↔ reciprocalPotential f k ξ z ≤ h⁻¹ := by
  have hy := Real.rpow_pos_of_pos hz k
  rw [potential,ENNReal.ofReal_rpow_of_nonneg hz.le hk,
    ENNReal.le_div_iff_mul_le
      (Or.inr (ne_of_gt (ENNReal.ofReal_pos.mpr hy))) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul hh.le,ENNReal.ofReal_le_ofReal_iff hy.le,reciprocalPotential,
    div_le_iff₀ hy,inv_mul_eq_div,le_div_iff₀ hh]
  exact mul_comm h ‖f z-ξ‖ ▸ Iff.rfl

lemma compact_squaredReciprocal_sublevel {f : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    {ξ : ℂ} (hg : GoodPair f k ξ) {d : ℝ} (hd : 0 < d) :
    IsCompact {z | z ∈ halfPlane ∧ squaredReciprocalPotential f k ξ z ≤ d} := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have he : {z | z ∈ halfPlane ∧ squaredReciprocalPotential f k ξ z ≤ d} =
      {z | z ∈ halfPlane ∧ ENNReal.ofReal ((Real.sqrt d)⁻¹) ≤ potential f k ξ z} := by
    ext z
    constructor
    · rintro ⟨hz,hzval⟩
      refine ⟨hz,(potential_ge_iff_reciprocalPotential_le hk (inv_pos.mpr hs) hz).mpr ?_⟩
      rw [inv_inv]
      rw [squaredReciprocalPotential_eq_sq hz] at hzval
      nlinarith [Real.sq_sqrt hd.le]
    · rintro ⟨hz,hzval⟩
      have hv := (potential_ge_iff_reciprocalPotential_le hk (inv_pos.mpr hs) hz).mp hzval
      rw [inv_inv] at hv
      refine ⟨hz,?_⟩
      rw [squaredReciprocalPotential_eq_sq hz]
      have hn : 0 ≤ reciprocalPotential f k ξ z := div_nonneg (norm_nonneg _) (Real.rpow_nonneg hz.le _)
      nlinarith [Real.sq_sqrt hd.le]
  rw [he]
  exact hg.1 _ (inv_pos.mpr hs)

lemma regularizedGradient_formula {f : ℂ → ℂ} {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ halfPlane) :
    regularizedGradient f k ξ z =
      ((k : ℂ)*Complex.I/(z.im : ℂ))*((‖f z-ξ‖^2 : ℝ) : ℂ) -
        (f z-ξ)*conj (deriv f z) := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have he : conj (criticalMap f k z-ξ) = conj (f z-ξ) +
      Complex.I/(k : ℂ)*(z.im : ℂ)*conj (deriv f z) := by
    simp only [criticalMap, div_eq_mul_inv, map_sub, map_mul, map_inv₀, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [regularizedGradient,he,mul_add, mul_assoc _ (f z-ξ),Complex.mul_conj',
    ← Complex.ofReal_pow]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma fderiv_squaredReciprocalPotential_apply {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ halfPlane) (v : ℂ) :
    fderiv ℝ (squaredReciprocalPotential f k ξ) z v =
      -2*z.im^(-2*k)*(regularizedGradient f k ξ z * conj v).re := by
  have hd := (((hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)).hasDerivAt.sub_const ξ).hasFDerivAt.restrictScalars ℝ
  have hy := Complex.imCLM.hasFDerivAt.rpow_const (p := -2*k) (Or.inl (ne_of_gt hz))
  have hu := hd.norm_sq.fun_mul hy
  simp only [Complex.imCLM_apply] at hu
  change (fderiv ℝ (fun w => ‖f w - ξ‖ ^ 2 * w.im ^ (-2*k)) z) v = _
  rw [hu.fderiv]
  simp only [smul_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,innerSL_apply_apply,Complex.imCLM_apply]
  rw [regularizedGradient_formula hk hz,Real.rpow_sub hz,Real.rpow_one]
  simp only [Complex.inner,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.sub_re,Complex.sub_im,Complex.div_re,Complex.div_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.normSq_ofReal]
  field_simp [ne_of_gt (show 0 < z.im from hz)]
  ring

lemma fderiv_squaredReciprocalPotential_eq_zero_iff {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ halfPlane) :
    fderiv ℝ (squaredReciprocalPotential f k ξ) z = 0 ↔
      regularizedGradient f k ξ z = 0 := by
  constructor
  · intro hzero
    have hh := fderiv_squaredReciprocalPotential_apply hf hk (ξ := ξ) hz
      (regularizedGradient f k ξ z)
    rw [hzero, zero_apply, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re] at hh
    have hp := Real.rpow_pos_of_pos hz (-2*k)
    have hn := norm_nonneg (regularizedGradient f k ξ z)
    apply norm_eq_zero.mp
    have hsq : ‖regularizedGradient f k ξ z‖^2 = 0 :=
      (mul_eq_zero.mp hh.symm).resolve_left (mul_ne_zero (by norm_num) (ne_of_gt hp))
    nlinarith
  · intro hzero
    ext v
    rw [fderiv_squaredReciprocalPotential_apply hf hk hz v, hzero]
    simp

lemma det_regularizedGradient_ne_zero {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : k ≠ 0) {ξ : ℂ} (hg : GoodPair f k ξ)
    {z : ℂ} (hz : z ∈ halfPlane) (hzero : regularizedGradient f k ξ z = 0) :
    LinearMap.det (fderiv ℝ (regularizedGradient f k ξ) z).toLinearMap ≠ 0 := by
  rcases (regularizedGradient_eq_zero_iff hk hz).mp hzero with hp | hc
  · exact ne_of_gt (det_regularizedGradient_at_pole_pos hf hk hz hp)
  · rw [det_regularizedGradient_at_critical hf hz hc]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact neg_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr
          (mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk)
            Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
            (sub_ne_zero.mpr (criticalMap_ne_pole hf hk hz hc)))))
      · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
          (univalent_deriv_ne_zero isOpen_halfPlane hf hz))
    · exact hg.2 z hz hc

lemma compact_convex_halfPlane_envelope {P : Set ℂ} (hP : IsCompact P)
    (hPH : P ⊆ halfPlane) :
    ∃ K : Set ℂ, IsCompact K ∧ Convex ℝ K ∧ P ⊆ K ∧ K ⊆ halfPlane := by
  obtain ⟨η,hη,hheight⟩ := hP.exists_forall_le' Complex.continuous_im.continuousOn hPH
  obtain ⟨R,hR⟩ := hP.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨Metric.closedBall 0 R ∩ {z : ℂ | η ≤ z.im},
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const Complex.continuous_im),
    (convex_closedBall (0 : ℂ) R).inter (convex_halfSpace_im_ge η),?_,?_⟩
  · exact fun z hz => ⟨hR hz,hheight z hz⟩
  · exact fun z hz => hη.trans_le hz.2

lemma continuous_extension_near_compact {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {x : ℂ → ℂ}
    (hx : ∀ z ∈ U, ContinuousAt x z) :
    ∃ X : C(ℂ,ℂ), ∀ z ∈ K, (X : ℂ → ℂ) =ᶠ[𝓝 z] x := by
  obtain ⟨χ,hχc,_hχK,hχU,hχ1,_hχrange⟩ := exists_smooth_cutoff hK hU hKU
  let X := fun z => (χ z : ℂ)*x z
  have hX : Continuous X := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact (Complex.continuous_ofReal.continuousAt.comp hχc.continuous.continuousAt).mul
        (hx z (hχU hz))
    · have he : X =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
        have hzero : χ w = 0 := notMem_support.mp (fun h => hw (subset_tsupport χ h))
        simp only [X,hzero,Complex.ofReal_zero,zero_mul]
      exact continuousAt_const.congr he.symm
  refine ⟨⟨X,hX⟩,?_⟩
  intro z hz
  filter_upwards [hχ1 z hz] with w hw
  simp only [ContinuousMap.coe_mk,X,hw,Complex.ofReal_one,one_mul]

lemma squaredReciprocalPotential_lt_windingInterior {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k c : ℝ} (hk : 0 < k) (hc : 0 < c) (ξ : ℂ)
    (γ : C(unitInterval,ℂ)) (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ halfPlane)
    (hlevel : ∀ t, squaredReciprocalPotential f k ξ (γ t) = c)
    {z : ℂ} (hz : z ∈ windingInterior γ) :
    z ∈ halfPlane ∧ squaredReciprocalPotential f k ξ z < c := by
  have hzH := closure_windingInterior_subset_halfPlane γ hloop hγ (subset_closure hz)
  have hb : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hl (t) : reciprocalPotential f k ξ (γ t) = Real.sqrt c := by
    have hsq := hlevel t
    rw [squaredReciprocalPotential_eq_sq (hγ t)] at hsq
    have hn : 0 ≤ reciprocalPotential f k ξ (γ t) :=
      div_nonneg (norm_nonneg _) (Real.rpow_nonneg (hγ t).le _)
    nlinarith [Real.sq_sqrt hc.le]
  have hh := reciprocalPotential_lt_on_windingInterior hf hk hb ξ γ hloop hγ hl hz
  have hn : 0 ≤ reciprocalPotential f k ξ z :=
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg hzH.le _)
  refine ⟨hzH,?_⟩
  rw [squaredReciprocalPotential_eq_sq hzH]
  nlinarith [Real.sq_sqrt hc.le]

lemma regular_potential_level_index_sum {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {c : ℝ} (hc : 0 < c)
    (hreg : ∀ z ∈ halfPlane, squaredReciprocalPotential f k ξ z = c →
      regularizedGradient f k ξ z ≠ 0) :
    ∃ (s : Finset ℂ) (N : ℕ),
      (∀ z ∈ s, z ∈ halfPlane ∧ regularizedGradient f k ξ z = 0) ∧
      (∀ z ∈ halfPlane, squaredReciprocalPotential f k ξ z < c →
        (z ∈ s ↔ regularizedGradient f k ξ z = 0)) ∧
      (∑ z ∈ s, if squaredReciprocalPotential f k ξ z < c then
        planeIndex (fderiv ℝ (regularizedGradient f k ξ) z) else 0) = (N : ℤ) ∧
      ((∃ z ∈ halfPlane, f z = ξ) → 1 ≤ N) := by
  classical
  let u := squaredReciprocalPotential f k ξ
  let x := regularizedGradient f k ξ
  let d := c+1
  have hcd : c < d := by dsimp [d]; linarith
  have hd : 0 < d := hc.trans hcd
  have hP := compact_squaredReciprocal_sublevel hk.le hg hd
  obtain ⟨K,hK,hKcv,hPK,hKH⟩ := compact_convex_halfPlane_envelope hP (fun _ h => h.1)
  obtain ⟨F,hFc,hFs,hFeq,hFout,hFle,hFlt⟩ := extend_compact_sublevel isOpen_halfPlane
    (fun z hz => contDiffAt_squaredReciprocalPotential hf hz k ξ) hP
  have hlevel (z) (hz : F z = c) : z ∈ halfPlane ∧ u z = c := by
    have hh := (hFle z c hcd).mp hz.le
    exact ⟨hh.1, ((hFeq z hh.1 (hh.2.trans hcd.le)).self_of_nhds).symm.trans hz⟩
  have hFreg (z) (hz : F z = c) : fderiv ℝ F z ≠ 0 := by
    obtain ⟨hzH,huz⟩ := hlevel z hz
    rw [(hFeq z hzH (huz.le.trans hcd.le)).fderiv_eq]
    exact fun hh => hreg z hzH huz ((fderiv_squaredReciprocalPotential_eq_zero_iff
      hf (ne_of_gt hk) hzH).mp hh)
  have hL : IsCompact {z | F z = c} := hP.of_isClosed_subset
    (isClosed_eq hFc.continuous continuous_const)
    (fun z hz => ⟨(hlevel z hz).1, (hlevel z hz).2.le.trans hcd.le⟩)
  obtain ⟨C,hC,hdis,hcurves⟩ := compact_regular_level_oriented_curves hFc hFs hFreg hL
  let ι := {S : Set ℂ // S ∈ C}
  choose γ hγrange hγc hγp hγi hγd hγm hγr hγdown using
    (fun S : ι => hcurves S.1 S.2)
  have hγlevel (i : ι) (t : ℝ) : F (γ i t) = c := by
    have hh : γ i t ∈ ⋃ S ∈ C, S := mem_iUnion₂.mpr
      ⟨i.1,i.2,hγrange i ▸ mem_range_self t⟩
    rwa [hC] at hh
  have hγH (i : ι) (t : ℝ) : γ i t ∈ halfPlane := (hlevel _ (hγlevel i t)).1
  have hγu (i : ι) (t : ℝ) : u (γ i t) = c := (hlevel _ (hγlevel i t)).2
  have hcover (z) : F z = c ↔ ∃ i : ι, z ∈ range (γ i) := by
    constructor
    · intro hz
      have hm : z ∈ ⋃ S ∈ C, S := hC.symm ▸ hz
      obtain ⟨S,hS,hzS⟩ := mem_iUnion₂.mp hm
      exact ⟨⟨S,hS⟩, (hγrange ⟨S,hS⟩).symm ▸ hzS⟩
    · rintro ⟨i,t,rfl⟩
      exact hγlevel i t
  have hγdis (i j : ι) (hij : i ≠ j) : Disjoint (range (γ i)) (range (γ j)) := by
    rw [hγrange,hγrange]
    exact hdis i.1 i.2 j.1 j.2 (Subtype.val_injective.ne hij)
  have hbelow (i : ι) (w : ℂ) (hw : w ∉ range (γ i))
      (hind : loopIndex (periodicLoop (hγc i).continuous 0) w ≠ 0) : F w < c := by
    have hw' : w ∈ windingInterior (periodicLoop (hγc i).continuous 0) :=
      ⟨by rwa [periodicLoop_range _ (hγp i) 0],hind⟩
    have hh := squaredReciprocalPotential_lt_windingInterior hf hk hc ξ
      (periodicLoop (hγc i).continuous 0) (periodicLoop_closed _ (hγp i) 0)
      (fun t => hγH i ((t:ℝ)+0)) (fun t => hγu i ((t:ℝ)+0)) hw'
    exact (hFlt w c hcd).mpr hh
  have hFzero : F 0 = d := hFout 0 (by simp [halfPlane])
  have habove : ∃ z, c < F z := ⟨0,hFzero ▸ hcd⟩
  obtain ⟨X,hXeq⟩ := continuous_extension_near_compact hK isOpen_halfPlane hKH
    (fun z hz => (differentiableAt_regularizedGradient hf hz k ξ).continuousAt)
  have hfinite : {z | z ∈ K ∧ x z = 0}.Finite := finite_regular_zeros_on_compact hK
    (fun z hz => (differentiableAt_regularizedGradient hf (hKH hz) k ξ).continuousAt.continuousWithinAt)
    (fun z hz hzero => ⟨differentiableAt_regularizedGradient hf (hKH hz) k ξ,
      det_regularizedGradient_ne_zero hf (ne_of_gt hk) hg (hKH hz) hzero⟩)
  let s := hfinite.toFinset
  have hs (z) : z ∈ s ↔ z ∈ K ∧ x z = 0 := hfinite.mem_toFinset
  have hsK (z) (hz : z ∈ s) : z ∈ K := ((hs z).mp hz).1
  have hXzero (z) (hz : z ∈ K) : X z = 0 ↔ z ∈ s := by
    rw [(hXeq z hz).self_of_nhds,hs]
    exact ⟨fun h => ⟨hz,h⟩,fun h => h.2⟩
  have hD (z) (hz : z ∈ s) :
      HasFDerivAt X (fderiv ℝ x z) z ∧ LinearMap.det (fderiv ℝ x z).toLinearMap ≠ 0 := by
    refine ⟨(differentiableAt_regularizedGradient hf (hKH (hsK z hz)) k ξ).hasFDerivAt.congr_of_eventuallyEq
      (hXeq z (hsK z hz)),?_⟩
    exact det_regularizedGradient_ne_zero hf (ne_of_gt hk) hg (hKH (hsK z hz)) ((hs z).mp hz).2
  have hγK (i : ι) (t : ℝ) : γ i t ∈ K := hPK ⟨hγH i t,(hγu i t).le.trans hcd.le⟩
  have hX (i : ι) (t : ℝ) : X (γ i t) ≠ 0 := by
    rw [(hXeq _ (hγK i t)).self_of_nhds]
    exact hreg _ (hγH i t) (hγu i t)
  have horth (i : ι) (t : ℝ) : (X (γ i t)*conj (deriv (γ i) t)).re = 0 := by
    have he : HasDerivAt (fun q => F (γ i q))
        (fderiv ℝ F (γ i t) (deriv (γ i) t)) t :=
      ((hFc.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt t
        (((hγc i).differentiable (by norm_num)) t).hasDerivAt
    have he0 : fderiv ℝ F (γ i t) (deriv (γ i) t) = 0 :=
      (he.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun q => (hγlevel i q).symm))).unique (hasDerivAt_const t c)
    rw [(hFeq _ (hγH i t) ((hγu i t).le.trans hcd.le)).fderiv_eq,
      fderiv_squaredReciprocalPotential_apply hf (ne_of_gt hk) (hγH i t)] at he0
    rw [(hXeq _ (hγK i t)).self_of_nhds]
    exact (mul_eq_zero.mp he0).resolve_left (mul_ne_zero (by norm_num)
      (ne_of_gt (Real.rpow_pos_of_pos (hγH i t) (-2*k))))
  have hsum := regular_level_index_sum hFc.continuous γ hγc hγp hγi hγd hγm hγr hγdown
    hγlevel (fun z hz => ⟨hFc.contDiffAt.of_le (by norm_num),hFreg z hz⟩)
    hcover hγdis hbelow habove hKcv hγK s X (fderiv ℝ x) hsK hXzero hD hX horth
  refine ⟨s,Fintype.card ι,?_,?_,?_,?_⟩
  · intro z hz
    exact ⟨hKH (hsK z hz),((hs z).mp hz).2⟩
  · intro z hzH hzu
    rw [hs]
    exact ⟨fun h => h.2,fun hx => ⟨hPK ⟨hzH,hzu.le.trans hcd.le⟩,hx⟩⟩
  · convert hsum using 1
    apply Finset.sum_congr rfl
    intro z hz
    simp only [show (F z < c) ↔ u z < c from (hFlt z c hcd).trans
      (and_iff_right (hKH (hsK z hz)))]
    rfl
  · rintro ⟨z,hzH,hpole⟩
    have huz : u z = 0 := by simp [u,squaredReciprocalPotential,hpole]
    have hFz : F z = 0 := (hFeq z hzH (huz.le.trans hd.le)).self_of_nhds.trans huz
    obtain ⟨w,hw⟩ := intermediate_value_univ z 0 hFc.continuous
      (show c ∈ Icc (F z) (F 0) by rw [hFz,hFzero]; exact ⟨hc.le,hcd.le⟩)
    obtain ⟨i,_hi⟩ := (hcover w).mp hw
    exact Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)

lemma planeIndex_regularizedGradient_at_critical {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ halfPlane) (hcrit : criticalMap f k z = ξ) :
    planeIndex (fderiv ℝ (regularizedGradient f k ξ) z) =
      if normalizedJacobian f k z < 0 then 1 else -1 := by
  have hp : 0 < ‖((k : ℂ)*Complex.I/(z.im : ℂ))*(f z-ξ)‖^2 * ‖deriv f z‖^2 := by
    apply mul_pos
    · apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      exact mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk)
        Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
        (sub_ne_zero.mpr (criticalMap_ne_pole hf hk hz hcrit))
    · exact sq_pos_of_pos (norm_pos_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane hf hz))
  rw [planeIndex,det_regularizedGradient_at_critical hf hz hcrit]
  congr 1
  apply propext
  rw [neg_mul,neg_mul,neg_pos]
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg hp.le (le_of_not_gt hn))) h
  · exact mul_neg_of_pos_of_neg hp

lemma critical_count_strict_sublevel {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {c : ℝ} (hc : 0 < c)
    (hreg : ∀ z ∈ halfPlane, squaredReciprocalPotential f k ξ z = c →
      regularizedGradient f k ξ z ≠ 0) :
    let critical := {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧
      squaredReciprocalPotential f k ξ z < c}
    critical.Finite ∧ ({z ∈ critical | 0 < normalizedJacobian f k z}).ncard ≤
      ({z ∈ critical | normalizedJacobian f k z < 0}).ncard := by
  classical
  dsimp only
  obtain ⟨s,N,hs,hsall,hsum,hpole⟩ := regular_potential_level_index_sum hf hk hg hc hreg
  let u := squaredReciprocalPotential f k ξ
  let p := s.filter (fun z => u z < c ∧ f z = ξ)
  let m := s.filter (fun z => u z < c ∧ criticalMap f k z = ξ ∧ normalizedJacobian f k z < 0)
  let a := s.filter (fun z => u z < c ∧ criticalMap f k z = ξ ∧ 0 < normalizedJacobian f k z)
  have hcritmem (z) (hz : z ∈ halfPlane) (hG : criticalMap f k z = ξ) (hu : u z < c) : z ∈ s :=
    (hsall z hz hu).mpr ((regularizedGradient_eq_zero_iff (ne_of_gt hk) hz).mpr (Or.inr hG))
  have hfinite : {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c}.Finite :=
    s.finite_toSet.subset (fun z hz => hcritmem z hz.1 hz.2.1 hz.2.2)
  have hmset : {z | (z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c) ∧
      normalizedJacobian f k z < 0} = (m : Set ℂ) := by
    ext z
    simp only [m,Finset.mem_coe,Finset.mem_filter,mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hz,hG,hu⟩,hJ⟩
      exact ⟨hcritmem z hz hG hu,hu,hG,hJ⟩
    · rintro ⟨hz,hu,hG,hJ⟩
      exact ⟨⟨(hs z hz).1,hG,hu⟩,hJ⟩
  have haset : {z | (z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c) ∧
      0 < normalizedJacobian f k z} = (a : Set ℂ) := by
    ext z
    simp only [a,Finset.mem_coe,Finset.mem_filter,mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hz,hG,hu⟩,hJ⟩
      exact ⟨hcritmem z hz hG hu,hu,hG,hJ⟩
    · rintro ⟨hz,hu,hG,hJ⟩
      exact ⟨⟨(hs z hz).1,hG,hu⟩,hJ⟩
  have hpcard : p.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    obtain ⟨hz,huz,hpz⟩ := Finset.mem_filter.mp hz
    obtain ⟨hw,huw,hpw⟩ := Finset.mem_filter.mp hw
    exact hf.2 (hs z hz).1 (hs w hw).1 (hpz.trans hpw.symm)
  have hpN : p.card ≤ N := by
    by_cases hpe : p = ∅
    · simp [hpe]
    · obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.mpr hpe
      obtain ⟨hz,huz,hpz⟩ := Finset.mem_filter.mp hz
      exact hpcard.trans (hpole ⟨z,(hs z hz).1,hpz⟩)
  have hterm (z) (hz : z ∈ s) :
      (if u z < c then planeIndex (fderiv ℝ (regularizedGradient f k ξ) z) else 0) =
        (if u z < c ∧ f z = ξ then (1 : ℤ) else 0) +
        (if u z < c ∧ criticalMap f k z = ξ ∧ normalizedJacobian f k z < 0 then 1 else 0) -
        (if u z < c ∧ criticalMap f k z = ξ ∧ 0 < normalizedJacobian f k z then 1 else 0) := by
    by_cases hu : u z < c
    · simp only [hu,true_and,ite_true]
      rcases (regularizedGradient_eq_zero_iff (ne_of_gt hk) (hs z hz).1).mp (hs z hz).2 with hpz | hG
      · have hGn : criticalMap f k z ≠ ξ := fun h => criticalMap_ne_pole hf (ne_of_gt hk) (hs z hz).1 h hpz
        simp [hpz,hGn,planeIndex,det_regularizedGradient_at_pole_pos hf (ne_of_gt hk) (hs z hz).1 hpz]
      · have hpn := criticalMap_ne_pole hf (ne_of_gt hk) (hs z hz).1 hG
        rw [planeIndex_regularizedGradient_at_critical hf (ne_of_gt hk) (hs z hz).1 hG]
        rcases lt_or_gt_of_ne (hg.2 z (hs z hz).1 hG) with hJ | hJ
        · simp [hpn,hG,hJ,not_lt_of_ge hJ.le]
        · simp [hpn,hG,hJ,not_lt_of_ge hJ.le]
    · simp [hu]
  have heuler : (p.card : ℤ) + m.card - a.card = N := by
    rw [← hsum]
    calc
      (p.card : ℤ) + m.card - a.card =
          ∑ z ∈ s, ((if u z < c ∧ f z = ξ then (1 : ℤ) else 0) +
            (if u z < c ∧ criticalMap f k z = ξ ∧ normalizedJacobian f k z < 0 then 1 else 0) -
            (if u z < c ∧ criticalMap f k z = ξ ∧ 0 < normalizedJacobian f k z then 1 else 0)) := by
        simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_boole,p,m,a]
      _ = _ := Finset.sum_congr rfl (fun z hz => (hterm z hz).symm)
  refine ⟨hfinite,?_⟩
  change ({z | (z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c) ∧
      0 < normalizedJacobian f k z}).ncard ≤
    ({z | (z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c) ∧
      normalizedJacobian f k z < 0}).ncard
  rw [haset,hmset,Set.ncard_coe_finset,Set.ncard_coe_finset]
  omega

lemma finite_critical_squared_sublevel {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 ≤ k) {ξ : ℂ} (hg : GoodPair f k ξ) {d : ℝ} (hd : 0 < d) :
    {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧
      squaredReciprocalPotential f k ξ z ≤ d}.Finite := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  apply (finite_critical_superlevel hf hg (h := (Real.sqrt d)⁻¹) (inv_pos.mpr hs)).subset
  intro z hz
  refine ⟨hz.1,hz.2.1,(potential_ge_iff_reciprocalPotential_le hk (inv_pos.mpr hs) hz.1).mpr ?_⟩
  rw [inv_inv]
  have hh := hz.2.2
  rw [squaredReciprocalPotential_eq_sq hz.1] at hh
  nlinarith [Real.sq_sqrt hd.le]

lemma potential_ge_iff_squaredReciprocal_le {f : ℂ → ℂ} {k h : ℝ}
    (hk : 0 ≤ k) (hh : 0 < h) {ξ z : ℂ} (hz : z ∈ halfPlane) :
    ENNReal.ofReal h ≤ potential f k ξ z ↔
      squaredReciprocalPotential f k ξ z ≤ (h⁻¹)^2 := by
  rw [potential_ge_iff_reciprocalPotential_le hk hh hz,squaredReciprocalPotential_eq_sq hz]
  exact (sq_le_sq₀ (div_nonneg (norm_nonneg _) (Real.rpow_nonneg hz.le _))
    (inv_nonneg.mpr hh.le)).symm

lemma finset_gap_above (s : Finset ℝ) (r d : ℝ) (hrd : r < d) :
    ∃ c, r < c ∧ c < d ∧ ∀ a ∈ s, r < a → c < a := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty =>
    obtain ⟨c,hrc,hcd⟩ := exists_between hrd
    exact ⟨c,hrc,hcd,by simp⟩
  | @insert a s ha ih =>
    by_cases hra : r < a
    · obtain ⟨c,hrc,hcd,hcs⟩ := ih (min d a) (lt_min hrd hra)
      refine ⟨c,hrc,hcd.trans_le (min_le_left _ _),?_⟩
      intro b hb hrb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hcd.trans_le (min_le_right _ _)
      · exact hcs b hb hrb
    · obtain ⟨c,hrc,hcd,hcs⟩ := ih d hrd
      refine ⟨c,hrc,hcd,?_⟩
      intro b hb hrb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (hra hrb).elim
      · exact hcs b hb hrb

theorem critical_count {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {h : ℝ} (hh : 0 < h) :
    let critical := {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧
      ENNReal.ofReal h ≤ potential f k ξ z}
    critical.Finite ∧ ({z ∈ critical | 0 < normalizedJacobian f k z}).ncard ≤
      ({z ∈ critical | normalizedJacobian f k z < 0}).ncard := by
  classical
  let u := squaredReciprocalPotential f k ξ
  let r := (h⁻¹)^2
  have hr : 0 < r := sq_pos_of_pos (inv_pos.mpr hh)
  have hd : 0 < r+1 := by linarith
  have hfinite := finite_critical_squared_sublevel hf hk.le hg hd
  let s := hfinite.toFinset.image u
  obtain ⟨c,hrc,hcd,hcs⟩ := finset_gap_above s r (r+1) (by linarith)
  have hcmem (z) (hz : z ∈ halfPlane) (hG : criticalMap f k z = ξ)
      (hu : u z ≤ r+1) : u z ∈ s :=
    Finset.mem_image.mpr ⟨z,hfinite.mem_toFinset.mpr ⟨hz,hG,hu⟩,rfl⟩
  have hcut (z) (hz : z ∈ halfPlane) (hG : criticalMap f k z = ξ) : u z < c ↔ u z ≤ r := by
    constructor
    · intro huc
      by_contra hn
      have hru : r < u z := lt_of_not_ge hn
      exact (hcs (u z) (hcmem z hz hG (huc.trans hcd).le) hru).not_gt huc
    · exact fun h => h.trans_lt hrc
  have hreg (z) (hz : z ∈ halfPlane) (huc : u z = c) : regularizedGradient f k ξ z ≠ 0 := by
    intro hzero
    rcases (regularizedGradient_eq_zero_iff (ne_of_gt hk) hz).mp hzero with hp | hG
    · have huz : u z = 0 := by simp [u,squaredReciprocalPotential,hp]
      linarith
    · have hmem := hcmem z hz hG (huc.le.trans hcd.le)
      have hcc := hcs (u z) hmem (hrc.trans_eq huc.symm)
      linarith
  have hc := critical_count_strict_sublevel hf hk hg (hr.trans hrc) hreg
  have he : {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ ENNReal.ofReal h ≤ potential f k ξ z} =
      {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c} := by
    ext z
    constructor
    · rintro ⟨hz,hG,hV⟩
      exact ⟨hz,hG,(hcut z hz hG).mpr ((potential_ge_iff_squaredReciprocal_le hk.le hh hz).mp hV)⟩
    · rintro ⟨hz,hG,hu⟩
      exact ⟨hz,hG,(potential_ge_iff_squaredReciprocal_le hk.le hh hz).mpr ((hcut z hz hG).mp hu)⟩
  dsimp only
  rw [he]
  exact hc

theorem criticalCountStatement_proved : CriticalCountStatement := by
  intro f hf k hk ξ hg h hh
  exact critical_count hf (lt_trans zero_lt_one hk) hg hh

end Brennan

end

end OAI
