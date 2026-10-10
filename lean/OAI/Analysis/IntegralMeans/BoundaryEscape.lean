import OAI.Analysis.IntegralMeans.TraceIdentity

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

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

lemma halfPlane_ball_subset {z : ℂ} (_hz : z ∈ halfPlane) :
    Metric.ball z z.im ⊆ halfPlane := by
  intro w hw
  have hh : ‖w-z‖ < z.im := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
  have hb := Complex.abs_im_le_norm (w-z)
  change 0 < w.im
  simp only [Complex.sub_im] at hb
  linarith [neg_le_abs (w.im-z.im)]

lemma omitted_quarter_bound {F : ℂ → ℂ} (hf : UnivalentOn F halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hξ : ξ ∉ F '' halfPlane) :
    z.im*‖deriv F z‖ ≤ 4*‖F z-ξ‖ := by
  have hr : 0 < z.im := hz
  have hb := univalent_ball_quarter hr
    (show UnivalentOn F (Metric.ball z z.im) from ⟨hf.1.mono (halfPlane_ball_subset hz),hf.2.mono (halfPlane_ball_subset hz)⟩)
  have hn : ξ ∉ Metric.ball (F z) (z.im*‖deriv F z‖/4) := by
    intro hh
    exact hξ ((image_mono (halfPlane_ball_subset hz)) (hb hh))
  have hn' : z.im*‖deriv F z‖/4 ≤ ‖F z-ξ‖ := by
    simpa only [Metric.mem_ball,dist_eq_norm,not_lt,norm_sub_rev] using hn
  linarith

lemma class_omitted_cell_bound {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ (g : DiskClass) (w : ℂ), |w.re| ≤ 1 → (1/2 : ℝ) ≤ w.im → w.im ≤ 1 → ‖classFun g w‖ ≤ M)
    (g : DiskClass) {h x y x' : ℝ} {ξ : ℂ} (hh : 0 < h)
    (hy : h ≤ y) (hyy : y ≤ 2*h) (hxx : |x'-x| ≤ h)
    (hξ : ξ ∉ classFun g '' halfPlane) :
    ‖classFun g (x'+h*Complex.I)-ξ‖ ≤ (1+4*M)*‖classFun g (x+y*Complex.I)-ξ‖ := by
  let z : ℂ := x+y*Complex.I
  let w : ℂ := ((x'-x)/y : ℝ)+(h/y : ℝ)*Complex.I
  have hy0 : 0 < y := hh.trans_le hy
  have hz : z ∈ halfPlane := by simpa [z,halfPlane] using hy0
  have hwy : w.im = h/y := by simp [w]
  have hwx : w.re = (x'-x)/y := by simp [w]
  have hw : w ∈ halfPlane := by simpa [halfPlane,hwy] using (div_pos hh hy0)
  have hwr : |w.re| ≤ 1 := by rw [hwx,abs_div,abs_of_pos hy0]; exact (div_le_one hy0).mpr (hxx.trans hy)
  have hwl : (1/2 : ℝ) ≤ w.im := by rw [hwy,le_div_iff₀ hy0]; linarith
  have hwu : w.im ≤ 1 := by rw [hwy]; exact (div_le_one hy0).mpr hy
  have hwa : affine z w = x'+h*Complex.I := by
    apply Complex.ext <;> simp [affine,z,w,Complex.mul_re,Complex.mul_im]
    · field_simp
      ring
    · field_simp
  have hd : ‖deriv (classFun g) z‖ > 0 := norm_pos_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 hz)
  have hm := hb (rerootClass g ⟨z,hz⟩) w hwr hwl hwu
  rw [classFun_rerootClass _ _ hw,reroot,hwa,norm_div,norm_mul,Complex.norm_real] at hm
  have hzim : z.im = y := by simp [z]
  rw [hzim,Real.norm_eq_abs,abs_of_pos hy0] at hm
  have hm' := (div_le_iff₀ (mul_pos hy0 hd)).mp hm
  have hq := omitted_quarter_bound (classFun_schlicht g).1 hz hξ
  rw [hzim] at hq
  have hsum := norm_add_le (classFun g (x'+h*Complex.I)-classFun g z) (classFun g z-ξ)
  simp only [sub_add_sub_cancel] at hsum
  have hhq := mul_le_mul_of_nonneg_left hq hM
  dsimp only [z] at *
  nlinarith

def closedPositiveSuperlevel (F : ℂ → ℂ) (k δ : ℝ) (ξ : ℂ) : Set ℂ :=
  {z | 0 < z.im ∧ ‖F z-ξ‖ ≤ z.im^k/δ}

lemma interior_positive_superlevel_height {F : ℂ → ℂ} {k δ : ℝ}
    (hk : 0 < k) (_hδ : 0 < δ)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hopen : ∀ z : ℂ, 0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    {ξ : ℂ} (hξ : ξ ∈ F '' {z : ℂ | 0 < z.im}) :
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
      ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im := by
  obtain ⟨z₀,hz₀,rfl⟩ := hξ
  change 0 < z₀.im at hz₀
  have hn : {z : ℂ | z₀.im/2 < z.im} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by change z₀.im/2 < z₀.im; linarith)
  have hn' := image_mem_map (m := F) hn
  rw [hopen z₀ hz₀] at hn'
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp hn'
  have hc : ContinuousAt (fun y : ℝ => y^k/δ) 0 :=
    (Real.continuous_rpow_const hk.le).continuousAt.div_const δ
  have he : (0 : ℝ)^k/δ = 0 := by rw [Real.zero_rpow (ne_of_gt hk),zero_div]
  have hevent : ∀ᶠ y : ℝ in 𝓝 0, y^k/δ < r := by
    have hh := hc.eventually (gt_mem_nhds (show (0 : ℝ)^k/δ < r by rwa [he]))
    exact hh
  obtain ⟨a,ha,haB⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨min a (z₀.im/2),lt_min ha (by linarith),fun z hz hzw => ?_⟩
  by_contra! hsmall
  have hza : z.im < a := hsmall.trans_le (min_le_left _ _)
  have hm : F z ∈ Metric.ball (F z₀) r := by
    rw [Metric.mem_ball,dist_eq_norm]
    exact hzw.trans_lt (haB (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hz] using hza))
  obtain ⟨w,hw,hwe⟩ := hrB hm
  have hwH : 0 < w.im := by change z₀.im/2 < w.im at hw; linarith
  have hwz : w = z := hi hwH hz hwe
  subst w
  change z₀.im/2 < z.im at hw
  exact (not_lt_of_ge hw.le) (hsmall.trans_le (min_le_right _ _))

lemma positive_superlevel_compact {F : ℂ → ℂ} {k δ : ℝ} {ξ : ℂ}
    (hk : 0 ≤ k) (hδ : 0 < δ)
    (hc : ContinuousOn F {z : ℂ | 0 < z.im})
    (ht : HasQuarticTail F (4*k))
    (hp : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hheight : ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
      ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im) :
    IsCompact (closedPositiveSuperlevel F k δ ξ) := by
  obtain ⟨η,hη,hηb⟩ := hheight
  obtain ⟨R₀,hR₀⟩ := (hp (Metric.closedBall (0 : ℂ) (2*‖ξ‖+1))
    (isCompact_closedBall _ _) η hη).isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R₁,hR₁⟩ := quartic_tail_iff_power ht (δ/2) (by linarith)
  have hb : closedPositiveSuperlevel F k δ ξ ⊆ Metric.closedBall 0 (max R₀ R₁) := by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra! hn
    have hno : 2*‖ξ‖+1 < ‖F z‖ := by
      by_contra! hle
      have hh := hR₀ ⟨hηb z hz.1 hz.2,by simpa using hle⟩
      have hh' : ‖z‖ ≤ R₀ := by simpa using hh
      linarith [le_max_left R₀ R₁]
    have hFn : 0 < ‖F z‖ := by nlinarith [norm_nonneg ξ]
    have ht' := hR₁ z hz.1 ((le_max_right _ _).trans hn.le)
    rw [← div_eq_mul_inv,div_lt_iff₀ hFn] at ht'
    have hpot := (le_div_iff₀ hδ).mp hz.2
    have hnorm : ‖F z‖ ≤ ‖F z-ξ‖+‖ξ‖ := by
      simpa only [sub_add_cancel] using norm_add_le (F z-ξ) ξ
    nlinarith
  have he : closedPositiveSuperlevel F k δ ξ =
      {z : ℂ | η ≤ z.im} ∩ (fun z => ‖F z-ξ‖-z.im^k/δ) ⁻¹' Iic 0 := by
    ext z
    constructor
    · intro hz
      exact ⟨hηb z hz.1 hz.2,sub_nonpos.mpr hz.2⟩
    · intro hz
      exact ⟨hη.trans_le hz.1,sub_nonpos.mp hz.2⟩
  have hcc : ContinuousOn (fun z : ℂ => ‖F z-ξ‖-z.im^k/δ) {z : ℂ | η ≤ z.im} := by
    apply ((hc.mono (fun z hz => hη.trans_le hz)).sub continuousOn_const).norm.sub
    exact ((Real.continuous_rpow_const hk).comp Complex.continuous_im).continuousOn.div_const δ
  apply (isCompact_closedBall (0 : ℂ) (max R₀ R₁)).of_isClosed_subset _ hb
  rw [he]
  exact hcc.preimage_isClosed_of_isClosed (isClosed_le continuous_const Complex.continuous_im) isClosed_Iic

def realCell (h : ℝ) (j : ℤ) : Set ℝ := Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)

lemma realCell_disjoint {h : ℝ} (hh : 0 < h) : Pairwise (Function.onFun Disjoint (realCell h)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hhij : (i : ℝ)+1 ≤ j := by exact_mod_cast Int.add_one_le_iff.mpr hij
    have hm := mul_le_mul_of_nonneg_right hhij hh.le
    exact (not_lt_of_ge (hm.trans hy.1)) hx.2
  · have hhji : (j : ℝ)+1 ≤ i := by exact_mod_cast Int.add_one_le_iff.mpr hji
    have hm := mul_le_mul_of_nonneg_right hhji hh.le
    exact (not_lt_of_ge (hm.trans hx.1)) hy.2

lemma measure_realCell {h : ℝ} (_hh : 0 ≤ h) (j : ℤ) :
    volume (realCell h j) = ENNReal.ofReal h := by
  rw [realCell,Real.volume_Ico]
  congr 1
  ring

lemma mem_realCell_floor {h : ℝ} (hh : 0 < h) (x : ℝ) : x ∈ realCell h ⌊x/h⌋ := by
  constructor
  · exact (le_div_iff₀ hh).mp (Int.floor_le _)
  · exact (div_lt_iff₀ hh).mp (Int.lt_floor_add_one _)

lemma realCell_length_bound {h : ℝ} (_hh : 0 < h) {j : ℤ} {x x' : ℝ}
    (hx : x ∈ realCell h j) (hx' : x' ∈ realCell h j) : |x'-x| ≤ h := by
  rw [abs_le]
  constructor <;> dsimp [realCell] at hx hx' <;> nlinarith [hx.1,hx.2,hx'.1,hx'.2]

lemma cell_target_cover_bound {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (W : Set ℤ) (centers : ℤ → ℂ) {S : Set ℝ} {C : ℝ≥0∞}
    (hsub : ∀ j ∈ W, realCell h j ⊆ S) (hS : volume S ≤ C) :
    volume (⋃ j : W, Metric.closedBall (centers j) r) ≤
      (ENNReal.ofReal (Real.pi*r^2)/ENNReal.ofReal h)*C := by
  have hlen : (∑' j : W, ENNReal.ofReal h) ≤ C := by
    have hd : Pairwise (Function.onFun Disjoint (fun j : W => realCell h j)) := by
      intro i j hij
      exact realCell_disjoint hh (fun he => hij (Subtype.ext he))
    have he := measure_iUnion (μ := volume) hd (fun _ => measurableSet_Ico)
    simp only [measure_realCell hh.le] at he
    rw [← he]
    exact (measure_mono (iUnion_subset (fun (j : W) => hsub j.val j.property))).trans hS
  have harea (j : W) : volume (Metric.closedBall (centers j) r) = ENNReal.ofReal (Real.pi*r^2) := by
    rw [Complex.volume_closedBall]
    have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
      rw [ENNReal.ofReal,ENNReal.coe_inj]
      apply Subtype.ext
      exact (Real.coe_toNNReal Real.pi Real.pi_pos.le).symm
    rw [hpi,ENNReal.ofReal_mul Real.pi_pos.le,ENNReal.ofReal_pow hr]
    exact mul_comm _ _
  calc
    _ ≤ ∑' j : W, volume (Metric.closedBall (centers j) r) := measure_iUnion_le _
    _ = ∑' j : W, (ENNReal.ofReal (Real.pi*r^2)/ENNReal.ofReal h)*ENNReal.ofReal h := by
      apply tsum_congr
      intro j
      rw [harea]
      exact (ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hh)) ENNReal.ofReal_ne_top).symm
    _ = (ENNReal.ofReal (Real.pi*r^2)/ENNReal.ofReal h)*(∑' j : W, ENNReal.ofReal h) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul le_rfl hlen zero_le zero_le

lemma summable_geometric_ofReal {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, ENNReal.ofReal (r^n)) < ∞ := by
  have hs : Summable (fun n : ℕ => (⟨r^n,pow_nonneg hr0 n⟩ : ℝ≥0)) :=
    NNReal.summable_coe.mp (summable_geometric_of_lt_one hr0 hr1)
  have ht := ENNReal.tsum_coe_ne_top_iff_summable.mpr hs
  apply lt_top_iff_ne_top.mpr
  convert ht using 1
  congr 1
  ext n
  exact ENNReal.ofReal_eq_coe_nnreal (pow_nonneg hr0 n)

lemma ae_eventually_outside_geometric_covers {E : ℕ → Set ℂ} {C : ℝ≥0∞} (hC : C < ∞)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hE : ∀ n, volume (E n) ≤ C*ENNReal.ofReal (r^n)) :
    ∀ᵐ ξ : ℂ, ∀ᶠ n : ℕ in atTop, ξ ∉ E n := by
  apply ae_eventually_notMem
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hE)
  rw [ENNReal.tsum_mul_left]
  exact ne_of_lt (ENNReal.mul_lt_top hC (summable_geometric_ofReal hr0 hr1))

def dyadicHeight (n : ℕ) : ℝ := (1/2)^n

lemma dyadicHeight_pos (n : ℕ) : 0 < dyadicHeight n := pow_pos (by norm_num) n

lemma dyadicHeight_le_one (n : ℕ) : dyadicHeight n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

lemma exists_dyadic_slab {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ∃ n : ℕ, dyadicHeight n ≤ y ∧ y ≤ 2*dyadicHeight n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near_of_lt_one hy hy1
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨n+1,hn.le,?_⟩
  dsimp [dyadicHeight]
  rw [pow_succ]
  nlinarith

lemma dyadicHeight_antitone : Antitone dyadicHeight := by
  intro m n hmn
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn

lemma small_height_dyadic_slab (N : ℕ) {y : ℝ} (hy : 0 < y) (hyN : y < dyadicHeight N) :
    ∃ n ≥ N, dyadicHeight n ≤ y ∧ y ≤ 2*dyadicHeight n := by
  obtain ⟨n,hn,hn'⟩ := exists_dyadic_slab hy (hyN.le.trans (dyadicHeight_le_one N))
  refine ⟨n,?_,hn,hn'⟩
  by_contra! h
  exact (not_lt_of_ge ((dyadicHeight_antitone h.le).trans hn)) hyN

lemma slab_power_bound {k h y : ℝ} (hk : 1 ≤ k) (hh : 0 < h) (hh1 : h ≤ 1)
    (hy : 0 ≤ y) (hyh : y ≤ 2*h) : y^k ≤ (2 : ℝ)^k*h := by
  calc
    y^k ≤ (2*h)^k := Real.rpow_le_rpow hy hyh (by linarith)
    _ = (2 : ℝ)^k*h^k := Real.mul_rpow (by norm_num) hh.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_le_one hh.le hh1 hk) (by positivity)

def omittedTargets (F : ℂ → ℂ) (k R δ h : ℝ) : Set ℂ :=
  {ξ | ξ ∉ F '' {z : ℂ | 0 < z.im} ∧ ‖ξ‖ ≤ R ∧
    ∃ x y : ℝ, h ≤ y ∧ y ≤ 2*h ∧ ‖F (x+y*Complex.I)-ξ‖ ≤ y^k/δ}

lemma omitted_targets_cover {F : ℂ → ℂ} {k L R δ : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      volume (omittedTargets F k R δ h) ≤ C*ENNReal.ofReal h := by
  let D := L*(2 : ℝ)^k/δ
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hL (by positivity)) hδ.le
  let K := Metric.closedBall (0 : ℂ) (R+D)
  obtain ⟨C,hC,hCt⟩ := htrace K (isCompact_closedBall _ _)
  refine ⟨ENNReal.ofReal (Real.pi*D^2)*C, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC,fun h hh hh1 => ?_⟩
  let W : Set ℤ := {j | ∃ ξ ∈ omittedTargets F k R δ h,
    ∃ x y : ℝ, x ∈ realCell h j ∧ h ≤ y ∧ y ≤ 2*h ∧ ‖F (x+y*Complex.I)-ξ‖ ≤ y^k/δ}
  let center (j : ℤ) := F ((((j : ℝ)+1/2)*h : ℝ)+h*Complex.I)
  have hb {j : ℤ} {ξ : ℂ} (hξ : ξ ∈ omittedTargets F k R δ h)
      {x y x' : ℝ} (hx : x ∈ realCell h j) (hy : h ≤ y) (hyy : y ≤ 2*h)
      (hFw : ‖F (x+y*Complex.I)-ξ‖ ≤ y^k/δ) (hx' : x' ∈ realCell h j) :
      ‖F (x'+h*Complex.I)-ξ‖ ≤ D*h := by
    have ht := hcell h x y x' ξ hh hy hyy (realCell_length_bound hh hx hx') hξ.1
    have hp := div_le_div_of_nonneg_right (slab_power_bound hk hh hh1 (hh.le.trans hy) hyy) hδ.le
    have hp' := mul_le_mul_of_nonneg_left (hFw.trans hp) hL
    dsimp [D]
    calc
      _ ≤ L*((2 : ℝ)^k*h/δ) := ht.trans hp'
      _ = _ := by ring
  have hsub (j : ℤ) (hj : j ∈ W) : realCell h j ⊆ {x : ℝ | F (x+h*Complex.I) ∈ K} := by
    rcases hj with ⟨ξ,hξ,x,y,hx,hy,hyy,hFw⟩
    intro x' hx'
    have hhB := hb hξ hx hy hyy hFw hx'
    have hn := norm_add_le (F (x'+h*Complex.I)-ξ) ξ
    simp only [sub_add_cancel] at hn
    change F (x'+h*Complex.I) ∈ Metric.closedBall (0 : ℂ) (R+D)
    rw [Metric.mem_closedBall,dist_zero_right]
    nlinarith [hξ.2.1,mul_le_of_le_one_right hD hh1]
  have hcovered : omittedTargets F k R δ h ⊆ ⋃ j : W, Metric.closedBall (center j) (D*h) := by
    intro ξ hξ
    obtain ⟨x,y,hy,hyy,hFw⟩ := hξ.2.2
    let j : ℤ := ⌊x/h⌋
    have hx : x ∈ realCell h j := mem_realCell_floor hh _
    have hj : j ∈ W := ⟨ξ,hξ,x,y,hx,hy,hyy,hFw⟩
    apply mem_iUnion.mpr
    refine ⟨⟨j,hj⟩,?_⟩
    rw [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev]
    change ‖F ((((j : ℝ)+1/2)*h : ℝ)+h*Complex.I)-ξ‖ ≤ D*h
    exact hb (x' := ((j : ℝ)+1/2)*h) hξ hx hy hyy hFw (by constructor <;> nlinarith)
  calc
    _ ≤ volume (⋃ j : W, Metric.closedBall (center j) (D*h)) := measure_mono hcovered
    _ ≤ (ENNReal.ofReal (Real.pi*(D*h)^2)/ENNReal.ofReal h)*C :=
      cell_target_cover_bound hh (mul_nonneg hD hh.le) W center hsub (hCt h hh)
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos hh]
      have he : Real.pi*(D*h)^2/h = (Real.pi*D^2)*h := by field_simp
      rw [he,ENNReal.ofReal_mul (by positivity)]
      ring

lemma ae_omitted_positive_superlevel_height {F : ℂ → ℂ} {k L R δ : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∀ᵐ ξ : ℂ, ξ ∉ F '' {z : ℂ | 0 < z.im} → ‖ξ‖ ≤ R →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
        ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im := by
  obtain ⟨C,hC,hCb⟩ := omitted_targets_cover hk hL hδ hcell htrace (R := R)
  have hae := ae_eventually_outside_geometric_covers hC
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
    (E := fun n => omittedTargets F k R δ (dyadicHeight n))
    (fun n => hCb _ (dyadicHeight_pos n) (dyadicHeight_le_one n))
  filter_upwards [hae] with ξ hξ
  intro ho hR
  obtain ⟨N,hN⟩ := eventually_atTop.mp hξ
  refine ⟨dyadicHeight N,dyadicHeight_pos N,fun z hz hzw => ?_⟩
  by_contra! hh
  obtain ⟨n,hn,hy,hyy⟩ := small_height_dyadic_slab N hz hh
  apply hN n hn
  refine ⟨ho,hR,z.re,z.im,hy,hyy,?_⟩
  simpa only [Complex.re_add_im] using hzw

lemma ae_positive_superlevel_height {F : ℂ → ℂ} {k L : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hopen : ∀ z : ℂ, 0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
        ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im := by
  have hae : ∀ᵐ ξ : ℂ, ∀ R n : ℕ,
      ξ ∉ F '' {z : ℂ | 0 < z.im} → ‖ξ‖ ≤ R →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
        ‖F z-ξ‖ ≤ z.im^k/(1/(n+1 : ℝ)) → η ≤ z.im := by
    apply ae_all_iff.mpr
    intro R
    apply ae_all_iff.mpr
    intro n
    exact ae_omitted_positive_superlevel_height hk hL (by positivity) hcell htrace
  filter_upwards [hae] with ξ hξ
  intro δ hδ
  by_cases ho : ξ ∈ F '' {z : ℂ | 0 < z.im}
  · exact interior_positive_superlevel_height (by linarith) hδ hi hopen ho
  obtain ⟨R,hR⟩ := exists_nat_ge ‖ξ‖
  obtain ⟨n,hn⟩ := exists_nat_gt (1/δ)
  have hn0 : 0 < (n+1 : ℝ) := by positivity
  have hnδ : 1/(n+1 : ℝ) ≤ δ := by
    apply (div_le_iff₀ hn0).mpr
    have hh := (div_lt_iff₀ hδ).mp hn
    nlinarith
  obtain ⟨η,hη,hηb⟩ := hξ R n ho hR
  refine ⟨η,hη,fun z hz hzw => ?_⟩
  exact hηb z hz (hzw.trans (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) (by positivity) hnδ))

lemma ae_positive_superlevel_compact {F : ℂ → ℂ} {k L : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L)
    (hc : ContinuousOn F {z : ℂ | 0 < z.im})
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hopen : ∀ z : ℂ, 0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    (ht : HasQuarticTail F (4*k))
    (hp : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ → IsCompact (closedPositiveSuperlevel F k δ ξ) := by
  filter_upwards [ae_positive_superlevel_height hk hL hi hopen hcell htrace] with ξ hξ
  intro δ hδ
  exact positive_superlevel_compact (by linarith) hδ hc ht hp (hξ δ hδ)

lemma class_ae_compact_superlevels (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞) :
    ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ →
      IsCompact (closedPositiveSuperlevel (classFun g) ((β+3)/4) δ ξ) := by
  obtain ⟨M,hM,hMb⟩ := uniform_relative_class_bound
  have ht : HasQuarticTail (classFun g) (4*((β+3)/4)) := by
    convert class_quartic_tail g hβ hfin using 1; ring
  apply ae_positive_superlevel_compact (by linarith : 1 ≤ (β+3)/4)
    (by linarith : 0 ≤ 1+4*M) (classFun_schlicht g).1.1.continuousOn
    (classFun_schlicht g).1.2 _ ht
    (fun _ hK _ hη => class_proper_preimage g hβ hfin hK hη)
    (fun _ _ _ _ _ hh hy hyy hxx hξ => class_omitted_cell_bound hM hMb g hh hy hyy hxx hξ)
    (fun _ hK => class_trace_bound g hβ hfin hK)
  intro z hz
  have hd := ((classFun_schlicht g).1.1.analyticAt (isOpen_halfPlane.mem_nhds hz)).contDiffAt (n := 1)
  exact (hd.hasStrictDerivAt (by norm_num)).map_nhds_eq
    (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 hz)

end Brennan

end

end OAI
