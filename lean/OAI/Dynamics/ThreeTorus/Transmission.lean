import OAI.Dynamics.ThreeTorus.Averaging
import OAI.Dynamics.ThreeTorus.Jitter
import OAI.Dynamics.ThreeTorus.PassageDensity
import OAI.Dynamics.ThreeTorus.PositiveLaws

namespace OAI

/-! Law averaging and weighted errors, folded packet transmission, and concrete signal-circle comparison. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics
open MeasureTheory Set Filter Function

namespace ThreeTorus
open MeasureTheory Set Filter Function Topology
open scoped Topology BigOperators FourierTransform

/-- Compactly supported realized laws have a locally finite scaled lattice sum,
jointly in the nonzero scale and the unfolded circle coordinate. -/
lemma continuousAt_scaled_periodization_compact {q : ℝ → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    ContinuousAt (fun v : ℝ × ℝ => periodizedReal (scaledDensity q v.1) v.2) p := by
  classical
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  let R' := max 1 R
  have hR' : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨N,hN⟩ := exists_nat_gt ((|p.1|+1)*R'+|p.2|+1)
  let S : Finset ℤ := Finset.Icc (-(N:ℤ)) N
  have hn : ∀ᶠ v : ℝ × ℝ in 𝓝 p,
      |v.1| < |p.1|+1 ∧ |v.2| < |p.2|+1 ∧ v.1 ≠ 0 := by
    filter_upwards [((continuous_abs.comp continuous_fst).tendsto p).eventually
      (eventually_lt_nhds (by linarith : |p.1| < |p.1|+1)),
      ((continuous_abs.comp continuous_snd).tendsto p).eventually
      (eventually_lt_nhds (by linarith : |p.2| < |p.2|+1)),
      continuous_fst.continuousAt.eventually_ne hp] with v hv hx hs
    exact ⟨hv,hx,hs⟩
  have he : ∀ᶠ v : ℝ × ℝ in 𝓝 p,
      periodizedReal (scaledDensity q v.1) v.2 = ∑ k ∈ S, scaledDensity q v.1 (v.2+k) := by
    filter_upwards [hn] with v hv
    apply tsum_eq_sum
    intro k hk
    by_cases hqk : q ((v.2+k)/v.1) = 0
    · simp [scaledDensity,hqk]
    have hqr : |(v.2+k)/v.1| ≤ R' := by
      exact (hR _ (subset_tsupport q hqk)).trans (le_max_right _ _)
    have hxk : |v.2+(k:ℝ)| ≤ |v.1| * R' := by
      rw [abs_div] at hqr
      exact (div_le_iff₀ (abs_pos.mpr hv.2.2)).mp hqr |>.trans_eq (mul_comm _ _)
    have hh : |(k:ℝ)| < (N:ℝ) := calc
      |(k:ℝ)| = |(v.2+k)-v.2| := by congr 1; ring
      _ ≤ |v.2+(k:ℝ)|+|v.2| := abs_sub _ _
      _ < (|p.1|+1)*R'+|p.2|+1 := by nlinarith [hxk,hv.1,hv.2.1]
      _ < (N:ℝ) := hN
    have hkm : k ∈ S := by
      apply Finset.mem_Icc.mpr
      have := abs_le.mp hh.le
      exact_mod_cast this
    exact False.elim (hk hkm)
  have hfin : ContinuousAt (fun v : ℝ × ℝ => ∑ k ∈ S, scaledDensity q v.1 (v.2+k)) p := by
    apply tendsto_finsetSum
    intro k _
    exact (continuousAt_fst.abs.inv₀ (abs_ne_zero.mpr hp)).mul
      (hq.continuousAt.comp (((continuousAt_snd.add_const (k:ℝ)).div continuousAt_fst hp)))
  exact hfin.congr_of_eventuallyEq he

/-- Compact bandwidth gives local joint continuity of the ideal law's folded density. -/
lemma continuousAt_scaled_periodization_bandlimited {q : ℝ → ℝ} (hq : Continuous q)
    (hqi : Integrable q) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |q y| ≤ C/(1+y^2))
    {D : ℝ} (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0)
    {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    ContinuousAt (fun v : ℝ × ℝ => periodizedReal (scaledDensity q v.1) v.2) p := by
  let ε := |p.1|/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (D/ε)
  have hN' : D < (N:ℝ)*ε := (div_lt_iff₀ hε).mp hN
  let S := Finset.Icc (-(N:ℤ)) N
  let F : ℝ → ℂ := 𝓕 (fun y => (q y : ℂ))
  have hFc : Continuous F := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hqi.ofReal
  have hn : ∀ᶠ v : ℝ × ℝ in 𝓝 p, ε ≤ |v.1| := by
    have hε' : ε < |p.1| := by dsimp [ε]; linarith [abs_pos.mpr hp]
    exact (((continuous_abs.comp continuous_fst).tendsto p).eventually
      (eventually_gt_nhds hε')).mono (fun _ h => h.le)
  have hfin : Continuous (fun v : ℝ × ℝ =>
      (∑ k ∈ S, F ((k:ℝ)*v.1)*fourier k (v.2:UnitAddCircle)).re) := by
    apply Complex.continuous_re.comp
    apply continuous_finsetSum
    intro k _
    exact (hFc.comp (continuous_const.mul continuous_fst)).mul
      ((fourier k).continuous.comp ((AddCircle.continuous_mk' 1).comp continuous_snd))
  apply hfin.continuousAt.congr_of_eventuallyEq
  filter_upwards [hn] with v hv
  have he := periodization_scaled_finite hq hC hb hε hF hN' hv v.2
  rw [← Complex.ofReal_tsum] at he
  exact congrArg Complex.re he

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function Topology
open scoped Topology BigOperators FourierTransform

lemma continuous_weighted_fold_difference {w q r : ℝ → ℝ}
    (hw : Continuous w) (hw0 : 0 ∉ tsupport w)
    (hq : Continuous q) (hqc : HasCompactSupport q)
    (hr : Continuous r) (hri : Integrable r) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, |r y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (r y : ℂ)) v = 0) :
    Continuous (fun p : ℝ × UnitAddCircle => w p.1 *
      |foldCircleDensity (scaledDensity q p.1) p.2-
        foldCircleDensity (scaledDensity r p.1) p.2|) := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1:ℝ))).continuous_lift_prod_right
  simp_rw [foldCircleDensity_coe_all]
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 = 0
  · have hz : w =ᶠ[𝓝 p.1] 0 := by
      rw [hp]
      exact notMem_tsupport_iff_eventuallyEq.mp hw0
    apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hz] with v hv
    simp only [Pi.zero_apply] at hv
    simp only [hv,zero_mul]
  · exact (hw.continuousAt.comp continuousAt_fst).mul
      ((continuousAt_scaled_periodization_compact hq hqc hp).sub
        (continuousAt_scaled_periodization_bandlimited hr hri hC hb hF hp)).abs

/-- Scaling and folding are contractions for the total variation distance of
real densities, including subprobability densities and negative scales. -/
lemma scaled_fold_l1_difference {q r : ℝ → ℝ} (hqm : Measurable q) (hqi : Integrable q)
    (hrm : Measurable r) (hri : Integrable r) {s : ℝ} (hs : s ≠ 0) :
    (∫ y, |foldCircleDensity (scaledDensity q s) y-foldCircleDensity (scaledDensity r s) y|
      ∂AddCircle.haarAddCircle) ≤ ∫ x, |q x-r x| := by
  have hqm' : Measurable (scaledDensity q s) :=
    measurable_const.mul (hqm.comp (measurable_id.div_const s))
  have hrm' : Measurable (scaledDensity r s) :=
    measurable_const.mul (hrm.comp (measurable_id.div_const s))
  have he : (fun x => |scaledDensity q s x-scaledDensity r s x|) =
      scaledDensity (fun x => |q x-r x|) s := by
    ext x
    simp only [scaledDensity,← mul_sub,abs_mul,abs_inv,abs_abs]
  exact (foldCircleDensity_l1_difference hqm' (integrable_scaledDensity hqi hs)
    hrm' (integrable_scaledDensity hri hs)).trans_eq (by rw [he,integral_scaledDensity hs])

/-- Exact fast law comparison, with the missing mass of the
realized subprobability included. All arbitrary offsets are allowed. -/
theorem weighted_fold_law_average {w q r : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : 0 ∉ tsupport w)
    (hwn : ∀ s, 0 ≤ w s)
    (hq : Continuous q) (hqc : HasCompactSupport q)
    (hr : Continuous r) (hri : Integrable r) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, |r y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (r y : ℂ)) v = 0)
    (β : ℕ → UnitAddCircle) :
    Tendsto (fun n : ℕ => ∫ s, w s *
      |foldCircleDensity (scaledDensity q s) ((((n:ℝ)*s:ℝ):UnitAddCircle)+β n)-
        foldCircleDensity (scaledDensity r s) ((((n:ℝ)*s:ℝ):UnitAddCircle)+β n)|) atTop
      (𝓝 (∫ s, w s * ∫ y,
        |foldCircleDensity (scaledDensity q s) y-foldCircleDensity (scaledDensity r s) y|
          ∂AddCircle.haarAddCircle)) ∧
    (∫ s, w s * ∫ y,
      |foldCircleDensity (scaledDensity q s) y-foldCircleDensity (scaledDensity r s) y|
        ∂AddCircle.haarAddCircle) ≤ (∫ s, w s) * ∫ x, |q x-r x| := by
  constructor
  · have hH := continuous_weighted_fold_difference hw hw0 hq hqc hr hri hC hb hF
    obtain ⟨R,hR0,hR⟩ := hwc.isBounded.exists_pos_norm_le
    obtain ⟨M,hM⟩ := exists_nat_gt R
    have hM0 : 0 < M := by exact_mod_cast hR0.trans hM
    have hs : ∀ s y, (M:ℝ) ≤ |s| →
        w s * |foldCircleDensity (scaledDensity q s) y-foldCircleDensity (scaledDensity r s) y| = 0 := by
      intro s y hs
      have hz : w s = 0 := by
        by_contra hn
        have hh := hR s (subset_tsupport w hn)
        simp only [Real.norm_eq_abs] at hh
        linarith
      rw [hz,zero_mul]
    simpa only [integral_const_mul] using fast_average_real_compact_real hH hM0 hs β
  · have hwi : Integrable w := hw.integrable_of_hasCompactSupport hwc
    rw [← integral_mul_const]
    apply integral_mono_of_nonneg
      (Eventually.of_forall (fun s => mul_nonneg (hwn s) (integral_nonneg (fun _ => abs_nonneg _))))
      (hwi.mul_const _)
    filter_upwards [] with s
    by_cases hs : s = 0
    · subst s
      have hwz : w 0 = 0 := image_eq_zero_of_notMem_tsupport hw0
      simp only [hwz,zero_mul,le_refl]
    · exact mul_le_mul_of_nonneg_left (scaled_fold_l1_difference hq.measurable
        (hq.integrable_of_hasCompactSupport hqc) hr.measurable hri hs) (hwn s)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function Topology
open scoped Topology BigOperators FourierTransform

lemma continuous_weighted_fold_of_local {w q : ℝ → ℝ}
    (hw : Continuous w) (hw0 : 0 ∉ tsupport w)
    (hq : ∀ p : ℝ × ℝ, p.1 ≠ 0 →
      ContinuousAt (fun v : ℝ × ℝ => periodizedReal (scaledDensity q v.1) v.2) p) :
    Continuous (fun p : ℝ × UnitAddCircle => w p.1 * foldCircleDensity (scaledDensity q p.1) p.2) := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1:ℝ))).continuous_lift_prod_right
  simp_rw [foldCircleDensity_coe_all]
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 = 0
  · have hz : w =ᶠ[𝓝 p.1] 0 := by
      rw [hp]
      exact notMem_tsupport_iff_eventuallyEq.mp hw0
    apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hz] with v hv
    simp only [Pi.zero_apply] at hv
    simp only [hv,zero_mul]
  · exact (hw.continuousAt.comp continuousAt_fst).mul (hq p hp)

lemma continuous_weighted_fold_compact {w q : ℝ → ℝ}
    (hw : Continuous w) (hw0 : 0 ∉ tsupport w) (hq : Continuous q) (hqc : HasCompactSupport q) :
    Continuous (fun p : ℝ × UnitAddCircle => w p.1 * foldCircleDensity (scaledDensity q p.1) p.2) :=
  continuous_weighted_fold_of_local hw hw0 (fun _ hp => continuousAt_scaled_periodization_compact hq hqc hp)

lemma continuous_weighted_fold_bandlimited {w q : ℝ → ℝ}
    (hw : Continuous w) (hw0 : 0 ∉ tsupport w) (hq : Continuous q) (hqi : Integrable q)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |q y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0) :
    Continuous (fun p : ℝ × UnitAddCircle => w p.1 * foldCircleDensity (scaledDensity q p.1) p.2) :=
  continuous_weighted_fold_of_local hw hw0
    (fun _ hp => continuousAt_scaled_periodization_bandlimited hq hqi hC hb hF hp)

lemma continuous_fast_circle (n : ℕ) (β : UnitAddCircle) :
    Continuous (fun s : ℝ => (((n:ℝ)*s:ℝ):UnitAddCircle)+β) :=
  ((AddCircle.continuous_mk' 1).comp (continuous_const.mul continuous_id)).add_const β

lemma continuous_weighted_fast_compact {w q : ℝ → ℝ}
    (hw : Continuous w) (hw0 : 0 ∉ tsupport w) (hq : Continuous q) (hqc : HasCompactSupport q)
    (n : ℕ) (β : UnitAddCircle) :
    Continuous (fun s : ℝ => w s *foldCircleDensity (scaledDensity q s)
      ((((n:ℝ)*s:ℝ):UnitAddCircle)+β)) :=
  (continuous_weighted_fold_compact hw hw0 hq hqc).comp
    (continuous_id.prodMk (continuous_fast_circle n β))

lemma foldCircleDensity_mul_circle (w : ℝ → ℝ) (g : UnitAddCircle → ℝ) (z : UnitAddCircle) :
    foldCircleDensity (fun s => w s*g (s:UnitAddCircle)) z = foldCircleDensity w z*g z := by
  induction z using Quotient.inductionOn with | h x =>
    simp only [foldCircleDensity_coe_all,quotient_add_int,tsum_mul_right]

lemma fast_circle_coe (n : ℕ) (s : ℝ) :
    (((n:ℝ)*s:ℝ):UnitAddCircle) = (n:ℤ) • (s:UnitAddCircle) := by
  simpa only [zsmul_eq_mul,Int.cast_natCast] using
    (AddCircle.coe_zsmul (p := (1:ℝ)) (n := (n:ℤ)) (x := s))

lemma foldCircleDensity_mul_fast (w : ℝ → ℝ) (g : UnitAddCircle → ℝ)
    (n : ℕ) (β z : UnitAddCircle) :
    foldCircleDensity (fun s => w s*g ((((n:ℝ)*s:ℝ):UnitAddCircle)+β)) z =
      foldCircleDensity w z*g ((n:ℤ) • z+β) := by
  simp_rw [fast_circle_coe]
  exact foldCircleDensity_mul_circle w (fun z => g ((n:ℤ) • z+β)) z

/-- Quantitative transfer from an ideal folded law to a realized compact law.
The phase may have any prescribed offset at every passage integer. -/
theorem realized_fold_signal_estimate {w q r : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : 0 ∉ tsupport w)
    (hwn : ∀ s, 0 ≤ w s)
    (hq : Continuous q) (hqc : HasCompactSupport q)
    (hr : Continuous r) (hri : Integrable r) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, |r y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (r y : ℂ)) v = 0)
    {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
    (hideal : ∀ s ∈ support w, ∀ y, |foldCircleDensity (scaledDensity r s) y-g y| ≤ ε)
    (β : ℕ → UnitAddCircle) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (∫ z,
      |foldCircleDensity (fun s => w s*foldCircleDensity (scaledDensity q s)
        ((((n:ℝ)*s:ℝ):UnitAddCircle)+β n)) z-
        foldCircleDensity w z*g ((n:ℤ) • z+β n)| ∂AddCircle.haarAddCircle) <
      (∫ s, w s)*(∫ x, |q x-r x|) + (∫ s, w s)*ε + η := by
  have hav := weighted_fold_law_average hw hwc hw0 hwn hq hqc hr hri hC hb hF β
  have hlim : (∫ s, w s * ∫ y,
      |foldCircleDensity (scaledDensity q s) y-foldCircleDensity (scaledDensity r s) y|
        ∂AddCircle.haarAddCircle) < (∫ s, w s)*(∫ x, |q x-r x|)+η :=
    lt_of_le_of_lt hav.2 (lt_add_of_pos_right _ hη)
  filter_upwards [hav.1.eventually (eventually_lt_nhds hlim)] with n hn
  let y : ℝ → UnitAddCircle := fun s => (((n:ℝ)*s:ℝ):UnitAddCircle)+β n
  have hy : Continuous y := continuous_fast_circle n (β n)
  let R : ℝ → ℝ := fun s => w s*foldCircleDensity (scaledDensity q s) (y s)
  let G : ℝ → ℝ := fun s => w s*g (y s)
  let E : ℝ → ℝ := fun s => w s*
    |foldCircleDensity (scaledDensity q s) (y s)-foldCircleDensity (scaledDensity r s) (y s)|
  have hRc : Continuous R := continuous_weighted_fast_compact hw hw0 hq hqc n (β n)
  have hRi : Integrable R := hRc.integrable_of_hasCompactSupport hwc.mul_right
  have hGc : Continuous G := hw.mul (hg.comp hy)
  have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hwc.mul_right
  have hEc : Continuous E :=
    (continuous_weighted_fold_difference hw hw0 hq hqc hr hri hC hb hF).comp
      (continuous_id.prodMk hy)
  have hEi : Integrable E := hEc.integrable_of_hasCompactSupport hwc.mul_right
  have hwi : Integrable w := hw.integrable_of_hasCompactSupport hwc
  have hpt (s : ℝ) : |R s-G s| ≤ E s+w s*ε := by
    dsimp only [R,G,E]
    rw [← mul_sub,abs_mul,abs_of_nonneg (hwn s)]
    by_cases hs : w s = 0
    · simp [hs]
    · calc
        _ ≤ w s*(|foldCircleDensity (scaledDensity q s) (y s)-foldCircleDensity (scaledDensity r s) (y s)|+
          |foldCircleDensity (scaledDensity r s) (y s)-g (y s)|) :=
          mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) (hwn s)
        _ ≤ _ := by nlinarith [hideal s hs (y s),hwn s]
  have hbound : (∫ s, |R s-G s|) ≤ (∫ s, E s)+(∫ s, w s)*ε := by
    calc
      _ ≤ ∫ s, E s+w s*ε := integral_mono (hRi.sub hGi).abs (hEi.add (hwi.mul_const ε)) hpt
      _ = _ := by rw [integral_add hEi (hwi.mul_const ε),integral_mul_const]
  have hfold := foldCircleDensity_l1_difference hRc.measurable hRi hGc.measurable hGi
  have heG : ∀ z, foldCircleDensity G z = foldCircleDensity w z*g ((n:ℤ) • z+β n) :=
    foldCircleDensity_mul_fast w g n (β n)
  simp_rw [heG] at hfold
  exact hfold.trans hbound |>.trans_lt (by dsimp only [E,y]; linarith)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma lawJitter_injOn {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : Continuous ρ) (hi : Integrable ρ) (hp : ∀ y, 0 < ρ y)
    (hm : ∫ y, ρ y = 1) (hδ : 0 < δ) : InjOn (lawJitter ρ c) (Ioo δ (1-δ)) := by
  intro a ha b hb he
  rw [lawJitter_eq_quantile c hδ ⟨ha.1.le,ha.2.le⟩,
    lawJitter_eq_quantile c hδ ⟨hb.1.le,hb.2.le⟩] at he
  have he' := congrArg (cumulative ρ) he
  rwa [cumulative_quantile hρ hi hp hm ⟨by linarith [ha.1],by linarith [ha.2]⟩,
    cumulative_quantile hρ hi hp hm ⟨by linarith [hb.1],by linarith [hb.2]⟩] at he'

/-- The inverse-branch Jacobian is exactly the realized quantile density,
not merely some density representing the same measure. -/
lemma lawJitter_branchKernel {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ)
    (w : ℝ → ℝ) (y s : ℝ) :
    branchKernel (Ioo δ (1-δ)) (lawJitter ρ c) (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2) (y,s) =
      w s*lawDensity ρ c y := by
  classical
  by_cases hy : y ∈ lawJitter ρ c '' Ioo δ (1-δ)
  · let a := invFunOn (lawJitter ρ c) (Ioo δ (1-δ)) y
    have ha : a ∈ Ioo δ (1-δ) := (invFunOn_pos hy).1
    have hay : lawJitter ρ c a = y := (invFunOn_pos hy).2
    have hqay : quantile ρ a = y :=
      (lawJitter_eq_quantile c hδ ⟨ha.1.le,ha.2.le⟩).symm.trans hay
    have hca : cumulative ρ y = a := by
      rw [← hqay]
      exact cumulative_quantile hρ.continuous hi hp hm ⟨by linarith [ha.1],by linarith [ha.2]⟩
    have hd : deriv (lawJitter ρ c) a = (ρ y)⁻¹ := by
      simpa only [hqay] using (lawJitter_deriv_pos c hρ hi hp hm hδ ha).1.deriv
    simp only [branchKernel,hy,ite_eq_left]
    change w s*c.ψ a^2/|deriv (lawJitter ρ c) a| = w s*lawDensity ρ c y
    rw [hd,abs_of_pos (inv_pos.mpr (hp y)),div_inv_eq_mul,lawDensity,hca]
    ring
  · have hz : c.ψ (cumulative ρ y) = 0 := by
      by_contra hn
      have ha := c.ψ_support (subset_tsupport c.ψ hn)
      apply hy
      refine ⟨cumulative ρ y,ha,?_⟩
      rw [lawJitter_eq_quantile c hδ ⟨ha.1.le,ha.2.le⟩]
      exact quantile_cumulative hρ.continuous hi hp y
    simp [branchKernel,hy,lawDensity,hz]

lemma lawJitter_passageKernel {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ)
    (w : ℝ → ℝ) (s y : ℝ) :
    passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c)
      (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2) s y =
      w s*scaledDensity (lawDensity ρ c) s y := by
  rw [passageBranchKernel_formula,lawJitter_branchKernel c hρ hi hp hm hδ]
  simp only [scaledDensity]
  ring

lemma lawJitter_fineKernel {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ)
    (w : ℝ → ℝ) (n : ℕ) (s : ℝ) :
    fineResidueKernel (passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c)
      (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2)) 1 0 n s =
      w s*foldCircleDensity (scaledDensity (lawDensity ρ c) s) (((n:ℝ)*s:ℝ):UnitAddCircle) := by
  simp only [fineResidueKernel,lawJitter_passageKernel c hρ hi hp hm hδ,
    Int.cast_zero,sub_zero,Nat.cast_one,mul_one,tsum_mul_left,foldCircleDensity_coe_all]
  congr 1
  have he := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => scaledDensity (lawDensity ρ c) s ((n:ℝ)*s+k))
  simpa only [Equiv.neg_apply,Int.cast_neg,sub_eq_add_neg] using he

lemma stationaryWeight_modulus_independent {A : UnitAddCircle → ℝ → ℂ}
    (hA : ∀ a x, ‖A a x‖ = ‖A 0 x‖) (C : Set ℝ) (V : ℝ → ℝ) (a : UnitAddCircle) :
    stationaryWeight C V (A a) = stationaryWeight C V (A 0) := by
  unfold stationaryWeight
  congr 1
  funext x
  rw [hA a x]

lemma stationaryCutoffLift_modulus_independent {A : UnitAddCircle → ℝ → ℂ}
    (hA : ∀ a x, ‖A a x‖ = ‖A 0 x‖) (C : Set ℝ) (V ψ : ℝ → ℝ) :
    stationaryCutoffLift C V (fun p : ℝ × ℝ => A (p.2:UnitAddCircle) p.1) ψ =
      fun p : ℝ × ℝ => stationaryWeight C V (A 0) p.2*ψ p.1^2 := by
  funext p
  simp only [stationaryCutoffLift,stationaryWeight_modulus_independent hA]
  ring

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma stationaryWeight_nonneg (C : Set ℝ) (V : ℝ → ℝ) (A : ℝ → ℂ) (s : ℝ) :
    0 ≤ stationaryWeight C V A s := by
  classical
  unfold stationaryWeight branchDensity
  simp only [Set.indicator_apply]
  split_ifs <;> positivity

lemma stationaryWeight_tsupport_subset {C K : Set ℝ} {V : ℝ → ℝ} {A : ℝ → ℂ}
    (hV : Continuous V) (hK : IsCompact K) (hA : support A ⊆ K) :
    tsupport (stationaryWeight C V A) ⊆ V '' K :=
  closure_minimal (stationaryWeight_support_subset hA) (hK.image hV).isClosed

lemma stationaryWeight_slice_regular {V : ℝ → ℝ} {m : ℤ}
    {l u R : ℝ} {A : UnitAddCircle → ℝ → ℂ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u) :
    let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A 0)
    Continuous w ∧ HasCompactSupport w ∧ 0 ∉ tsupport w := by
  have hb := scaled_speed_good_branch hm hR hV hdV
  have hc := stationaryWeight_signed_compact_continuous (contDiff_const.mul hV) hA hs hR hb.1 hb.2
  have hv : Continuous (fun x => (m:ℝ)*V x) := continuous_const.mul hV.continuous
  have ht := stationaryWeight_tsupport_subset (C := Icc (l-R) (u+R)) hv isCompact_Icc (hs 0)
  refine ⟨hc.1.comp (continuous_id.prodMk continuous_const),?_,fun hz => h0 (ht hz)⟩
  exact (isCompact_Icc.image hv).of_isClosed_subset (isClosed_tsupport _) ht

/-- Fully realized smooth quantile law: the exact branch kernel has the desired
signal, with both its missing mass and total variation error explicitly included. -/
theorem quantile_fine_signal_estimate {w ρ : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : 0 ∉ tsupport w)
    (hwn : ∀ s, 0 ≤ w s)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
    (hideal : ∀ s ∈ support w, ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g y| ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (∫ z,
      |foldCircleDensity (fineResidueKernel (passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c)
        (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2)) 1 0 n) z-
        foldCircleDensity w z*g ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
      (∫ s, w s)*(4*δ+ε) + η := by
  have hq := (lawDensity_smooth c hρ hi).continuous
  have hqc := lawDensity_compact c hρ hi hp hm hδ hδ'
  have ht := realized_fold_signal_estimate hw hwc hw0 hwn hq hqc hρ.continuous hi hC hb hF
    hg hideal (fun _ => 0) hη
  have he : (∫ y, |lawDensity ρ c y-ρ y|) ≤ 4*δ := by
    simpa only [abs_sub_comm] using (lawDensity_error c hρ hi hp hm hδ hδ').2
  have hn : 0 ≤ ∫ s, w s := integral_nonneg hwn
  filter_upwards [ht] with n ht
  simp only [add_zero] at ht
  have heq : fineResidueKernel (passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c)
      (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2)) 1 0 n =
      fun s => w s*foldCircleDensity (scaledDensity (lawDensity ρ c) s) (((n:ℝ)*s:ℝ):UnitAddCircle) :=
    funext (lawJitter_fineKernel c hρ hi hp hm hδ w n)
  rw [heq]
  apply ht.trans_le
  nlinarith [mul_le_mul_of_nonneg_left he hn]

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

def quantileCircleJitter {δ : ℝ} (ρ : ℝ → ℝ) (c : LawCutoffs δ) : UnitAddCircle → ℝ :=
  (periodize_periodic (fun a => c.ξ a*quantile ρ a)).lift

lemma quantileCircleJitter_coe {δ : ℝ} (ρ : ℝ → ℝ) (c : LawCutoffs δ) (a : ℝ) :
    quantileCircleJitter ρ c (a:UnitAddCircle) = lawJitter ρ c a := rfl

lemma continuous_quantileCircleJitter {δ : ℝ} {ρ : ℝ → ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) : Continuous (quantileCircleJitter ρ c) := by
  apply Continuous.quotient_lift
  exact (lawJitter_smooth c hρ hi hp hm).continuous

/-- The finite retained spectral density of one actual signed Fourier packet. -/
def exactRetainedPacketDensity (I : Set ℝ) (J₀ : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ) (n : ℕ) : UnitAddCircle → ℝ :=
  foldCircleDensity (fun t => ∑ j ∈ S,
    unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
      (circleDensityLift 0 (retainedCircleWeight ψ χ
        (fun n j => exactPassageCoeff m (H n) A j) n j)) n j t)

lemma exactRetainedPacketDensity_integrable
    {I : Set ℝ} {J₀ : ℝ → ℝ} {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) :
    Integrable (exactRetainedPacketDensity I J₀ ψ χ m H A S n) AddCircle.haarAddCircle := by
  have hreg (j : ℤ) (hj : j ∈ S) := retained_unfolded_regular hJ hIo hinj hd hψ hχ
    (fun n j => continuous_exactPassageCoeff (m := m) (hH n) hA j) 0 hn (hS j hj)
  exact integrable_foldCircleDensity
    (Finset.measurable_sum _ (fun j hj => (hreg j hj).1))
    (integrable_finsetSum _ (fun j hj => (hreg j hj).2))

lemma integral_abs_sub_triangle {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g h : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, |f x-h x| ∂μ) ≤ (∫ x, |f x-g x| ∂μ)+(∫ x, |g x-h x| ∂μ) := by
  calc
    _ ≤ ∫ x, |f x-g x|+|g x-h x| ∂μ :=
      integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
        (fun x => abs_sub_le _ _ _)
    _ = _ := integral_add (hf.sub hg).abs (hg.sub hh).abs

/-- Source transmission analytic assembly, for the actual retained signed
coefficients and actual smooth quantile jitter. The law's lost mass is counted.
The model bound has to be established for the ideal law; no passage limit is
assumed. Every sufficiently large integer works. -/
theorem exact_quantile_circle_spectral_estimate
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {Δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+Δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hΔt : Tendsto Δ atTop (𝓝 0))
    (hmod : ∀ a x, ‖A₀ a x‖ = ‖A₀ 0 x‖)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hρm : ∫ y, ρ y = 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ℝ → UnitAddCircle → ℝ}
    (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
    (hideal : ∀ s ∈ support (stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)),
      ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g y| ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ j ∈ S n, j ≠ 0) ∧
      (∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) ∧
      ∀ᶠ n : ℕ in atTop, (∫ z,
        |exactRetainedPacketDensity (Ioo δ (1-δ)) (lawJitter ρ c) (neutralCircleCutoff c)
          χ m H A (S n) n z - foldCircleDensity w z*g ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
        (∫ s, w s)*(4*δ+ε)+η := by
  dsimp only
  let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)
  have hw := stationaryWeight_slice_regular hm hR hV hdV hAc
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) h0
  have hJs := lawJitter_smooth c hρ hi hp hρm
  have hJinj := lawJitter_injOn c hρ.continuous hi hp hρm hδ
  have hJd : ∀ x ∈ Ioo δ (1-δ), deriv (lawJitter ρ c) x ≠ 0 := by
    intro x hx
    obtain ⟨hh,hp⟩ := lawJitter_deriv_pos c hρ hi hp hρm hδ hx
    rw [hh.deriv]
    exact hp.ne'
  have hψs : tsupport c.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
    intro x hx
    have hh := c.ψ_support hx
    exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
  have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), c.ψ x = neutralCircleCutoff c (x:UnitAddCircle) := by
    intro x hx
    exact (lawPsi_eq c hδ ⟨hx.1.le,by simpa using hx.2⟩).symm
  obtain ⟨S,hSN,hST,ht⟩ := exact_passage_circle_spectral_limit hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hΔt hJs isOpen_Ioo hJinj hJd
    (continuous_quantileCircleJitter c hρ hi hp hρm).measurable
    (fun x _ => quantileCircleJitter_coe ρ c x) c.ψ_smooth c.ψ_compact hψs heψ
    (continuous_neutralCircleCutoff c) hχc hcχ hzχ (neutralCircleCutoff_bounds c hδ) hχ hχW
    (by norm_num : 0 < (1:ℕ)) 0
  simp only [Nat.cast_one,mul_one,zero_add] at hSN hST ht
  refine ⟨S,hSN,hST,?_⟩
  have hweight := stationaryCutoffLift_modulus_independent hmod (Icc (l-R) (u+R))
    (fun x => (m:ℝ)*V x) c.ψ
  rw [hweight] at ht
  let K : ℕ → UnitAddCircle → ℝ := fun n => foldCircleDensity (fineResidueKernel
    (passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c) (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2)) 1 0 n)
  have ht' : Tendsto (fun n => ∫ z,
      |exactRetainedPacketDensity (Ioo δ (1-δ)) (lawJitter ρ c) (neutralCircleCutoff c)
        χ m H A (S n) n z-K n z| ∂AddCircle.haarAddCircle) atTop (𝓝 0) := ht
  have h2 := quantile_fine_signal_estimate hw.1 hw.2.1 hw.2.2
    (stationaryWeight_nonneg _ _ _) hρ hi hp hρm hC hb hF c hδ hδ' hg hideal (half_pos hη)
  filter_upwards [ht'.eventually (eventually_lt_nhds (half_pos hη)),h2,eventually_gt_atTop (0:ℕ)]
    with n hn hn2 hnpos
  have hDi := exactRetainedPacketDensity_integrable (m := m) hJs isOpen_Ioo hJinj hJd
    (continuous_neutralCircleCutoff c) hχc hHc hAcont hnpos (hSN n hnpos)
  have hqc := (lawDensity_smooth c hρ hi).continuous
  have hqcomp := lawDensity_compact c hρ hi hp hρm hδ hδ'
  have hK : K n = foldCircleDensity (fun s => w s*foldCircleDensity (scaledDensity (lawDensity ρ c) s)
      (((n:ℝ)*s:ℝ):UnitAddCircle)) := by
    dsimp only [K]
    congr 1
    exact funext (lawJitter_fineKernel c hρ hi hp hρm hδ w n)
  have hRcont : Continuous (fun s => w s*foldCircleDensity (scaledDensity (lawDensity ρ c) s)
      (((n:ℝ)*s:ℝ):UnitAddCircle)) := by
    simpa only [add_zero] using continuous_weighted_fast_compact hw.1 hw.2.2 hqc hqcomp n 0
  have hKi : Integrable (K n) AddCircle.haarAddCircle := by
    rw [hK]
    exact integrable_foldCircleDensity hRcont.measurable
      (hRcont.integrable_of_hasCompactSupport hw.2.1.mul_right)
  have hGcont : Continuous (fun s : ℝ => w s*g (((n:ℝ)*s:ℝ):UnitAddCircle)) :=
    hw.1.mul (hg.comp ((AddCircle.continuous_mk' 1).comp (continuous_const.mul continuous_id)))
  have hG : (fun z => foldCircleDensity w z*g ((n:ℤ) • z)) =
      foldCircleDensity (fun s => w s*g (((n:ℝ)*s:ℝ):UnitAddCircle)) := by
    funext z
    simpa only [add_zero] using (foldCircleDensity_mul_fast w g n 0 z).symm
  have hGi : Integrable (fun z => foldCircleDensity w z*g ((n:ℤ) • z)) AddCircle.haarAddCircle := by
    rw [hG]
    exact integrable_foldCircleDensity hGcont.measurable
      (hGcont.integrable_of_hasCompactSupport hw.2.1.mul_right)
  have hh := integral_abs_sub_triangle hDi hKi hGi
  exact hh.trans_lt (by change _ < _ at hn2; linarith)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

/-- The exact three-mode index signal, in the source's positive-moment convention. -/
noncomputable def signalCircleModel (P : ℕ) (γ B : ℝ) (d : ℝ → ℂ) (m : ℤ) (z : UnitAddCircle) : ℝ := by
  classical
  exact 1+2*((if IsUnit (m : ZMod P) then (γ:ℂ)*d ((m:ℝ)/B) else 0)*fourier (-1) z).re

lemma continuous_signalCircleModel (P : ℕ) (γ B : ℝ) (d : ℝ → ℂ) (m : ℤ) :
    Continuous (signalCircleModel P γ B d m) := by
  unfold signalCircleModel
  fun_prop

lemma signalCircleModel_uniform_on_weight {α B b D : ℝ}
    (hα : 0 < α) (hαb : α < b) (hαD : α ≤ D) (hB : 0 < B) (hb : 0 < b)
    {L : ℕ} (hL : D/b < L) (γ : ℝ) {d : ℝ → ℂ}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) (hcomp : HasCompactSupport d)
    (hr : ∀ v, d (-v) = starRingEnd ℂ (d v)) (h0 : d 0 = 0)
    (hs : Function.support d ⊆ Icc (-D) D) (m : ℤ) (hm : b ≤ |(m:ℝ)/B|)
    (hbound : ∀ h R, signalBaseline α R/(2*signalPrimeProduct L) ≤
        signalJoint α γ d (signalPrimeProduct L) h R ∧
      signalJoint α γ d (signalPrimeProduct L) h R ≤
        3*signalBaseline α R/(2*signalPrimeProduct L))
    {φ : ℝ → ℝ} {K C : Set ℝ} {A : ℝ → ℂ}
    (hA : support A ⊆ K) {V₀ : ℝ} (hV : ∀ x ∈ K, |φ x| ≤ V₀) :
    ∀ ε > 0, ∀ᶠ c : ℝ in atTop,
      ∀ s ∈ support (stationaryWeight C (fun x => (m:ℝ)*(c+φ x)) A), ∀ y,
      |foldCircleDensity (scaledDensity (signalJitter α γ d (signalPrimeProduct L) B c) s) y-
        signalCircleModel (signalPrimeProduct L) γ B d m y| ≤ ε := by
  classical
  intro ε hε
  filter_upwards [signalJitter_periodic_approximation hα hαb hαD hB hb hL γ hd hcomp hr
    h0 hs m hm hbound V₀ ε hε] with c hc
  intro s hs y
  obtain ⟨x,hx,rfl⟩ := stationaryWeight_support_subset hA hs
  induction y using Quotient.inductionOn with | h y =>
    have ht := hc (φ x) (hV x hx) y
    rw [← Complex.ofReal_tsum] at ht
    let a : ℂ := (if IsUnit (m : ZMod (signalPrimeProduct L)) then
      (γ:ℂ)*d ((m:ℝ)/B) else 0)*fourier (-1) (y:UnitAddCircle)
    have he : (1 : ℂ)+2*(a.re : ℂ) =
        (signalCircleModel (signalPrimeProduct L) γ B d m (y:UnitAddCircle) : ℂ) := by
      norm_num [signalCircleModel, a]
    change dist _ ((1 : ℂ)+2*(a.re : ℂ)) < ε at ht
    rw [he,Complex.isometry_ofReal.dist_eq,Real.dist_eq] at ht
    simpa only [foldCircleDensity_coe_all,periodizedReal] using ht.le

/-- All the analytic prerequisites of the actual signal law, including mass one,
are consequences of the explicit positive joint law. -/
lemma signalJitter_law_regular {α B c D γ : ℝ}
    (hα : 0 < α) (hB : 0 < B) (hc : 0 < c) (hαD : α ≤ D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hcomp : HasCompactSupport d) (hr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (h0 : d 0 = 0) (hs : Function.support d ⊆ Icc (-D) D) (P : ℕ) [NeZero P]
    (hbound : ∀ h R, signalBaseline α R/(2*P) ≤ signalJoint α γ d P h R ∧
      signalJoint α γ d P h R ≤ 3*signalBaseline α R/(2*P)) :
    let ρ := signalJitter α γ d P B c
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
      (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
      ∃ C > 0, (∀ y, |ρ y| ≤ C/(1+y^2)) ∧
        ∀ v, c*B*D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0 := by
  dsimp only
  obtain ⟨a,C,_ha,hC,hCb⟩ := signalJitter_quadratic_tails hα hB hc P hbound
  refine ⟨signalJitter_smooth hα γ hd hcomp P B c,
    signalJitter_integrable hα hB hc γ hd hcomp P,
    signalJitter_pos hα hB hc P hbound,?_,C,hC,?_,?_⟩
  · exact integral_signalJitter hα hB hc γ hd hcomp hr h0 P
  · intro y
    rw [abs_of_pos (signalJitter_pos hα hB hc P hbound y)]
    exact (hCb y).2
  · intro v hv
    have ht := signalJitter_fourierInv_support hα hB hc hαD γ hd hcomp hr hs P
      (v := -v) (by simpa only [abs_neg] using hv)
    simpa only [Real.fourierInv_eq_fourier_neg,neg_neg] using ht

end ThreeTorus

end

end OAI
