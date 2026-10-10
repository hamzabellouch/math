import OAI.Analysis.SignedDisk.IntrinsicMarks1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff

noncomputable section

namespace SignedDisk

open Finset

namespace LabelSwitches

/-- Whether a switch has occurred since the most recent exceptional level. -/
def active (bad sw : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n+1 => if bad n then false else active bad sw n || sw n

def count (p : ℕ → Bool) (n : ℕ) : ℕ := ∑ i ∈ range n, if p i then 1 else 0

lemma active_witness (bad sw : ℕ → Bool) (n : ℕ) (h : active bad sw n = true) :
    ∃ i < n, sw i = true ∧ ∀ j, i ≤ j → j < n → bad j = false := by
  induction n with
  | zero => simp [active] at h
  | succ n ih =>
    by_cases hb : bad n = true
    · simp [active,hb] at h
    · have hb' : bad n = false := by cases hbn : bad n <;> simp_all
      simp only [active,hb',Bool.false_eq_true,↓reduceIte,Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨i,hi,hs,hn⟩ := ih h
        refine ⟨i,Nat.lt_succ_of_lt hi,hs,?_⟩
        intro j hij hj
        by_cases hjn : j < n
        · exact hn j hij hjn
        · have : j = n := by omega
          simpa [this] using hb'
      · refine ⟨n,Nat.lt_succ_self n,h,?_⟩
        intro j hj hj'
        have : j=n := by omega
        simpa [this] using hb'

theorem count_le (bad sw : ℕ → Bool) (n : ℕ)
    (hsep : ∀ i j, i < j → j < n → sw i = true → sw j = true →
      ∃ k, i ≤ k ∧ k ≤ j ∧ bad k = true) :
    count sw n ≤ 1+2*count bad n := by
  have hns (j : ℕ) (hj : j < n) (ha : active bad sw j = true) (hb : bad j = false) :
      sw j = false := by
    obtain ⟨i,hi,hs,hb0⟩ := active_witness bad sw j ha
    cases hv : sw j with
    | false => rfl
    | true =>
      obtain ⟨k,hik,hkj,hbk⟩ := hsep i j hi hj hs hv
      by_cases hkj' : k < j
      · have := hb0 k hik hkj'
        simp_all
      · have : k=j := by omega
        simp_all
  have aux : ∀ m ≤ n, count sw m ≤ 2*count bad m + if active bad sw m then 1 else 0 := by
    intro m hm
    induction m with
    | zero => simp [count,active]
    | succ m ih =>
      have ih' := ih (Nat.le_trans (Nat.le_succ m) hm)
      have hstep := hns m (by omega)
      simp only [count,sum_range_succ] at ih' ⊢
      simp only [active]
      by_cases hb : bad m = true <;> by_cases hs : sw m = true <;>
        by_cases ha : active bad sw m = true <;> simp_all <;> omega
  have h := aux n le_rfl
  split_ifs at h <;> omega

/-- Quantitative energy version. The exceptional set is the union of marks
and levels with energy exceeding c. This includes an arbitrary birth offset. -/
theorem count_energy (mark sw : ℕ → Bool) (E : ℕ → ℝ) (n : ℕ) {c : ℝ}
    (hc : 0 < c) (hE : ∀ i < n, 0 ≤ E i)
    (hsep : ∀ i j, i < j → j < n → sw i = true → sw j = true →
      ∃ k, i ≤ k ∧ k ≤ j ∧ (mark k = true ∨ c < E k)) :
    ((count sw n : ℕ) : ℝ) ≤ 1+2*((count mark n : ℕ) : ℝ)+(2/c)*∑ i ∈ range n, E i := by
  let bad : ℕ → Bool := fun i => decide (mark i = true ∨ c < E i)
  have hb := count_le bad sw n (by
    intro i j hij hj hi hj'
    obtain ⟨k,hik,hkj,hk⟩ := hsep i j hij hj hi hj'
    exact ⟨k,hik,hkj,by simpa [bad] using hk⟩)
  have henergy : ((count bad n : ℕ) : ℝ) ≤ ((count mark n : ℕ) : ℝ)+(1/c)*∑ i ∈ range n, E i := by
    simp only [count,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    have hi' : i < n := mem_range.mp hi
    have he := hE i hi'
    have hec : 0 ≤ (1/c)*E i := mul_nonneg (by positivity) he
    by_cases hm : mark i = true
    · simp only [bad,hm,true_or,decide_true,↓reduceIte]
      linarith
    · by_cases hce : c < E i
      · have he1 : 1 ≤ (1/c)*E i := by
          rw [one_div,mul_comm,← div_eq_mul_inv,le_div_iff₀ hc]
          simpa using hce.le
        simpa [bad,hm,hce] using he1
      · simpa [bad,hm,hce] using hec
  have hb' : ((count sw n : ℕ) : ℝ) ≤ 1+2*((count bad n : ℕ) : ℝ) := by exact_mod_cast hb
  calc
    _ ≤ 1+2*(((count mark n : ℕ) : ℝ)+(1/c)*∑ i ∈ range n, E i) := by linarith
    _ = _ := by ring

end LabelSwitches

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace PlanePotential

/-- The global segment kernel vanishes off the region on which the actual
finite density decomposition is valid. -/
lemma green_eq_zero_of_outside {ψ : ℂ → ℝ} {R X : ℝ}
    (hs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hRX : R ≤ X) {x y : ℂ}
    (hx : ‖x‖ ≤ X) (hy : X < ‖y‖) : green ψ x y = 0 := by
  have hz (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : ψ (x+t⁻¹ • (y-x)) = 0 := by
    by_contra hh
    have hw := hs _ hh
    have heq : y = (1-t) • x+t • (x+t⁻¹ • (y-x)) := by
      rw [smul_add,smul_smul,mul_inv_cancel₀ ht.1.ne',one_smul]
      module
    have hn := norm_add_le ((1-t) • x) (t • (x+t⁻¹ • (y-x)))
    rw [← heq,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_pos ht.1] at hn
    have hle := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hw.trans hRX) ht.1.le)
    nlinarith
  have hi : greenScalar ψ x y = 0 := by
    unfold greenScalar
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    simp only [hz t ht,zero_mul]
  simp only [green,hi,neg_zero,zero_smul]

lemma green_gradient_representation {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1) (x : ℂ) :
    (∫ y, ⟪green ψ x y,gradient g y⟫) = g x-∫ z, ψ z*g z := by
  simpa only [inner_gradient_right,RCLike.conj_to_real] using
    green_representation hψ hψc hg hD hψ1 x

theorem green_finite_decomposition {ι : Type*} [Fintype ι]
    {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ 1 g) {D R X Y B : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1)
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (β : ι → ℂ → ℂ) (hβ : ∀ i, Integrable (β i))
    (hβs : ∀ i y, β i y ≠ 0 → ‖y‖ ≤ Y)
    (hdecomp : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β i y) :
    ∀ᵐ x ∂volume.restrict {x : ℂ | ‖x‖ ≤ X},
      g x-∫ z, ψ z*g z = ∑ i, ∫ y, ⟪green ψ x y,β i y⟫ := by
  have hall := ae_all_iff.mpr (fun i => green_ae_integrable hψ.measurable hψs hψB hM hB hXY
    (hβ i) (hβs i))
  filter_upwards [hall,ae_restrict_mem (measurableSet_le measurable_norm measurable_const)] with x hi hx
  rw [← green_gradient_representation hψ hψc hg hD hψ1 x,← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [hdecomp] with y hy
  by_cases hyX : ‖y‖ ≤ X
  · rw [hy hyX,inner_sum]
  · rw [green_eq_zero_of_outside hψs hRX hx (lt_of_not_ge hyX)]
    simp

/-- The complete finite Minkowski step, after genuine kernel insertion. -/
theorem green_decomposition_norm {ι : Type*} [Fintype ι]
    {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ 1 g) {D R X Y B : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1)
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hRX : R ≤ X) (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (β : ι → ℂ → ℂ) (hβ : ∀ i, Integrable (β i))
    (hβs : ∀ i y, β i y ≠ 0 → ‖y‖ ≤ Y)
    (hdecomp : ∀ᵐ y, ‖y‖ ≤ X → gradient g y = ∑ i, β i y) :
    eLpNorm (fun x => g x-∫ z, ψ z*g z) (3/2) (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ≤
      ∑ i, eLpNorm (fun x => ∫ y, ⟪green ψ x y,β i y⟫) (3/2)
        (volume.restrict {x : ℂ | ‖x‖ ≤ X}) := by
  let μ := volume.restrict {x : ℂ | ‖x‖ ≤ X}
  let F : ι → ℂ → ℝ := fun i x => ∫ y, ⟪green ψ x y,β i y⟫
  have hmeas : ∀ i, AEStronglyMeasurable (F i) μ := fun i =>
    potential_aestronglyMeasurable _ (green_measurable ψ hψ.measurable) (hβ i)
  have heq : (fun x => g x-∫ z, ψ z*g z) =ᵐ[μ] fun x => ∑ i, F i x :=
    green_finite_decomposition hψ hψc hg hD hψ1 hψs hψB hRX hM hB hXY β hβ hβs hdecomp
  have hsum : eLpNorm (∑ i, F i) (3/2) μ ≤ ∑ i, eLpNorm (F i) (3/2) μ :=
    eLpNorm_sum_le (by
      rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
      norm_num)
  rw [eLpNorm_congr_ae heq]
  have hfun : (∑ i, F i) = fun x => ∑ i, F i x := by ext x; simp
  rw [hfun] at hsum
  exact hsum

end PlanePotential

namespace RadiusEnvelope
variable {E : Type*}

/-- The signed envelope over the entire compact real-radius interval. -/
def envelope (u : ℝ → E → ℝ) (a b : ℝ) (x : E) : ℝ :=
  sSup ((fun r => u r x) '' Icc a b)

lemma attains {u : ℝ → E → ℝ} {a b : ℝ} (hab : a ≤ b) (x : E)
    (hc : ContinuousOn (fun r => u r x) (Icc a b)) :
    ∃ r ∈ Icc a b, envelope u a b x = u r x ∧ ∀ t ∈ Icc a b, u t x ≤ u r x := by
  obtain ⟨r,hr,hm⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hc
  refine ⟨r,hr,?_,hm⟩
  apply le_antisymm
  · apply csSup_le ((Set.nonempty_Icc.mpr hab).image _)
    rintro _ ⟨t,ht,rfl⟩
    exact hm ht
  · apply le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    exact mem_image_of_mem _ hr

lemma le_envelope {u : ℝ → E → ℝ} {a b r : ℝ} (hr : r ∈ Icc a b) (x : E)
    (hc : ContinuousOn (fun r => u r x) (Icc a b)) : u r x ≤ envelope u a b x := by
  obtain ⟨t,ht,he,hm⟩ := attains (hr.1.trans hr.2) x hc
  rw [he]
  exact hm r hr

lemma lipschitz [NormedAddCommGroup E] {u : ℝ → E → ℝ} {a b : ℝ} {L : ℝ≥0} (hab : a ≤ b)
    (hc : ∀ x, ContinuousOn (fun r => u r x) (Icc a b))
    (hL : ∀ r ∈ Icc a b, LipschitzWith L (u r)) :
    LipschitzWith L (envelope u a b) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  obtain ⟨r,hr,her,hmr⟩ := attains hab x (hc x)
  obtain ⟨t,ht,het,hmt⟩ := attains hab y (hc y)
  rw [Real.dist_eq,abs_le]
  constructor
  · have h := (hL t ht).dist_le_mul x y
    rw [Real.dist_eq] at h
    rw [het]
    have hx := le_envelope ht x (hc x)
    have ha := (abs_le.mp h).1
    linarith
  · have h := (hL r hr).dist_le_mul x y
    rw [Real.dist_eq] at h
    rw [her]
    have hy := le_envelope hr y (hc y)
    have ha := (abs_le.mp h).2
    linarith

lemma zero_of_all_zero {u : ℝ → E → ℝ} {a b : ℝ} (hab : a ≤ b) {x : E}
    (hc : ContinuousOn (fun r => u r x) (Icc a b))
    (hz : ∀ r ∈ Icc a b, u r x = 0) : envelope u a b x = 0 := by
  obtain ⟨r,hr,he,_⟩ := attains hab x hc
  exact he.trans (hz r hr)

/-- Differentiable touching holds for every attaining radius; no derivative of
an argmax selector is taken. -/
theorem fderiv_touching [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℝ → E → ℝ} {a b r : ℝ} {x : E}
    (hr : r ∈ Icc a b) (hc : ∀ y, ContinuousOn (fun t => u t y) (Icc a b))
    (he : envelope u a b x = u r x)
    (hd : DifferentiableAt ℝ (envelope u a b) x) (hu : DifferentiableAt ℝ (u r) x) :
    fderiv ℝ (envelope u a b) x = fderiv ℝ (u r) x := by
  have hm : IsLocalMin (fun y => envelope u a b y-u r y) x := by
    apply IsMinOn.isLocalMin (s := univ) _ univ_mem
    intro y _
    change envelope u a b x-u r x ≤ envelope u a b y-u r y
    rw [he,sub_self]
    exact sub_nonneg.mpr (le_envelope hr y (hc y))
  have hz := hm.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub hu.hasFDerivAt)
  exact sub_eq_zero.mp hz

end RadiusEnvelope

namespace DiskMoments

lemma signedAverage_lipschitz {g : ℂ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {t : ℝ} (ht : 0 < t) : LipschitzWith L (fun x => signedAverage g x t) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [signedAverage_fixedDomain g x ht,signedAverage_fixedDomain g y ht,Real.dist_eq,
    ← sub_div,abs_div,abs_of_pos Real.pi_pos]
  have hxi : IntegrableOn (fun z : ℂ => g (x+t • z)) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1)
      (hg.continuous.comp (by fun_prop)).continuousOn).mono_set Metric.ball_subset_closedBall
  have hyi : IntegrableOn (fun z : ℂ => g (y+t • z)) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1)
      (hg.continuous.comp (by fun_prop)).continuousOn).mono_set Metric.ball_subset_closedBall
  rw [← integral_sub hxi hyi]
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0:ℂ) 1)) :=
    ⟨by simp⟩
  have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict (Metric.ball (0:ℂ) 1))
    (C := (L:ℝ)*dist x y) (f := fun z : ℂ => g (x+t • z)-g (y+t • z)) (by
      filter_upwards with z
      simpa only [Real.norm_eq_abs,← Real.dist_eq,dist_add_right] using hg.dist_le_mul (x+t • z) (y+t • z))
  have hv : (volume.restrict (Metric.ball (0:ℂ) 1)).real univ = Real.pi := by
    simp [measureReal_def,Complex.volume_ball]
  rw [hv,Real.norm_eq_abs] at hi
  exact (div_le_iff₀ Real.pi_pos).mpr hi

lemma signedAverage_radius_continuousOn {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => signedAverage g x t) (Icc a b) := by
  intro t ht
  exact (hasDerivAt_signedAverage hg x (ha.trans_le ht.1)).continuousAt.continuousWithinAt

lemma hasFDerivAt_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasFDerivAt (fun x => signedAverage g x t)
      ((1/Real.pi) • ∫ z in Metric.ball 0 1, fderiv ℝ g (x+t • z)) x := by
  let F : ℂ → ℂ → ℝ := fun x z => g (x+t • z)
  have hFi : IntegrableOn (F x) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1)
      (hg.continuous.comp (by fun_prop)).continuousOn).mono_set Metric.ball_subset_closedBall
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Metric.ball (0:ℂ) 1)) (F := F)
    (F' := fun x z => fderiv ℝ g (x+t • z)) (bound := fun _ => D)
    (s := univ) (x₀ := x) univ_mem
    (Eventually.of_forall (fun x => (hg.continuous.comp (by fun_prop)).aestronglyMeasurable))
    hFi ((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ (fun z x _ => hD (x+t • z))) (integrableOn_const (by finiteness))
    (ae_of_all _ (fun z x _ => by
      simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq,F] using
        (hg.differentiable one_ne_zero (x+t • z)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (t • z))))
  convert! hd.const_mul (1/Real.pi) using 1
  · funext y
    simpa only [F,div_eq_mul_inv,one_div,mul_comm,mul_one] using signedAverage_fixedDomain g y ht

/-- Actual signed run envelopes: locally differentiable almost everywhere, over
all radii in their compact interval. -/
theorem run_envelope_lipschitz {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L : ℝ≥0, LipschitzWith L (RadiusEnvelope.envelope (fun r x => signedAverage g x r) a b) := by
  obtain ⟨L,hL⟩ := hg.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
  exact ⟨L,RadiusEnvelope.lipschitz hab (fun x => signedAverage_radius_continuousOn hg x ha)
    (fun r hr => signedAverage_lipschitz hL (ha.trans_le hr.1))⟩

lemma signedAverage_eq_zero_of_outside {g : ℂ → ℝ} {R : ℝ}
    (hs : ∀ y, g y ≠ 0 → ‖y‖ ≤ R) {x : ℂ} {t : ℝ} (hx : R+t ≤ ‖x‖) :
    signedAverage g x t = 0 := by
  unfold signedAverage
  have hz : (∫ y in Metric.ball x t, g y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    by_contra hny
    have hn := hs y hny
    have hd : ‖x-y‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hy
    have hh : ‖x‖ ≤ ‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
    linarith
  rw [hz,zero_div]

/-- Every radius in the run is retained, but a common compact spatial support
still exists. -/
theorem run_envelope_hasCompactSupport {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    HasCompactSupport (RadiusEnvelope.envelope (fun r x => signedAverage g x r) a b) := by
  obtain ⟨R,hR⟩ := hgc.isBounded.subset_closedBall (0:ℂ)
  have hs : ∀ y, g y ≠ 0 → ‖y‖ ≤ R := by
    intro y hy
    simpa only [Metric.mem_closedBall,dist_zero_right] using hR (subset_tsupport g hy)
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0:ℂ) (R+b)) isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  by_contra hn
  have hz : RadiusEnvelope.envelope (fun r x => signedAverage g x r) a b x = 0 := by
    apply RadiusEnvelope.zero_of_all_zero hab (signedAverage_radius_continuousOn hg x ha)
    intro r hr
    exact signedAverage_eq_zero_of_outside hs (by linarith [hr.2])
  exact hx hz

/-- AE differentiability and universal touching of actual run gradients. -/
theorem run_envelope_ae_touching {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∀ᵐ x, ∀ r ∈ Icc a b,
      RadiusEnvelope.envelope (fun r x => signedAverage g x r) a b x = signedAverage g x r →
      fderiv ℝ (RadiusEnvelope.envelope (fun r x => signedAverage g x r) a b) x =
        (1/Real.pi) • ∫ z in Metric.ball 0 1, fderiv ℝ g (x+r • z) := by
  obtain ⟨L,hL⟩ := run_envelope_lipschitz hg hgc ha hab
  obtain ⟨K,hK⟩ := hg.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
  filter_upwards [hL.ae_differentiableAt] with x hx
  intro r hr he
  have hd := hasFDerivAt_signedAverage hg (fun y => norm_fderiv_le_of_lipschitz ℝ hK) x
    (ha.trans_le hr.1)
  exact (RadiusEnvelope.fderiv_touching hr (fun y => signedAverage_radius_continuousOn hg y ha)
    he hx hd.differentiableAt).trans hd.fderiv

end DiskMoments

end SignedDisk

end

end OAI
