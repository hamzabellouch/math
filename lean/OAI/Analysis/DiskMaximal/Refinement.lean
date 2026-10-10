import OAI.Analysis.DiskMaximal.Marks

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset

noncomputable section

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

end DiskMoments

namespace DiskMoments

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

namespace DyadicHats

def point (r : ℝ) (p : ℤ × ℤ) : ℂ := ⟨r*p.1,r*p.2⟩
def boxNorm (x : ℂ) : ℝ := max |x.re| |x.im|

lemma boxNorm_nonneg (x : ℂ) : 0 ≤ boxNorm x := le_trans (abs_nonneg _) (le_max_left _ _)
lemma boxNorm_le_norm (x : ℂ) : boxNorm x ≤ ‖x‖ :=
  max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
lemma norm_le_two_boxNorm (x : ℂ) : ‖x‖ ≤ 2*boxNorm x := by
  have h := Complex.norm_le_abs_re_add_abs_im x
  have hr : |x.re| ≤ boxNorm x := le_max_left _ _
  have hi : |x.im| ≤ boxNorm x := le_max_right _ _
  linarith
lemma boxNorm_add_le (x y : ℂ) : boxNorm (x+y) ≤ boxNorm x+boxNorm y := by
  apply max_le
  · exact (abs_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (abs_add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
lemma boxNorm_neg (x : ℂ) : boxNorm (-x) = boxNorm x := by simp [boxNorm]
lemma boxNorm_sub_comm (x y : ℂ) : boxNorm (x-y) = boxNorm (y-x) := by
  rw [← neg_sub y x,boxNorm_neg]

lemma hat_pos_iff {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) (x : ℂ) :
    0 < hat r p x ↔ boxNorm (x-point r p) < r := by
  have hp : 0 < hat r p x ↔ 0 < tent (x.re/r-p.1) ∧ 0 < tent (x.im/r-p.2) := by
    constructor
    · intro h
      exact ⟨pos_of_mul_pos_left h (tent_nonneg _),pos_of_mul_pos_right h (tent_nonneg _)⟩
    · intro h
      exact mul_pos h.1 h.2
  rw [hp,tent_pos_iff,tent_pos_iff]
  have hr0 : r ≠ 0 := ne_of_gt hr
  have h1 : x.re/r-p.1 = (x.re-r*p.1)/r := by field_simp
  have h2 : x.im/r-p.2 = (x.im-r*p.2)/r := by field_simp
  rw [h1,h2,abs_div,abs_div,abs_of_pos hr,div_lt_one hr,div_lt_one hr]
  simp only [boxNorm,Complex.sub_re,Complex.sub_im,point,max_lt_iff]

lemma hat_ne_zero_iff {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) (x : ℂ) :
    hat r p x ≠ 0 ↔ boxNorm (x-point r p) < r := by
  constructor
  · intro h
    exact (hat_pos_iff hr p x).mp (lt_of_le_of_ne (hat_nonneg r p x) (Ne.symm h))
  · intro h
    exact ne_of_gt ((hat_pos_iff hr p x).mpr h)

lemma support_hat_subset {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) :
    Function.support (hat r p) ⊆ Metric.closedBall (point r p) (2*r) := by
  intro x hx
  rw [Metric.mem_closedBall,dist_eq_norm]
  exact (norm_le_two_boxNorm _).trans (mul_le_mul_of_nonneg_left ((hat_ne_zero_iff hr p x).mp hx).le (by norm_num))

lemma hasCompactSupport_hat {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) :
    HasCompactSupport (hat r p) := by
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (point r p) (2*r)) isClosed_closure
  exact closure_minimal (support_hat_subset hr p) Metric.isClosed_closedBall

/-- Globally uniform spatial Lipschitz bound for the literal bilinear hats. -/
lemma lipschitz_hat {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) :
    LipschitzWith (Real.toNNReal (2/r)) (hat r p) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  let a := tent (x.re/r-p.1)
  let b := tent (x.im/r-p.2)
  let c := tent (y.re/r-p.1)
  let d := tent (y.im/r-p.2)
  have h1 : |a-c| ≤ ‖x-y‖/r := by
    have h := lipschitz_tent.dist_le_mul (x.re/r-p.1) (y.re/r-p.1)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right,← sub_div,
      abs_div,abs_of_pos hr] at h
    exact h.trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm (x-y)) hr.le)
  have h2 : |b-d| ≤ ‖x-y‖/r := by
    have h := lipschitz_tent.dist_le_mul (x.im/r-p.2) (y.im/r-p.2)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right,← sub_div,
      abs_div,abs_of_pos hr] at h
    exact h.trans (div_le_div_of_nonneg_right (Complex.abs_im_le_norm (x-y)) hr.le)
  have hab : |a*b-c*d| ≤ |a-c|+|b-d| := by
    calc
      _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
      _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
      _ = |a-c| *b+c*|b-d| := by rw [abs_mul,abs_mul,abs_of_nonneg (tent_nonneg _),abs_of_nonneg (tent_nonneg _)]
      _ ≤ |a-c| *1+1*|b-d| := add_le_add
        (mul_le_mul_of_nonneg_left (tent_le_one _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (tent_le_one _) (abs_nonneg _))
      _ = _ := by ring
  change |a*b-c*d| ≤ _
  rw [Real.coe_toNNReal (2/r) (by positivity),dist_eq_norm]
  calc
    _ ≤ ‖x-y‖/r+‖x-y‖/r := hab.trans (add_le_add h1 h2)
    _ = _ := by ring

lemma step_locality {p q : ℤ × ℤ} (hpq : 0 < step p q) {r : ℝ} (hr : 0 < r) :
    boxNorm (point (r/2) q-point r p) ≤ r/2 := by
  have h1 : |(q.1:ℝ)/2-p.1| < 1 := (tent_pos_iff _).mp
    (pos_of_mul_pos_left hpq (tent_nonneg _))
  have h2 : |(q.2:ℝ)/2-p.2| < 1 := (tent_pos_iff _).mp
    (pos_of_mul_pos_right hpq (tent_nonneg _))
  have hbound (j k : ℤ) (h : |(j:ℝ)/2-k| < 1) : |(j:ℝ)/2-k| ≤ 1/2 := by
    have habs := abs_lt.mp h
    have hlow : 2*k-1 ≤ j := by
      have : (2*k-2:ℝ) < j := by linarith
      have : 2*k-2 < j := by exact_mod_cast this
      omega
    have hhigh : j ≤ 2*k+1 := by
      have : (j:ℝ) < 2*k+2 := by linarith
      have : j < 2*k+2 := by exact_mod_cast this
      omega
    have hlo : (2:ℝ)*k-1 ≤ j := by exact_mod_cast hlow
    have hhi : (j:ℝ) ≤ 2*k+1 := by exact_mod_cast hhigh
    rw [abs_le]
    constructor <;> linarith
  have h1' := hbound q.1 p.1 h1
  have h2' := hbound q.2 p.2 h2
  change max |r/2*q.1-r*p.1| |r/2*q.2-r*p.2| ≤ r/2
  have hm (j k : ℤ) (h : |(j:ℝ)/2-k| ≤ 1/2) : |r/2*j-r*k| ≤ r/2 := by
    rw [show r/2*j-r*k = r*((j:ℝ)/2-k) by ring,abs_mul,abs_of_pos hr]
    nlinarith
  exact max_le (hm _ _ h1') (hm _ _ h2')

end DyadicHats

namespace DyadicHats
open scoped BigOperators

/-- Literal nine-child support of an adjacent dyadic refinement row. -/
def children (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (2*p.1-1) (2*p.1+1)).product (Finset.Icc (2*p.2-1) (2*p.2+1))

lemma tent_half_zero {j k : ℤ} (h : j ∉ Finset.Icc (2*k-1) (2*k+1)) :
    tent ((j:ℝ)/2-k) = 0 := by
  have ht : j-2*k ∉ Finset.Icc (-1) 1 := by
    simp only [Finset.mem_Icc] at *
    omega
  convert tent_half_integer ht using 1
  push_cast
  congr 1
  ring

lemma step_zero_of_not_child {p q : ℤ × ℤ} (hq : q ∉ children p) : step p q = 0 := by
  have hq' : ¬(q.1 ∈ Finset.Icc (2*p.1-1) (2*p.1+1) ∧ q.2 ∈ Finset.Icc (2*p.2-1) (2*p.2+1)) := by
    exact fun hn => hq (Finset.mem_product.mpr hn)
  rw [not_and_or] at hq'
  rcases hq' with hq | hq
  · rw [step,tent_half_zero hq,zero_mul]
  · rw [step,tent_half_zero hq,mul_zero]

lemma hat_refine_finite (r : ℝ) (p : ℤ × ℤ) (x : ℂ) :
    hat (2*r) p x = ∑ q ∈ children p, step p q*hat r q x := by
  rw [hat_refine,tsum_eq_sum (s := children p)]
  intro q hq
  rw [step_zero_of_not_child hq,zero_mul]

/-- The vector mass of the actual density, not an abstract additive tree. -/
def vectorMass (h : ℂ → ℂ) (r : ℝ) (p : ℤ × ℤ) : ℂ := ∫ y, hat r p y • h y

def scalarMass (h : ℂ → ℂ) (r : ℝ) (p : ℤ × ℤ) : ℝ := ‖vectorMass h r p‖

lemma integrable_hat_smul {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) (p : ℤ × ℤ) :
    Integrable (fun y => hat r p y • h y) := by
  apply hh.bdd_smul 1 (continuous_hat r p).aestronglyMeasurable
  filter_upwards with y
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hat_nonneg r p y)] using hat_le_one r p y

lemma vectorMass_refine {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) (p : ℤ × ℤ) :
    vectorMass h (2*r) p = ∑ q ∈ children p, step p q • vectorMass h r q := by
  unfold vectorMass
  simp_rw [hat_refine_finite,Finset.sum_smul,mul_smul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    exact integral_smul _ _
  · intro q hq
    exact (integrable_hat_smul hh r q).smul _

lemma scalarMass_le_integral {h : ℂ → ℂ} (r : ℝ) (p : ℤ × ℤ) :
    scalarMass h r p ≤ ∫ y, hat r p y * ‖h y‖ := by
  unfold scalarMass vectorMass
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hat_nonneg _ _ _)] using
    norm_integral_le_integral_norm (fun y => hat r p y • h y)

/-- Any finite set of roots carries at most the total L1 density, uniformly
in the scale. This proves the full-grid mass budget once finite support is used. -/
lemma sum_scalarMass_le {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) (S : Finset (ℤ × ℤ)) :
    ∑ p ∈ S, scalarMass h r p ≤ ∫ y, ‖h y‖ := by
  have hi (p : ℤ × ℤ) : Integrable (fun y => hat r p y * ‖h y‖) := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hat_nonneg _ _ _)] using
      (integrable_hat_smul hh r p).norm
  calc
    _ ≤ ∑ p ∈ S, ∫ y, hat r p y * ‖h y‖ := Finset.sum_le_sum (fun p _ => scalarMass_le_integral r p)
    _ = ∫ y, ∑ p ∈ S, hat r p y * ‖h y‖ := (integral_finsetSum _ (fun p _ => hi p)).symm
    _ ≤ ∫ y, ‖h y‖ := by
      apply integral_mono (integrable_finsetSum _ (fun p _ => hi p)) hh.norm
      intro y
      change (∑ p ∈ S, hat r p y * ‖h y‖) ≤ ‖h y‖
      rw [← Finset.sum_mul]
      have hs := Summable.sum_le_tsum S (fun p _ => hat_nonneg r p y) (summable_hat r y)
      rw [tsum_hat] at hs
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (norm_nonneg (h y))

lemma scalarMass_refine_le {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) (p : ℤ × ℤ) :
    scalarMass h (2*r) p ≤ ∑ q ∈ children p, step p q*scalarMass h r q := by
  unfold scalarMass
  rw [vectorMass_refine hh]
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (step_nonneg _ _)] using
    norm_sum_le (children p) (fun q => step p q • vectorMass h r q)

/-- A finite index set that contains every hat meeting a fixed bounded region. -/
def boundedIndices (r R : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-⌈R/r+1⌉) ⌈R/r+1⌉).product (Finset.Icc (-⌈R/r+1⌉) ⌈R/r+1⌉)

lemma mem_boundedIndices {r R : ℝ} (hr : 0 < r) {x : ℂ} (hx : ‖x‖ ≤ R)
    {p : ℤ × ℤ} (hp : hat r p x ≠ 0) : p ∈ boundedIndices r R := by
  have hpos : 0 < hat r p x := lt_of_le_of_ne (hat_nonneg r p x) (Ne.symm hp)
  have h1 := (tent_pos_iff _).mp (pos_of_mul_pos_left hpos (tent_nonneg _))
  have h2 := (tent_pos_iff _).mp (pos_of_mul_pos_right hpos (tent_nonneg _))
  have hbound (a : ℝ) (j : ℤ) (ha : |a| ≤ R) (hj : |a/r-j| < 1) :
      j ∈ Finset.Icc (-⌈R/r+1⌉) ⌈R/r+1⌉ := by
    have hq : |a/r| ≤ R/r := by rw [abs_div,abs_of_pos hr]; exact div_le_div_of_nonneg_right ha hr.le
    have hja : |(j:ℝ)| ≤ R/r+1 := by
      calc
        _ = |a/r-(a/r-j)| := by congr 1; ring
        _ ≤ |a/r|+|a/r-j| := abs_sub _ _
        _ ≤ R/r+1 := add_le_add hq hj.le
    have hlo := (abs_le.mp hja).1
    have hhi := (abs_le.mp hja).2
    have hc := Int.le_ceil (R/r+1)
    simp only [Finset.mem_Icc]
    constructor
    · have : (-(⌈R/r+1⌉:ℝ)) ≤ j := by linarith
      exact_mod_cast this
    · have : (j:ℝ) ≤ ⌈R/r+1⌉ := hhi.trans hc
      exact_mod_cast this
  exact Finset.mem_product.mpr ⟨hbound x.re p.1 ((Complex.abs_re_le_norm x).trans hx) h1,
    hbound x.im p.2 ((Complex.abs_im_le_norm x).trans hx) h2⟩

lemma vectorMass_zero_of_not_index {h : ℂ → ℂ} {r R : ℝ} (hr : 0 < r)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) {p : ℤ × ℤ} (hp : p ∉ boundedIndices r R) :
    vectorMass h r p = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with y
  by_cases hy : h y = 0
  · simp only [hy,smul_zero,Pi.zero_apply]
  · have hh : hat r p y = 0 := by
      by_contra hn
      exact hp (mem_boundedIndices hr (hs y hy) hn)
    simp only [hh,zero_smul,Pi.zero_apply]

/-- Compactly supported actual densities have finitely many nonzero vector
masses at each positive scale. -/
lemma finite_vectorMass_support {h : ℂ → ℂ} (hc : HasCompactSupport h) {r : ℝ} (hr : 0 < r) :
    (Function.support (vectorMass h r)).Finite := by
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:ℂ)
  apply (boundedIndices r R).finite_toSet.subset
  intro p hp
  by_contra hn
  exact hp (vectorMass_zero_of_not_index hr (fun y hy => by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hR (subset_tsupport h hy)) hn)

end DyadicHats

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
noncomputable section

namespace LipschitzWith
open scoped _root_.LipschitzWith
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ] {f g : E → ℝ} {L K : ℝ≥0}

/-- Genuine integration by parts for Lipschitz weights and compact Lipschitz
potentials. Differentiability is required only almost everywhere, and follows
from Rademacher rather than being a new premise. -/
theorem integral_fderiv_mul_eq_neg (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (hgc : HasCompactSupport g) (v : E) :
    (∫ x, fderiv ℝ f x v * g x ∂μ) = -∫ x, fderiv ℝ g x v * f x ∂μ := by
  have h1 : (fun x => fderiv ℝ f x v*g x) =ᵐ[μ] fun x => lineDeriv ℝ f x v*g x := by
    filter_upwards [hf.ae_differentiableAt (μ := μ)] with x hx
    rw [hx.lineDeriv_eq_fderiv]
  have h2 : (fun x => lineDeriv ℝ g x (-v)*f x) =ᵐ[μ] fun x => -(fderiv ℝ g x v*f x) := by
    filter_upwards [hg.ae_differentiableAt (μ := μ)] with x hx
    rw [hx.lineDeriv_eq_fderiv,map_neg,neg_mul]
  rw [integral_congr_ae h1,hf.integral_lineDeriv_mul_eq hg hgc v,integral_congr_ae h2,integral_neg]

/-- The total gradient version obtained from Riesz and measurable fderiv is
locally integrable, including on the nondifferentiability set. -/
theorem locallyIntegrable_gradient (hf : LipschitzWith L f) :
    LocallyIntegrable (gradient f) μ := by
  have hm : AEStronglyMeasurable (gradient f) μ :=
    ((InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ f)).aestronglyMeasurable
  have hb : ∀ x, ‖gradient f x‖ ≤ (L:ℝ) := by
    intro x
    simpa only [gradient,(InnerProductSpace.toDual ℝ E).symm.norm_map] using
      (norm_fderiv_le_of_lipschitz ℝ hf : ‖fderiv ℝ f x‖ ≤ (L:ℝ))
  exact (memLp_top_of_bound hm (L:ℝ) (ae_of_all _ hb)).locallyIntegrable le_top

theorem integrable_gradient (hf : LipschitzWith L f) (hc : HasCompactSupport f) :
    Integrable (gradient f) μ := by
  have hs : HasCompactSupport (gradient f) :=
    (hc.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ E).symm)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport (gradient f))).mp
    ((_root_.OAI.LipschitzWith.locallyIntegrable_gradient (μ := μ) hf).integrableOn_isCompact hs)

theorem integral_mul_fderiv_eq_neg (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (hgc : HasCompactSupport g) (v : E) :
    (∫ x, f x * fderiv ℝ g x v ∂μ) = -∫ x, inner ℝ (gradient f x) v * g x ∂μ := by
  simp only [gradient,InnerProductSpace.toDual_symm_apply]
  have h := _root_.OAI.LipschitzWith.integral_fderiv_mul_eq_neg (μ := μ) hf hg hgc v
  rw [show (fun x => f x * fderiv ℝ g x v) = (fun x => fderiv ℝ g x v * f x) by
    funext x; exact mul_comm _ _]
  linarith

end LipschitzWith

open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace DyadicHats

def indexBox (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(N:ℤ)) N).product (Finset.Icc (-(N:ℤ)) N)
abbrev Grid (N : ℕ) := {p : ℤ × ℤ // p ∈ indexBox N}

lemma parent_in_box {N : ℕ} {p q : ℤ × ℤ} (hq : q ∈ indexBox N) (hpq : step p q ≠ 0) :
    p ∈ indexBox N := by
  have hq1 : -(N:ℤ) ≤ q.1 ∧ q.1 ≤ N := Finset.mem_Icc.mp (Finset.mem_product.mp hq).1
  have hq2 : -(N:ℤ) ≤ q.2 ∧ q.2 ≤ N := Finset.mem_Icc.mp (Finset.mem_product.mp hq).2
  have hh : 0 < step p q := lt_of_le_of_ne (step_nonneg p q) (Ne.symm hpq)
  have h1 := (tent_pos_iff _).mp (pos_of_mul_pos_left hh (tent_nonneg _))
  have h2 := (tent_pos_iff _).mp (pos_of_mul_pos_right hh (tent_nonneg _))
  have hbound (j k : ℤ) (hk : -(N:ℤ) ≤ k ∧ k ≤ N) (ha : |(k:ℝ)/2-j| < 1) :
      j ∈ Finset.Icc (-(N:ℤ)) N := by
    have hlo : -(N:ℝ) ≤ k := by exact_mod_cast hk.1
    have hhi : (k:ℝ) ≤ N := by exact_mod_cast hk.2
    have hj := abs_lt.mp ha
    simp only [Finset.mem_Icc]
    constructor
    · by_contra hn
      have : j ≤ -(N:ℤ)-1 := by omega
      have : (j:ℝ) ≤ -(N:ℝ)-1 := by exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    · by_contra hn
      have : (N:ℤ)+1 ≤ j := by omega
      have : (N:ℝ)+1 ≤ j := by exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact Finset.mem_product.mpr ⟨hbound _ _ hq1 h1,hbound _ _ hq2 h2⟩

/-- Restriction to a finite box retains the exact column normalization of the
positive dyadic refinement matrix; it does not normalize its rows. -/
lemma grid_step_column (N : ℕ) (q : Grid N) : (∑ p : Grid N, step p q) = 1 := by
  have he := step_column q.val
  rw [tsum_eq_sum (s := indexBox N)] at he
  · exact (Finset.sum_coe_sort (indexBox N) (fun p => step p q)).trans he
  · intro p hp
    by_contra hn
    exact hp (parent_in_box q.property hn)

lemma mem_indexBox_of_le {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {x : ℂ} (hx : ‖x‖ ≤ R) {p : ℤ × ℤ} (hp : hat r p x ≠ 0) :
    p ∈ indexBox N := by
  have hm := mem_boundedIndices hr hx hp
  have hc : ⌈R/r+1⌉ ≤ (N:ℤ) := Int.ceil_le.mpr (by simpa only [Int.cast_natCast] using hN)
  have h1 := Finset.mem_Icc.mp (Finset.mem_product.mp hm).1
  have h2 := Finset.mem_Icc.mp (Finset.mem_product.mp hm).2
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega

lemma hat_mul_zero_outside {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    {p : ℤ × ℤ} (hp : p ∉ indexBox N) (x : ℂ) : hat r p x*h x = 0 := by
  by_cases hx : h x = 0
  · rw [hx,mul_zero]
  · have ht : hat r p x = 0 := by
      by_contra hn
      exact hp (mem_indexBox_of_le hr hN (hs x hx) hn)
    rw [ht,zero_mul]

lemma density_partition_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (x : ℂ) :
    (∑ p : Grid N, hat r p x*h x) = h x := by
  have he : (∑' p : ℤ × ℤ, hat r p x*h x) = ∑ p ∈ indexBox N, hat r p x*h x :=
    tsum_eq_sum (fun p hp => hat_mul_zero_outside hr hN hs hp x)
  rw [Finset.sum_coe_sort (indexBox N) (fun p => hat r p x*h x),← he,
    tsum_mul_right,tsum_hat,one_mul]

lemma density_refine_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (p : Grid N) (x : ℂ) :
    hat (2*r) p x*h x = ∑ q : Grid N, step p q*(hat r q x*h x) := by
  rw [hat_refine,← tsum_mul_right,tsum_eq_sum (s := indexBox N)]
  · rw [Finset.sum_coe_sort (indexBox N) (fun q => step p q*(hat r q x*h x))]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  · intro q hq
    rw [mul_assoc,hat_mul_zero_outside hr hN hs hq x,mul_zero]

lemma integrable_hat_mul {h : ℂ → ℝ} (hh : Integrable h) (r : ℝ) (p : ℤ × ℤ) :
    Integrable (fun y => hat r p y*h y) := by
  exact hh.bdd_smul 1 (continuous_hat r p).aestronglyMeasurable
    (ae_of_all _ (fun y => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hat_nonneg r p y)] using hat_le_one r p y))

def scale (r : ℝ) (k : ℕ) : ℝ := (2:ℝ)^k*r
lemma scale_pos {r : ℝ} (hr : 0 < r) (k : ℕ) : 0 < scale r k := by unfold scale; positivity
lemma scale_succ (r : ℝ) (k : ℕ) : scale r (k+1) = 2*scale r k := by
  unfold scale
  rw [pow_succ]
  ring
lemma le_scale {r : ℝ} (hr : 0 ≤ r) (k : ℕ) : r ≤ scale r k := by
  have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  simpa only [one_mul,scale] using mul_le_mul_of_nonneg_right hp hr

lemma scale_index_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) (k : ℕ) : R/scale r k+1 ≤ (N:ℝ) := by
  have hd : R / scale r k ≤ R / r := div_le_div_of_nonneg_left hR hr (le_scale hr.le k)
  linarith

end DyadicHats

end
end

end OAI
