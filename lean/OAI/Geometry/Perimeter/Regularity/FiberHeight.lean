import OAI.Geometry.Perimeter.Regularity.EllipticLocality

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Pointwise
namespace RPISingularHarnack
open RPI.Boundary

theorem minimizing_phase_constant_off_support {n : ℕ} (hn : 1 < n)
    {E U : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hU : IsPreconnected U) (hdis : Disjoint U (perimeterSupport E)) :
    (∀ᵐ x ∂volume, x ∈ U → x ∈ E) ∨ (∀ᵐ x ∂volume, x ∈ U → x ∉ E) := by
  let K := (volume.restrict E).support
  have hK : IsClosed K := Measure.isClosed_support
  have hp : Real.HolderConjugate (n : ℝ) (Real.conjExponent (n : ℝ)) :=
    Real.HolderConjugate.conjExponent (by exact_mod_cast hn)
  have heK : E =ᵐ[volume] K := minimizing_ae_eq_phaseSupport hp hmin
  have hf : frontier K = perimeterSupport E := minimizing_frontier_phaseSupport hp hmin
  have hcover : U ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · left
      by_contra hxi
      have hxf : x ∈ frontier K := by
        rw [frontier, hK.closure_eq]
        exact ⟨hxK,hxi⟩
      exact Set.disjoint_left.mp hdis hx (hf ▸ hxf)
    · exact Or.inr hxK
  rcases hU.subset_or_subset isOpen_interior hK.isOpen_compl
    (Set.disjoint_left.mpr fun x hx hx' ↦ hx' (interior_subset hx)) hcover with h | h
  · left
    filter_upwards [heK.mem_iff] with x hx
    intro hxU
    exact hx.mpr (interior_subset (h hxU))
  · right
    filter_upwards [heK.mem_iff] with x hx
    intro hxU hxE
    exact h hxU (hx.mp hxE)

theorem minimizing_phase_absent_of_anchor {n : ℕ} (hn : 1 < n)
    {E U A : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hU : IsPreconnected U) (hdis : Disjoint U (perimeterSupport E))
    (hAU : A ⊆ U) (hanchor : 0 < volume (A \ E)) :
    ∀ᵐ x ∂volume, x ∈ U → x ∉ E := by
  rcases minimizing_phase_constant_off_support hn hmin hU hdis with h | h
  · have hz : volume (A \ E) = 0 := by
      apply measure_mono_null (fun x hx ↦ show x ∈ {x | ¬ (x ∈ U → x ∈ E)} from
        fun hh ↦ hx.2 (hh (hAU hx.1)))
      exact ae_iff.mp h
    exact (hanchor.ne' hz).elim
  · exact h

theorem minimizing_phase_present_of_anchor {n : ℕ} (hn : 1 < n)
    {E U A : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hU : IsPreconnected U) (hdis : Disjoint U (perimeterSupport E))
    (hAU : A ⊆ U) (hanchor : 0 < volume (A ∩ E)) :
    ∀ᵐ x ∂volume, x ∈ U → x ∈ E := by
  rcases minimizing_phase_constant_off_support hn hmin hU hdis with h | h
  · exact h
  · have hz : volume (A ∩ E) = 0 := by
      apply measure_mono_null (fun x hx ↦ show x ∈ {x | ¬ (x ∈ U → x ∉ E)} from
        fun hh ↦ hh (hAU hx.1) hx.2)
      exact ae_iff.mp h
    exact (hanchor.ne' hz).elim

theorem minimizing_slab_phase_agreement {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (v : Euc n) {R a : ℝ} (ha : 0 ≤ a)
    (hheight : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| ≤ a)
    {A B : Set (Euc n)}
    (hA : A ⊆ Metric.ball 0 R ∩ {x | a < inner ℝ v x})
    (hB : B ⊆ Metric.ball 0 R ∩ {x | inner ℝ v x < -a})
    (hanchorA : 0 < volume (A \ E)) (hanchorB : 0 < volume (B ∩ E)) :
    ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0) := by
  have hu : IsPreconnected (Metric.ball (0 : Euc n) R ∩ {x | a < inner ℝ v x}) :=
    ((convex_ball _ _).inter ((convex_Ioi a).linear_preimage (innerSL ℝ v).toLinearMap)).isPreconnected
  have hl : IsPreconnected (Metric.ball (0 : Euc n) R ∩ {x | inner ℝ v x < -a}) :=
    ((convex_ball _ _).inter ((convex_Iio (-a)).linear_preimage (innerSL ℝ v).toLinearMap)).isPreconnected
  have hdu : Disjoint (Metric.ball (0 : Euc n) R ∩ {x | a < inner ℝ v x})
      (perimeterSupport E) := by
    apply Set.disjoint_left.mpr
    intro x hx hs
    exact (hx.2.trans_le ((le_abs_self _).trans (hheight x ⟨hs,hx.1⟩))).false
  have hdl : Disjoint (Metric.ball (0 : Euc n) R ∩ {x | inner ℝ v x < -a})
      (perimeterSupport E) := by
    apply Set.disjoint_left.mpr
    intro x hx hs
    have hh := (abs_le.mp (hheight x ⟨hs,hx.1⟩)).1
    exact (hx.2.trans_le hh).false
  have hupper := minimizing_phase_absent_of_anchor hn hmin hu hdu hA hanchorA
  have hlower := minimizing_phase_present_of_anchor hn hmin hl hdl hB hanchorB
  filter_upwards [hupper,hlower] with x hx hy
  intro hxball hxa
  rcases lt_abs.mp hxa with hpos | hneg
  · have hnot := hx ⟨hxball,hpos⟩
    simp only [hnot, false_iff, not_lt]
    exact ha.trans hpos.le
  · have hyes := hy ⟨hxball,by change inner ℝ v x < -a; linarith⟩
    simp only [hyes, true_iff]
    linarith

def localizedPhaseError {n : ℕ} (E : Set (Euc n)) (v : Euc n) (R : ℝ) : Euc n → ℝ :=
  (Metric.ball 0 R).indicator (fun x ↦ E.indicator (fun _ ↦ (1:ℝ)) x -
    {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) x)

def fiberHeight {n : ℕ} (E : Set (Euc n)) (v : Euc n) (R : ℝ) (x : Euc n) : ℝ :=
  ∫ s : ℝ, localizedPhaseError E v R (x + s • v)

theorem localizedPhaseError_measurable {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (v : Euc n) (R : ℝ) :
    Measurable (localizedPhaseError E v R) := by
  exact ((measurable_const.indicator hE).sub (measurable_const.indicator
    (isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet)).indicator
      measurableSet_ball

theorem localizedPhaseError_norm_le_one {n : ℕ} (E : Set (Euc n))
    (v : Euc n) (R : ℝ) (x : Euc n) : ‖localizedPhaseError E v R x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ Metric.ball (0 : Euc n) R
  · by_cases hE : x ∈ E <;> by_cases hH : inner ℝ v x < 0 <;>
      simp [localizedPhaseError,hx,hE,hH]
  · simp [localizedPhaseError,hx]

theorem fiberHeight_add_smul {n : ℕ} (E : Set (Euc n)) (v : Euc n) (R t : ℝ)
    (x : Euc n) : fiberHeight E v R (x+t•v) = fiberHeight E v R x := by
  unfold fiberHeight
  have heq : (fun s : ℝ ↦ localizedPhaseError E v R (x+t•v+s•v)) =
      (fun s : ℝ ↦ localizedPhaseError E v R (x+(s+t)•v)) := by
    funext s
    congr 1
    rw [add_smul]
    abel
  rw [heq]
  exact integral_add_right_eq_self (fun s : ℝ ↦ localizedPhaseError E v R (x+s•v)) t

theorem fiberHeight_stronglyMeasurable {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (v : Euc n) (R : ℝ) :
    StronglyMeasurable (fiberHeight E v R) := by
  apply StronglyMeasurable.integral_prod_right
  exact ((localizedPhaseError_measurable hE v R).comp
    (continuous_fst.add (continuous_snd.smul continuous_const)).measurable).stronglyMeasurable

theorem unit_inner_add_smul {n : ℕ} {v : Euc n} (hv : ‖v‖ = 1)
    (x : Euc n) (s : ℝ) : inner ℝ v (x+s•v) = inner ℝ v x+s := by
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv,
    one_pow, mul_one]

theorem ae_fiber_norm_bound {n : ℕ} {f : Euc n → ℝ} (hf : Measurable f)
    {v : Euc n} (hv : ‖v‖ = 1) {a : ℝ}
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ (Icc (-a) a).indicator (fun _ ↦ (1:ℝ)) (inner ℝ v x)) :
    ∀ᵐ x ∂volume, ∀ᵐ s : ℝ ∂volume,
      ‖f (x+s•v)‖ ≤ (Icc (-a-inner ℝ v x) (a-inner ℝ v x)).indicator (fun _ ↦ (1:ℝ)) s := by
  have hall : ∀ᵐ s : ℝ ∂volume, ∀ᵐ x ∂volume,
      ‖f (x+s•v)‖ ≤ (Icc (-a) a).indicator (fun _ ↦ (1:ℝ)) (inner ℝ v (x+s•v)) := by
    exact ae_of_all _ fun s ↦ (measurePreserving_add_right volume (s•v)).quasiMeasurePreserving.ae hbound
  have hm : MeasurableSet {p : ℝ × Euc n |
      ‖f (p.2+p.1•v)‖ ≤ (Icc (-a) a).indicator (fun _ ↦ (1:ℝ)) (inner ℝ v (p.2+p.1•v))} := by
    apply measurableSet_le
    · exact (hf.comp (continuous_snd.add (continuous_fst.smul continuous_const)).measurable).norm
    · exact (measurable_const.indicator measurableSet_Icc).comp
        ((continuous_const.inner (continuous_snd.add (continuous_fst.smul continuous_const))).measurable)
  have hh := (Measure.ae_ae_comm hm).mp hall
  filter_upwards [hh] with x hx
  filter_upwards [hx] with s hs
  have he : inner ℝ v (x+s•v) ∈ Icc (-a) a ↔
      s ∈ Icc (-a-inner ℝ v x) (a-inner ℝ v x) := by
    rw [unit_inner_add_smul hv]
    simp only [mem_Icc]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  simpa only [indicator_apply, he] using hs

theorem norm_fiber_integral_le {n : ℕ} {f : Euc n → ℝ} (hf : Measurable f)
    {v : Euc n} (hv : ‖v‖ = 1) {a : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ (Icc (-a) a).indicator (fun _ ↦ (1:ℝ)) (inner ℝ v x)) :
    ∀ᵐ x ∂volume, ‖∫ s : ℝ, f (x+s•v)‖ ≤ 2*a := by
  filter_upwards [ae_fiber_norm_bound hf hv hbound] with x hx
  let I := Icc (-a-inner ℝ v x) (a-inner ℝ v x)
  have hI : Integrable (I.indicator (fun _ ↦ (1:ℝ))) volume := by
    exact ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
  have hfx : Integrable (fun s : ℝ ↦ f (x+s•v)) volume :=
    hI.mono' (hf.comp (continuous_const.add (continuous_id.smul continuous_const)).measurable).aestronglyMeasurable hx
  calc
    ‖∫ s : ℝ, f (x+s•v)‖ ≤ ∫ s : ℝ, ‖f (x+s•v)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ, I.indicator (fun _ ↦ (1:ℝ)) s := integral_mono_ae hfx.norm hI hx
    _ = 2*a := by
      rw [integral_indicator measurableSet_Icc, integral_const]
      simp only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc]
      rw [show a-inner ℝ v x-(-a-inner ℝ v x) = 2*a by ring, ENNReal.toReal_ofReal (by positivity)]

theorem localizedPhaseError_slab_bound {n : ℕ} (E : Set (Euc n)) (v : Euc n)
    (R a : ℝ)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0)) :
    ∀ᵐ x ∂volume, ‖localizedPhaseError E v R x‖ ≤
      (Icc (-a) a).indicator (fun _ ↦ (1:ℝ)) (inner ℝ v x) := by
  classical
  filter_upwards [hphase] with x hx
  by_cases hc : inner ℝ v x ∈ Icc (-a) a
  · simpa only [indicator_of_mem hc] using localizedPhaseError_norm_le_one E v R x
  · rw [indicator_of_notMem hc]
    have hez : localizedPhaseError E v R x = 0 := by
      by_cases hxball : x ∈ Metric.ball (0 : Euc n) R
      · have hh : a < |inner ℝ v x| := lt_of_not_ge (fun h ↦ hc (abs_le.mp h))
        have he := hx hxball hh
        by_cases hxE : x ∈ E
        · simp [localizedPhaseError,hxball,hxE,he.mp hxE]
        · have hxH : ¬inner ℝ v x < 0 := fun hh ↦ hxE (he.mpr hh)
          simp [localizedPhaseError,hxball,hxE,hxH]
      · simp [localizedPhaseError,hxball]
    simp only [hez,norm_zero,le_refl]

theorem fiberHeight_slab_bound {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} (hv : ‖v‖ = 1) (R : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0)) :
    ∀ᵐ x ∂volume, ‖fiberHeight E v R x‖ ≤ 2*a :=
  norm_fiber_integral_le (localizedPhaseError_measurable hE v R) hv ha
    (localizedPhaseError_slab_bound E v R a hphase)

theorem lintegral_fiber_bound {n : ℕ} {f : Euc n → ℝ} (hf : Measurable f)
    {v : Euc n} (hv : ‖v‖ = 1) {a : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ (Icc (-a) a).indicator (fun _ ↦ (1:ℝ)) (inner ℝ v x)) :
    ∀ᵐ x ∂volume, (∫⁻ s : ℝ, ‖f (x+s•v)‖ₑ) ≤ ENNReal.ofReal (2*a) := by
  filter_upwards [ae_fiber_norm_bound hf hv hbound] with x hx
  calc
    _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal
        ((Icc (-a-inner ℝ v x) (a-inner ℝ v x)).indicator (fun _ ↦ (1:ℝ)) s) := by
      apply lintegral_mono_ae
      filter_upwards [hx] with s hs
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hs
    _ = ENNReal.ofReal (2*a) := by
      have he : (fun s : ℝ ↦ ENNReal.ofReal
          ((Icc (-a-inner ℝ v x) (a-inner ℝ v x)).indicator (fun _ ↦ (1:ℝ)) s)) =
          (Icc (-a-inner ℝ v x) (a-inner ℝ v x)).indicator (fun _ ↦ (1:ℝ≥0∞)) := by
        funext s
        by_cases hs : s ∈ Icc (-a-inner ℝ v x) (a-inner ℝ v x) <;> simp [hs]
      rw [he]
      rw [lintegral_indicator measurableSet_Icc]
      simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
      rw [← uIcc_of_le (show -a-inner ℝ v x ≤ a-inner ℝ v x by linarith [ha]),
        Real.volume_interval, abs_of_nonneg (by linarith [ha])]
      congr 1
      ring

theorem slab_lintegral_bound {n : ℕ} {f : Euc n → ℝ} (hf : Measurable f)
    {v : Euc n} (hv : ‖v‖ = 1) {a : ℝ} (ha : 0 ≤ a) {R : ℝ} (hR : 0 < R)
    (hs : Function.support f ⊆ Metric.ball 0 R)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ (Icc (-a) a).indicator (fun _ ↦ (1:ℝ)) (inner ℝ v x)) :
    ENNReal.ofReal (2*R) * (∫⁻ x, ‖f x‖ₑ) ≤
      ENNReal.ofReal (2*a) * volume (Metric.ball (0:Euc n) (2*R)) := by
  let I := Icc (-R) R
  let B := Metric.ball (0:Euc n) (2*R)
  have hm : Measurable (fun p : Euc n × ℝ ↦ ‖f (p.1+p.2•v)‖ₑ) :=
    (hf.comp (continuous_fst.add (continuous_snd.smul continuous_const)).measurable).enorm
  have hswap : ENNReal.ofReal (2*R) * (∫⁻ x, ‖f x‖ₑ) =
      ∫⁻ x, ∫⁻ s in I, ‖f (x+s•v)‖ₑ := by
    rw [lintegral_lintegral_swap hm.aemeasurable]
    simp_rw [lintegral_add_right_eq_self (fun x : Euc n ↦ ‖f x‖ₑ)]
    simp only [lintegral_const, Measure.restrict_apply_univ, I]
    rw [← uIcc_of_le (show -R ≤ R by linarith [hR]), Real.volume_interval,
      sub_neg_eq_add, ← two_mul, abs_of_pos (mul_pos (by norm_num) hR), mul_comm]
  rw [hswap]
  calc
    _ ≤ ∫⁻ x, B.indicator (fun _ ↦ ENNReal.ofReal (2*a)) x := by
      apply lintegral_mono_ae
      filter_upwards [lintegral_fiber_bound hf hv ha hbound] with x hx
      by_cases hxB : x ∈ B
      · rw [indicator_of_mem hxB]
        exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans hx
      · rw [indicator_of_notMem hxB]
        apply le_of_eq
        apply (lintegral_eq_zero_iff' (hf.comp (continuous_const.add (continuous_id.smul continuous_const)).measurable).enorm.aemeasurable).mpr
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hsI
        have hz : f (x+s•v) = 0 := by
          by_contra hnz
          have hy := hs hnz
          have hsn : ‖s•v‖ ≤ R := by
            rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
            exact abs_le.mpr hsI
          have hxb : ‖x‖ < 2*R := by
            have hxy : x = (x+s•v) - s•v := by abel
            calc
              ‖x‖ = ‖(x+s•v) - s•v‖ := congrArg norm hxy
              _ ≤ ‖x+s•v‖ + ‖s•v‖ := norm_sub_le _ _
              _ < R+R := add_lt_add_of_lt_of_le (by simpa only [Metric.mem_ball, dist_zero_right] using hy) hsn
              _ = 2*R := by ring
          exact hxB (Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hxb))
        change ‖f (x+s•v)‖ₑ = 0
        simp only [hz, enorm_zero]
    _ = _ := by rw [lintegral_indicator measurableSet_ball]; simp [mul_comm]

theorem slab_integral_bound {n : ℕ} {f : Euc n → ℝ} (hf : Measurable f)
    {v : Euc n} (hv : ‖v‖ = 1) {a : ℝ} (ha : 0 ≤ a) {R : ℝ} (hR : 0 < R)
    (hs : Function.support f ⊆ Metric.ball 0 R)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ (Icc (-a) a).indicator (fun _ ↦ (1:ℝ)) (inner ℝ v x)) :
    (2*R) * (∫ x, ‖f x‖) ≤ (2*a) * volume.real (Metric.ball (0:Euc n) (2*R)) := by
  have hfinite : volume (Metric.ball (0:Euc n) (2*R)) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0:Euc n) (2*R)).measure_ne_top
      (measure_mono Metric.ball_subset_closedBall)
  have hi := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite)
    (slab_lintegral_bound hf hv ha hR hs hbound)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*R),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*a), Measure.real,
    ← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable] using hi

def cutoffPhaseError {n : ℕ} (E : Set (Euc n)) (v : Euc n) (η : Euc n → ℝ)
    (x : Euc n) : ℝ := η x * (E.indicator (fun _ ↦ (1:ℝ)) x -
      {z | inner ℝ v z < 0}.indicator (fun _ ↦ (1:ℝ)) x)

theorem cutoffPhaseError_measurable {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (v : Euc n) {η : Euc n → ℝ} (hη : Measurable η) :
    Measurable (cutoffPhaseError E v η) :=
  hη.mul ((measurable_const.indicator hE).sub (measurable_const.indicator
    (isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet))

theorem cutoffPhaseError_support {n : ℕ} (E : Set (Euc n)) (v : Euc n)
    (η : Euc n → ℝ) : Function.support (cutoffPhaseError E v η) ⊆ Function.support η := by
  intro x hx hz
  exact hx (by simp [cutoffPhaseError, hz])

theorem cutoffPhaseError_eq_mul_localized {n : ℕ} (E : Set (Euc n)) (v : Euc n)
    (η : Euc n → ℝ) {R : ℝ} (hs : Function.support η ⊆ Metric.ball 0 R) :
    cutoffPhaseError E v η = fun x ↦ η x * localizedPhaseError E v R x := by
  funext x
  by_cases hx : x ∈ Metric.ball (0:Euc n) R
  · simp [cutoffPhaseError, localizedPhaseError, hx]
  · have hz : η x = 0 := Function.notMem_support.mp (fun hn ↦ hx (hs hn))
    simp [cutoffPhaseError, hz]

theorem cutoffPhaseError_slab_bound {n : ℕ} (E : Set (Euc n)) (v : Euc n)
    (η : Euc n → ℝ) {R a : ℝ} (hs : Function.support η ⊆ Metric.ball 0 R)
    (hη : ∀ x, ‖η x‖ ≤ 1)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0)) :
    ∀ᵐ x ∂volume, ‖cutoffPhaseError E v η x‖ ≤
      (Icc (-a) a).indicator (fun _ ↦ (1:ℝ)) (inner ℝ v x) := by
  rw [cutoffPhaseError_eq_mul_localized E v η hs]
  filter_upwards [localizedPhaseError_slab_bound E v R a hphase] with x hx
  rw [norm_mul]
  exact ((mul_le_mul_of_nonneg_right (hη x) (norm_nonneg _)).trans_eq (one_mul _)).trans hx

end RPISingularHarnack

end

end OAI
