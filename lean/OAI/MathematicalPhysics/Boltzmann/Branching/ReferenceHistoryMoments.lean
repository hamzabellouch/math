import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceBranchingHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceFlightLaws
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

section

/-! # Measurable extension of retained-state observables to the physical velocity space -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

private theorem state_projection_exists :
    ∃ f : V → RetainedState, Measurable f ∧ ∀ v : RetainedState, f v.1 = v :=
  referenceRegion_measurable.exists_measurable_proj ⟨0,by simp [referenceRegion]⟩

def stateProjection : V → RetainedState := Classical.choose state_projection_exists

theorem stateProjection_measurable : Measurable stateProjection :=
  (Classical.choose_spec state_projection_exists).1

theorem stateProjection_apply (v : RetainedState) : stateProjection v.1 = v :=
  (Classical.choose_spec state_projection_exists).2 v

theorem stateProjection_coe {v : V} (hv : v ∈ referenceRegion) :
    (stateProjection v : V) = v := by
  have h := congrArg (Subtype.val : RetainedState → V) (stateProjection_apply ⟨v,hv⟩)
  exact h

theorem branchingKernel_lintegral_physical (v : RetainedState)
    {F : RetainedState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ u, F u ∂branchingKernel v) =
      ENNReal.ofReal (4*Real.pi*‖v.1-beamAxis‖)*
        (∫⁻ n, referenceRegion.indicator (fun w => F (stateProjection w))
          (child v.1 beamAxis n.1) ∂sphereProbability) +
      ENNReal.ofReal (4*Real.pi*‖v.1+beamAxis‖)*
        (∫⁻ n, referenceRegion.indicator (fun w => F (stateProjection w))
          (child v.1 (-beamAxis) n.1) ∂sphereProbability) +
      ENNReal.ofReal (48*Real.pi-stateFrequency v)*F v := by
  let G : V → ℝ≥0∞ := fun w => F (stateProjection w)
  have hG : Measurable G := hF.comp stateProjection_measurable
  have he : (∫⁻ w, G w ∂(branchingKernel v).map (Subtype.val : RetainedState → V)) =
      ∫⁻ u, F u ∂branchingKernel v := by
    rw [lintegral_map hG measurable_subtype_coe]
    apply lintegral_congr
    intro u
    exact congrArg F (stateProjection_apply u)
  rw [← he,branchingKernel_beam_projection,lintegral_add_measure,
    ← lintegral_indicator referenceRegion_measurable,
    lintegral_add_measure,lintegral_smul_measure,lintegral_smul_measure,lintegral_smul_measure,
    lintegral_dirac]
  rw [outgoing_apply,outgoing_apply,
    lintegral_map (hG.indicator referenceRegion_measurable) (by unfold child; fun_prop),
    lintegral_map (hG.indicator referenceRegion_measurable) (by unfold child; fun_prop)]
  simp only [smul_eq_mul,G,stateProjection_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A common positive bound for the nearby physical beam-history weights -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem medium_frequency_bounds {v wp wm : V} {bp bm : ℝ}
    (hv : ‖v‖ ≤ 6) (hwp : ‖wp‖ ≤ 2) (hwm : ‖wm‖ ≤ 2)
    (hbp : 0 ≤ bp) (hbm : 0 ≤ bm) (hbp1 : bp ≤ 5/4) (hbm1 : bm ≤ 5/4) :
    0 ≤ mediumFrequency v wp wm bp bm ∧ mediumFrequency v wp wm bp bm ≤ 40*Real.pi := by
  have hp : ‖v-wp‖ ≤ 8 := (norm_sub_le v wp).trans (by linarith)
  have hm : ‖v-wm‖ ≤ 8 := (norm_sub_le v wm).trans (by linarith)
  have hp' : bp*‖v-wp‖ ≤ 10 := by
    calc
      _ ≤ (5/4:ℝ)*8 := mul_le_mul hbp1 hp (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hm' : bm*‖v-wm‖ ≤ 10 := by
    calc
      _ ≤ (5/4:ℝ)*8 := mul_le_mul hbm1 hm (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  constructor
  · unfold mediumFrequency
    positivity
  · unfold mediumFrequency
    have h := mul_le_mul_of_nonneg_left (add_le_add hp' hm') (by positivity : 0 ≤ 2*Real.pi)
    nlinarith

theorem marked_rate_bounds (m : HistoryMark) {v wp wm : V} {bp bm : ℝ}
    (hv : ‖v‖ ≤ 6) (hwp : ‖wp‖ ≤ 2) (hwm : ‖wm‖ ≤ 2)
    (hbp : 0 ≤ bp) (hbm : 0 ≤ bm) (hbp1 : bp ≤ 5/4) (hbm1 : bm ≤ 5/4) :
    0 ≤ markedRate m v wp wm bp bm ∧ markedRate m v wp wm bp bm ≤ 48*Real.pi := by
  have hf := medium_frequency_bounds hv hwp hwm hbp hbm hbp1 hbm1
  unfold markedRate
  split
  · constructor <;> linarith [Real.pi_pos]
  · split
    · have hn := norm_sub_le v wp
      have hp : bp*‖v-wp‖ ≤ 10 := by
        have h := mul_le_mul hbp1 (show ‖v-wp‖ ≤ 8 by linarith) (norm_nonneg (v-wp)) (by norm_num)
        norm_num at h
        exact h
      constructor
      · positivity
      · have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*Real.pi)
        nlinarith [Real.pi_pos]
    · have hn := norm_sub_le v wm
      have hp : bm*‖v-wm‖ ≤ 10 := by
        have h := mul_le_mul hbm1 (show ‖v-wm‖ ≤ 8 by linarith) (norm_nonneg (v-wm)) (by norm_num)
        norm_num at h
        exact h
      constructor
      · positivity
      · have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*Real.pi)
        nlinarith [Real.pi_pos]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Explicit mark-and-angle formula for one positive reference event -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def markedReferenceWeight (v : RetainedState) (m : HistoryMark) (n : Sphere) : ℝ≥0∞ :=
  ENNReal.ofReal (markedRate m v.1 beamAxis (-beamAxis) 1 1) *
    referenceRegion.indicator 1 (markedChild m v.1 beamAxis (-beamAxis) n.1)

def markedReferenceState (v : RetainedState) (m : HistoryMark) (n : Sphere) : RetainedState :=
  stateProjection (markedChild m v.1 beamAxis (-beamAxis) n.1)

theorem reference_frequency_eq (v : V) :
    mediumFrequency v beamAxis (-beamAxis) 1 1 = frequency v beamAxis := by
  simp only [mediumFrequency,frequency,one_mul,sub_neg_eq_add]

theorem markedReference_integral (v : RetainedState) {F : RetainedState → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ u, F u ∂branchingKernel v) =
      ∑ m : HistoryMark, ∫⁻ n, markedReferenceWeight v m n*F (markedReferenceState v m n)
        ∂sphereProbability := by
  have hmul (w : V) : referenceRegion.indicator 1 w * F (stateProjection w) =
      referenceRegion.indicator (fun u => F (stateProjection u)) w := by
    by_cases hw : w ∈ referenceRegion <;> simp [hw]
  have hzero : (∫⁻ n, markedReferenceWeight v 0 n * F (markedReferenceState v 0 n)
      ∂sphereProbability) = ENNReal.ofReal (48*Real.pi-stateFrequency v)*F v := by
    have he (n : Sphere) : markedReferenceWeight v 0 n * F (markedReferenceState v 0 n) =
        ENNReal.ofReal (48*Real.pi-stateFrequency v)*F v := by
      simp [markedReferenceWeight,markedReferenceState,markedChild,markedRate,
        reference_frequency_eq,stateFrequency,v.2,stateProjection_apply]
    simp_rw [he]
    rw [lintegral_const,measure_univ,mul_one]
  have hone : (∫⁻ n, markedReferenceWeight v 1 n * F (markedReferenceState v 1 n)
      ∂sphereProbability) = ENNReal.ofReal (4*Real.pi*‖v.1-beamAxis‖) *
        ∫⁻ n, referenceRegion.indicator (fun u => F (stateProjection u))
          (child v.1 beamAxis n.1) ∂sphereProbability := by
    simp only [markedReferenceWeight,markedReferenceState,markedChild,markedRate,
      Fin.isValue,one_ne_zero,↓reduceIte,mul_one,mul_assoc,hmul]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have htwo : (∫⁻ n, markedReferenceWeight v 2 n * F (markedReferenceState v 2 n)
      ∂sphereProbability) = ENNReal.ofReal (4*Real.pi*‖v.1+beamAxis‖) *
        ∫⁻ n, referenceRegion.indicator (fun u => F (stateProjection u))
          (child v.1 (-beamAxis) n.1) ∂sphereProbability := by
    simp only [markedReferenceWeight,markedReferenceState,markedChild,markedRate,
      Fin.isValue,show (2 : HistoryMark) ≠ 0 by decide,show (2 : HistoryMark) ≠ 1 by decide,
      ↓reduceIte,mul_one,sub_neg_eq_add,mul_assoc,hmul]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [Fin.sum_univ_three,hzero,hone,htwo,branchingKernel_lintegral_physical v hF]
  ac_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite propagation and integrability for the actual flight histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyKernel_displacement (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    ∀ᵐ z ∂historyKernel n p, ‖z.1-p.2.1‖ ≤ 5*p.1 := by
  induction n generalizing p with
  | zero =>
    rw [historyKernel_zero,Kernel.deterministic_apply,ae_dirac_iff (by measurability)]
    simpa only [finishFlight,abs_of_nonneg hT] using freeFlight_displacement p.1 p.2
  | succ n ih =>
    let A : Set FlightState := {z | ¬ ‖z.1-p.2.1‖ ≤ 5*p.1}
    have hA : MeasurableSet A := by dsimp [A]; measurability
    change historyKernel (n+1) p A = 0
    rw [← lintegral_indicator_one hA,
      historyKernel_succ_lintegral n p (f := A.indicator 1) (measurable_const.indicator hA)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro u
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ih (advanceState p s u) (sub_nonneg.mpr hs.2)] with z hz
    have hb : ‖z.1-p.2.1‖ ≤ 5*p.1 := by
      calc
        ‖z.1-p.2.1‖ ≤ ‖z.1-(advanceState p s u).2.1‖ +
            ‖(advanceState p s u).2.1-p.2.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 5*(p.1-s)+5*s := by
          exact add_le_add hz (by simpa only [advanceState,abs_of_pos hs.1] using
            freeFlight_displacement s p.2)
        _ = _ := by ring
    exact indicator_of_notMem (show z ∉ A from not_not.mpr hb) 1

theorem historyKernel_isFinite (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    IsFiniteMeasure (historyKernel n p) := by
  constructor
  rw [historyKernel_mass n p hT]
  exact (simplexTime_ne_top n p.1).lt_top

theorem history_displacement_integrable (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    Integrable (fun z : FlightState => z.1-p.2.1) (historyKernel n p) := by
  let _ := historyKernel_isFinite n p hT
  exact (integrable_const (5*p.1)).mono' (by fun_prop) (historyKernel_displacement n p hT)

theorem history_displacement_sq_integrable (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    Integrable (fun z : FlightState => ‖z.1-p.2.1‖^2) (historyKernel n p) := by
  let _ := historyKernel_isFinite n p hT
  apply (integrable_const ((5*p.1)^2)).mono' (by fun_prop)
  filter_upwards [historyKernel_displacement n p hT] with z hz
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖z.1-p.2.1‖)] using
    pow_le_pow_left₀ (norm_nonneg _) hz 2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform finite-product control for perturbed positive collision histories -/

noncomputable section

open scoped BigOperators

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem product_error_on_range {a b : ℕ → ℝ} {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (n : ℕ) (ha : ∀ j < n, |a j| ≤ M) (hb : ∀ j < n, |b j| ≤ M)
    (hab : ∀ j < n, |a j-b j| ≤ δ) :
    |(∏ j ∈ Finset.range n, a j)-(∏ j ∈ Finset.range n, b j)| ≤ (n:ℝ)*M^n*δ := by
  let a' : ℕ → ℝ := fun j => if j < n then a j else 0
  let b' : ℕ → ℝ := fun j => if j < n then b j else 0
  have he := product_error_bound (a := a') (b := b') hM hδ
    (fun j => by dsimp [a']; split <;> simp_all; linarith)
    (fun j => by dsimp [b']; split <;> simp_all; linarith)
    (fun j => by dsimp [a',b']; by_cases h : j < n <;> simp [h,hab j,hδ]) n
  have hp (f : ℕ → ℝ) : (∏ j ∈ Finset.range n, if j < n then f j else 0) =
      ∏ j ∈ Finset.range n, f j := by
    apply Finset.prod_congr rfl
    intro j hj
    exact ite_eq_left (Finset.mem_range.mp hj)
  simpa only [a',b',hp] using he

theorem marked_product_error {n : ℕ} {mark : ℕ → HistoryMark}
    {v u wp wm : ℕ → V} {bp bm : ℕ → ℝ} {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hvp : ∀ j < n, ‖v j-u j‖+‖wp j-beamAxis‖ ≤ δ)
    (hvm : ∀ j < n, ‖v j-u j‖+‖wm j-(-beamAxis)‖ ≤ δ)
    (hv : ∀ j < n, ‖v j‖ ≤ 6) (hu : ∀ j < n, ‖u j‖ ≤ 5)
    (hwp : ∀ j < n, ‖wp j‖ ≤ 2) (hwm : ∀ j < n, ‖wm j‖ ≤ 2)
    (hbp : ∀ j < n, 0 ≤ bp j ∧ bp j ≤ 5/4)
    (hbm : ∀ j < n, 0 ≤ bm j ∧ bm j ≤ 5/4)
    (hep : ∀ j < n, |bp j-1| ≤ ε) (hem : ∀ j < n, |bm j-1| ≤ ε) :
    |(∏ j ∈ Finset.range n, markedRate (mark j) (v j) (wp j) (wm j) (bp j) (bm j))-
      (∏ j ∈ Finset.range n, markedRate (mark j) (u j) beamAxis (-beamAxis) 1 1)| ≤
      (n:ℝ)*(48*Real.pi)^n*(4*Real.pi*(2*δ+6*ε)) := by
  apply product_error_on_range (by have := Real.pi_gt_three; linarith) (by positivity)
  · intro j hj
    have h := marked_rate_bounds (mark j) (hv j hj) (hwp j hj) (hwm j hj)
      (hbp j hj).1 (hbm j hj).1 (hbp j hj).2 (hbm j hj).2
    simpa only [abs_of_nonneg h.1] using h.2
  · intro j hj
    have h := marked_rate_bounds (mark j) (v := u j) (wp := beamAxis) (wm := -beamAxis)
      (bp := 1) (bm := 1) (by linarith [hu j hj])
      (by rw [axis_norms.2.2]; norm_num) (by rw [norm_neg,axis_norms.2.2]; norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [abs_of_nonneg h.1] using h.2
  · intro j hj
    have hR_plus : ‖u j-beamAxis‖ ≤ 6 :=
      (norm_sub_le _ _).trans (by rw [axis_norms.2.2]; linarith [hu j hj])
    have hR_minus : ‖u j-(-beamAxis)‖ ≤ 6 :=
      (norm_sub_le _ _).trans (by rw [norm_neg,axis_norms.2.2]; linarith [hu j hj])
    have h := marked_rate_error (mark j) (hbp j hj).1 (hbm j hj).1
      (by linarith [(hbp j hj).2]) (by linarith [(hbm j hj).2])
      (hep j hj) (hem j hj) (hvp j hj) (hvm j hj) hR_plus hR_minus
    convert h using 1
    ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Pointwise coupling of good reference histories with a nearby measurable medium -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def referenceVelocity (v₀ : V) (mark : ℕ → HistoryMark) (direction : ℕ → V) : ℕ → V :=
  markedVelocity v₀ mark (fun _ => beamAxis) (fun _ => -beamAxis) direction

theorem coupled_velocity_error (v₀ : V) (mark : ℕ → HistoryMark)
    (wp wm direction : ℕ → V) {ε : ℝ}
    (hn : ∀ j, ‖direction j‖ = 1)
    (hp : ∀ j, ‖wp j-beamAxis‖ ≤ ε) (hm : ∀ j, ‖wm j-(-beamAxis)‖ ≤ ε) (j : ℕ) :
    ‖markedVelocity v₀ mark wp wm direction j-referenceVelocity v₀ mark direction j‖ ≤ (j:ℝ)*ε :=
  marked_velocity_error v₀ mark wp wm (fun _ => beamAxis) (fun _ => -beamAxis) direction hn hp hm j

theorem coupled_velocity_bound (v₀ : V) (mark : ℕ → HistoryMark)
    (wp wm direction : ℕ → V) {ε : ℝ} {n j : ℕ}
    (hε : 0 ≤ ε) (hsmall : (n:ℝ)*ε ≤ 1) (hj : j ≤ n)
    (hn : ∀ i, ‖direction i‖ = 1)
    (hp : ∀ i, ‖wp i-beamAxis‖ ≤ ε) (hm : ∀ i, ‖wm i-(-beamAxis)‖ ≤ ε)
    (hgood : ‖referenceVelocity v₀ mark direction j‖ ≤ 5) :
    ‖markedVelocity v₀ mark wp wm direction j‖ ≤ 6 := by
  have he := coupled_velocity_error v₀ mark wp wm direction hn hp hm j
  have hi : (j:ℝ)*ε ≤ (n:ℝ)*ε := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hε
  have hh := norm_add_le
    (markedVelocity v₀ mark wp wm direction j-referenceVelocity v₀ mark direction j)
    (referenceVelocity v₀ mark direction j)
  rw [sub_add_cancel] at hh
  linarith

theorem coupled_marked_product_error (v₀ : V) (mark : ℕ → HistoryMark)
    (wp wm direction : ℕ → V) (bp bm : ℕ → ℝ) {ε : ℝ} {n : ℕ}
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/4) (hsmall : (n:ℝ)*ε ≤ 1)
    (hn : ∀ j, ‖direction j‖ = 1)
    (hp : ∀ j, ‖wp j-beamAxis‖ ≤ ε) (hm : ∀ j, ‖wm j-(-beamAxis)‖ ≤ ε)
    (hgood : ∀ j < n, ‖referenceVelocity v₀ mark direction j‖ ≤ 5)
    (hbp : ∀ j < n, |bp j-1| ≤ ε) (hbm : ∀ j < n, |bm j-1| ≤ ε) :
    |(∏ j ∈ Finset.range n, markedRate (mark j)
        (markedVelocity v₀ mark wp wm direction j) (wp j) (wm j) (bp j) (bm j))-
      (∏ j ∈ Finset.range n, markedRate (mark j)
        (referenceVelocity v₀ mark direction j) beamAxis (-beamAxis) 1 1)| ≤
      (n:ℝ)*(48*Real.pi)^n*(4*Real.pi*((2*(n:ℝ)+8)*ε)) := by
  have he (j : ℕ) (hj : j < n) :
      ‖markedVelocity v₀ mark wp wm direction j-referenceVelocity v₀ mark direction j‖ ≤ (n:ℝ)*ε :=
    (coupled_velocity_error v₀ mark wp wm direction hn hp hm j).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) hε)
  have hpv (j : ℕ) : ‖wp j‖ ≤ 2 := by
    have hh := norm_add_le (wp j-beamAxis) beamAxis
    rw [sub_add_cancel,axis_norms.2.2] at hh
    linarith [hp j]
  have hmv (j : ℕ) : ‖wm j‖ ≤ 2 := by
    have hh := norm_add_le (wm j-(-beamAxis)) (-beamAxis)
    rw [sub_add_cancel,norm_neg,axis_norms.2.2] at hh
    linarith [hm j]
  have hdens {b : ℝ} (hb : |b-1| ≤ ε) : 0 ≤ b ∧ b ≤ 5/4 := by
    have hb' := abs_le.mp hb
    constructor <;> linarith
  have H := marked_product_error (mark := mark) (ε := ε) (δ := ((n:ℝ)+1)*ε) hε (by positivity)
    (fun j hj => by have := add_le_add (he j hj) (hp j); nlinarith)
    (fun j hj => by have := add_le_add (he j hj) (hm j); nlinarith)
    (fun j hj => coupled_velocity_bound v₀ mark wp wm direction hε hsmall hj.le hn hp hm (hgood j hj))
    hgood (fun j _ => hpv j) (fun j _ => hmv j)
    (fun j hj => hdens (hbp j hj)) (fun j hj => hdens (hbm j hj)) hbp hbm
  convert H using 1
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Mark-and-angle expansion of every finite positive reference history -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem markedChild_measurable (m : HistoryMark) :
    Measurable (fun p : RetainedState × Sphere =>
      markedChild m p.1.1 beamAxis (-beamAxis) p.2.1) := by
  unfold markedChild
  split
  · fun_prop
  · split <;> unfold child <;> fun_prop

theorem markedRate_measurable (m : HistoryMark) :
    Measurable (fun v : RetainedState => markedRate m v.1 beamAxis (-beamAxis) 1 1) := by
  unfold markedRate
  split
  · unfold mediumFrequency
    fun_prop
  · split <;> fun_prop

theorem markedReferenceWeight_measurable (m : HistoryMark) :
    Measurable (fun p : RetainedState × Sphere => markedReferenceWeight p.1 m p.2) := by
  unfold markedReferenceWeight
  exact ((markedRate_measurable m).comp measurable_fst).ennreal_ofReal.mul
    ((measurable_const.indicator referenceRegion_measurable).comp (markedChild_measurable m))

theorem markedReferenceState_measurable (m : HistoryMark) :
    Measurable (fun p : RetainedState × Sphere => markedReferenceState p.1 m p.2) :=
  stateProjection_measurable.comp (markedChild_measurable m)

theorem eventHistory_marked_succ {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D)
    (n : ℕ) (p : TimeFlightState) :
    eventHistory referenceClock branchingKernel D (n+1) p =
      ∫⁻ s in Ioc 0 p.1, clockSurvival referenceClock s *
        ∑ m : HistoryMark, ∫⁻ θ, markedReferenceWeight p.2.2 m θ *
          eventHistory referenceClock branchingKernel D n
            (advanceState p s (markedReferenceState p.2.2 m θ)) ∂sphereProbability := by
  have he : (eventStep referenceClock branchingKernel)^(n+1) =
      ((eventStep referenceClock branchingKernel)^n) ∘ₖ eventStep referenceClock branchingKernel := by
    simpa only [pow_one] using Kernel.pow_add (eventStep referenceClock branchingKernel) n 1
  rw [eventHistory,he,Kernel.lintegral_comp _ _ _ hD]
  change (∫⁻ q, eventHistory referenceClock branchingKernel D n q
    ∂eventStep referenceClock branchingKernel p) = _
  rw [eventStep_lintegral _ _ _ (eventHistory_measurable _ _ hD n)]
  apply lintegral_congr
  intro s
  have hm : Measurable (fun u : RetainedState =>
      eventHistory referenceClock branchingKernel D n (advanceState p s u)) :=
    (eventHistory_measurable _ _ hD n).comp (by unfold advanceState; fun_prop)
  rw [markedReference_integral p.2.2 hm]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite time-and-angle parameter measures for the selected positive histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev EventParameter := ℝ × Sphere

def eventParameterMeasure (T : ℝ) : Measure EventParameter :=
  (volume.restrict (Ioc 0 T)).prod sphereProbability

instance eventParameterMeasure_isFinite (T : ℝ) : IsFiniteMeasure (eventParameterMeasure T) := by
  unfold eventParameterMeasure
  infer_instance

theorem eventParameterMeasure_mass (T : ℝ) :
    eventParameterMeasure T univ = ENNReal.ofReal T := by
  rw [eventParameterMeasure,Measure.prod_apply MeasurableSet.univ]
  simp only [Set.preimage_univ,measure_univ,lintegral_const,one_mul,
    Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero]

def referenceParameterState (p : TimeFlightState) (m : HistoryMark) (a : EventParameter) :
    TimeFlightState := advanceState p a.1 (markedReferenceState p.2.2 m a.2)

def referenceParameterDensity (p : TimeFlightState) (m : HistoryMark) (a : EventParameter) : ℝ≥0∞ :=
  waitingDensity p a.1 * clockSurvival referenceClock a.1 * markedReferenceWeight p.2.2 m a.2

theorem referenceParameterState_measurable (m : HistoryMark) :
    Measurable (fun q : TimeFlightState × EventParameter => referenceParameterState q.1 m q.2) := by
  unfold referenceParameterState advanceState
  have hi : Measurable (fun q : TimeFlightState × EventParameter => (q.1.2.2,q.2.2)) := by
    fun_prop
  have hu : Measurable (fun q : TimeFlightState × EventParameter =>
      markedReferenceState q.1.2.2 m q.2.2) := by
    simpa only [Function.comp_def] using (markedReferenceState_measurable m).comp hi
  have ht : Measurable (fun q : TimeFlightState × EventParameter => q.1.1-q.2.1) := by
    fun_prop
  have hx : Measurable (fun q : TimeFlightState × EventParameter => (freeFlight q.2.1 q.1.2).1) := by
    unfold freeFlight
    fun_prop
  exact ht.prodMk (hx.prodMk hu)

theorem referenceParameterDensity_measurable (m : HistoryMark) :
    Measurable (fun q : TimeFlightState × EventParameter => referenceParameterDensity q.1 m q.2) := by
  unfold referenceParameterDensity
  have ht : Measurable (fun q : TimeFlightState × EventParameter => (q.1,q.2.1)) := by
    fun_prop
  have hi : Measurable (fun q : TimeFlightState × EventParameter => (q.1.2.2,q.2.2)) := by
    fun_prop
  have hw : Measurable (fun q : TimeFlightState × EventParameter => waitingDensity q.1 q.2.1) := by
    simpa only [Function.comp_def,Function.uncurry_def] using waitingDensity_measurable.comp ht
  have hc : Measurable (fun q : TimeFlightState × EventParameter => clockSurvival referenceClock q.2.1) := by
    unfold clockSurvival
    fun_prop
  have hm : Measurable (fun q : TimeFlightState × EventParameter => markedReferenceWeight q.1.2.2 m q.2.2) := by
    simpa only [Function.comp_def] using (markedReferenceWeight_measurable m).comp hi
  exact (hw.mul hc).mul hm

theorem reference_parameter_integral {F : TimeFlightState → ℝ≥0∞} (hF : Measurable F)
    (p : TimeFlightState) (m : HistoryMark) {T : ℝ} (hT : p.1 ≤ T) :
    (∫⁻ a, referenceParameterDensity p m a*F (referenceParameterState p m a) ∂eventParameterMeasure T) =
      ∫⁻ s in Ioc 0 p.1, clockSurvival referenceClock s *
        ∫⁻ θ, markedReferenceWeight p.2.2 m θ *
          F (advanceState p s (markedReferenceState p.2.2 m θ)) ∂sphereProbability := by
  have hm : Measurable (fun a : EventParameter => referenceParameterDensity p m a*
      F (referenceParameterState p m a)) :=
    ((referenceParameterDensity_measurable m).comp (measurable_const.prodMk measurable_id)).mul
      (hF.comp ((referenceParameterState_measurable m).comp (measurable_const.prodMk measurable_id)))
  rw [eventParameterMeasure,lintegral_prod _ hm.aemeasurable]
  have he (s : ℝ) : (∫⁻ θ, referenceParameterDensity p m (s,θ)*
      F (referenceParameterState p m (s,θ)) ∂sphereProbability) =
      (Ioc 0 p.1).indicator (fun r => clockSurvival referenceClock r*
        ∫⁻ θ, markedReferenceWeight p.2.2 m θ*
          F (advanceState p r (markedReferenceState p.2.2 m θ)) ∂sphereProbability) s := by
    by_cases hs : s ∈ Ioc 0 p.1
    · simp only [referenceParameterDensity,referenceParameterState,waitingDensity,
        indicator_of_mem hs,Pi.one_apply,one_mul,mul_assoc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    · simp only [referenceParameterDensity,waitingDensity,indicator_of_notMem hs,zero_mul,lintegral_zero]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioc,Measure.restrict_restrict_of_subset]
  exact Ioc_subset_Ioc_right hT

theorem eventHistory_parameter_succ {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D)
    (n : ℕ) (p : TimeFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    eventHistory referenceClock branchingKernel D (n+1) p =
      ∑ m : HistoryMark, ∫⁻ a, referenceParameterDensity p m a *
        eventHistory referenceClock branchingKernel D n (referenceParameterState p m a)
          ∂eventParameterMeasure T := by
  rw [eventHistory_marked_succ hD]
  have h (m : HistoryMark) := reference_parameter_integral
    (eventHistory_measurable referenceClock branchingKernel hD n) p m hT
  simp_rw [h]
  simp_rw [Finset.mul_sum]
  apply lintegral_finsetSum
  intro m _
  have hm : Measurable (fun a : EventParameter => markedReferenceWeight p.2.2 m a.2 *
      eventHistory referenceClock branchingKernel D n
        (advanceState p a.1 (markedReferenceState p.2.2 m a.2))) := by
    exact ((markedReferenceWeight_measurable m).comp (measurable_const.prodMk measurable_snd)).mul
      ((eventHistory_measurable referenceClock branchingKernel hD n).comp
        ((referenceParameterState_measurable m).comp (measurable_const.prodMk measurable_id)))
  exact (show Measurable (clockSurvival referenceClock) by unfold clockSurvival; fun_prop).mul
    hm.lintegral_prod_right'

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A fixed finite parameter measure including the three event marks -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev MarkedEventParameter := HistoryMark × EventParameter

def markedEventMeasure (T : ℝ) : Measure MarkedEventParameter :=
  Measure.count.prod (eventParameterMeasure T)

instance markedEventMeasure_isFinite (T : ℝ) : IsFiniteMeasure (markedEventMeasure T) := by
  unfold markedEventMeasure
  infer_instance

def markedParameterState (p : TimeFlightState) (a : MarkedEventParameter) : TimeFlightState :=
  referenceParameterState p a.1 a.2

def markedParameterDensity (p : TimeFlightState) (a : MarkedEventParameter) : ℝ≥0∞ :=
  referenceParameterDensity p a.1 a.2

theorem markedParameterState_measurable :
    Measurable (fun q : TimeFlightState × MarkedEventParameter => markedParameterState q.1 q.2) := by
  have hm : Measurable (fun q : HistoryMark × (TimeFlightState × EventParameter) =>
      referenceParameterState q.2.1 q.1 q.2.2) :=
    measurable_from_prod_countable_right (fun m => referenceParameterState_measurable m)
  exact hm.comp (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))

theorem markedParameterDensity_measurable :
    Measurable (fun q : TimeFlightState × MarkedEventParameter => markedParameterDensity q.1 q.2) := by
  have hm : Measurable (fun q : HistoryMark × (TimeFlightState × EventParameter) =>
      referenceParameterDensity q.2.1 q.1 q.2.2) :=
    measurable_from_prod_countable_right (fun m => referenceParameterDensity_measurable m)
  exact hm.comp (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))

theorem markedParameterDensity_ne_top (p : TimeFlightState) (a : MarkedEventParameter) :
    markedParameterDensity p a ≠ ⊤ := by
  unfold markedParameterDensity referenceParameterDensity markedReferenceWeight waitingDensity
  by_cases hs : a.2.1 ∈ Ioc 0 p.1
  · rw [indicator_of_mem hs,Pi.one_apply,one_mul]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    by_cases hv : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∈ referenceRegion <;>
      simp [hv]
  · simp [hs]

theorem eventHistory_marked_parameter_succ {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D)
    (n : ℕ) (p : TimeFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    eventHistory referenceClock branchingKernel D (n+1) p =
      ∫⁻ a, markedParameterDensity p a *
        eventHistory referenceClock branchingKernel D n (markedParameterState p a)
          ∂markedEventMeasure T := by
  have hm : Measurable (fun a : MarkedEventParameter => markedParameterDensity p a*
      eventHistory referenceClock branchingKernel D n (markedParameterState p a)) :=
    ((markedParameterDensity_measurable.comp (measurable_const.prodMk measurable_id)).mul
      ((eventHistory_measurable referenceClock branchingKernel hD n).comp
        (markedParameterState_measurable.comp (measurable_const.prodMk measurable_id))))
  rw [markedEventMeasure,lintegral_prod _ hm.aemeasurable,lintegral_fintype]
  simp only [Measure.count_singleton,mul_one]
  exact eventHistory_parameter_succ hD n p hT

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Fixed finite products of time, mark and angle parameters -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev ParameterWord : ℕ → Type
  | 0 => PUnit
  | n+1 => MarkedEventParameter × ParameterWord n

abbrev parameterWordMeasurable : (n : ℕ) → MeasurableSpace (ParameterWord n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => by
    letI := parameterWordMeasurable n
    exact inferInstanceAs (MeasurableSpace (MarkedEventParameter × ParameterWord n))

attribute [instance] parameterWordMeasurable

def parameterWordMeasure (T : ℝ) : (n : ℕ) → Measure (ParameterWord n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => (markedEventMeasure T).prod (parameterWordMeasure T n)

instance parameterWordMeasure_isFinite (T : ℝ) (n : ℕ) : IsFiniteMeasure (parameterWordMeasure T n) := by
  induction n with
  | zero => change IsFiniteMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
    let _ := ih
    change IsFiniteMeasure ((markedEventMeasure T).prod (parameterWordMeasure T n))
    infer_instance

def parameterWordState : (n : ℕ) → TimeFlightState → ParameterWord n → TimeFlightState
  | 0,p,_ => p
  | n+1,p,a => parameterWordState n (markedParameterState p a.1) a.2

def parameterWordDensity : (n : ℕ) → TimeFlightState → ParameterWord n → ℝ≥0∞
  | 0,_,_ => 1
  | n+1,p,a => markedParameterDensity p a.1 *
      parameterWordDensity n (markedParameterState p a.1) a.2

theorem parameterWordState_measurable (n : ℕ) :
    Measurable (fun q : TimeFlightState × ParameterWord n => parameterWordState n q.1 q.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hh : Measurable (fun q : TimeFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by fun_prop
    have ht : Measurable (fun q : TimeFlightState × ParameterWord (n+1) => q.2.2) := by fun_prop
    have hs : Measurable (fun q : TimeFlightState × ParameterWord (n+1) =>
        (markedParameterState q.1 q.2.1,q.2.2)) :=
      (markedParameterState_measurable.comp hh).prodMk ht
    exact ih.comp hs

theorem parameterWordDensity_measurable (n : ℕ) :
    Measurable (fun q : TimeFlightState × ParameterWord n => parameterWordDensity n q.1 q.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hh : Measurable (fun q : TimeFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by fun_prop
    have ht : Measurable (fun q : TimeFlightState × ParameterWord (n+1) => q.2.2) := by fun_prop
    have hs : Measurable (fun q : TimeFlightState × ParameterWord (n+1) =>
        (markedParameterState q.1 q.2.1,q.2.2)) :=
      (markedParameterState_measurable.comp hh).prodMk ht
    exact (markedParameterDensity_measurable.comp hh).mul (ih.comp hs)

theorem parameterWordDensity_ne_top (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) :
    parameterWordDensity n p a ≠ ⊤ := by
  induction n generalizing p with
  | zero => exact ENNReal.one_ne_top
  | succ n ih => exact ENNReal.mul_ne_top (markedParameterDensity_ne_top p a.1) (ih _ a.2)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact finite-history integrals over a fixed product parameter space -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem markedParameterDensity_zero (p : TimeFlightState) (a : MarkedEventParameter)
    (ha : a.2.1 ∉ Ioc 0 p.1) : markedParameterDensity p a = 0 := by
  simp [markedParameterDensity,referenceParameterDensity,waitingDensity,ha]

theorem markedParameterState_time (p : TimeFlightState) (a : MarkedEventParameter)
    (ha : a.2.1 ∈ Ioc 0 p.1) : (markedParameterState p a).1 ∈ Icc 0 p.1 :=
  ⟨sub_nonneg.mpr ha.2,sub_le_self _ ha.1.le⟩

theorem eventHistory_zero (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] (D : TimeFlightState → ℝ≥0∞) (p : TimeFlightState) :
    eventHistory rate K D 0 p = D p := by
  have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
  rw [eventHistory,pow_zero,hi,Kernel.id_apply,lintegral_dirac]

theorem parameterWord_integral {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D)
    (T : ℝ) (n : ℕ) (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) :
    (∫⁻ a, parameterWordDensity n p a * D (parameterWordState n p a)
      ∂parameterWordMeasure T n) = eventHistory referenceClock branchingKernel D n p := by
  induction n generalizing p with
  | zero =>
    rw [eventHistory_zero]
    change (∫⁻ _a : PUnit, 1*D p ∂Measure.dirac PUnit.unit) = D p
    rw [lintegral_const,Measure.dirac_apply_of_mem (mem_univ _),mul_one,one_mul]
  | succ n ih =>
    have hmap : Measurable (fun a : ParameterWord (n+1) => (p,a)) :=
      measurable_const.prodMk measurable_id
    have hd : Measurable (fun a : ParameterWord (n+1) => parameterWordDensity (n+1) p a) := by
      simpa only [Function.comp_def] using (parameterWordDensity_measurable (n+1)).comp hmap
    have hs : Measurable (fun a : ParameterWord (n+1) => parameterWordState (n+1) p a) := by
      simpa only [Function.comp_def] using (parameterWordState_measurable (n+1)).comp hmap
    have hm : Measurable (fun a : ParameterWord (n+1) =>
        parameterWordDensity (n+1) p a * D (parameterWordState (n+1) p a)) := hd.mul (hD.comp hs)
    rw [parameterWordMeasure,lintegral_prod _ hm.aemeasurable,
      eventHistory_marked_parameter_succ hD n p hp.2]
    apply lintegral_congr
    intro a
    change (∫⁻ w, (markedParameterDensity p a *
      parameterWordDensity n (markedParameterState p a) w) *
        D (parameterWordState n (markedParameterState p a) w) ∂parameterWordMeasure T n) = _
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (markedParameterDensity_ne_top p a)]
    by_cases ha : a.2.1 ∈ Ioc 0 p.1
    · have ht := markedParameterState_time p a ha
      rw [ih (markedParameterState p a) ⟨ht.1,ht.2.trans hp.2⟩]
    · rw [markedParameterDensity_zero p a ha,zero_mul,zero_mul]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Bochner integration over the first collision in an actual history -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyKernel_succ (n : ℕ) :
    historyKernel (n+1) = historyKernel n ∘ₖ historyStep := by
  unfold historyKernel
  rw [show historyStep^(n+1) = (historyStep^n) ∘ₖ historyStep by
    simpa only [pow_one] using Kernel.pow_add historyStep n 1]
  exact Kernel.map_comp _ _ _

theorem jumpAfterWait_apply (p : TimeFlightState) (s : ℝ) :
    jumpAfterWait (p,s) = (uniformizedKernel p.2.2).map (advanceState p s) := by
  ext A hA
  rw [jumpAfterWait,Kernel.map_apply' _ advanceState_measurable _ hA,
    Kernel.id_prod_apply' _ _ (advanceState_measurable hA),Kernel.comap_apply,
    Measure.map_apply (by unfold advanceState; fun_prop) hA]
  rfl

private theorem id_prod_integral {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : Kernel α β) [IsSFiniteKernel κ]
    (a : α) {f : α × β → E} (hf : StronglyMeasurable f) :
    (∫ q, f q ∂(Kernel.id ×ₖ κ) a) = ∫ b, f (a,b) ∂κ a := by
  rw [Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod]
  exact integral_map_of_stronglyMeasurable (by fun_prop) hf

theorem historyStep_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : TimeFlightState) {f : TimeFlightState → E} (hf : StronglyMeasurable f)
    (hi : Integrable f (historyStep p)) :
    (∫ q, f q ∂historyStep p) =
      ∫ s in Ioc 0 p.1, ∫ u, f (advanceState p s u) ∂uniformizedKernel p.2.2 := by
  rw [historyStep] at hi ⊢
  rw [Kernel.integral_comp hi,id_prod_integral _ _ hf.integral_kernel,waitingTime_apply]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [jumpAfterWait_apply]
  exact integral_map_of_stronglyMeasurable (by unfold advanceState; fun_prop) hf

theorem historyKernel_succ_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (p : TimeFlightState) {f : FlightState → E} (hf : StronglyMeasurable f)
    (hi : Integrable f (historyKernel (n+1) p)) :
    (∫ z, f z ∂historyKernel (n+1) p) =
      ∫ s in Ioc 0 p.1, ∫ u, ∫ z, f z ∂historyKernel n (advanceState p s u)
        ∂uniformizedKernel p.2.2 := by
  rw [historyKernel_succ] at hi ⊢
  rw [Kernel.integral_comp hi]
  exact historyStep_integral p hf.integral_kernel hi.integral_comp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The exact mean displacement of each finite collision history -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def historyMean (n : ℕ) (p : TimeFlightState) : V :=
  ∫ z, z.1-p.2.1 ∂historyKernel n p

theorem historyMean_shift (n : ℕ) (p q : TimeFlightState) (hT : 0 ≤ q.1) :
    (∫ z, z.1-p.2.1 ∂historyKernel n q) =
      historyMean n q + simplexVolume n q.1 • (q.2.1-p.2.1) := by
  let _ := historyKernel_isFinite n q hT
  have heq (z : FlightState) : z.1-p.2.1 = (z.1-q.2.1)+(q.2.1-p.2.1) := by abel
  rw [show (fun z : FlightState => z.1-p.2.1) =
    (fun z => (z.1-q.2.1)+(q.2.1-p.2.1)) from funext heq]
  rw [integral_add (history_displacement_integrable n q hT) (integrable_const _),integral_const]
  change historyMean n q + (historyKernel n q univ).toReal • _ = _
  rw [historyKernel_mass n q hT,simplexTime_toReal n hT]

theorem historyMean_formula (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    historyMean n p = simplexVolume (n+1) p.1 • velocitySum n p.2.2 := by
  induction n generalizing p with
  | zero =>
    simp [historyMean,historyKernel_zero,Kernel.deterministic_apply,finishFlight,freeFlight,
      simplexVolume,velocitySum,chainAverage_zero]
  | succ n ih =>
    have hi := history_displacement_integrable (n+1) p hT
    rw [historyMean,historyKernel_succ_integral n p (by fun_prop) hi]
    have heq (s : ℝ) (hs : s ∈ Ioc 0 p.1) (u : RetainedState) :
        (∫ z, z.1-p.2.1 ∂historyKernel n (advanceState p s u)) =
          simplexVolume (n+1) (p.1-s) • velocitySum n u +
          (s*simplexVolume n (p.1-s)) • (p.2.2 : V) := by
      rw [historyMean_shift n p _ (sub_nonneg.mpr hs.2),ih _ (sub_nonneg.mpr hs.2)]
      simp only [advanceState,freeFlight,add_sub_cancel_left,smul_smul]
      rw [mul_comm]
    have hinner (s : ℝ) (hs : s ∈ Ioc 0 p.1) :
        (∫ u, ∫ z, z.1-p.2.1 ∂historyKernel n (advanceState p s u) ∂uniformizedKernel p.2.2) =
          simplexVolume (n+1) (p.1-s) • (∫ u, velocitySum n u ∂uniformizedKernel p.2.2) +
          (s*simplexVolume n (p.1-s)) • (p.2.2 : V) := by
      simp_rw [heq s hs]
      have hj : Integrable (fun u => simplexVolume (n+1) (p.1-s) • velocitySum n u)
          (uniformizedKernel p.2.2) := by
        have hf : Measurable (fun u : RetainedState =>
            simplexVolume (n+1) (p.1-s) • velocitySum n u) :=
          (measurable_const (a := simplexVolume (n+1) (p.1-s))).smul (velocitySum_measurable n)
        apply (integrable_const (‖simplexVolume (n+1) (p.1-s)‖*((n+1 : ℕ)*5 : ℝ))).mono'
          hf.aestronglyMeasurable
        apply ae_of_all
        intro u
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (velocitySum_bound n u) (norm_nonneg _)
      rw [integral_add hj (integrable_const _),integral_smul,integral_const,
        probReal_univ,one_smul]
    rw [setIntegral_congr_fun measurableSet_Ioc hinner,← intervalIntegral.integral_of_le hT]
    rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_smul_const,intervalIntegral.integral_smul_const,
        integral_simplexVolume,integral_time_simplexVolume,← smul_add]
      congr 1
      rw [add_comm,velocitySum_succ]
    · exact (show Continuous (fun s : ℝ => simplexVolume (n+1) (p.1-s) •
        (∫ u, velocitySum n u ∂uniformizedKernel p.2.2)) by
          unfold simplexVolume; fun_prop).intervalIntegrable _ _
    · exact (show Continuous (fun s : ℝ => (s*simplexVolume n (p.1-s)) • (p.2.2 : V)) by
          unfold simplexVolume; fun_prop).intervalIntegrable _ _

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Translation of the exact second displacement moment -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def historySecondMoment (n : ℕ) (p : TimeFlightState) : ℝ :=
  ∫ z, ‖z.1-p.2.1‖^2 ∂historyKernel n p

theorem historySecondMoment_shift (n : ℕ) (p q : TimeFlightState) (hT : 0 ≤ q.1) :
    (∫ z, ‖z.1-p.2.1‖^2 ∂historyKernel n q) =
      historySecondMoment n q + 2*inner ℝ (q.2.1-p.2.1) (historyMean n q) +
        simplexVolume n q.1 * ‖q.2.1-p.2.1‖^2 := by
  let _ := historyKernel_isFinite n q hT
  have hi := history_displacement_integrable n q hT
  have hs := history_displacement_sq_integrable n q hT
  have hj : Integrable (fun z : FlightState => inner ℝ (q.2.1-p.2.1) (z.1-q.2.1))
      (historyKernel n q) := (innerSL ℝ (q.2.1-p.2.1)).integrable_comp hi
  have hj2 : Integrable (fun z : FlightState => 2*inner ℝ (q.2.1-p.2.1) (z.1-q.2.1))
      (historyKernel n q) := hj.const_mul 2
  have hsum : Integrable (fun z : FlightState => ‖z.1-q.2.1‖^2 +
      2*inner ℝ (q.2.1-p.2.1) (z.1-q.2.1)) (historyKernel n q) := hs.add hj2
  have heq (z : FlightState) : ‖z.1-p.2.1‖^2 =
      ‖z.1-q.2.1‖^2 + 2*inner ℝ (q.2.1-p.2.1) (z.1-q.2.1) + ‖q.2.1-p.2.1‖^2 := by
    rw [show z.1-p.2.1 = (z.1-q.2.1)+(q.2.1-p.2.1) by abel,norm_add_sq_real,real_inner_comm]
  rw [show (fun z : FlightState => ‖z.1-p.2.1‖^2) = _ from funext heq,
    integral_add hsum (integrable_const _),
    integral_add hs hj2,integral_const_mul,integral_const]
  have hc := (innerSL ℝ (q.2.1-p.2.1)).integral_comp_comm hi
  change (∫ z, inner ℝ (q.2.1-p.2.1) (z.1-q.2.1) ∂historyKernel n q) =
    inner ℝ (q.2.1-p.2.1) (historyMean n q) at hc
  rw [hc]
  change historySecondMoment n q + _ + (historyKernel n q univ).toReal • _ = _
  rw [historyKernel_mass n q hT,simplexTime_toReal n hT,smul_eq_mul]

theorem historyMean_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (n : ℕ) (p : TimeFlightState), 0 ≤ p.1 →
      ‖historyMean n p‖ ≤ B*simplexVolume (n+1) p.1 := by
  obtain ⟨B,hB,hbound⟩ := velocitySum_uniform_bound
  refine ⟨B,hB,?_⟩
  intro n p hT
  rw [historyMean_formula n p hT,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (simplexVolume_nonneg _ hT),mul_comm B]
  exact mul_le_mul_of_nonneg_left (hbound n p.2.2) (simplexVolume_nonneg _ hT)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A linear-in-count bound for the second moment on each time simplex -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historySecondMoment_uniform_bound : ∃ K : ℝ, 0 < K ∧
    ∀ (n : ℕ) (p : TimeFlightState), 0 ≤ p.1 →
      historySecondMoment n p ≤ K*(n+1 : ℕ)*simplexVolume (n+2) p.1 := by
  obtain ⟨B,hB,hmean⟩ := historyMean_bound
  let K := 50+10*B
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro n
  induction n with
  | zero =>
    intro p hT
    have hv := retainedState_norm p.2.2
    have hv2 : ‖(p.2.2 : V)‖^2 ≤ 25 := by nlinarith [norm_nonneg (p.2.2 : V)]
    simp only [historySecondMoment,historyKernel_zero,Kernel.deterministic_apply,integral_dirac,
      finishFlight,freeFlight,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hT]
    norm_num only [Nat.reduceAdd,Nat.cast_one,mul_one]
    have hc : K*simplexVolume 2 p.1 = K*p.1^2/2 := by norm_num [simplexVolume]; ring
    rw [hc,mul_pow]
    have hh := mul_le_mul_of_nonneg_left hv2 (sq_nonneg p.1)
    dsimp [K]
    nlinarith [mul_nonneg hB.le (sq_nonneg p.1)]
  | succ n ih =>
    intro p hT
    let F : ℝ → ℝ := fun s => K*(n+1 : ℕ)*simplexVolume (n+2) (p.1-s) +
      (10*B)*(s*simplexVolume (n+1) (p.1-s)) +
      25*(s^2*simplexVolume n (p.1-s))
    have hpoint (s : ℝ) (hs : s ∈ Ioc 0 p.1) (u : RetainedState) :
        (∫ z, ‖z.1-p.2.1‖^2 ∂historyKernel n (advanceState p s u)) ≤ F s := by
      let q := advanceState p s u
      have hq : 0 ≤ q.1 := sub_nonneg.mpr hs.2
      have hm := hmean n q hq
      have hsq := ih q hq
      have hd : ‖q.2.1-p.2.1‖ ≤ 5*s := by
        simpa only [q,advanceState,abs_of_pos hs.1] using freeFlight_displacement s p.2
      have hcross : 2*inner ℝ (q.2.1-p.2.1) (historyMean n q) ≤
          (10*B)*(s*simplexVolume (n+1) (p.1-s)) := by
        have hh := real_inner_le_norm (q.2.1-p.2.1) (historyMean n q)
        have hprod := mul_le_mul hd hm (norm_nonneg _) (mul_nonneg (by norm_num) hs.1.le : 0 ≤ 5*s)
        change ‖q.2.1-p.2.1‖*‖historyMean n q‖ ≤ 5*s*(B*simplexVolume (n+1) (p.1-s)) at hprod
        nlinarith
      have hlast : simplexVolume n q.1 * ‖q.2.1-p.2.1‖^2 ≤
          25*(s^2*simplexVolume n (p.1-s)) := by
        have hh := pow_le_pow_left₀ (norm_nonneg _) hd 2
        have hm := mul_le_mul_of_nonneg_left hh (simplexVolume_nonneg n hq)
        change simplexVolume n (p.1-s)*‖q.2.1-p.2.1‖^2 ≤
          simplexVolume n (p.1-s)*(5*s)^2 at hm
        change simplexVolume n (p.1-s)*‖q.2.1-p.2.1‖^2 ≤ _
        nlinarith
      rw [historySecondMoment_shift n p q hq]
      change historySecondMoment n q ≤ K*(n+1 : ℕ)*simplexVolume (n+2) (p.1-s) at hsq
      dsimp [F]
      linarith
    have hinner (s : ℝ) (hs : s ∈ Ioc 0 p.1) :
        (∫ u, ∫ z, ‖z.1-p.2.1‖^2 ∂historyKernel n (advanceState p s u)
          ∂uniformizedKernel p.2.2) ≤ F s := by
      calc
        _ ≤ ∫ _u, F s ∂uniformizedKernel p.2.2 :=
          integral_mono_of_nonneg (ae_of_all _ (fun _ => integral_nonneg (fun _ => sq_nonneg _)))
            (integrable_const _) (ae_of_all _ (hpoint s hs))
        _ = F s := by simp
    have hF : IntegrableOn F (Ioc 0 p.1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
        ((show Continuous F by dsimp [F,simplexVolume]; fun_prop).intervalIntegrable _ _)
    calc
      historySecondMoment (n+1) p =
          ∫ s in Ioc 0 p.1, ∫ u, ∫ z, ‖z.1-p.2.1‖^2
            ∂historyKernel n (advanceState p s u) ∂uniformizedKernel p.2.2 :=
        historyKernel_succ_integral n p (by fun_prop) (history_displacement_sq_integrable _ p hT)
      _ ≤ ∫ s in Ioc 0 p.1, F s := integral_mono_of_nonneg
        (ae_of_all _ (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))))
        hF (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs; exact hinner s hs)
      _ = K*(n+1+1 : ℕ)*simplexVolume (n+1+2) p.1 := by
        rw [← intervalIntegral.integral_of_le hT]
        dsimp [F]
        rw [intervalIntegral.integral_add,intervalIntegral.integral_add,
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul,integral_simplexVolume,
          integral_time_simplexVolume,integral_time_sq_simplexVolume]
        · dsimp [K]
          push_cast
          ring
        all_goals
          apply Continuous.intervalIntegrable
          unfold simplexVolume
          fun_prop

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A linear displacement second moment for the actual reference flight -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flight_displacement_second_moment : ∃ K : ℝ, 0 < K ∧
    ∀ (rate T : ℝ≥0), 0 < rate → ∀ z : FlightState,
      (∫⁻ w, ENNReal.ofReal (‖w.1-z.1‖^2) ∂flightKernel rate T z) ≤
        ENNReal.ofReal (K*(T : ℝ)/rate) := by
  obtain ⟨K,hK,hbound⟩ := historySecondMoment_uniform_bound
  refine ⟨K,hK,?_⟩
  intro rate T hr z
  have hn (n : ℕ) :
      (∫⁻ w, ENNReal.ofReal (‖w.1-z.1‖^2) ∂historyKernel n ((T : ℝ),z)) ≤
        ENNReal.ofReal K * ENNReal.ofReal ((n+1 : ℕ)*simplexVolume (n+2) T) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (history_displacement_sq_integrable n _ T.coe_nonneg)
      (ae_of_all _ (fun _ => sq_nonneg _)),← ENNReal.ofReal_mul hK.le]
    apply ENNReal.ofReal_le_ofReal
    simpa only [historySecondMoment,mul_assoc] using hbound n ((T : ℝ),z) T.coe_nonneg
  rw [flightKernel_apply,lintegral_sum_measure]
  simp only [lintegral_smul_measure,smul_eq_mul]
  calc
    _ ≤ ∑' n : ℕ, flightWeight rate T n *
        (ENNReal.ofReal K * ENNReal.ofReal ((n+1 : ℕ)*simplexVolume (n+2) T)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      gcongr
      exact hn n
    _ = ENNReal.ofReal K * (∑' n : ℕ, flightWeight rate T n *
        ENNReal.ofReal ((n+1 : ℕ)*simplexVolume (n+2) T)) := by
      simp_rw [mul_left_comm _ (ENNReal.ofReal K)]
      exact ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((T : ℝ)/rate) := by
      gcongr
      exact flightWeight_secondMoment_sum_le rate T hr
    _ = ENNReal.ofReal (K*(T : ℝ)/rate) := by
      rw [← ENNReal.ofReal_mul hK.le]
      congr 1
      ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform sublinear displacement probability for the actual flight -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flight_displacement_tail : ∃ K : ℝ, 0 < K ∧
    ∀ (rate T : ℝ≥0), 0 < rate → 0 < T → ∀ a : ℝ, 0 < a → ∀ z : FlightState,
      flightKernel rate T z {w | a*(T : ℝ) ≤ ‖w.1-z.1‖} ≤
        ENNReal.ofReal (K/((rate : ℝ)*a^2*T)) := by
  obtain ⟨K,hK,hbound⟩ := flight_displacement_second_moment
  refine ⟨K,hK,?_⟩
  intro rate T hr hT a ha z
  have hr' : 0 < (rate : ℝ) := hr
  have hT' : 0 < (T : ℝ) := hT
  have he : 0 < (a*(T : ℝ))^2 := sq_pos_of_pos (mul_pos ha hT')
  have hf : Measurable (fun w : FlightState => ENNReal.ofReal (‖w.1-z.1‖^2)) := by fun_prop
  calc
    _ ≤ flightKernel rate T z {w | ENNReal.ofReal ((a*(T : ℝ))^2) ≤
        ENNReal.ofReal (‖w.1-z.1‖^2)} := by
      apply measure_mono
      intro w hw
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hw 2)
    _ ≤ (∫⁻ w, ENNReal.ofReal (‖w.1-z.1‖^2) ∂flightKernel rate T z) /
        ENNReal.ofReal ((a*(T : ℝ))^2) :=
      meas_ge_le_lintegral_div hf.aemeasurable (by positivity) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K*(T : ℝ)/rate) / ENNReal.ofReal ((a*(T : ℝ))^2) :=
      ENNReal.div_le_div (hbound rate T hr z) le_rfl
    _ = ENNReal.ofReal (K/((rate : ℝ)*a^2*T)) := by
      rw [← ENNReal.ofReal_div_of_pos he]
      congr 1
      field_simp

theorem flight_small_displacement (rate : ℝ≥0) (hr : 0 < rate) {a : ℝ} (ha : 0 < a) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ≥0, T₀ ≤ (T : ℝ) → ∀ z : FlightState,
      (1/2 : ℝ≥0∞) ≤ flightKernel rate T z {w | ‖w.1-z.1‖ < a*(T : ℝ)} := by
  obtain ⟨K,hK,hbound⟩ := flight_displacement_tail
  have hr' : 0 < (rate : ℝ) := hr
  let T₀ := 2*K/((rate : ℝ)*a^2)
  have hT₀ : 0 < T₀ := by dsimp [T₀]; positivity
  refine ⟨T₀,hT₀,?_⟩
  intro T hT z
  have hT' : 0 < (T : ℝ) := hT₀.trans_le hT
  have hd : 0 < (rate : ℝ)*a^2*T := by positivity
  have hlarge : 2*K ≤ (rate : ℝ)*a^2*T := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < (rate : ℝ)*a^2)).mp hT
  have hquot : K/((rate : ℝ)*a^2*T) ≤ (1:ℝ)/2 := by
    rw [div_le_iff₀ hd]
    nlinarith
  have hbad : flightKernel rate T z {w | a*(T : ℝ) ≤ ‖w.1-z.1‖} ≤ (1/2 : ℝ≥0∞) := by
    exact (hbound rate T hr hT' a ha z).trans (by
      simpa using ENNReal.ofReal_le_ofReal hquot)
  calc
    (1/2 : ℝ≥0∞) = 1-1/2 := by norm_num
    _ ≤ 1-flightKernel rate T z {w | a*(T : ℝ) ≤ ‖w.1-z.1‖} := tsub_le_tsub_left hbad 1
    _ = flightKernel rate T z {w | ‖w.1-z.1‖ < a*(T : ℝ)} := by
      rw [← prob_compl_eq_one_sub (by measurability)]
      congr 1
      ext w
      simp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact volume of the fixed finite history parameter domains -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem markedEventMeasure_mass (T : ℝ) : markedEventMeasure T univ = 3*ENNReal.ofReal T := by
  rw [markedEventMeasure,Measure.prod_apply MeasurableSet.univ]
  simp only [preimage_univ,eventParameterMeasure_mass,lintegral_const]
  rw [Measure.count_univ]
  norm_num [mul_comm]

theorem parameterWordMeasure_mass (T : ℝ) (n : ℕ) :
    parameterWordMeasure T n univ = (3*ENNReal.ofReal T)^n := by
  induction n with
  | zero =>
    change (Measure.dirac PUnit.unit) univ = _
    rw [Measure.dirac_apply_of_mem (mem_univ _),pow_zero]
  | succ n ih =>
    rw [parameterWordMeasure,Measure.prod_apply MeasurableSet.univ]
    simp only [preimage_univ,ih,lintegral_const]
    rw [markedEventMeasure_mass,pow_succ]

theorem parameterWordMeasure_mass_ne_top (T : ℝ) (n : ℕ) :
    parameterWordMeasure T n univ ≠ ⊤ := by
  rw [parameterWordMeasure_mass]
  exact ENNReal.pow_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
