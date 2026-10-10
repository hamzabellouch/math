import OAI.Analysis.SignedDisk.DiskScales3

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

noncomputable section

namespace SignedDisk

namespace DiskMaximalTools

lemma maximal_layer_coefficient {t p : ℝ} (ht : 0 < t) :
    (25 / ENNReal.ofReal (t/2))*ENNReal.ofReal (t^(p-1)) =
      ENNReal.ofReal 50*ENNReal.ofReal (t^(p-2)) := by
  rw [← show ENNReal.ofReal (25:ℝ) = 25 by norm_num,
    ← ENNReal.ofReal_div_of_pos (by linarith : 0 < t/2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (25:ℝ)/(t/2)),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 50)]
  congr 1
  have hpow : t^(p-1) = t*t^(p-2) := by
    calc
      _ = t^(1+(p-2)) := by congr 1; ring
      _ = t^(1:ℝ)*t^(p-2) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hpow]
  field_simp
  ring

/-- A full strong p estimate from Vitali, truncation and Tonelli. No maximal
inequality is supplied as an assumption. The real representative is controlled
even before a separate almost-everywhere finiteness argument. -/
theorem strong_rationalMaximal {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) [IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))]
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, ENNReal.ofReal ((rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x))) x).toReal^p)) ≤
      ENNReal.ofReal (50*p*2^(p-1)/(p-1)) * (∫⁻ x, ENNReal.ofReal ((f x)^p)) := by
  let M := rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x)))
  have hM : Measurable M := measurable_rationalMaximal _
  have htail (t : ℝ) (ht : 0 < t) : volume {x | t < (M x).toReal} ≤
      (25/ENNReal.ofReal (t/2)) * ∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0 := by
    have hsub : {x | t < (M x).toReal} ⊆ {x | ENNReal.ofReal t < M x} := by
      intro x hx
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hx |>.trans_le ENNReal.ofReal_toReal_le
    apply le_trans (measure_mono hsub)
    have hweak := weak_truncated hf.ennreal_ofReal ht
    apply hweak.trans_eq
    congr 1
    apply lintegral_congr
    intro x
    have heq : ENNReal.ofReal (t/2) < ENNReal.ofReal (f x) ↔ t < 2*f x := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith : 0 ≤ t/2)]
      constructor <;> intro h <;> linarith
    simp only [Set.indicator,Set.mem_ofPred_eq,heq]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    hM.ennreal_toReal.aemeasurable (by linarith : 0 < p)]
  have hlayer : (∫⁻ t in Ioi 0, volume {x | t < (M x).toReal}*ENNReal.ofReal (t^(p-1))) ≤
      ENNReal.ofReal 50 * (∫⁻ t in Ioi 0,
        (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) := by
    calc
      _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal 50 *
          ((∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        calc
          _ ≤ ((25/ENNReal.ofReal (t/2)) * ∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*
              ENNReal.ofReal (t^(p-1)) := by gcongr; exact htail t ht
          _ = _ := by
            rw [mul_right_comm, maximal_layer_coefficient ht]
            ring
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal p*(ENNReal.ofReal 50 * (∫⁻ t in Ioi 0,
        (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2)))) := by
      gcongr
    _ = _ := by
      rw [truncation_layer_integral hf hf0 hp]
      have hc : ENNReal.ofReal p*(ENNReal.ofReal 50 * ENNReal.ofReal (2^(p-1)/(p-1))) =
          ENNReal.ofReal (50*p*2^(p-1)/(p-1)) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 50),
          ← ENNReal.ofReal_mul (by linarith : 0 ≤ p)]
        congr 1
        ring
      simpa only [mul_assoc] using congrArg
        (fun c => c*(∫⁻ x, ENNReal.ofReal ((f x)^p))) hc

lemma disk_average_le_rationalMaximal_exact (ν : Measure ℂ) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ν (ball x r) / volume (ball x r) ≤ rationalMaximal ν x := by
  let I := {q : ℚ // 0 < q ∧ (q:ℝ) < r}
  have hdir : Directed (· ⊆ ·) (fun q : I => ball x (q:ℚ)) := by
    intro i j
    refine ⟨⟨max i.val j.val,?_,?_⟩,?_,?_⟩
    · exact lt_max_of_lt_left i.property.1
    · exact_mod_cast max_lt i.property.2 j.property.2
    · exact ball_subset_ball (by exact_mod_cast le_max_left i.val j.val)
    · exact ball_subset_ball (by exact_mod_cast le_max_right i.val j.val)
  have heq : (⋃ q : I, ball x (q:ℚ)) = ball x r := by
    ext y
    constructor
    · intro hy
      obtain ⟨q,hq⟩ := mem_iUnion.mp hy
      exact (ball_subset_ball q.property.2.le) hq
    · intro hy
      have hd : dist y x < r := hy
      obtain ⟨q,hq0,hqr⟩ := exists_rat_btwn (show max 0 (dist y x) < r by exact max_lt hr hd)
      have hq : 0 < (q:ℝ) := lt_of_le_of_lt (le_max_left _ _) hq0
      have hqRat : (0:ℚ) < q := by exact_mod_cast hq
      refine mem_iUnion.mpr ⟨⟨q,hqRat,hqr⟩,?_⟩
      exact lt_of_le_of_lt (le_max_right _ _) hq0
  have hv0 : volume (ball x r) ≠ 0 := by
    rw [volume_disk_real _ hr.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hr)))
  apply (ENNReal.div_le_iff hv0 measure_ball_lt_top.ne).mpr
  rw [← heq,hdir.measure_iUnion]
  apply iSup_le
  intro q
  have hq0 : 0 < (q.val:ℝ) := by exact_mod_cast q.property.1
  have hqv : volume (ball x (q.val:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq0.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq0)))
  have hav : ν (ball x (q.val:ℝ)) / volume (ball x (q.val:ℝ)) ≤ rationalMaximal ν x :=
    le_iSup_of_le q.val (le_iSup_of_le q.property.1 le_rfl)
  calc
    _ ≤ rationalMaximal ν x * volume (ball x (q.val:ℝ)) :=
      (ENNReal.div_le_iff hqv measure_ball_lt_top.ne).mp hav
    _ ≤ _ := by
      gcongr
      exact subset_iUnion (fun q : I => ball x (q:ℚ)) q

/-- Countability loses neither radii nor high values: the rational expression is
exactly the centered disk maximal function of the measure. -/
theorem all_radii_eq_rational (ν : Measure ℂ) (x : ℂ) :
    (⨆ (r : ℝ) (_ : 0 < r), ν (ball x r)/volume (ball x r)) = rationalMaximal ν x := by
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    exact disk_average_le_rationalMaximal_exact ν x hr
  · unfold rationalMaximal
    apply iSup_le
    intro q
    apply iSup_le
    intro hq
    have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
    exact le_iSup_of_le (q:ℝ) (le_iSup_of_le hq' le_rfl)

lemma rationalMaximal_le_of_density_le {f : ℂ → ℝ≥0∞} {B : ℝ≥0∞} (hf : ∀ x, f x ≤ B) (x : ℂ) :
    rationalMaximal (volume.withDensity f) x ≤ B := by
  unfold rationalMaximal
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  apply (ENNReal.div_le_iff hv0 measure_ball_lt_top.ne).mpr
  rw [withDensity_apply _ measurableSet_ball]
  calc
    _ ≤ ∫⁻ y in ball x (q:ℝ), B := lintegral_mono hf
    _ = _ := by simp

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ScalarCancellation

/-- A nonnegative scalar residual retaining exactly the net mass. Its removal
has the exact cancellation defect as L1 cost. -/
theorem positive_residual {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} (hh : Integrable h μ) (hc : 0 ≤ ∫ x, h x ∂μ) :
    ∃ ρ : α → ℝ, Integrable ρ μ ∧ (∀ x, 0 ≤ ρ x) ∧
      (∀ x, ρ x ≤ max (h x) 0) ∧ (∫ x, ρ x ∂μ) = ∫ x, h x ∂μ ∧
      (∫ x, |h x-ρ x| ∂μ) = (∫ x, |h x| ∂μ) - ∫ x, h x ∂μ ∧
      (∀ x, h x = 0 → ρ x = 0) := by
  let p : α → ℝ := fun x => max (h x) 0
  have hp : Integrable p μ := by
    convert (hh.add hh.abs).div_const 2 using 1
    funext x
    by_cases hx : 0 ≤ h x
    · simp only [p,max_eq_left hx,abs_of_nonneg hx,Pi.add_apply]
      ring
    · simp only [p,max_eq_right (le_of_not_ge hx),abs_of_nonpos (le_of_not_ge hx),Pi.add_apply]
      ring
  have hp0 : 0 ≤ ∫ x, p x ∂μ := integral_nonneg (fun x => le_max_right _ _)
  have hcp : (∫ x, h x ∂μ) ≤ ∫ x, p x ∂μ := integral_mono hh hp (fun x => le_max_left _ _)
  by_cases hP : (∫ x, p x ∂μ) = 0
  · have hc0 : (∫ x, h x ∂μ) = 0 := le_antisymm (hP ▸ hcp) hc
    refine ⟨0,integrable_zero _ _ _,fun _ => le_rfl,fun x => le_max_right _ _,?_,?_,fun _ _ => rfl⟩
    · simp [hc0]
    · simp [hc0]
  · have hPpos : 0 < ∫ x, p x ∂μ := lt_of_le_of_ne hp0 (Ne.symm hP)
    let q := (∫ x, h x ∂μ)/(∫ x, p x ∂μ)
    have hq0 : 0 ≤ q := div_nonneg hc hp0
    have hq1 : q ≤ 1 := (div_le_one hPpos).mpr hcp
    let ρ : α → ℝ := fun x => q*p x
    have hρ : Integrable ρ μ := hp.const_mul q
    have hρ0 : ∀ x, 0 ≤ ρ x := fun x => mul_nonneg hq0 (le_max_right _ _)
    have hρp : ∀ x, ρ x ≤ p x := fun x => mul_le_of_le_one_left (le_max_right _ _) hq1
    have hi : (∫ x, ρ x ∂μ) = ∫ x, h x ∂μ := by
      rw [show ρ = fun x => q*p x from rfl,integral_const_mul]
      exact div_mul_cancel₀ _ hP
    have habs : ∀ x, |h x-ρ x| = |h x|-ρ x := by
      intro x
      by_cases hhx : 0 ≤ h x
      · rw [abs_of_nonneg hhx,abs_of_nonneg]
        simpa only [p,max_eq_left hhx] using sub_nonneg.mpr (hρp x)
      · have hx0 : h x ≤ 0 := (lt_of_not_ge hhx).le
        have : ρ x = 0 := by simp [ρ,p,max_eq_right hx0]
        simp [this]
    refine ⟨ρ,hρ,hρ0,hρp,hi,?_,?_⟩
    · simp_rw [habs]
      rw [integral_sub hh.abs hρ,hi]
    · intro x hx
      simp [ρ,p,hx]

/-- Every integrable scalar density splits into a constant-sign root and a
zero-mass error, without replacing the actual terminal density by its mass. -/
theorem residual_split {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} (hh : Integrable h μ) :
    ∃ ρ β : α → ℝ, Integrable ρ μ ∧ Integrable β μ ∧
      (∀ x, h x = ρ x+β x) ∧ (∫ x, ρ x ∂μ) = ∫ x, h x ∂μ ∧
      (∫ x, β x ∂μ) = 0 ∧ (∫ x, |ρ x| ∂μ) = |∫ x, h x ∂μ| ∧
      (∫ x, |β x| ∂μ) = (∫ x, |h x| ∂μ)-|∫ x, h x ∂μ| ∧
      ((0 ≤ ∫ x, h x ∂μ) → ∀ x, 0 ≤ ρ x) ∧
      ((∫ x, h x ∂μ) < 0 → ∀ x, ρ x ≤ 0) ∧
      (∀ x, h x = 0 → ρ x = 0 ∧ β x = 0) := by
  by_cases hc : 0 ≤ ∫ x, h x ∂μ
  · obtain ⟨ρ,hρ,hρ0,_,hi,hcost,hzero⟩ := positive_residual hh hc
    refine ⟨ρ,fun x => h x-ρ x,hρ,hh.sub hρ,fun x => by ring,hi,?_,?_,?_,
      fun _ => hρ0,fun hn => (not_lt_of_ge hc hn).elim,?_⟩
    · rw [integral_sub hh hρ,hi,sub_self]
    · simp_rw [abs_of_nonneg (hρ0 _)]
      rw [hi,abs_of_nonneg hc]
    · rwa [abs_of_nonneg hc]
    · intro x hx
      simp [hx,hzero x hx]
  · have hc' : (∫ x, h x ∂μ) < 0 := lt_of_not_ge hc
    have hn : 0 ≤ ∫ x, -h x ∂μ := by rw [integral_neg]; linarith
    obtain ⟨ρ,hρ,hρ0,_,hi,hcost,hzero⟩ := positive_residual hh.neg hn
    have hi' : (∫ x, ρ x ∂μ) = -(∫ x, h x ∂μ) := by simpa only [Pi.neg_apply,integral_neg] using hi
    refine ⟨fun x => -ρ x,fun x => h x+ρ x,hρ.neg,hh.add hρ,fun x => by ring,?_,?_,?_,?_,
      fun hn => (not_le_of_gt hc' hn).elim,fun _ x => neg_nonpos.mpr (hρ0 x),?_⟩
    · rw [integral_neg,hi',neg_neg]
    · rw [integral_add hh hρ,hi',add_neg_cancel]
    · simp_rw [abs_neg,abs_of_nonneg (hρ0 _)]
      rw [hi',abs_of_neg hc']
    · have heq : (fun x => |-h x-ρ x|) = fun x => |h x+ρ x| := by
        funext x
        rw [show -h x-ρ x = -(h x+ρ x) by ring,abs_neg]
      simp only [Pi.neg_apply] at hcost
      rw [heq] at hcost
      simpa only [abs_neg,integral_neg,abs_of_neg hc',sub_neg_eq_add] using hcost
    · intro x hx
      have hz := hzero x (by simp [hx])
      simp [hx,hz]

/-- One backward refinement step. The new cancelling piece has cost no larger
than the scalar norm defect of the children; overlap can only lower this cost. -/
theorem refinement_residual {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ρ : ι → α → ℝ)
    (hρ : ∀ i, Integrable (ρ i) μ) :
    ∃ R β : α → ℝ, Integrable R μ ∧ Integrable β μ ∧
      (∀ x, (∑ i, w i*ρ i x) = R x+β x) ∧
      (∫ x, R x ∂μ) = ∑ i, w i*(∫ x, ρ i x ∂μ) ∧
      (∫ x, β x ∂μ) = 0 ∧
      (∫ x, |R x| ∂μ) = |∑ i, w i*(∫ x, ρ i x ∂μ)| ∧
      (∫ x, |β x| ∂μ) ≤
        (∑ i, w i*(∫ x, |ρ i x| ∂μ))-|∑ i, w i*(∫ x, ρ i x ∂μ)| ∧
      ((0 ≤ ∑ i, w i*(∫ x, ρ i x ∂μ)) → ∀ x, 0 ≤ R x) ∧
      (∀ x, (∀ i, w i*ρ i x = 0) → R x = 0 ∧ β x = 0) := by
  classical
  let f : α → ℝ := fun x => ∑ i, w i*ρ i x
  have hf : Integrable f μ := integrable_finsetSum _ (fun i _ => (hρ i).const_mul _)
  have hfi : (∫ x, f x ∂μ) = ∑ i, w i*(∫ x, ρ i x ∂μ) := by
    rw [show f = fun x => ∑ i, w i*ρ i x from rfl,integral_finsetSum]
    · simp only [integral_const_mul]
    · exact fun i _ => (hρ i).const_mul _
  have hcost : (∫ x, |f x| ∂μ) ≤ ∑ i, w i*(∫ x, |ρ i x| ∂μ) := by
    calc
      _ ≤ ∫ x, ∑ i, w i*|ρ i x| ∂μ := by
        apply integral_mono hf.abs (integrable_finsetSum _ (fun i _ => (hρ i).abs.const_mul _))
        intro x
        calc
          _ ≤ ∑ i, |w i*ρ i x| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp_rw [abs_mul,abs_of_nonneg (hw _)]
      _ = _ := by
        rw [integral_finsetSum _ (fun i _ => (hρ i).abs.const_mul _)]
        simp only [integral_const_mul]
  obtain ⟨R,β,hR,hβ,hdec,hi,hzero,habs,hβcost,hpos,_,hsupp⟩ := residual_split hf
  refine ⟨R,β,hR,hβ,hdec,hi.trans hfi,hzero,?_,?_,?_,?_⟩
  · rwa [hfi] at habs
  · rw [hβcost,hfi]
    exact sub_le_sub_right hcost _
  · intro hp
    apply hpos
    rwa [hfi]
  · intro x hx
    apply hsupp
    exact Finset.sum_eq_zero (fun i _ => hx i)

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Canonical positive/negative root selected from the proved scalar splitting,
not an assumed decomposition. -/
def root (μ : Measure α) (f : α → ℝ) : α → ℝ := by
  classical
  exact if h : Integrable f μ then (residual_split h).choose else 0

lemma root_spec {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (root μ f) μ ∧
      (∫ x, root μ f x ∂μ) = ∫ x, f x ∂μ ∧
      (∫ x, |root μ f x| ∂μ) = |∫ x, f x ∂μ| ∧
      (∫ x, |f x-root μ f x| ∂μ) = (∫ x, |f x| ∂μ)-|∫ x, f x ∂μ| ∧
      ((0 ≤ ∫ x, f x ∂μ) → ∀ x, 0 ≤ root μ f x) ∧
      ((∫ x, f x ∂μ) < 0 → ∀ x, root μ f x ≤ 0) ∧
      (∀ x, f x = 0 → root μ f x = 0) := by
  rw [root,dite_eq_left hf]
  obtain ⟨β,hR,_,hdec,hi,_,habs,hcost,hpos,hneg,hsupp⟩ := (residual_split hf).choose_spec
  refine ⟨hR,hi,habs,?_,hpos,hneg,fun x hx => (hsupp x hx).1⟩
  convert hcost using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only; rw [hdec x]; congr 1; ring)

variable {ι : Type*} [Fintype ι]

def refined (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) : ℕ → ι → α → ℝ
  | 0,q => f q
  | k+1,q => fun x => ∑ s, w k q s*refined w f k s x

def roots (μ : Measure α) (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) : ℕ → ι → α → ℝ
  | 0,q => root μ (f q)
  | k+1,q => root μ (fun x => ∑ s, w k q s*roots μ w f k s x)

def errors (μ : Measure α) (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) : ℕ → ι → α → ℝ
  | 0,q => fun x => f q x-roots μ w f 0 q x
  | k+1,q => fun x => (∑ s, w k q s*roots μ w f k s x)-roots μ w f (k+1) q x

lemma refined_integrable (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    Integrable (refined w f k q) μ := by
  induction k generalizing q with
  | zero => exact hf q
  | succ k ih => exact integrable_finsetSum _ (fun s _ => (ih s).const_mul _)

lemma roots_integrable (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    Integrable (roots μ w f k q) μ := by
  induction k generalizing q with
  | zero => exact (root_spec (hf q)).1
  | succ k ih => exact (root_spec (integrable_finsetSum _ (fun s _ => (ih s).const_mul _))).1

lemma roots_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, roots μ w f k q x ∂μ) = ∫ x, refined w f k q x ∂μ := by
  induction k generalizing q with
  | zero => exact (root_spec (hf q)).2.1
  | succ k ih =>
    rw [roots,(root_spec (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _))).2.1,
      refined,integral_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _),
      integral_finsetSum _ (fun s _ => (refined_integrable w hf k s).const_mul _)]
    simp_rw [integral_const_mul,ih]

lemma roots_abs_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, |roots μ w f k q x| ∂μ) = |∫ x, refined w f k q x ∂μ| := by
  cases k with
  | zero => exact (root_spec (hf q)).2.2.1
  | succ k =>
    have hs := root_spec (integrable_finsetSum Finset.univ
      (fun s _ => (roots_integrable w hf k s).const_mul (w k q s)))
    change (∫ x, |root μ _ x| ∂μ) = _
    rw [hs.2.2.1,← hs.2.1]
    exact congrArg abs (roots_mass w hf (k+1) q)

lemma errors_integrable (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    Integrable (errors μ w f k q) μ := by
  cases k with
  | zero => exact (hf q).sub (roots_integrable w hf 0 q)
  | succ k =>
    exact (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _)).sub
      (roots_integrable w hf (k+1) q)

lemma errors_zero_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, errors μ w f k q x ∂μ) = 0 := by
  cases k with
  | zero =>
    rw [errors,integral_sub (hf q) (roots_integrable w hf 0 q),roots_mass]
    exact sub_self _
    exact hf
  | succ k =>
    rw [errors,integral_sub
      (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _))
      (roots_integrable w hf (k+1) q),roots,
      (root_spec (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _))).2.1,
      sub_self]

/-- The whole scalar cancellation tree is built by backward splitting. Each
nonterminal zero-mass piece costs at most its positive refinement norm defect. -/
theorem errors_cost (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    {f : ι → α → ℝ} (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, |errors μ w f (k+1) q x| ∂μ) ≤
      (∑ s, w k q s*|∫ x, refined w f k s x ∂μ|)-|∫ x, refined w f (k+1) q x ∂μ| := by
  have hi : Integrable (fun x => ∑ s, w k q s*roots μ w f k s x) μ :=
    integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _)
  have hs := root_spec hi
  change (∫ x, |(∑ s, w k q s*roots μ w f k s x)-root μ _ x| ∂μ) ≤ _
  rw [hs.2.2.2.1]
  have hm : (∫ x, ∑ s, w k q s*roots μ w f k s x ∂μ) = ∫ x, refined w f (k+1) q x ∂μ := by
    rw [← hs.2.1]
    exact roots_mass w hf (k+1) q
  rw [hm]
  apply sub_le_sub_right
  calc
    _ ≤ ∫ x, ∑ s, w k q s*|roots μ w f k s x| ∂μ := by
      apply integral_mono hi.abs (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).abs.const_mul _))
      intro x
      calc
        _ ≤ ∑ s, |w k q s*roots μ w f k s x| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp_rw [abs_mul,abs_of_nonneg (hw k q _)]
    _ = _ := by
      rw [integral_finsetSum _ (fun s _ => (roots_integrable w hf k s).abs.const_mul _)]
      simp_rw [integral_const_mul,roots_abs_mass w hf]

lemma errors_terminal_cost (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (q : ι) :
    (∫ x, |errors μ w f 0 q x| ∂μ) = (∫ x, |f q x| ∂μ)-|∫ x, f q x ∂μ| :=
  (root_spec (hf q)).2.2.2.1

lemma error_recurrence (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) (k : ℕ) (q : ι) (x : α) :
    refined w f (k+1) q x-roots μ w f (k+1) q x = errors μ w f (k+1) q x+
      ∑ s, w k q s*(refined w f k s x-roots μ w f k s x) := by
  simp only [refined,errors,mul_sub,Finset.sum_sub_distrib]
  ring

/-- Support nesting is preserved by the new construction, even when child
scalar masses vanish or overlapping densities cancel each other. -/
theorem roots_errors_support (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (S : ℕ → ι → Set α)
    (hfS : ∀ q x, x ∉ S 0 q → f q x = 0)
    (hS : ∀ k q s, w k q s ≠ 0 → S k s ⊆ S (k+1) q) :
    ∀ k q x, x ∉ S k q → roots μ w f k q x = 0 ∧ errors μ w f k q x = 0 := by
  intro k
  induction k with
  | zero =>
    intro q x hx
    have hf0 := hfS q x hx
    have hR0 := (root_spec (hf q)).2.2.2.2.2.2 x hf0
    exact ⟨hR0,by simp only [errors,roots,hf0,hR0,sub_self]⟩
  | succ k ih =>
    intro q x hx
    have hz : (∑ s, w k q s*roots μ w f k s x) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      by_cases hw : w k q s = 0
      · simp [hw]
      · have hs : x ∉ S k s := fun h => hx (hS k q s hw h)
        rw [(ih s x hs).1,mul_zero]
    have hR0 := (root_spec (integrable_finsetSum Finset.univ
      (fun s _ => (roots_integrable w hf k s).const_mul (w k q s)))).2.2.2.2.2.2 x hz
    exact ⟨hR0,by simp only [errors,roots,hz,hR0,sub_self]⟩

end ScalarCancellation

end SignedDisk

end

end OAI
