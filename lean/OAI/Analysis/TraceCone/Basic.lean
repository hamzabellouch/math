import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Extended traces and positive cuts

We use the extended lower semicontinuous traces of
*The trace cone classifies Razak–Jacelon stabilizations*, Sections 1 and 2.
The finite domain need not be dense. Positive cuts are defined by nonunital
continuous functional calculus, and canonical convergence is stated using filters.
-/

noncomputable section

open Filter Topology
open scoped NNReal ENNReal

namespace TraceConeClassification

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The positive cone of the algebra, with its norm-subspace topology. -/
abbrev Positive := {a : A // 0 ≤ a}

namespace Positive

variable {A}

def zero : Positive A := ⟨0, le_rfl⟩
def add (a b : Positive A) : Positive A := ⟨a.1 + b.1, add_nonneg a.2 b.2⟩
def scale (r : ℝ≥0) (a : Positive A) : Positive A :=
  ⟨(r : ℝ) • a.1, smul_nonneg r.2 a.2⟩
def starMul (x : A) : Positive A := ⟨star x * x, star_mul_self_nonneg x⟩
def mulStar (x : A) : Positive A := ⟨x * star x, mul_star_self_nonneg x⟩

/-- The nonunital positive cut `(a - ε)₊`, defined using functional calculus. -/
def cut (a : Positive A) (ε : ℝ≥0) : Positive A :=
  ⟨cfcₙ (fun t : ℝ => max (t - (ε : ℝ)) 0) a.1,
    cfcₙ_nonneg (fun _ _ => le_max_right _ _)⟩

end Positive

/-- Extended lower semicontinuous traces, with no finiteness restriction. -/
structure ExtendedTrace where
  toFun : Positive A → ℝ≥0∞
  map_zero : toFun Positive.zero = 0
  map_add : ∀ a b, toFun (Positive.add a b) = toFun a + toFun b
  map_scale : ∀ (r : ℝ≥0), 0 < r → ∀ a,
    toFun (Positive.scale r a) = (r : ℝ≥0∞) * toFun a
  tracial : ∀ x : A, toFun (Positive.starMul x) = toFun (Positive.mulStar x)
  lowerSemicontinuous : LowerSemicontinuous toFun

instance : CoeFun (ExtendedTrace A) (fun _ => Positive A → ℝ≥0∞) :=
  ⟨ExtendedTrace.toFun⟩

/-- Literal filter version of the manuscript's canonical convergence formula.
Every directed net is covered by its tail filter.
-/
def CanonicalConvergence {ι : Type*} (l : Filter ι) (τ : ι → ExtendedTrace A)
    (σ : ExtendedTrace A) : Prop :=
  ∀ (a : Positive A) (ε : ℝ≥0), 0 < ε →
    Filter.limsup (fun i => τ i (Positive.cut a ε)) l ≤ σ a ∧
    σ a ≤ Filter.liminf (fun i => τ i a) l

namespace ExtendedTrace

variable {A} (τ : ExtendedTrace A)

lemma monotone : Monotone τ := by
  intro a b hab
  let c : Positive A := ⟨b.1 - a.1, sub_nonneg.mpr hab⟩
  have hac : Positive.add a c = b := Subtype.ext (add_sub_cancel _ _)
  calc
    τ a ≤ τ a + τ c := le_add_right le_rfl
    _ = τ b := by rw [← τ.map_add, hac]

lemma map_scale_all (r : ℝ≥0) (a : Positive A) :
    τ (Positive.scale r a) = (r : ℝ≥0∞) * τ a := by
  rcases eq_or_lt_of_le r.2 with h | h
  · have hr : r = 0 := NNReal.eq (by simpa using h.symm)
    subst r
    simpa [Positive.scale, Positive.zero] using τ.map_zero
  · exact τ.map_scale r h a


end ExtendedTrace

namespace Positive

variable {A}

lemma cut_le (a : Positive A) (ε : ℝ≥0) : cut a ε ≤ a := by
  change cfcₙ (fun t : ℝ => max (t - (ε : ℝ)) 0) a.1 ≤ a.1
  conv_rhs => rw [← cfcₙ_id ℝ a.1 a.2.isSelfAdjoint]
  refine cfcₙ_mono ?_ (by fun_prop) (by fun_prop) ?_ rfl
  · intro t ht
    exact max_le (sub_le_self _ ε.2) (quasispectrum_nonneg_of_nonneg a.1 a.2 t ht)
  · simp

lemma norm_cut_sub_le (a : Positive A) (ε : ℝ≥0) :
    ‖(cut a ε).1 - a.1‖ ≤ ε := by
  rw [norm_sub_rev]
  have heq : a.1 - (cut a ε).1 =
      cfcₙ (fun t : ℝ => t - max (t - (ε : ℝ)) 0) a.1 := by
    rw [cfcₙ_sub (fun t : ℝ => t) (fun t : ℝ => max (t - (ε : ℝ)) 0) a.1
      (by fun_prop) rfl (by fun_prop) (by simp)]
    simp only [cfcₙ_id' ℝ a.1 a.2.isSelfAdjoint, cut]
  rw [heq]
  apply norm_cfcₙ_le
  intro t ht
  have ht0 := quasispectrum_nonneg_of_nonneg a.1 a.2 t ht
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hm : max (t - (ε : ℝ)) 0 ≤ t := max_le (sub_le_self _ ε.2) ht0
    exact (neg_nonpos.mpr ε.2).trans (sub_nonneg.mpr hm)
  · have hm := le_max_left (t - (ε : ℝ)) 0
    linarith

lemma tendsto_cut_reciprocal (a : Positive A) :
    Tendsto (fun n : ℕ => cut a (1 / (n + 1))) atTop (𝓝 a) := by
  rw [tendsto_subtype_rng, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun _ => norm_cut_sub_le _ _)
  simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end Positive

/-- Lower semicontinuity recovers a trace value from its positive cuts. -/
theorem trace_eq_iSup_positive_cuts (τ : ExtendedTrace A) (a : Positive A) :
    τ a = ⨆ (ε : ℝ≥0) (_ : 0 < ε), τ (Positive.cut a ε) := by
  apply le_antisymm
  · let c := ⨆ (ε : ℝ≥0) (_ : 0 < ε), τ (Positive.cut a ε)
    apply (τ.lowerSemicontinuous.isClosed_preimage c).mem_of_tendsto
        (Positive.tendsto_cut_reciprocal a)
    apply Filter.Eventually.of_forall
    intro n
    change τ (Positive.cut a (1 / (n + 1))) ≤ c
    exact le_iSup_of_le (1 / (n + 1)) (le_iSup_of_le (by positivity) le_rfl)
  · exact iSup_le fun ε => iSup_le fun _ => τ.monotone (Positive.cut_le a ε)


variable {A}

def positiveCut (b : A) (δ : ℝ) : A := cfcₙ (fun t : ℝ => max (t - δ) 0) b

def CuntzSubequivalent (a b : A) : Prop :=
  ∃ v : ℕ → A, Tendsto (fun n => star (v n) * b * v n) atTop (𝓝 a)

/-- A continuous extension of the manuscript's `gδ` away from the nonnegative
spectrum. The denominator is never zero when `δ>0`. -/
def cutTransfer (δ t : ℝ) : ℝ := Real.sqrt (max (t - δ) 0 / max t δ)

lemma cutTransfer_continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (cutTransfer δ) := by
  unfold cutTransfer
  apply Continuous.sqrt
  exact (continuous_id.sub continuous_const |>.max continuous_const).div
    (continuous_id.max continuous_const) (fun t => ne_of_gt (hδ.trans_le (le_max_right t δ)))

lemma cutTransfer_zero {δ : ℝ} (hδ : 0 < δ) : cutTransfer δ 0 = 0 := by
  simp [cutTransfer, max_eq_right hδ.le, max_eq_right (neg_nonpos.mpr hδ.le)]

lemma cutTransfer_sq {δ t : ℝ} (hδ : 0 < δ) :
    cutTransfer δ t * cutTransfer δ t = max (t - δ) 0 / max t δ := by
  exact Real.mul_self_sqrt (div_nonneg (le_max_right _ _) (hδ.le.trans (le_max_right t δ)))

lemma cutTransfer_eq_source (δ t : ℝ) :
    cutTransfer δ t = Real.sqrt (max (t - δ) 0 / t) := by
  by_cases h : δ ≤ t
  · simp [cutTransfer, max_eq_left h]
  · have h' : t - δ ≤ 0 := sub_nonpos.mpr (le_of_not_ge h)
    simp [cutTransfer, max_eq_right h']

lemma cutTransfer_product {δ t : ℝ} (hδ : 0 < δ) :
    cutTransfer δ t * t * cutTransfer δ t = max (t - δ) 0 := by
  rw [mul_right_comm, cutTransfer_sq hδ]
  by_cases h : δ ≤ t
  · rw [max_eq_left h]
    exact div_mul_cancel₀ _ (ne_of_gt (hδ.trans_le h))
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    simp

lemma cutTransfer_bound {δ t : ℝ} (hδ : 0 < δ) :
    cutTransfer δ t * cutTransfer δ t ≤ δ⁻¹ * max (t - δ) 0 := by
  rw [cutTransfer_sq hδ, ← div_eq_inv_mul]
  exact div_le_div_of_nonneg_left (le_max_right _ _) hδ (le_max_right _ _)

lemma cutTransfer_cfc_product {b : A} (hb : 0 ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    let g := cfcₙ (cutTransfer δ) b
    g * b * g = positiveCut b δ := by
  have hc := (cutTransfer_continuous hδ).continuousOn (s := quasispectrum ℝ b)
  have hz := cutTransfer_zero hδ
  have hid : ContinuousOn (fun t : ℝ => t) (quasispectrum ℝ b) := continuous_id.continuousOn
  dsimp only
  calc
    cfcₙ (cutTransfer δ) b * b * cfcₙ (cutTransfer δ) b =
        cfcₙ (cutTransfer δ) b * cfcₙ (fun t : ℝ => t) b * cfcₙ (cutTransfer δ) b := by
      rw [cfcₙ_id' ℝ b]
    _ = cfcₙ (fun t : ℝ => cutTransfer δ t * t * cutTransfer δ t) b := by
      rw [cfcₙ_mul (fun t : ℝ => cutTransfer δ t * t) (cutTransfer δ) b
        (hf := hc.mul hid) (hf0 := by simp [hz]) (hg := hc) (hg0 := hz)]
      rw [cfcₙ_mul (cutTransfer δ) (fun t : ℝ => t) b
        (hf := hc) (hf0 := hz) (hg := hid) (hg0 := rfl)]
    _ = positiveCut b δ := cfcₙ_congr (fun t _ => cutTransfer_product hδ)

lemma cutTransfer_cfc_bound {b : A} {δ : ℝ} (hδ : 0 < δ) :
    let g := cfcₙ (cutTransfer δ) b
    g * g ≤ δ⁻¹ • positiveCut b δ := by
  have hc := (cutTransfer_continuous hδ).continuousOn (s := quasispectrum ℝ b)
  have hz := cutTransfer_zero hδ
  have hcut : ContinuousOn (fun t : ℝ => max (t - δ) 0) (quasispectrum ℝ b) :=
    (continuous_id.sub continuous_const |>.max continuous_const).continuousOn
  have hzcut : max (0 - δ) 0 = 0 := max_eq_right (by linarith)
  dsimp only
  calc
    cfcₙ (cutTransfer δ) b * cfcₙ (cutTransfer δ) b =
        cfcₙ (fun t : ℝ => cutTransfer δ t * cutTransfer δ t) b := by
      rw [cfcₙ_mul (cutTransfer δ) (cutTransfer δ) b
        (hf := hc) (hf0 := hz) (hg := hc) (hg0 := hz)]
    _ ≤ cfcₙ (fun t : ℝ => δ⁻¹ * max (t - δ) 0) b :=
      cfcₙ_mono (fun t _ => cutTransfer_bound hδ)
        (hf := hc.mul hc) (hf0 := by simp [hz])
        (hg := continuousOn_const.mul hcut) (hg0 := by change δ⁻¹ * max (0 - δ) 0 = 0; rw [hzcut, mul_zero])
    _ = δ⁻¹ • positiveCut b δ :=
      cfcₙ_const_mul δ⁻¹ (fun t : ℝ => max (t - δ) 0) b (hf := hcut) (h0 := hzcut)



namespace Positive

/-- Positive conjugation inside the same (possibly nonunital) C*-algebra. -/
def conjugate (x : A) (b : Positive A) : Positive A :=
  ⟨star x * b.1 * x, star_left_conjugate_nonneg b.2 x⟩

end Positive

namespace ExtendedTrace

lemma conjugate_le (τ : ExtendedTrace A) (x : A) (b : Positive A) :
    τ (Positive.conjugate x b) ≤ (‖x * star x‖₊ : ℝ≥0∞) * τ b := by
  let y := CFC.sqrt b.1 * x
  have hs : star (CFC.sqrt b.1) = CFC.sqrt b.1 :=
    (CFC.sqrt_nonneg b.1).isSelfAdjoint.star_eq
  have hy : Positive.starMul y = Positive.conjugate x b := by
    apply Subtype.ext
    dsimp [Positive.starMul, Positive.conjugate, y]
    calc
      star (CFC.sqrt b.1 * x) * (CFC.sqrt b.1 * x) =
          star x * (CFC.sqrt b.1 * CFC.sqrt b.1) * x := by simp only [star_mul, hs, mul_assoc]
      _ = star x * b.1 * x := by rw [CFC.sqrt_mul_sqrt_self _ b.2]
  have hbound : Positive.mulStar y ≤ Positive.scale ‖x * star x‖₊ b := by
    have h := CStarAlgebra.star_left_conjugate_le_norm_smul
      (a := CFC.sqrt b.1) (b := x * star x)
    change y * star y ≤ ‖x * star x‖ • b.1
    simpa only [y, star_mul, hs, mul_assoc, CFC.sqrt_mul_sqrt_self _ b.2] using h
  calc
    τ (Positive.conjugate x b) = τ (Positive.starMul y) := congrArg τ hy.symm
    _ = τ (Positive.mulStar y) := τ.tracial y
    _ ≤ τ (Positive.scale ‖x * star x‖₊ b) := τ.monotone hbound
    _ = _ := τ.map_scale_all _ _

lemma conjugate_finite (τ : ExtendedTrace A) (x : A) (b : Positive A) (hb : τ b < ∞) :
    τ (Positive.conjugate x b) < ∞ :=
  (τ.conjugate_le x b).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hb)

end ExtendedTrace

/-- A necessary finite-domain consequence of positive norm-cut comparison. -/
theorem trace_cut_finite_of_near_finite (τ : ExtendedTrace A) (a b : Positive A)
    (ε : ℝ≥0) (hε : 0 < ε) (hab : ‖a.1 - b.1‖ < ε) (hb : τ b < ∞) :
    τ (Positive.cut a ε) < ∞ := by
  let g := cfcₙ (cutTransfer (ε : ℝ)) a.1
  have hε' : (0 : ℝ) < ε := hε
  have hg : g * a.1 * g = (Positive.cut a ε).1 := cutTransfer_cfc_product a.2 hε'
  have hgpos : 0 ≤ g := cfcₙ_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hgstar : star g = g := hgpos.isSelfAdjoint.star_eq
  have hgbound : g * g ≤ (ε : ℝ)⁻¹ • (Positive.cut a ε).1 := cutTransfer_cfc_bound hε'
  have hraw : (Positive.cut a ε).1 - g * b.1 * g ≤ ‖a.1 - b.1‖ • (g * g) := by
    have h := CStarAlgebra.star_left_conjugate_le_norm_smul
      (a := g) (b := a.1 - b.1) (a.2.isSelfAdjoint.sub b.2.isSelfAdjoint)
    simpa only [hgstar, mul_sub, sub_mul, hg] using h
  have hscaled : ‖a.1 - b.1‖ • (g * g) ≤
      (‖a.1 - b.1‖ / (ε : ℝ)) • (Positive.cut a ε).1 := by
    simpa only [smul_smul, div_eq_mul_inv] using
      smul_le_smul_of_nonneg_left hgbound (norm_nonneg (a.1 - b.1))
  have horder : (1 - ‖a.1 - b.1‖ / (ε : ℝ)) • (Positive.cut a ε).1 ≤ g * b.1 * g := by
    rw [sub_smul, one_smul, sub_le_iff_le_add]
    exact (sub_le_iff_le_add.mp (hraw.trans hscaled)).trans_eq (add_comm _ _)
  have hr : 0 < 1 - ‖a.1 - b.1‖ / (ε : ℝ) :=
    sub_pos.mpr ((div_lt_one hε').mpr hab)
  let r : ℝ≥0 := ⟨1 - ‖a.1 - b.1‖ / (ε : ℝ), hr.le⟩
  have htrace : (r : ℝ≥0∞) * τ (Positive.cut a ε) < ∞ := by
    rw [← τ.map_scale_all]
    apply lt_of_le_of_lt (τ.monotone (show Positive.scale r (Positive.cut a ε) ≤
        Positive.conjugate g b from by
          change (r : ℝ) • (Positive.cut a ε).1 ≤ star g * b.1 * g
          rw [hgstar]
          exact horder))
    exact τ.conjugate_finite g b hb
  by_contra hn
  have ht : τ (Positive.cut a ε) = ∞ := not_lt_top_iff.mp hn
  rw [ht, ENNReal.mul_top (ENNReal.coe_ne_zero.mpr (ne_of_gt (show (0 : ℝ≥0) < r from hr)))] at htrace
  exact lt_irrefl _ htrace


namespace ExtendedTrace

def scale (r : ℝ≥0) (τ : ExtendedTrace A) : ExtendedTrace A where
  toFun a := (r : ℝ≥0∞) * τ a
  map_zero := by rw [τ.map_zero, mul_zero]
  map_add a b := by rw [τ.map_add, mul_add]
  map_scale s hs a := by rw [τ.map_scale s hs]; ac_rfl
  tracial x := by rw [τ.tracial x]
  lowerSemicontinuous :=
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp_lowerSemicontinuous
      τ.lowerSemicontinuous (fun _ _ h => mul_le_mul_of_nonneg_left h bot_le)

@[simp] lemma scale_apply (r : ℝ≥0) (τ : ExtendedTrace A) (a : Positive A) :
    τ.scale r a = (r : ℝ≥0∞) * τ a := rfl


end ExtendedTrace

end TraceConeClassification

end

end OAI
