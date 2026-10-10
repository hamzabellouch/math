import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import OAI.Analysis.FactorGeneration.GroupTrace
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

noncomputable section

namespace Generator

/-! Bounded positive monotone nets have actual least upper bounds in M.
Every displayed vector-trace bound passes to the constructed bound. -/
section
open Filter
open scoped Topology
namespace Tracial

section
open UltrapowerBridge
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]

theorem exists_monotone_positive_limit (a : I → M.toStarSubalgebra)
    (hmono : Monotone (fun i => (a i).val))
    (hpos : ∀ i, 0 ≤ (a i).val) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i, ‖a i‖ ≤ C) (r : ℝ) (htrace : ∀ i, (τ.trace (a i)).re ≤ r) :
    ∃ b : M.toStarSubalgebra, 0 ≤ b.val ∧ ‖b‖ ≤ C ∧
      (∀ i, (a i).val ≤ b.val) ∧
      (∀ c : M.toStarSubalgebra, (∀ i, (a i).val ≤ c.val) → b.val ≤ c.val) ∧
      (τ.trace b).re ≤ r := by
  let ω : Ultrafilter I := Ultrafilter.of atTop
  obtain ⟨T, hT, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val) C hC hbound
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M a T ht⟩
  have hw : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (a i).val) (ω : Filter I)
      (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
  refine ⟨b, ?_, hT, ?_, ?_, ?_⟩
  · exact weakOperator_nonneg_isClosed.mem_of_tendsto hw (Eventually.of_forall hpos)
  · intro i
    apply (weakOperator_lowerBound_isClosed (a i).val).mem_of_tendsto hw
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact hmono hj
  · intro c hc
    exact (weakOperator_upperBound_isClosed c.val).mem_of_tendsto hw (Eventually.of_forall hc)
  · exact le_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (ht τ.vector τ.vector))
      (Eventually.of_forall htrace)

end

/-! Positivity, order, and faithfulness of the actual vector trace, using
ambient operator order throughout. No identification with subtype spectral
order is needed. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem ambient_trace_nonneg (a : M.toStarSubalgebra) (ha : 0 ≤ a.val) :
    0 ≤ (τ.trace a).re :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp ha |>.re_inner_nonneg_right τ.vector

theorem ambient_trace_mono {a b : M.toStarSubalgebra} (hab : a.val ≤ b.val) :
    (τ.trace a).re ≤ (τ.trace b).re := by
  have h := ambient_trace_nonneg τ (b-a) (sub_nonneg.mpr hab)
  change 0 ≤ (inner ℂ τ.vector (b.val τ.vector - a.val τ.vector)).re at h
  simpa only [TracialRepresentation.trace, inner_sub_right, Complex.sub_re, sub_nonneg] using h

theorem ambient_sqrt_mem (a : M.toStarSubalgebra) (ha : 0 ≤ a.val) :
    CFC.sqrt a.val ∈ M.toStarSubalgebra := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed M
  rw [CFC.sqrt_eq_real_sqrt a.val ha, cfcₙ_eq_cfc Real.continuous_sqrt.continuousOn]
  exact cfc_mem (𝕜' := ℂ) Real.sqrt a.property

theorem ambient_eq_zero_of_trace_zero (a : M.toStarSubalgebra)
    (ha : 0 ≤ a.val) (ht : (τ.trace a).re = 0) : a = 0 := by
  let s : M.toStarSubalgebra := ⟨CFC.sqrt a.val, ambient_sqrt_mem a ha⟩
  have hs : star s * s = a := by
    apply Subtype.ext
    change star (CFC.sqrt a.val) * CFC.sqrt a.val = a.val
    rw [(CFC.sqrt_nonneg a.val).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a.val ha]
  have h := congrArg Complex.re (τ.trace_star_mul s)
  rw [hs, ht] at h
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at h
  have hz : τ.norm₂ s = 0 := by nlinarith [sq_nonneg (τ.norm₂ s)]
  have sz := (τ.norm₂_eq_zero_iff s).mp hz
  simpa only [sz, star_zero, mul_zero] using hs.symm

/-- Any lower bound of a uniformly bounded positive sequence whose traces
tend to zero is nonpositive. The sequence need not itself be monotone. -/
theorem ambient_lowerBound_nonpos_of_trace_tendsto_zero
    (b : ℕ → M.toStarSubalgebra) (hpos : ∀ n, 0 ≤ (b n).val)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖b n‖ ≤ C)
    (ht : Tendsto (fun n => (τ.trace (b n)).re) atTop (𝓝 0))
    (c : M.toStarSubalgebra) (hc : ∀ n, c.val ≤ (b n).val) : c.val ≤ 0 := by
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨T, _, hT⟩ := exists_weak_operator_ultralimit ω (fun n => (b n).val) C hC hbound
  let d : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M b T hT⟩
  have hw : Tendsto (fun n => ContinuousLinearMapWOT.ofCLM (b n).val) (ω : Filter ℕ)
      (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr hT
  have hd : 0 ≤ d.val := weakOperator_nonneg_isClosed.mem_of_tendsto hw
    (Eventually.of_forall hpos)
  have hz : (τ.trace d).re = 0 := tendsto_nhds_unique
    (Complex.continuous_re.tendsto _ |>.comp (hT τ.vector τ.vector))
    (ht.mono_left (Ultrafilter.of_le atTop))
  have hcd : c.val ≤ d.val := (weakOperator_lowerBound_isClosed c.val).mem_of_tendsto hw
    (Eventually.of_forall hc)
  simpa only [ambient_eq_zero_of_trace_zero τ d hd hz, ZeroMemClass.coe_zero] using hcd

end Tracial

end

/-! Absolute values in the represented algebra, with ambient order bounds
and the actual trace two-norm. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def ambientAbsoluteValue (a : M.toStarSubalgebra) : M.toStarSubalgebra :=
  ⟨CFC.abs a.val, ambient_sqrt_mem (star a*a) (star_mul_self_nonneg a.val)⟩

theorem ambientAbsoluteValue_nonneg (a : M.toStarSubalgebra) :
    0 ≤ (ambientAbsoluteValue a).val := CFC.abs_nonneg _

theorem ambientAbsoluteValue_norm (a : M.toStarSubalgebra) :
    ‖ambientAbsoluteValue a‖ = ‖a‖ := by
  change ‖CFC.abs a.val‖ = ‖a.val‖
  exact CFC.norm_abs

theorem ambientAbsoluteValue_norm₂ (a : M.toStarSubalgebra) :
    τ.norm₂ (ambientAbsoluteValue a) = τ.norm₂ a := by
  have he : star (ambientAbsoluteValue a)*ambientAbsoluteValue a = star a*a := by
    apply Subtype.ext
    change star (CFC.abs a.val)*CFC.abs a.val = star a.val*a.val
    rw [(CFC.abs_nonneg a.val).isSelfAdjoint.star_eq, CFC.abs_mul_abs]
  have h := congrArg Complex.re (τ.trace_star_mul (ambientAbsoluteValue a))
  rw [he, τ.trace_star_mul] at h
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at h
  nlinarith [show 0 ≤ τ.norm₂ a from norm_nonneg _,
    show 0 ≤ τ.norm₂ (ambientAbsoluteValue a) from norm_nonneg _]

theorem ambientAbsoluteValue_trace_le_norm₂ (a : M.toStarSubalgebra) :
    (τ.trace (ambientAbsoluteValue a)).re ≤ τ.norm₂ a :=
  (Complex.re_le_norm _).trans ((τ.norm_trace_le_norm₂ _).trans_eq
    (ambientAbsoluteValue_norm₂ τ a))

theorem ambient_le_absoluteValue (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a.val) :
    a.val ≤ (ambientAbsoluteValue a).val := by
  apply sub_nonneg.mp
  change 0 ≤ CFC.abs a.val - a.val
  rw [CFC.abs_sub_self a.val ha]
  exact nsmul_nonneg (CFC.negPart_nonneg a.val) 2

theorem ambient_neg_absoluteValue_le (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a.val) :
    -(ambientAbsoluteValue a).val ≤ a.val := by
  have h : 0 ≤ CFC.abs a.val + a.val := by
    rw [CFC.abs_add_self a.val ha]
    exact nsmul_nonneg (CFC.posPart_nonneg a.val) 2
  apply neg_le_iff_add_nonneg.mpr
  change 0 ≤ a.val + CFC.abs a.val
  simpa only [add_comm] using h

theorem norm₂_realPart_le (a : M.toStarSubalgebra) :
    τ.norm₂ (realPart a) ≤ τ.norm₂ a := by
  have he : τ.norm₂ (realPart a) = (1/2 : ℝ) * τ.norm₂ (a+star a) := by
    rw [realPart_apply_coe]
    change ‖(2 : ℝ)⁻¹ • ((a+star a).val τ.vector)‖ = _
    rw [norm_smul]
    norm_num
    rfl
  rw [he]
  have h := τ.norm₂_add_le a (star a)
  rw [τ.norm₂_star] at h
  linarith

theorem norm₂_imaginaryPart_le (a : M.toStarSubalgebra) :
    τ.norm₂ (imaginaryPart a) ≤ τ.norm₂ a := by
  have h := norm₂_realPart_le τ (Complex.I • (-a))
  have hr : (realPart (Complex.I • (-a)) : M.toStarSubalgebra) = imaginaryPart a := by
    rw [smul_neg, map_neg, realPart_I_smul, neg_neg]
  rw [hr, τ.norm₂_smul, Complex.norm_I, one_mul] at h
  have hn : τ.norm₂ (-a) = τ.norm₂ a := norm_neg _
  rwa [hn] at h

end Tracial

/-! The bounded monotone transform a ↦ 1 - (1+a)⁻¹ of positive operators.
Its bounds prepare a construction of decreasing order majorants from small
trace tails. No tail majorant or predual continuity is asserted here. -/
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveResolvent (a : A) : A := cfc (fun t : ℝ => 1 - (1 + t)⁻¹) a

theorem positiveResolvent_continuousOn (a : A) (ha : 0 ≤ a) :
    ContinuousOn (fun t : ℝ => 1 - (1 + t)⁻¹) (spectrum ℝ a) := by
  apply continuousOn_const.sub
  apply (continuousOn_const.add continuousOn_id).inv₀
  intro t ht
  have := spectrum_nonneg_of_nonneg ha ht
  change 1 + t ≠ 0
  linarith

theorem positiveResolvent_eq (a : A) (ha : 0 ≤ a) :
    positiveResolvent a = 1 - Ring.inverse (1 + a) := by
  have hn (t : ℝ) (ht : t ∈ spectrum ℝ a) : 1 + t ≠ 0 := by
    have := spectrum_nonneg_of_nonneg ha ht
    positivity
  have hi : ContinuousOn (fun t : ℝ => (1 + t)⁻¹) (spectrum ℝ a) :=
    (continuousOn_const.add continuousOn_id).inv₀ hn
  rw [positiveResolvent, cfc_sub (fun _ : ℝ => 1) (fun t => (1 + t)⁻¹) a
    continuousOn_const hi,
    cfc_const_one ℝ a, cfc_inv (fun t : ℝ => 1 + t) a hn,
    cfc_const_add (1 : ℝ) (fun t : ℝ => t) a continuousOn_id ha.isSelfAdjoint,
    cfc_id' ℝ a ha.isSelfAdjoint]
  simp only [map_one]

theorem positiveResolvent_nonneg (a : A) (ha : 0 ≤ a) : 0 ≤ positiveResolvent a := by
  apply cfc_nonneg
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg ha ht
  have hi : (1 + t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  linarith

theorem positiveResolvent_le_one (a : A) (ha : 0 ≤ a) : positiveResolvent a ≤ 1 := by
  apply cfc_le_one
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg ha ht
  exact sub_le_self _ (inv_nonneg.mpr (by linarith))

theorem positiveResolvent_mono {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) :
    positiveResolvent a ≤ positiveResolvent b := by
  rw [positiveResolvent_eq a ha, positiveResolvent_eq b (ha.trans hab)]
  apply sub_le_sub_left
  exact CStarAlgebra.ringInverse_le_ringInverse (add_le_add le_rfl hab)
    (isStrictlyPositive_one.add_nonneg ha)

theorem positiveResolvent_le_self (a : A) (ha : 0 ≤ a) : positiveResolvent a ≤ a := by
  calc
    positiveResolvent a ≤ cfc (fun t : ℝ => t) a := by
      apply cfc_mono (hf := positiveResolvent_continuousOn a ha) (hg := continuousOn_id)
      intro t ht
      have ht0 := spectrum_nonneg_of_nonneg ha ht
      have hp : 0 < 1 + t := by linarith
      have hi : 1 - t ≤ (1 + t)⁻¹ := by
        rw [inv_eq_one_div]
        apply (le_div_iff₀ hp).mpr
        nlinarith [sq_nonneg t]
      change 1 - (1 + t)⁻¹ ≤ t
      linarith
    _ = a := cfc_id' ℝ a ha.isSelfAdjoint

theorem half_le_positiveResolvent (a : A) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 / 2 : ℝ) • a ≤ positiveResolvent a := by
  rw [← cfc_const_mul_id (1 / 2 : ℝ) a ha.isSelfAdjoint]
  apply cfc_mono (hf := by fun_prop) (hg := positiveResolvent_continuousOn a ha)
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg ha ht
  have ht1 : t ≤ 1 := (CFC.le_one_iff (R := ℝ) a ha.isSelfAdjoint).mp ha1 t ht
  have hp : 0 < 1 + t := by linarith
  have hi : (1 + t)⁻¹ ≤ 1 - t / 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  linarith

theorem positiveResolvent_norm_le_one (a : A) (ha : 0 ≤ a) : ‖positiveResolvent a‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (positiveResolvent_nonneg a ha)).mpr
    (positiveResolvent_le_one a ha)

end

/-! Decreasing positive order majorants for positive contractions with
summable trace. The finite-tail resolvents and their least upper bounds are
constructed in the actual algebra. -/
open Filter
open scoped Topology BigOperators
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def algebraPositiveResolvent (a : M.toStarSubalgebra) : M.toStarSubalgebra := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed M
  exact ⟨positiveResolvent a.val,
    cfc_mem (𝕜' := ℂ) (fun t : ℝ => 1 - (1+t)⁻¹) a.property⟩

theorem ambient_trace_finset_sum {ι : Type*} (s : Finset ι)
    (a : ι → M.toStarSubalgebra) :
    (τ.trace (∑ k ∈ s, a k)).re = ∑ k ∈ s, (τ.trace (a k)).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [TracialRepresentation.trace]
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, ← ih]
    change (inner ℂ τ.vector ((a k).val τ.vector + (∑ i ∈ s, a i).val τ.vector)).re = _
    rw [inner_add_right, Complex.add_re]
    rfl

theorem ambient_trace_real_smul (r : ℝ) (a : M.toStarSubalgebra) :
    (τ.trace (r • a)).re = r * (τ.trace a).re := by
  change (inner ℂ τ.vector ((r : ℂ) • a.val τ.vector)).re = _
  simp only [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rfl

theorem exists_positive_trace_tail_majorants (a : ℕ → M.toStarSubalgebra)
    (hpos : ∀ n, 0 ≤ (a n).val) (hbound : ∀ n, ‖a n‖ ≤ 1)
    (hsum : Summable (fun n => (τ.trace (a n)).re)) :
    ∃ b : ℕ → M.toStarSubalgebra,
      (∀ n, 0 ≤ (b n).val) ∧ (∀ n, ‖b n‖ ≤ 2) ∧
      Antitone (fun n => (b n).val) ∧ (∀ n, (a n).val ≤ (b n).val) ∧
      (∀ n, (τ.trace (b n)).re ≤ 2 * ∑' k, (τ.trace (a (n+k))).re) ∧
      (∀ c : M.toStarSubalgebra, (∀ n, c.val ≤ (b n).val) → c.val ≤ 0) := by
  classical
  let s (n m : ℕ) : M.toStarSubalgebra := ∑ k ∈ Finset.Ico n m, a k
  have hsval (n m : ℕ) : (s n m).val = ∑ k ∈ Finset.Ico n m, (a k).val := by
    exact map_sum M.toStarSubalgebra.subtype _ _
  have hspos (n m : ℕ) : 0 ≤ (s n m).val := by
    rw [hsval]
    exact Finset.sum_nonneg (fun k _ => hpos k)
  have hsmono (n : ℕ) : Monotone (fun m => (s n m).val) := by
    intro i j hij
    change (s n i).val ≤ (s n j).val
    rw [hsval, hsval]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hij)
      (fun k _ _ => hpos k)
  have hsanti (m : ℕ) : Antitone (fun n => (s n m).val) := by
    intro i j hij
    change (s j m).val ≤ (s i m).val
    rw [hsval, hsval]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico hij le_rfl)
      (fun k _ _ => hpos k)
  let u (n m : ℕ) := algebraPositiveResolvent (s n m)
  have hup (n m : ℕ) : 0 ≤ (u n m).val := positiveResolvent_nonneg _ (hspos n m)
  have huone (n m : ℕ) : (u n m).val ≤ 1 := positiveResolvent_le_one _ (hspos n m)
  have humono (n : ℕ) : Monotone (fun m => (u n m).val) :=
    fun i j hij => positiveResolvent_mono (hspos n i) (hsmono n hij)
  have hut (n m : ℕ) : (τ.trace (u n m)).re ≤ ∑' k, (τ.trace (a (n+k))).re := by
    calc
      (τ.trace (u n m)).re ≤ (τ.trace (s n m)).re :=
        ambient_trace_mono τ (positiveResolvent_le_self _ (hspos n m))
      _ = ∑ k ∈ Finset.range (m-n), (τ.trace (a (n+k))).re := by
        rw [ambient_trace_finset_sum, Finset.sum_Ico_eq_sum_range]
      _ ≤ ∑' k, (τ.trace (a (n+k))).re :=
        Summable.sum_le_tsum _ (fun k _ => ambient_trace_nonneg τ _ (hpos _))
          (by simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr hsum)
  have hc (n : ℕ) := exists_monotone_positive_limit τ (u n) (humono n) (hup n)
    1 zero_le_one (fun m => positiveResolvent_norm_le_one _ (hspos n m))
    (∑' k, (τ.trace (a (n+k))).re) (hut n)
  choose c hcp hcn hcu hcl hct using hc
  have hcanti : Antitone (fun n => (c n).val) := by
    intro i j hij
    apply hcl j
    intro m
    exact (positiveResolvent_mono (hspos j m) (hsanti m hij)).trans (hcu i m)
  let b (n : ℕ) : M.toStarSubalgebra := (2 : ℝ) • c n
  have hbp (n : ℕ) : 0 ≤ (b n).val := by
    change 0 ≤ (2 : ℝ) • (c n).val
    exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hcp n)
  have hbn (n : ℕ) : ‖b n‖ ≤ 2 := by
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left (hcn n) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
      (mul_one 2)
  have hbt (n : ℕ) : (τ.trace (b n)).re ≤ 2 * ∑' k, (τ.trace (a (n+k))).re := by
    rw [ambient_trace_real_smul]
    exact mul_le_mul_of_nonneg_left (hct n) (by norm_num)
  refine ⟨b, hbp, hbn, ?_, ?_, hbt, ?_⟩
  · intro i j hij
    change (2 : ℝ) • (c j).val ≤ (2 : ℝ) • (c i).val
    exact smul_le_smul_of_nonneg_left (hcanti hij) (by norm_num : (0 : ℝ) ≤ 2)
  · intro n
    change (a n).val ≤ (2 : ℝ) • (c n).val
    have ha1 : (a n).val ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hpos n)).mp (hbound n)
    have hn : s n (n+1) = a n := by simp [s]
    have hv := hcu n (n+1)
    change positiveResolvent (s n (n+1)).val ≤ (c n).val at hv
    rw [hn] at hv
    have hh : (1/2 : ℝ) • (a n).val ≤ (c n).val :=
      (half_le_positiveResolvent _ (hpos n) ha1).trans hv
    have hd := smul_le_smul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [smul_smul, show (2 : ℝ) * (1/2) = 1 by norm_num, one_smul] using hd
  · apply ambient_lowerBound_nonpos_of_trace_tendsto_zero τ b hbp 2 (by norm_num) hbn
    apply squeeze_zero (fun n => ambient_trace_nonneg τ _ (hbp n)) hbt
    simpa only [Nat.add_comm, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_sum_nat_add (fun n => (τ.trace (a n)).re)) :
        Tendsto (fun n => 2 * ∑' k, (τ.trace (a (k+n))).re) atTop (𝓝 (2*0)))

end Tracial

end Generator

end

end OAI
