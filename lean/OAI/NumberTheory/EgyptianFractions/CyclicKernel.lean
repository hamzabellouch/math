import OAI.NumberTheory.EgyptianFractions.FejerBounds
import OAI.NumberTheory.EgyptianFractions.FourierSecondMoment
import OAI.NumberTheory.EgyptianFractions.CyclicSmoothing

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace Problem337.CyclicSmoothing

lemma conj_stdAddChar {q : ℕ} [NeZero q] (x : ZMod q) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq,
    AddChar.norm_apply]
  simp

lemma stdAddChar_pow {q : ℕ} [NeZero q] (r : ℕ) (x : ZMod q) :
    (ZMod.stdAddChar x) ^ r = ZMod.stdAddChar ((r : ZMod q) * x) := by
  simpa only [nsmul_eq_mul] using (ZMod.stdAddChar.map_nsmul_eq_pow r x).symm

lemma cyclic_power_correlation {q h : ℕ} [NeZero q]
    (hhq : h ≤ q) {r s : ℕ} (hr : r < h) (hs : s < h) :
    (∑ x : ZMod q, (ZMod.stdAddChar x)^r * conj ((ZMod.stdAddChar x)^s)) =
      if r = s then (q : ℂ) else 0 := by
  have hcast : (r : ZMod q) - (s : ZMod q) = 0 ↔ r = s := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (hr.trans_le hhq), Nat.mod_eq_of_lt (hs.trans_le hhq)]
  have hpoint (x : ZMod q) :
      (ZMod.stdAddChar x)^r * conj ((ZMod.stdAddChar x)^s) =
        ZMod.stdAddChar (x * ((r : ZMod q) - (s : ZMod q))) := by
    rw [stdAddChar_pow, stdAddChar_pow, conj_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hpoint]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp [hcast, ZMod.card]

/-- Exact mass of the cyclic Fejer kernel below the modulus. -/
theorem sum_cyclic_kernel {q h : ℕ} [NeZero q] (hh : 0 < h) (hhq : h ≤ q) :
    (∑ x : ZMod q, GeometricKernel.kernel h (ZMod.stdAddChar x)) = (q : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  simp only [GeometricKernel.kernel]
  rw [← Finset.sum_div]
  have hraw : (∑ x : ZMod q, ‖∑ r ∈ Finset.range h, (ZMod.stdAddChar x)^r‖ ^ 2) =
      (h : ℝ) * q := by
    rw [finite_complex_second_moment_identity]
    calc
      (∑ r ∈ Finset.range h, ∑ s ∈ Finset.range h,
          (∑ x : ZMod q, (ZMod.stdAddChar x)^r * conj ((ZMod.stdAddChar x)^s)).re) =
          ∑ r ∈ Finset.range h, ∑ s ∈ Finset.range h,
            (if r = s then (q : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        rw [cyclic_power_correlation hhq (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)]
        split_ifs <;> simp
      _ = ∑ _r ∈ Finset.range h, (q : ℝ) := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [Finset.mem_range.mp hr]
      _ = (h : ℝ) * q := by simp
  rw [hraw]
  field_simp

/-- The kernel normalized for counting measure on `ZMod q`. -/
def normalizedKernel {q : ℕ} [NeZero q] (h : ℕ) (x : ZMod q) : ℝ :=
  GeometricKernel.kernel h (ZMod.stdAddChar x) / (q : ℝ)

lemma normalizedKernel_nonneg {q : ℕ} [NeZero q] (h : ℕ) (x : ZMod q) :
    0 ≤ normalizedKernel h x := by
  exact div_nonneg (GeometricKernel.kernel_nonneg _ _) (Nat.cast_nonneg q)

lemma sum_normalizedKernel {q h : ℕ} [NeZero q] (hh : 0 < h) (hhq : h ≤ q) :
    (∑ x : ZMod q, normalizedKernel h x) = 1 := by
  simp only [normalizedKernel]
  rw [← Finset.sum_div, sum_cyclic_kernel hh hhq]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  exact div_self hq

end Problem337.CyclicSmoothing

end

end OAI
