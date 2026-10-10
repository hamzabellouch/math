import OAI.NumberTheory.TwoPoint.Bounds.CRTComparison
import OAI.NumberTheory.TwoPoint.Circuits.FourierCorrection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Exact finite jitter encoding

For `Q = 2^B`, the integer code `⌊(r Q + j)/s⌋`, with `j` uniform in
`{0,…,Q-1}`, has exactly the distribution of the first `B` binary digits
of `(r + U)/s` for uniform `U` in `[0,1)`. This finite construction avoids
continuous auxiliary probability spaces. Jointly uniform residue and
jitter give a uniform code. Decoding can fail for at most `s` jitter values
at each fixed residue, giving the stronger bound `s/Q`.
-/

open Finset

namespace TwoPointCorrelations

/-- Regroup the `s Q` equally likely elementary outcomes into `Q` blocks of
size `s`. -/
def jitterPermutation (s Q : ℕ) : Fin s × Fin Q ≃ Fin Q × Fin s :=
  finProdFinEquiv.trans ((finCongr (Nat.mul_comm s Q)).trans finProdFinEquiv.symm)

/-- Finite version of a uniformly jittered residue, encoded in `Q` cells. -/
def jitterCode {s Q : ℕ} (r : Fin s) (j : Fin Q) : Fin Q :=
  (jitterPermutation s Q (r, j)).1

lemma jitterCode_val {s Q : ℕ} (r : Fin s) (j : Fin Q) :
    (jitterCode r j).val = (j.val + Q * r.val) / s := rfl

/-- Exact averaging identity for uniform residue and independent jitter. -/
lemma jitterCode_sum (s Q : ℕ) (F : Fin Q → ℝ) :
    (∑ r : Fin s, ∑ j : Fin Q, F (jitterCode r j)) =
      (s : ℝ) * ∑ k : Fin Q, F k := by
  rw [← Fintype.sum_prod_type']
  change (∑ x : Fin s × Fin Q,
    (fun y : Fin Q × Fin s => F y.1) (jitterPermutation s Q x)) = _
  rw [(jitterPermutation s Q).sum_comp (fun y : Fin Q × Fin s => F y.1),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]

/-- The induced code kernel sends the uniform residue law to the uniform
code law, exactly. -/
lemma jitterCode_uniform {s Q : ℕ} (hs : 0 < s) (hQ : 0 < Q) (k : Fin Q) :
    (∑ r : Fin s, (1 / (s : ℝ)) * finiteRandomKernel (@jitterCode s Q) r k) =
      1 / (Q : ℝ) := by
  let : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold finiteRandomKernel
  rw [← Finset.mul_sum, ← Finset.sum_div]
  rw [jitterCode_sum s Q (fun z => if z = k then (1 : ℝ) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fintype.card_fin]
  field_simp

/-- Decode the residue from the left endpoint of a code cell. -/
def jitterDecode {s Q : ℕ} (hs : 0 < s) (hQ : 0 < Q) (k : Fin Q) : Fin s :=
  ⟨s * k.val / Q, (Nat.div_lt_iff_lt_mul hQ).mpr
    (Nat.mul_lt_mul_of_pos_left k.isLt hs)⟩

/-- All jitter positions outside the first `s` positions decode correctly. -/
lemma jitterDecode_code {s Q : ℕ} (hs : 0 < s) (hQ : 0 < Q)
    (r : Fin s) (j : Fin Q) (hj : s ≤ j.val) :
    jitterDecode hs hQ (jitterCode r j) = r := by
  apply Fin.ext
  change s * (jitterCode r j).val / Q = r.val
  rw [jitterCode_val]
  have hmod := Nat.mod_lt (j.val + Q * r.val) hs
  have hsplit := Nat.mod_add_div (j.val + Q * r.val) s
  have hmod0 := Nat.zero_le ((j.val + Q * r.val) % s)
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · have hjQ := j.isLt
    nlinarith

/-- Conditional decoding error for every fixed residue, independent of the
law from which that residue was sampled. -/
theorem jitterDecode_error {s Q : ℕ} (hs : 0 < s) (hQ : 0 < Q) (r : Fin s) :
    (∑ j : Fin Q, if jitterDecode hs hQ (jitterCode r j) ≠ r then (1 : ℝ) else 0) /
        (Q : ℝ) ≤ (s : ℝ) / Q := by
  let E : Finset (Fin Q) := Finset.univ.filter
    (fun j => jitterDecode hs hQ (jitterCode r j) ≠ r)
  have hsmall (j : E) : j.val.val < s := by
    have he := (Finset.mem_filter.mp j.property).2
    by_contra h
    exact he (jitterDecode_code hs hQ r j.val (Nat.le_of_not_gt h))
  let emb : E → Fin s := fun j => ⟨j.val.val, hsmall j⟩
  have hinj : Function.Injective emb := by
    intro j k h
    apply Subtype.ext
    apply Fin.ext
    simpa only [emb] using congrArg (fun z : Fin s => z.val) h
  have hcard : E.card ≤ s := by
    simpa using Fintype.card_le_of_injective emb hinj
  have hsum : (∑ j : Fin Q,
      if jitterDecode hs hQ (jitterCode r j) ≠ r then (1 : ℝ) else 0) = (E.card : ℝ) := by
    exact Finset.sum_boole _ _
  rw [hsum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg Q)
  exact_mod_cast hcard

/-- Any fixed bijective labeling of the `2^B` cells by `B` bits suffices:
the decoded equalities are represented by their truth tables. -/
noncomputable def binaryCellEquiv (B : ℕ) : Fin (2 ^ B) ≃ BooleanCube B :=
  Fintype.equivOfCardEq (by simp [BooleanCube])

noncomputable def jitterBits {s B : ℕ} (r : Fin s) (j : Fin (2 ^ B)) : BooleanCube B :=
  binaryCellEquiv B (jitterCode r j)

noncomputable def decodeBits {s B : ℕ} (hs : 0 < s) (x : BooleanCube B) : Fin s :=
  jitterDecode hs (by positivity) ((binaryCellEquiv B).symm x)

@[simp] lemma decode_jitterBits {s B : ℕ} (hs : 0 < s) (r : Fin s) (j : Fin (2 ^ B)) :
    decodeBits hs (jitterBits r j) = jitterDecode hs (by positivity) (jitterCode r j) := by
  simp [decodeBits, jitterBits]

/-- Exact independent uniformity of the encoded bits under uniform residues. -/
lemma jitterBits_uniform {s B : ℕ} (hs : 0 < s) (x : BooleanCube B) :
    (∑ r : Fin s, (1 / (s : ℝ)) * finiteRandomKernel (@jitterBits s B) r x) =
      1 / (2 ^ B : ℕ) := by
  have heq (r : Fin s) : finiteRandomKernel (@jitterBits s B) r x =
      finiteRandomKernel (@jitterCode s (2 ^ B)) r ((binaryCellEquiv B).symm x) := by
    unfold finiteRandomKernel
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have heq : jitterBits r j = x ↔ jitterCode r j = (binaryCellEquiv B).symm x := by
      change binaryCellEquiv B (jitterCode r j) = x ↔ _
      exact (binaryCellEquiv B).eq_symm_apply.symm
    simp only [heq]
  simp_rw [heq]
  exact jitterCode_uniform hs (by positivity) _

end TwoPointCorrelations

end OAI
