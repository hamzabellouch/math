import OAI.Analysis.BoundedHochschild.AbelianPartitions
import OAI.Analysis.BoundedHochschild.Conditional
import OAI.Analysis.BoundedHochschild.CochainLimitDifferential

namespace OAI

/-!
# Norm-one primitives on abelian von Neumann algebras

The abelian case of the classical type-I input is proved directly. Finite
families of projections admit common finite partitions. Their separability
homotopies have norm at most one; a bounded weak-* limit is exact on every
projection, hence everywhere by density of the span of projections.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

section FirstIdentity

variable {M : Type*} [CStarAlgebra M]

lemma mergeInputs_cons_zero {n : ℕ} (p : M) (v : Fin (n + 1) → M) :
    mergeInputs (Fin.cons p v) (0 : Fin (n + 1)) =
      Fin.cons (p * v 0) (fun i : Fin n => v i.succ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs]

lemma mergeInputs_cons_succ {n : ℕ} (p : M) (v : Fin (n + 1) → M)
    (j : Fin n) :
    mergeInputs (Fin.cons p v) j.succ = Fin.cons p (mergeInputs v j) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs, Fin.succ_lt_succ_iff]

lemma differentialValue_cons {n : ℕ} (f : Cochain M (n + 1))
    (p : M) (v : Fin (n + 1) → M) :
    differentialValue f (Fin.cons p v) =
      p * f v - f (Fin.cons (p * v 0) (fun i : Fin n => v i.succ)) -
        differentialValue (f.curryLeft p) v +
        v 0 * f (Fin.cons p (fun i : Fin n => v i.succ)) := by
  rw [differentialValue, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mergeInputs_cons_zero,
    mergeInputs_cons_succ, Fin.val_zero, zero_add, pow_one, neg_smul, one_smul,
    Fin.val_succ]
  have hi : (fun i : Fin (n + 1) => (Fin.cons p v : Fin (n + 2) → M) i.castSucc) =
      Fin.cons p (fun i : Fin n => v i.castSucc) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [hi]
  simp only [differentialValue, ContinuousMultilinearMap.curryLeft_apply]
  have hs (j : Fin n) : (-1 : ℂ) ^ (j.val + 1 + 1) = -((-1 : ℂ) ^ (j.val + 1)) := by
    rw [pow_succ]
    ring
  have hn : (-1 : ℂ) ^ (n + 2) = -((-1 : ℂ) ^ (n + 1)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  simp only [hs, hn, neg_smul, Finset.sum_neg_distrib]
  abel

lemma first_homotopy_identity {n : ℕ} (f : Cochain M (n + 1))
    (hf : ∀ x, differentialValue f x = 0) (p : M) (v : Fin (n + 1) → M) :
    differentialValue (f.curryLeft p) v =
      p * f v - f (Fin.cons (p * v 0) (fun i : Fin n => v i.succ)) +
        v 0 * f (Fin.cons p (fun i : Fin n => v i.succ)) := by
  have h := hf (Fin.cons p v)
  rw [differentialValue_cons] at h
  symm
  apply sub_eq_zero.mp
  convert h using 1
  abel

end FirstIdentity

variable {M : Type*} [CommCStarAlgebra M]

def partitionHomotopy {r n : ℕ} (p : Fin r → M) (f : Cochain M (n + 1)) :
    Cochain M n := ∑ i, centralOutput (p i) (f.curryLeft (p i))

lemma partitionHomotopy_norm {r n : ℕ} (p : Fin r → M)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) (f : Cochain M (n + 1)) :
    ‖partitionHomotopy p f‖ ≤ ‖f‖ := by
  apply norm_sum_supported_cochains p hp horth
    (fun i => centralOutput (p i) (f.curryLeft (p i)))
    (fun i x => by
      simp only [centralOutput_apply, ← mul_assoc, (hp i).isIdempotentElem.eq])
    (fun i x => by
      simp only [centralOutput_apply]
      calc
        (p i * f.curryLeft (p i) x) * p i = (p i * p i) * f.curryLeft (p i) x := by ring
        _ = p i * f.curryLeft (p i) x := by rw [(hp i).isIdempotentElem.eq])
    ‖f‖ (norm_nonneg _) (fun i => ?_) Finset.univ
  refine (norm_centralOutput_le (p i) (hp i).norm_le _).trans ?_
  calc
    ‖f.curryLeft (p i)‖ ≤ ‖f.curryLeft‖ * ‖p i‖ := f.curryLeft.le_opNorm (p i)
    _ ≤ ‖f‖ := by
      rw [ContinuousMultilinearMap.curryLeft_norm]
      exact (mul_le_mul_of_nonneg_left (hp i).norm_le (norm_nonneg _)).trans_eq (mul_one _)

lemma partitionHomotopy_exact {r n : ℕ} (p : Fin r → M)
    (hp : ∀ i, IsStarProjection (p i)) (hsum : ∑ i, p i = 1)
    (q : M) (hq : ∀ i, q * p i = 0 ∨ q * p i = p i)
    (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0)
    (v : Fin n → M) :
    differentialValue (partitionHomotopy p f) (Fin.cons q v) = f (Fin.cons q v) := by
  have hpiece (i : Fin r) :
      differentialValue (centralOutput (p i) (f.curryLeft (p i))) (Fin.cons q v) =
        p i * f (Fin.cons q v) := by
    rw [← central_differential_values (p i) (fun a => mul_comm _ _) (f.curryLeft (p i))
      (centralOutput (p i) (f.curryLeft (p i))) (fun _ => rfl)]
    rw [first_homotopy_identity f hf]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rcases hq i with h | h
    · have hi : p i * q = 0 := (mul_comm _ _).trans h
      rw [hi]
      have hz : f (Fin.cons 0 v) = 0 := by
        change f.curryLeft 0 v = 0
        simp
      rw [hz]
      simp only [sub_zero, mul_add, ← mul_assoc, hi,
        (hp i).isIdempotentElem.eq, zero_mul, add_zero]
    · have hi : p i * q = p i := (mul_comm _ _).trans h
      rw [hi]
      simp only [mul_add, mul_sub, ← mul_assoc, hi,
        (hp i).isIdempotentElem.eq, sub_add_cancel]
  rw [partitionHomotopy, ← differential_apply]
  have hsumd : differential (∑ i, centralOutput (p i) (f.curryLeft (p i))) =
      ∑ i, differential (centralOutput (p i) (f.curryLeft (p i))) := by
    exact map_sum (differentialLinearMap M n) _ _
  rw [hsumd, sum_apply]
  simp only [differential_apply, hpiece, ← Finset.sum_mul, hsum, one_mul]

section Predual

variable {X : Type*} [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The abelian case of the classical input, proved with an explicit norm-one bound. -/
theorem abelian_primitive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  classical
  let P := {q : M // IsStarProjection q}
  choose r p hp horth hsum href using fun S : Finset P => exists_refining_partition S
  let F (S : Finset P) : Cochain M n := partitionHomotopy (p S) f
  have hFn (S : Finset P) : ‖F S‖ ≤ ‖f‖ := partitionHomotopy_norm (p S) (hp S) (horth S) f
  let U : Ultrafilter (Finset P) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset P)) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨g, hgn, ht⟩ := bounded_cochain_ultralimit e U F ‖f‖ (norm_nonneg _) hFn
  have hproj (q : P) (v : Fin n → M) :
      differentialValue g (Fin.cons (q : M) v) = f (Fin.cons (q : M) v) := by
    have he : (fun S => differentialValue (F S) (Fin.cons (q : M) v)) =ᶠ[U]
        (fun _ => f (Fin.cons (q : M) v)) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({q} : Finset P)] with S hS
      exact partitionHomotopy_exact (p S) (hp S) (hsum S) (q : M)
        (href S q (hS (Finset.mem_singleton_self q))) f hf v
    apply predual_tendsto_unique e (predual_tendsto_differential_of_predual e ht _)
    intro z
    exact tendsto_const_nhds.congr' (he.mono fun _ h =>
      congrArg (fun a : M => e.symm a z) h.symm)
  have hall (v : Fin n → M) (a : M) :
      differentialValue g (Fin.cons a v) = f (Fin.cons a v) := by
    let L := firstSliceN (differential g - f) v
    have hspan : Submodule.span ℂ {q : M | IsStarProjection q} ≤ L.ker := by
      apply Submodule.span_le.mpr
      intro q hq
      change L q = 0
      simpa only [L, firstSliceN_apply, sub_apply, differential_apply] using
        sub_eq_zero.mpr (hproj ⟨q, hq⟩ v)
    have hclosed : (Submodule.span ℂ {q : M | IsStarProjection q}).topologicalClosure ≤ L.ker :=
      Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
    rw [HochschildSakai.projection_span_dense e] at hclosed
    have ha := hclosed (Submodule.mem_top : a ∈ (⊤ : Submodule ℂ M))
    change L a = 0 at ha
    exact sub_eq_zero.mp (by
      simpa only [L, firstSliceN_apply, sub_apply, differential_apply] using ha)
  refine ⟨g, hgn, fun x => ?_⟩
  simpa only [Fin.cons_self_tail] using hall (Fin.tail x) (x 0)

end Predual

end KadisonRingrose
end BoundedHochschild

end

end OAI
