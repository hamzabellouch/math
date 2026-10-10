import OAI.Probability.TraceReconstruction.Amplification
import OAI.Probability.TraceReconstruction.Propagation

namespace OAI

/-!
# Restoration

Restoration to honest complete traces, degradation to the requested channel, and exact-length padding.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem approximate_hellinger_transfer (P Q : FiniteLaw α) (K : α→FiniteLaw β)
    (R S : FiniteLaw β) {E V : ℝ} (hH : P.hellingerSq Q ≤ V)
    (hR : R.tv (P.bind K) ≤ E) (hS : S.tv (Q.bind K) ≤ E) (m : ℕ) :
    (R.product m).tv (S.product m) ≤ Real.sqrt ((m:ℝ)*V)+2*m*E := by
  have hmid := (tv_le_sqrt_hellingerSq ((P.bind K).product m) ((Q.bind K).product m)).trans
    (Real.sqrt_le_sqrt ((hellingerSq_product_le _ _ m).trans
      (mul_le_mul_of_nonneg_left ((hellingerSq_bind_le P Q K).trans hH) (Nat.cast_nonneg m))))
  have hr := (tv_product_le R (P.bind K) m).trans (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg m))
  have hs := (tv_product_le S (Q.bind K) m).trans (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg m))
  rw [tv_symm (S.product m)] at hs
  linarith only [hr,hs,hmid,tv_triangle (R.product m) ((P.bind K).product m) (S.product m),
    tv_triangle ((P.bind K).product m) ((Q.bind K).product m) (S.product m)]

end FiniteLaw

/-- A total common finite projection. The fallback is never used by a
 genuine trace of a length-at-most-n input. -/
def boundedTraceProjection (n : ℕ) (w : List Bool) : BoundedTrace n :=
  if h : w∈traceSpace n then ⟨w,h⟩ else ⟨[],mem_traceSpace_of_length_le [] (by simp)⟩

theorem boundedTraceProjection_val {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    (boundedTraceProjection n w).val=w := by
  simp only [boundedTraceProjection,dite_eq_left (mem_traceSpace_of_length_le w hw)]

theorem listTraceLaw_projection (q : ℝ) (hq : q∈Set.Icc 0 1) (w : List Bool)
    (n : ℕ) (hw : w.length≤n) (f : BoundedTrace n→ℝ) :
    (listTraceLaw q hq w n hw).expect f=
      listDeletionExpectation q w (fun z=>f (boundedTraceProjection n z)) := by
  rw [←listTraceLaw_expect q hq w n hw]
  congr 1
  funext t
  congr 1
  apply Subtype.ext
  exact (boundedTraceProjection_val (length_le_of_mem_traceSpace t.property)).symm

theorem ApproximatesTrace.projected_tv {α : Type*} [Fintype α] {q E : ℝ}
    {P : FiniteLaw α} {decode : α→List Bool} {w : List Bool}
    (H : ApproximatesTrace q P decode w E) (hq : q∈Set.Icc 0 1)
    (n : ℕ) (hw : w.length≤n) :
    (listTraceLaw q hq w n hw).tv (P.map (fun a=>boundedTraceProjection n (decode a))) ≤ E := by
  apply FiniteLaw.tv_le_of_tests
  intro f hf
  rw [listTraceLaw_projection,FiniteLaw.expect_map]
  simp only [Function.comp_def]
  have hh := H (fun z=>f (boundedTraceProjection n z)) (fun z=>hf _)
  linarith only [(abs_le.mp hh).1]

/-- Restoration for m independent complete observations, not a single
 concatenated trace. -/
theorem HellingerTracePair.sample_tv {q E V : ℝ} {x y : List Bool}
    (C : HellingerTracePair q x y E V) (hq : q∈Set.Icc 0 1)
    (m n : ℕ) (hx : x.length≤n) (hy : y.length≤n) :
    ((listTraceLaw q hq x n hx).product m).tv ((listTraceLaw q hq y n hy).product m) ≤
      Real.sqrt ((m:ℝ)*V)+2*m*E := by
  let := C.finiteOutcome
  exact FiniteLaw.approximate_hellinger_transfer C.first C.second
    (fun a=>FiniteLaw.pure (boundedTraceProjection n (C.decode a))) _ _ C.bound
    (C.first_simulation.projected_tv hq n hx) (C.second_simulation.projected_tv hq n hy) m

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Independent deletion composes on the actual complete output list. -/
theorem listDeletionExpectation_comp (r t : ℝ) (w : List Bool) (F : List Bool→ℝ) :
    listDeletionExpectation r w (fun z=>listDeletionExpectation t z F)=
      listDeletionExpectation (r+(1-r)*t) w F := by
  induction w generalizing F with
  | nil => rfl
  | cons b w ih =>
    simp only [listDeletionExpectation]
    rw [listDeletionExpectation_linear,ih,ih]
    ring

def extraDeletion (r q : ℝ) : ℝ := (q-r)/(1-r)

theorem extraDeletion_bounds {r q : ℝ} (hr : r<1) (hrq : r≤q) (hq : q≤1) :
    extraDeletion r q∈Set.Icc 0 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hrq) (sub_pos.mpr hr).le
  · apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
    linarith only [hq]

theorem extraDeletion_comp {r q : ℝ} (hr : r<1) : r+(1-r)*extraDeletion r q=q := by
  unfold extraDeletion
  field_simp [(sub_pos.mpr hr).ne']
  ring

theorem listTraceLaw_degrade {r q : ℝ} (hr : r∈Set.Ico 0 1) (hq : q∈Set.Icc 0 1)
    (hrq : r≤q) (w : List Bool) (n : ℕ) (hw : w.length≤n) :
    listTraceLaw q hq w n hw=(listTraceLaw r ⟨hr.1,hr.2.le⟩ w n hw).bind
      (fun z=>listTraceLaw (extraDeletion r q) (extraDeletion_bounds hr.2 hrq hq.2)
        z.val n (length_le_of_mem_traceSpace z.property)) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_bind]
  simp_rw [listTraceLaw_projection]
  rw [listTraceLaw_expect r ⟨hr.1,hr.2.le⟩ w n hw
    (fun z=>listDeletionExpectation (extraDeletion r q) z (fun u=>f (boundedTraceProjection n u))),
    listDeletionExpectation_comp,extraDeletion_comp hr.2]

/-- The requested higher-deletion channel preserves the exact m-sample
 restoration estimate, through one common per-sample Markov kernel. -/
theorem HellingerTracePair.degraded_sample_tv {r q E V : ℝ} {x y : List Bool}
    (C : HellingerTracePair r x y E V) (hr : r∈Set.Ico 0 1) (hq : q∈Set.Icc 0 1)
    (hrq : r≤q) (m n : ℕ) (hx : x.length≤n) (hy : y.length≤n) :
    ((listTraceLaw q hq x n hx).product m).tv ((listTraceLaw q hq y n hy).product m) ≤
      Real.sqrt ((m:ℝ)*V)+2*m*E := by
  let := C.finiteOutcome
  let K : BoundedTrace n→FiniteLaw (BoundedTrace n) := fun z=>
    listTraceLaw (extraDeletion r q) (extraDeletion_bounds hr.2 hrq hq.2)
      z.val n (length_le_of_mem_traceSpace z.property)
  let f := fun z=>boundedTraceProjection n (C.decode z)
  have hP := C.first_simulation.projected_tv ⟨hr.1,hr.2.le⟩ n hx
  have hQ := C.second_simulation.projected_tv ⟨hr.1,hr.2.le⟩ n hy
  have hp := (FiniteLaw.tv_bind_le (listTraceLaw r ⟨hr.1,hr.2.le⟩ x n hx) (C.first.map f) K).trans hP
  have hq' := (FiniteLaw.tv_bind_le (listTraceLaw r ⟨hr.1,hr.2.le⟩ y n hy) (C.second.map f) K).trans hQ
  rw [←listTraceLaw_degrade hr hq hrq x n hx,FiniteLaw.bind_map] at hp
  rw [←listTraceLaw_degrade hr hq hrq y n hy,FiniteLaw.bind_map] at hq'
  exact FiniteLaw.approximate_hellinger_transfer C.first C.second (fun z=>K (f z)) _ _ C.bound hp hq' m

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

def wordOfLength {n : ℕ} (w : List Bool) (h : w.length=n) : Word n := h ▸ w.get

theorem ofFn_wordOfLength {n : ℕ} (w : List Bool) (h : w.length=n) :
    List.ofFn (wordOfLength w h)=w := by
  subst n
  exact List.ofFn_get w

theorem listTraceLaw_ofFn {n : ℕ} (q : ℝ) (hq : q∈Set.Icc 0 1) (x : Word n) :
    listTraceLaw q hq (List.ofFn x) n (by simp)=completeTraceLaw q hq x := by
  apply FiniteLaw.ext_expect
  intro f
  rw [listTraceLaw_projection,listDeletionExpectation_ofFn,completeTraceLaw_mask,FiniteLaw.expect_map]
  unfold FiniteLaw.expect maskLaw
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  apply Subtype.ext
  exact boundedTraceProjection_val (traceOfMask_length_le x a)

theorem listTraceLaw_wordOfLength {n : ℕ} (q : ℝ) (hq : q∈Set.Icc 0 1)
    (w : List Bool) (hw : w.length=n) :
    listTraceLaw q hq w n hw.le=completeTraceLaw q hq (wordOfLength w hw) := by
  have hh := listTraceLaw_ofFn q hq (wordOfLength w hw)
  simpa only [ofFn_wordOfLength] using hh

/-- Literal exact-length padding and degradation of a level witness. -/
theorem ConcreteLevelPair.restored_words {r q N Δ d ω F : ℝ} {hr : r∈Set.Icc 0 1}
    {i k : ℕ} (U : ConcreteLevelPair r hr N Δ d ω F i k)
    (hr1 : r<1) (hq : q∈Set.Icc 0 1) (hrq : r≤q) (hk : 1≤k)
    (n : ℕ) (hN : N≤n) :
    ∃x y : Word n,x≠y ∧ ∀m : ℕ,
      ((completeTraceLaw q hq x).product m).tv ((completeTraceLaw q hq y).product m) ≤
        Real.sqrt ((m:ℝ)*N^(-d))+2*m*U.error := by
  have hlen : U.left.length≤n := by exact_mod_cast U.length_upper.trans hN
  let tail := List.replicate (n-U.left.length) false
  let x := U.left++tail
  let y := U.right++tail
  have hx : x.length=n := by simp only [x,tail,List.length_append,List.length_replicate]; omega
  have hy : y.length=n := by simp only [y,tail,List.length_append,List.length_replicate,←U.equalLength]; omega
  have hxy : x≠y := fun h=>U.different (List.append_cancel_right h)
  let C := (U.oracle.pad hr [] tail).hellinger hk
  refine ⟨wordOfLength x hx,wordOfLength y hy,?_,?_⟩
  · intro hh
    have hh' := congrArg List.ofFn hh
    rw [ofFn_wordOfLength,ofFn_wordOfLength] at hh'
    exact hxy hh'
  · intro m
    have HH := C.degraded_sample_tv ⟨hr.1,hr1⟩ hq hrq m n
      (by simpa only [List.nil_append] using hx.le) (by simpa only [List.nil_append] using hy.le)
    change ((listTraceLaw q hq x n hx.le).product m).tv ((listTraceLaw q hq y n hy.le).product m) ≤ _ at HH
    rw [listTraceLaw_wordOfLength q hq x hx,listTraceLaw_wordOfLength q hq y hy] at HH
    exact HH

end TraceReconstruction

end
end
end
end

end OAI
