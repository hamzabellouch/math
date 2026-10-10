import Mathlib
import OAI.GroupTheory.BooneHigman.ActionEnvelope
import OAI.GroupTheory.FiniteType.BinaryPrefixOperators
import OAI.GroupTheory.FiniteType.TwistedBrin

namespace OAI


namespace BinaryPrefixOperators.Arithmetic

abbrev Word := List (Fin 2)
abbrev Pair := Word × Word

variable (K : Type*) [CommRing K]
noncomputable section

def insertion : Word → algebra K
  | [] => 1
  | i :: w => l K i * insertion w

def deletion : Word → algebra K
  | [] => 1
  | i :: w => deletion w * r K i

@[simp] theorem prefix_nil : insertion K [] = 1 := rfl
@[simp] theorem prefix_cons (i : Fin 2) (w : Word) :
    insertion K (i::w) = l K i * insertion K w := rfl
@[simp] theorem deletion_nil : deletion K [] = 1 := rfl
@[simp] theorem deletion_cons (i : Fin 2) (w : Word) :
    deletion K (i::w) = deletion K w * r K i := rfl

@[simp] theorem prefix_append (v w : Word) : insertion K (v++w) = insertion K v * insertion K w := by
  induction v <;> simp [*, mul_assoc]
@[simp] theorem deletion_append (v w : Word) :
    deletion K (v++w) = deletion K w * deletion K v := by
  induction v <;> simp [*, mul_assoc]

@[simp] theorem prefix_single (w : Word) (x : Stream' (Fin 2)) (a : K) :
    (insertion K w : Module.End K (Space K)) (Finsupp.single x a) =
      Finsupp.single (w ++ₛ x) a := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change left K i ((insertion K w : Module.End K (Space K)) (Finsupp.single x a)) = _
    rw [ih, left_single]
    rfl

@[simp] theorem deletion_single (w : Word) (x : Stream' (Fin 2)) (a : K) :
    (deletion K w : Module.End K (Space K)) (Finsupp.single x a) =
      if x.take w.length = w then Finsupp.single (x.drop w.length) a else 0 := by
  induction w generalizing x with
  | nil => simp [deletion]
  | cons i w ih =>
    change (deletion K w : Module.End K (Space K)) (right K i (Finsupp.single x a)) = _
    rw [right_single]
    by_cases hx : x.head = i
    · rw [ite_eq_left hx, ih]
      simp only [List.length_cons, Stream'.take_succ, List.cons.injEq, hx, true_and,
        Stream'.drop_succ]
    · rw [ite_eq_right hx, map_zero]
      simp [Stream'.take_succ, hx]

def replacement (p : Pair) : algebra K := insertion K p.1 * deletion K p.2

@[simp] theorem replacement_single (p : Pair) (x : Stream' (Fin 2)) (a : K) :
    (replacement K p : Module.End K (Space K)) (Finsupp.single x a) =
      if x.take p.2.length = p.2 then Finsupp.single (p.1 ++ₛ x.drop p.2.length) a else 0 := by
  change (insertion K p.1 : Module.End K (Space K))
    ((deletion K p.2 : Module.End K (Space K)) (Finsupp.single x a)) = _
  rw [deletion_single]
  split <;> simp [*]

theorem replacement_domain (v w t : Word) (x : Stream' (Fin 2)) (a : K)
    (hw : w.length = t.length) :
    (replacement K (v,w) : Module.End K (Space K)) (Finsupp.single (t ++ₛ x) a) =
      if w = t then Finsupp.single (v ++ₛ x) a else 0 := by
  rw [replacement_single]
  simp only [hw, Stream'.take_append_of_le_length _ _ _ (Nat.le_refl _), List.take_length,
    Stream'.drop_append_stream]
  by_cases h : w=t <;> simp [h, Ne.symm]

theorem split_replacement (v w : Word) :
    replacement K (v,w) = replacement K (v++[0],w++[0]) +
      replacement K (v++[1],w++[1]) := by
  simp only [replacement, prefix_append, deletion_append, prefix_cons, prefix_nil,
    deletion_cons, deletion_nil, mul_one, one_mul]
  calc insertion K v * deletion K w =
      insertion K v * (l K 0 * r K 0 + l K 1 * r K 1) * deletion K w := by
        rw [l_r_partition, mul_one]
    _ = _ := by noncomm_ring

def marker (L : ℕ) : Stream' (Fin 2) := fun n => if n=L then 1 else 0

theorem marker_after {L n : ℕ} (h : L < n) : marker L n = 0 := by
  simp [marker, Nat.ne_of_gt h]

theorem marker_separates (L : ℕ) {v w : Word} (hv : v.length ≤ L) (hw : w.length ≤ L)
    (h : v ++ₛ marker L = w ++ₛ marker L) : v=w := by
  have hlen : v.length = w.length := by
    have no_lt : ∀ (a b : Word), a.length ≤ L → b.length ≤ L →
        a ++ₛ marker L = b ++ₛ marker L → ¬ a.length < b.length := by
      intro a b ha hb he hab
      have ht := congrArg (fun s : Stream' (Fin 2) => s.get (b.length + L)) he
      have hi : b.length + L = a.length + (b.length + L - a.length) := by omega
      rw [Stream'.get_append_right, hi, Stream'.get_append_right] at ht
      have hh : L < b.length + L - a.length := by omega
      change marker L (b.length + L - a.length) = marker L L at ht
      simp [marker, Nat.ne_of_gt hh] at ht
    exact Nat.le_antisymm (Nat.le_of_not_gt (no_lt w v hw hv h.symm))
      (Nat.le_of_not_gt (no_lt v w hv hw h))
  exact Stream'.append_left_injective _ _ _ _ h hlen

def evaluate : (Pair →₀ K) →ₗ[K] algebra K :=
  Finsupp.linearCombination K (replacement K)

@[simp] theorem evaluate_single (p : Pair) (a : K) :
    evaluate K (Finsupp.single p a) = a • replacement K p := by
  simp [evaluate]

theorem coefficient_test (p : Pair →₀ K) (m L : ℕ)
    (hm : ∀ q ∈ p.support, q.2.length = m)
    (hL : ∀ q ∈ p.support, q.1.length ≤ L)
    (v w : Word) (hv : v.length ≤ L) (hw : w.length = m) :
    ((evaluate K p : Module.End K (Space K))
      (Finsupp.single (w ++ₛ marker L) 1)) (v ++ₛ marker L) = p (v,w) := by
  classical
  have hs : evaluate K p = p.sum (fun q a => a • replacement K q) := rfl
  rw [hs]
  change ((algebra K).val (∑ q ∈ p.support, p q • replacement K q))
    (Finsupp.single (w ++ₛ marker L) 1) (v ++ₛ marker L) = _
  simp only [map_sum, map_smul]
  simp only [LinearMap.sum_apply, Finsupp.finsetSum_apply, LinearMap.smul_apply,
    Finsupp.smul_apply, smul_eq_mul]
  apply (Finset.sum_congr rfl (fun q hq => ?_)).trans
    (show (∑ q ∈ p.support, (Finsupp.single q (p q)) (v,w)) = p (v,w) from by
      rw [← Finsupp.finsetSum_apply]
      exact congrArg (fun a : Pair →₀ K => a (v,w)) (Finsupp.sum_single p))
  change p q * (((replacement K q : Module.End K (Space K)))
    (Finsupp.single (w ++ₛ marker L) 1)) (v ++ₛ marker L) = _
  rw [replacement_domain K _ _ _ _ _ ((hm _ hq).trans hw.symm)]
  have hsep : q.1 ++ₛ marker L = v ++ₛ marker L ↔ q.1 = v :=
    ⟨marker_separates L (hL q hq) hv, by rintro rfl; rfl⟩
  by_cases hqw : q.2 = w
  · simp only [ite_eq_left hqw, Finsupp.single_apply, hsep]
    by_cases hqv : q.1 = v
    · simp [hqv, hqw, Prod.ext_iff]
    · simp [hqv, Prod.ext_iff]
  · simp [hqw, Prod.ext_iff]

theorem evaluate_eq_zero_of_depth (p : Pair →₀ K) (m : ℕ)
    (hm : ∀ q ∈ p.support, q.2.length = m) : evaluate K p = 0 ↔ p=0 := by
  classical
  constructor
  · intro hz
    let L := p.support.sup (fun q => q.1.length)
    have hL : ∀ q ∈ p.support, q.1.length ≤ L := fun q hq => Finset.le_sup (f := fun q : Pair => q.1.length) hq
    apply Finsupp.ext
    intro q
    by_cases hq : q ∈ p.support
    · have ht := coefficient_test K p m L hm hL q.1 q.2 (hL q hq) (hm q hq)
      rw [hz] at ht
      simpa only [Subalgebra.coe_zero, LinearMap.zero_apply, Finsupp.zero_apply] using ht.symm
    · exact Finsupp.notMem_support_iff.mp hq
  · rintro rfl
    exact map_zero _

def subdivide : ℕ → Pair → (Pair →₀ K)
  | 0, p => Finsupp.single p 1
  | n+1, (v,w) => subdivide n (v++[0],w++[0]) + subdivide n (v++[1],w++[1])

@[simp] theorem evaluate_subdivide (n : ℕ) (p : Pair) :
    evaluate K (subdivide K n p) = replacement K p := by
  induction n generalizing p with
  | zero => simp [subdivide]
  | succ n ih =>
    rcases p with ⟨v,w⟩
    rw [subdivide, map_add, ih, ih, ← split_replacement]

theorem subdivide_depth (n : ℕ) (p q : Pair) (h : q ∈ (subdivide K n p).support) :
    q.2.length = p.2.length + n := by
  induction n generalizing p with
  | zero =>
    have hq := ((Finsupp.mem_support_single _ _ _).mp h).1
    simp [hq]
  | succ n ih =>
    rcases p with ⟨v,w⟩
    rw [subdivide] at h
    rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
    · have hh := ih _ h
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · have hh := ih _ h
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

def uniform (m : ℕ) : (Pair →₀ K) →ₗ[K] (Pair →₀ K) :=
  Finsupp.linearCombination K (fun p => subdivide K (m-p.2.length) p)

@[simp] theorem uniform_single (m : ℕ) (p : Pair) (a : K) :
    uniform K m (Finsupp.single p a) = a • subdivide K (m-p.2.length) p := by
  simp [uniform]

@[simp] theorem evaluate_uniform (m : ℕ) (p : Pair →₀ K) :
    evaluate K (uniform K m p) = evaluate K p := by
  have he : (evaluate K).comp (uniform K m) = evaluate K := by
    apply Finsupp.lhom_ext
    intro q a
    simp [LinearMap.comp_apply]
  exact LinearMap.congr_fun he p

theorem uniform_depth (m : ℕ) (p : Pair →₀ K)
    (hm : ∀ q ∈ p.support, q.2.length ≤ m) :
    ∀ q ∈ (uniform K m p).support, q.2.length = m := by
  let V : Submodule K (Pair →₀ K) := Finsupp.supported K K {q | q.2.length = m}
  change uniform K m p ∈ V
  change (∑ q ∈ p.support, p q • subdivide K (m - q.2.length) q) ∈ V
  apply Submodule.sum_mem
  intro q hq
  apply Submodule.smul_mem
  intro t ht
  exact (subdivide_depth K _ q t ht).trans (Nat.add_sub_of_le (hm q hq))

def domainDepth (p : Pair →₀ K) : ℕ := p.support.sup (fun q => q.2.length)

theorem finite_zero_test (p : Pair →₀ K) :
    evaluate K p = 0 ↔ uniform K (domainDepth K p) p = 0 := by
  rw [← evaluate_eq_zero_of_depth K _ (domainDepth K p)
    (uniform_depth K _ p (fun q hq => Finset.le_sup (f := fun q : Pair => q.2.length) hq)),
    evaluate_uniform]

end
end BinaryPrefixOperators.Arithmetic

end OAI
