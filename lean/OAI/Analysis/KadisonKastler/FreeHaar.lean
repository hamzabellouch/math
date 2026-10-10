import OAI.Analysis.KadisonKastler.ConjugatedDiagonal
import Mathlib.Data.List.ChainOfFn

namespace OAI

/-!
# Free Haar moments imply freeness of the conjugated diagonals

The hypothesis records ordinary alternating centered moments with
nonzero interior Haar powers. The last power may be zero. A telescoping
product identity and traciality convert products from conjugated copies
into exactly these moments. No free-diagonal conclusion is a field of
the hypothesis.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

def haarPower (u : unitary B) (k : ℤ) : B := (u ^ k : unitary B)

@[simp]
theorem haarPower_zero (u : unitary B) : haarPower u 0 = 1 := by
  simp [haarPower]

theorem haarPower_add (u : unitary B) (k l : ℤ) :
    haarPower u (k + l) = haarPower u k * haarPower u l := by
  simp [haarPower, zpow_add]

theorem haarPower_neg (u : unitary B) (k : ℤ) :
    haarPower u (-k) = star (haarPower u k) := by
  simp only [haarPower, zpow_neg, ← Unitary.star_eq_inv, Unitary.coe_star]

@[simp]
theorem haarPower_natCast (u : unitary B) (k : ℕ) :
    haarPower u (k : ℤ) = (u : B) ^ k := by
  simp [haarPower]

private theorem haarPower_sub_mul (u : unitary B) (k l : ℤ) :
    haarPower u (k - l) * haarPower u l = haarPower u k := by
  rw [← haarPower_add, sub_add_cancel]

/-- Standard alternating centered moments of a subalgebra free from a
Haar unitary. Every interior exponent is nonzero; the final Haar letter
is optional. -/
structure FreeHaarMoments (τ : FaithfulTracialState B) (A : StarSubalgebra ℂ B)
    (u : unitary B) : Prop where
  haar_moment : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower u k) = 0
  alternating_moment : ∀ n : ℕ, 0 < n → ∀ (a : Fin n → B) (k : Fin n → ℤ),
    (∀ i, a i ∈ A) → (∀ i, τ.toLinearMap (a i) = 0) →
    (∀ i, i.val + 1 < n → k i ≠ 0) →
    τ.toLinearMap ((List.ofFn (fun i => a i * haarPower u (k i))).prod) = 0

private def differenceLetters (last : ℤ) : List (B × ℤ) → List (B × ℤ)
  | [] => []
  | [x] => [(x.1, x.2 - last)]
  | x :: y :: l => (x.1, x.2 - y.2) :: differenceLetters last (y :: l)

omit [CStarAlgebra B] in
private theorem differenceLetters_first (last : ℤ) (l : List (B × ℤ)) :
    (differenceLetters last l).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => rfl
    | cons y l => simpa only [differenceLetters, List.map_cons] using congrArg (x.1 :: ·) ih

omit [CStarAlgebra B] in
private theorem length_differenceLetters (last : ℤ) (l : List (B × ℤ)) :
    (differenceLetters last l).length = l.length := by
  have h := congrArg List.length (differenceLetters_first last l)
  simpa only [List.length_map] using h

omit [CStarAlgebra B] in
private theorem differenceLetters_property (last : ℤ) (l : List (B × ℤ))
    (P : B → Prop) (hP : ∀ x ∈ l, P x.1) :
    ∀ x ∈ differenceLetters last l, P x.1 := by
  intro x hx
  have hm : x.1 ∈ l.map Prod.fst := by
    rw [← differenceLetters_first last l]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
  simpa only [hxy] using hP y hy

omit [CStarAlgebra B] in
private theorem differenceLetters_nonzero (last : ℤ) (l : List (B × ℤ))
    (hl : l.IsChain (fun x y => x.2 ≠ y.2)) :
    (differenceLetters last l).IsChain (fun x _ => x.2 ≠ 0) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons x l ih =>
    cases l with
    | nil => exact List.isChain_singleton _
    | cons y l =>
      obtain ⟨hxy, htail⟩ := List.isChain_cons_cons.mp hl
      have ht := ih htail
      cases l with
      | nil =>
        simp only [differenceLetters, List.isChain_cons_cons, List.isChain_singleton, and_true]
        exact sub_ne_zero.mpr hxy
      | cons z l =>
        change ((x.1, x.2 - y.2) :: (y.1, y.2 - z.2) ::
          differenceLetters last (z :: l)).IsChain (fun x _ => x.2 ≠ 0)
        exact List.isChain_cons_cons.mpr ⟨sub_ne_zero.mpr hxy, ht⟩

/-- The product telescopes before any moment condition is used. -/
private theorem conjugateProduct_eq (u : unitary B) (last : ℤ) (x : B × ℤ)
    (l : List (B × ℤ)) :
    ((x :: l).map (fun y => haarPower u (-y.2) * y.1 * haarPower u y.2)).prod =
      haarPower u (-x.2) *
        ((differenceLetters last (x :: l)).map (fun y => y.1 * haarPower u y.2)).prod *
          haarPower u last := by
  induction l generalizing x with
  | nil =>
    simp only [differenceLetters, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc, haarPower_sub_mul]
  | cons y l ih =>
    rw [List.map_cons, List.prod_cons, ih y]
    simp only [differenceLetters, List.map_cons, List.prod_cons,
      sub_eq_add_neg, haarPower_add, mul_assoc]

private theorem trace_haar_conjugate (τ : FaithfulTracialState B) (u : unitary B)
    (k : ℤ) (x : B) :
    τ.toLinearMap (haarPower u (-k) * x * haarPower u k) = τ.toLinearMap x := by
  rw [τ.tracial (haarPower u (-k) * x) (haarPower u k), ← mul_assoc,
    ← haarPower_add, add_neg_cancel, haarPower_zero, one_mul]

namespace FreeHaarMoments

variable {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {u : unitary B}

private theorem alternating_list (h : FreeHaarMoments τ A u)
    (l : List (B × ℤ)) (hl : l ≠ [])
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hcentered : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hexp : l.IsChain (fun x _ => x.2 ≠ 0)) :
    τ.toLinearMap ((l.map (fun x => x.1 * haarPower u x.2)).prod) = 0 := by
  have hz := h.alternating_moment l.length (List.length_pos_iff.mpr hl)
    (fun i => (l.get i).1) (fun i => (l.get i).2)
    (fun i => hmem _ (List.get_mem _ _))
    (fun i => hcentered _ (List.get_mem _ _))
    (fun i hi => by simpa using hexp.getElem i.val hi)
  have hlist := congrArg (List.map (fun x : B × ℤ => x.1 * haarPower u x.2))
    (List.ofFn_get l)
  simp only [List.map_ofFn, Function.comp_def] at hlist
  rwa [hlist] at hz

/-- Adjacent distinct conjugating powers turn into the nonzero interior
Haar powers required by the alternating centered moment condition. -/
theorem trace_conjugateProduct_eq_zero (h : FreeHaarMoments τ A u)
    (l : List (B × ℤ)) (hl : l ≠ [])
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hcentered : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hexp : l.IsChain (fun x y => x.2 ≠ y.2)) :
    τ.toLinearMap ((l.map (fun x => haarPower u (-x.2) * x.1 * haarPower u x.2)).prod) = 0 := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons x l =>
    rw [conjugateProduct_eq u x.2 x l, trace_haar_conjugate]
    apply h.alternating_list
    · intro he
      have he' := congrArg List.length he
      rw [length_differenceLetters] at he'
      simp at he'
    · exact differenceLetters_property _ _ (· ∈ A) hmem
    · exact differenceLetters_property _ _ (fun x => τ.toLinearMap x = 0) hcentered
    · exact differenceLetters_nonzero _ _ hexp

/-- Equal-trace diagonal partitions conjugated by distinct powers of a
free Haar unitary form a scalar-free family. -/
theorem scalarFree_conjugatedDiagonal (h : FreeHaarMoments τ A u)
    {r d : ℕ} (e : Fin d → B)
    (hmem : ∀ a, e a ∈ A) (htrace : ∀ a, τ.toLinearMap (e a) = (d : ℂ)⁻¹) :
    ScalarFreeDiagonal τ (conjugatedDiagonal e (u : B) r) := by
  intro n hn position c hposition hc
  let a : Fin n → B := fun i => ∑ j, c i j • e j
  let m : Fin n → ℤ := fun i => (r - 1 - (position i).val : ℕ)
  let l : List (B × ℤ) := List.ofFn (fun i => (a i, m i))
  have ha (i : Fin n) : a i ∈ A := by
    apply A.sum_mem
    intro j _
    exact A.smul_mem (hmem j) _
  have hz (i : Fin n) : τ.toLinearMap (a i) = 0 := by
    simp only [a, map_sum, map_smul, htrace, smul_eq_mul, ← sum_mul, hc, zero_mul]
  have hm (i j : Fin n) (hij : i.val + 1 = j.val) : m i ≠ m j := by
    intro he
    apply hposition i j hij
    apply Fin.ext
    dsimp [m] at he
    have he' : r - 1 - (position i).val = r - 1 - (position j).val := by
      exact_mod_cast he
    have hi := (position i).isLt
    have hj := (position j).isLt
    omega
  have hchain : l.IsChain (fun x y => x.2 ≠ y.2) := by
    apply List.isChain_ofFn.mpr
    intro i hi
    exact hm ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
  have he (i : Fin n) :
      (∑ j, c i j • conjugatedDiagonal e (u : B) r (position i) j) =
        haarPower u (-(m i)) * a i * haarPower u (m i) := by
    simp only [a, m, conjugatedDiagonal, conjugatedCopy, haarPower_neg,
      haarPower_natCast, mul_sum, sum_mul, smul_mul_assoc, mul_smul_comm]
  have ht := h.trace_conjugateProduct_eq_zero l
    (by intro hl; have := congrArg List.length hl; simp [l] at this; omega)
    (by intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact ha i)
    (by intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hz i)
    hchain
  simpa only [l, List.map_ofFn, Function.comp_def, ← he] using ht

end FreeHaarMoments

end

end KadisonKastler

end OAI
