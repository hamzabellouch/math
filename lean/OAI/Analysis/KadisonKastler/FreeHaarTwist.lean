import OAI.Analysis.KadisonKastler.FreeHaar

namespace OAI

/-!
# Finite word reductions for unitary twists of a free Haar unitary

The reduction splits an uncentered separator into its centered and scalar
parts. A scalar separator is removed only between powers of the same
sign, so their merged exponent is nonzero. These are algebraic trace
arguments, with no additional free-probability input.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

private def leftHaarWord (s : unitary B) (l : List (B × ℤ)) : B :=
  (l.map (fun x => haarPower s x.2 * x.1)).prod

private def rightHaarWord (s : unitary B) (l : List (B × ℤ)) : B :=
  (l.map (fun x => x.1 * haarPower s x.2)).prod

private def shiftedPowers (last : ℤ) : List (B × ℤ) → List (B × ℤ)
  | [] => []
  | [x] => [(x.1, last)]
  | x :: y :: l => (x.1, y.2) :: shiftedPowers last (y :: l)

omit [CStarAlgebra B] in
private theorem shiftedPowers_fst (last : ℤ) (l : List (B × ℤ)) :
    (shiftedPowers last l).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => rfl
    | cons y l => simpa only [shiftedPowers, List.map_cons] using congrArg (x.1 :: ·) ih

omit [CStarAlgebra B] in
private theorem shiftedPowers_property (last : ℤ) (l : List (B × ℤ))
    (P : B → Prop) (h : ∀ x ∈ l, P x.1) :
    ∀ x ∈ shiftedPowers last l, P x.1 := by
  intro x hx
  have hm : x.1 ∈ l.map Prod.fst := by
    rw [← shiftedPowers_fst last l]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
  simpa only [he] using h y hy

omit [CStarAlgebra B] in
private theorem shiftedPowers_nonzero (last : ℤ) (l : List (B × ℤ))
    (h : ∀ x ∈ l.tail, x.2 ≠ 0) :
    (shiftedPowers last l).IsChain (fun x _ => x.2 ≠ 0) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons x l ih =>
    cases l with
    | nil => exact List.isChain_singleton _
    | cons y l =>
      have hy := h y (by simp)
      have ht := ih (fun z hz => h z (List.mem_cons_of_mem y hz))
      cases l with
      | nil =>
        simpa only [shiftedPowers, List.isChain_cons_cons, List.isChain_singleton, and_true]
          using hy
      | cons z l => exact List.isChain_cons_cons.mpr ⟨hy, ht⟩

private theorem shiftedPowers_word (s : unitary B) (last : ℤ) (x : B × ℤ)
    (l : List (B × ℤ)) :
    rightHaarWord s (shiftedPowers last (x :: l)) =
      x.1 * leftHaarWord s l * haarPower s last := by
  induction l generalizing x with
  | nil => simp [rightHaarWord, leftHaarWord, shiftedPowers]
  | cons y l ih =>
    simp only [shiftedPowers, rightHaarWord, List.map_cons, List.prod_cons]
    change (x.1 * haarPower s y.2) * rightHaarWord s (shiftedPowers last (y :: l)) = _
    rw [ih]
    simp only [leftHaarWord, List.map_cons, List.prod_cons, mul_assoc]

namespace FreeHaarMoments

variable {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {s : unitary B}

private theorem trace_rightWord_centered (h : FreeHaarMoments τ A s)
    (l : List (B × ℤ)) (hl : l ≠ [])
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hk : l.IsChain (fun x _ => x.2 ≠ 0)) :
    τ.toLinearMap (rightHaarWord s l) = 0 := by
  have ht := h.alternating_moment l.length (List.length_pos_iff.mpr hl)
    (fun i => (l.get i).1) (fun i => (l.get i).2)
    (fun i => hmem _ (List.get_mem _ _)) (fun i => hz _ (List.get_mem _ _))
    (fun i hi => by simpa using hk.getElem i.val hi)
  have he := congrArg (List.map (fun x : B × ℤ => x.1 * haarPower s x.2))
    (List.ofFn_get l)
  simp only [List.map_ofFn, Function.comp_def] at he
  simpa only [he, rightHaarWord] using ht

private theorem trace_leftWord_centered (h : FreeHaarMoments τ A s)
    (l : List (B × ℤ)) (hl : l ≠ []) (q : ℤ)
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hk : ∀ x ∈ l.tail, x.2 ≠ 0) :
    τ.toLinearMap (leftHaarWord s l * haarPower s q) = 0 := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons x l =>
    have htrace : τ.toLinearMap (leftHaarWord s (x :: l) * haarPower s q) =
        τ.toLinearMap (rightHaarWord s (shiftedPowers (q + x.2) (x :: l))) := by
      rw [shiftedPowers_word]
      change τ.toLinearMap ((haarPower s x.2 * x.1) * leftHaarWord s l * haarPower s q) = _
      rw [mul_assoc (haarPower s x.2) x.1, mul_assoc,
        τ.tracial (haarPower s x.2), mul_assoc, ← haarPower_add]
    rw [htrace]
    apply h.trace_rightWord_centered
    · intro he
      have hh := congrArg (List.map Prod.fst) he
      rw [shiftedPowers_fst] at hh
      simp at hh
    · exact shiftedPowers_property _ _ _ hmem
    · exact shiftedPowers_property _ _ (fun a => τ.toLinearMap a = 0) hz
    · exact shiftedPowers_nonzero _ _ hk

private def SameSignSeparated (q : ℤ) : List (B × ℤ) → Prop
  | [] => True
  | x :: l => x.2 ≠ 0 ∧ (q * x.2 < 0 → τ.toLinearMap x.1 = 0) ∧
      SameSignSeparated x.2 l

private theorem sameSign_merge {q k j : ℤ} (hk : k ≠ 0) (hqk : 0 ≤ q * k) :
    q + k ≠ 0 ∧ ((q + k) * j < 0 → k * j < 0) := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hq : q ≤ 0 := by nlinarith
    constructor
    · omega
    · intro hj
      have hj' : 0 < j := by nlinarith
      nlinarith
  · have hq : 0 ≤ q := by nlinarith
    constructor
    · omega
    · intro hj
      have hj' : j < 0 := by nlinarith
      nlinarith

private theorem separated_merge {q k : ℤ} {l : List (B × ℤ)}
    (hk : k ≠ 0) (hqk : 0 ≤ q * k) (hl : SameSignSeparated (τ := τ) k l) :
    SameSignSeparated (τ := τ) (q + k) l := by
  cases l with
  | nil => trivial
  | cons x l =>
    exact ⟨hl.1, fun hn => hl.2.1 ((sameSign_merge hk hqk).2 hn), hl.2.2⟩

/-- Finite sign reduction: only an uncentered separator between powers
of the same sign is removed in the scalar branch. -/
private theorem trace_signSeparated (h : FreeHaarMoments τ A s)
    (tail : List (B × ℤ)) (pref : List (B × ℤ)) (q : ℤ)
    (hp_mem : ∀ x ∈ pref, x.1 ∈ A)
    (hp_z : ∀ x ∈ pref, τ.toLinearMap x.1 = 0)
    (hp_k : ∀ x ∈ pref.tail, x.2 ≠ 0)
    (hq : q ≠ 0 ∨ pref = [])
    (ht_mem : ∀ x ∈ tail, x.1 ∈ A)
    (ht : SameSignSeparated (τ := τ) q tail)
    (hne : pref ≠ [] ∨ q ≠ 0 ∨ tail ≠ []) :
    τ.toLinearMap (leftHaarWord s pref * haarPower s q * rightHaarWord s tail) = 0 := by
  induction tail generalizing pref q with
  | nil =>
    simp only [rightHaarWord, List.map_nil, List.prod_nil, mul_one]
    by_cases hp : pref = []
    · subst pref
      simpa only [leftHaarWord, List.map_nil, List.prod_nil, one_mul] using
        h.haar_moment q (by simpa using hne)
    · exact h.trace_leftWord_centered pref hp q hp_mem hp_z hp_k
  | cons x tail ih =>
    obtain ⟨hk, hsep, ht⟩ := ht
    have extend (a : B) (ha : a ∈ A) (haz : τ.toLinearMap a = 0) :
        τ.toLinearMap (leftHaarWord s pref * haarPower s q * a *
          haarPower s x.2 * rightHaarWord s tail) = 0 := by
      have hh := ih (pref ++ [(a, q)]) x.2
        (by intro y hy; rcases List.mem_append.mp hy with hy | hy
            · exact hp_mem y hy
            · simpa using (List.mem_singleton.mp hy ▸ ha))
        (by intro y hy; rcases List.mem_append.mp hy with hy | hy
            · exact hp_z y hy
            · simpa using (List.mem_singleton.mp hy ▸ haz))
        (by
          cases pref with
          | nil => simp
          | cons p ps =>
            intro y hy
            rcases List.mem_append.mp hy with hy | hy
            · exact hp_k y hy
            · have he := List.mem_singleton.mp hy
              subst y
              exact hq.resolve_right (by simp))
        (Or.inl hk)
        (fun y hy => ht_mem y (List.mem_cons_of_mem _ hy)) ht
        (Or.inl (by simp))
      simpa only [leftHaarWord, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hh
    by_cases hx : τ.toLinearMap x.1 = 0
    · simpa only [rightHaarWord, List.map_cons, List.prod_cons, mul_assoc] using
        extend x.1 (ht_mem x List.mem_cons_self) hx
    · have hsame : 0 ≤ q * x.2 := le_of_not_gt (fun hn => hx (hsep hn))
      have hsum := (sameSign_merge (j := 0) hk hsame).1
      have hs := ih pref (q + x.2) hp_mem hp_z hp_k (Or.inl hsum)
        (fun y hy => ht_mem y (List.mem_cons_of_mem _ hy))
        (separated_merge hk hsame ht) (Or.inr (Or.inl hsum))
      let a : B := x.1 - τ.toLinearMap x.1 • 1
      have ha : a ∈ A := A.sub_mem (ht_mem x List.mem_cons_self)
        (A.smul_mem A.one_mem _)
      have haz : τ.toLinearMap a = 0 := by
        simp [a, map_sub, map_smul, τ.map_one]
      have hc := extend a ha haz
      have he :
          leftHaarWord s pref * haarPower s q * rightHaarWord s (x :: tail) =
            leftHaarWord s pref * haarPower s q * a * haarPower s x.2 *
              rightHaarWord s tail +
            τ.toLinearMap x.1 • (leftHaarWord s pref * haarPower s (q + x.2) *
              rightHaarWord s tail) := by
        dsimp [a]
        simp only [rightHaarWord, List.map_cons, List.prod_cons, haarPower_add,
          mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, sub_add_cancel,
          mul_assoc]
      rw [he, map_add, map_smul, hc, hs, smul_zero, add_zero]

private def signPower (b : Bool) : ℤ := if b then 1 else -1

private def twistCarry (U : unitary B) : Option Bool → B
  | some true => U
  | _ => 1

private def twistFront (U : unitary B) (b : Bool) : B := if b then 1 else star (U : B)

private theorem twistPower_sign (U : unitary B) (b : Bool) :
    haarPower (s * U) (signPower b) =
      twistFront U b * haarPower s (signPower b) * twistCarry U (some b) := by
  cases b <;> simp [signPower, twistFront, twistCarry, haarPower,
    zpow_neg, ← Unitary.star_eq_inv]

private def expandedAtoms (U : unitary B) : Option Bool → List (B × Bool) → List (B × ℤ)
  | _, [] => []
  | previous, x :: l =>
      (twistCarry U previous * x.1 * twistFront U x.2, signPower x.2) ::
        expandedAtoms U (some x.2) l

private def terminalCarry (U : unitary B) : Option Bool → List (B × Bool) → B
  | previous, [] => twistCarry U previous
  | _, x :: l => terminalCarry U (some x.2) l

private theorem expandedAtoms_word (U : unitary B) (previous : Option Bool)
    (l : List (B × Bool)) :
    twistCarry U previous *
      (l.map (fun x => x.1 * haarPower (s * U) (signPower x.2))).prod =
      rightHaarWord s (expandedAtoms U previous l) * terminalCarry U previous l := by
  induction l generalizing previous with
  | nil => simp [expandedAtoms, terminalCarry, rightHaarWord]
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [twistPower_sign, expandedAtoms, terminalCarry]
    change _ = ((twistCarry U previous * x.1 * twistFront U x.2) *
      haarPower s (signPower x.2) * rightHaarWord s (expandedAtoms U (some x.2) l)) * _
    rw [mul_assoc _ _ (terminalCarry U (some x.2) l), ← ih]
    simp only [mul_assoc]

private theorem twistCarry_mem (U : unitary B) (hU : (U : B) ∈ A) (p : Option Bool) :
    twistCarry U p ∈ A := by
  cases p with
  | none => exact A.one_mem
  | some b => cases b <;> first | exact A.one_mem | exact hU

private theorem twistFront_mem (U : unitary B) (hU : (U : B) ∈ A) (b : Bool) :
    twistFront U b ∈ A := by
  cases b with
  | false => exact star_mem hU
  | true => exact A.one_mem

private theorem expandedAtoms_mem (U : unitary B) (hU : (U : B) ∈ A)
    (previous : Option Bool) (l : List (B × Bool)) (hl : ∀ x ∈ l, x.1 ∈ A) :
    ∀ x ∈ expandedAtoms U previous l, x.1 ∈ A := by
  induction l generalizing previous with
  | nil => simp [expandedAtoms]
  | cons x l ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact A.mul_mem (A.mul_mem (twistCarry_mem U hU previous)
        (hl x List.mem_cons_self)) (twistFront_mem U hU x.2)
    · exact ih (some x.2) (fun z hz => hl z (List.mem_cons_of_mem _ hz)) y hy

private theorem terminalCarry_mem (U : unitary B) (hU : (U : B) ∈ A)
    (previous : Option Bool) (l : List (B × Bool)) : terminalCarry U previous l ∈ A := by
  induction l generalizing previous with
  | nil => exact twistCarry_mem U hU previous
  | cons x l ih => exact ih (some x.2)

private def previousPower : Option Bool → ℤ
  | none => 0
  | some b => signPower b

private theorem twist_separator_centered (U : unitary B) (p : Option Bool) (b : Bool)
    (a : B) (hz : τ.toLinearMap a = 0)
    (hopposite : previousPower p * signPower b < 0) :
    τ.toLinearMap (twistCarry U p * a * twistFront U b) = 0 := by
  cases p with
  | none => norm_num [previousPower] at hopposite
  | some p =>
    cases p <;> cases b <;> norm_num [previousPower, signPower] at hopposite
    · simpa [twistCarry, twistFront] using hz
    · change τ.toLinearMap ((U : B) * a * star (U : B)) = 0
      rw [τ.tracial ((U : B) * a) (star (U : B)), ← mul_assoc,
        Unitary.star_mul_self_of_mem U.property, one_mul, hz]

private theorem expandedAtoms_separated (U : unitary B) (p : Option Bool)
    (l : List (B × Bool))
    (hfirst : ∀ x ∈ l.head?, previousPower p * signPower x.2 < 0 → τ.toLinearMap x.1 = 0)
    (hchain : l.IsChain (fun x y => x.2 ≠ y.2 → τ.toLinearMap y.1 = 0)) :
    SameSignSeparated (τ := τ) (previousPower p) (expandedAtoms U p l) := by
  induction l generalizing p with
  | nil => trivial
  | cons x l ih =>
    refine ⟨by cases x.2 <;> norm_num [signPower], ?_, ?_⟩
    · intro hsign
      exact twist_separator_centered U p x.2 x.1 (hfirst x (by simp) hsign) hsign
    · apply ih (some x.2)
      · intro y hy hsign
        have hxy := hchain.rel_head? hy
        apply hxy
        intro he
        rw [he] at hsign
        have hn : 0 ≤ signPower y.2 * signPower y.2 := mul_self_nonneg _
        exact (not_lt_of_ge hn) hsign
      · exact hchain.tail

/-- A signed expansion with centered sign-change separators has zero
trace even after multiplication by its final coefficient in the base algebra. -/
private theorem trace_signed_atoms (h : FreeHaarMoments τ A s)
    (U : unitary B) (hU : (U : B) ∈ A) (l : List (B × Bool)) (hl : l ≠ [])
    (hmem : ∀ x ∈ l, x.1 ∈ A)
    (hchain : l.IsChain (fun x y => x.2 ≠ y.2 → τ.toLinearMap y.1 = 0))
    (b : B) (hb : b ∈ A) :
    τ.toLinearMap (b * (l.map (fun x => x.1 *
      haarPower (s * U) (signPower x.2))).prod) = 0 := by
  have hsep := expandedAtoms_separated U none l
    (by intro x hx hn; norm_num [previousPower] at hn) hchain
  have hmem' := expandedAtoms_mem U hU none l hmem
  have htail := terminalCarry_mem U hU none l
  have hword := expandedAtoms_word (s := s) U none l
  simp only [twistCarry, one_mul] at hword
  cases he : expandedAtoms U none l with
  | nil => cases l <;> simp [expandedAtoms] at he hl
  | cons x xs =>
    rw [he] at hsep hmem' hword
    have hm : ∀ y ∈ ((terminalCarry U none l * b) * x.1, x.2) :: xs, y.1 ∈ A := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact A.mul_mem (A.mul_mem htail hb) (hmem' x List.mem_cons_self)
      · exact hmem' y (List.mem_cons_of_mem _ hy)
    have hs : SameSignSeparated (τ := τ) 0
        (((terminalCarry U none l * b) * x.1, x.2) :: xs) :=
      ⟨hsep.1, by intro hn; omega, hsep.2.2⟩
    have hz := h.trace_signSeparated (((terminalCarry U none l * b) * x.1, x.2) :: xs)
      [] 0 (by simp) (by simp) (by simp) (Or.inr rfl) hm hs (Or.inr (Or.inr (by simp)))
    simp only [leftHaarWord, List.map_nil, List.prod_nil, haarPower_zero, one_mul] at hz
    rw [hword, ← mul_assoc, τ.tracial]
    simpa only [rightHaarWord, List.map_cons, List.prod_cons, mul_assoc] using hz

private def powerAtoms (a : B) : ℤ → List (B × Bool)
  | .ofNat 0 => []
  | .ofNat (n + 1) => (a, true) :: List.replicate n (1, true)
  | .negSucc n => (a, false) :: List.replicate n (1, false)

private theorem powerAtoms_ne_nil (a : B) (k : ℤ) (hk : k ≠ 0) : powerAtoms a k ≠ [] := by
  cases k with
  | ofNat n => cases n <;> simp_all [powerAtoms]
  | negSucc n => simp [powerAtoms]

private theorem powerAtoms_word (v : unitary B) (a : B) (k : ℤ) (hk : k ≠ 0) :
    ((powerAtoms a k).map (fun x => x.1 * haarPower v (signPower x.2))).prod =
      a * haarPower v k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact (hk rfl).elim
    | succ n =>
      rw [show haarPower v (Int.ofNat (n + 1)) = (v : B) ^ (n + 1) from
        haarPower_natCast v (n + 1)]
      simp [powerAtoms, signPower, List.map_replicate, haarPower, pow_succ', mul_assoc]
  | negSucc n =>
    have hn : haarPower v (Int.negSucc n) = star ((v : B) ^ (n + 1)) := by
      rw [Int.negSucc_eq, show (↑n + 1 : ℤ) = ↑(n + 1) by omega,
        haarPower_neg, haarPower_natCast]
    rw [hn]
    simp only [powerAtoms, List.map_cons, List.prod_cons, List.map_replicate,
      List.prod_replicate, signPower, Bool.false_eq_true, ite_false, one_mul]
    simp only [haarPower, zpow_neg_one, ← Unitary.star_eq_inv, Unitary.coe_star,
      star_pow]
    rw [mul_assoc, ← pow_succ']

private theorem powerAtoms_mem (a : B) (k : ℤ) (ha : a ∈ A) :
    ∀ x ∈ powerAtoms a k, x.1 ∈ A := by
  cases k with
  | ofNat n => cases n <;> simp_all [powerAtoms]
  | negSucc n => simp_all [powerAtoms]

private theorem powerAtoms_head (a : B) (k : ℤ) :
    ∀ x ∈ (powerAtoms a k).head?, x.1 = a := by
  cases k with
  | ofNat n => cases n <;> simp [powerAtoms]
  | negSucc n => simp [powerAtoms]

private theorem powerAtoms_chain (a : B) (k : ℤ) :
    (powerAtoms a k).IsChain (fun x y => x.2 ≠ y.2 → τ.toLinearMap y.1 = 0) := by
  have hc (a : B) (b : Bool) (n : ℕ) :
      ((a, b) :: List.replicate n (1, b)).IsChain
        (fun x y => x.2 ≠ y.2 → τ.toLinearMap y.1 = 0) := by
    induction n generalizing a with
    | zero => exact List.isChain_singleton _
    | succ n ih =>
      rw [List.replicate_succ, List.isChain_cons_cons]
      exact ⟨by simp, ih 1⟩
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact List.isChain_nil
    | succ n => exact hc a true n
  | negSucc n => exact hc a false n

private def allPowerAtoms (l : List (B × ℤ)) : List (B × Bool) :=
  l.flatMap (fun x => powerAtoms x.1 x.2)

private theorem allPowerAtoms_head (l : List (B × ℤ))
    (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0) :
    ∀ x ∈ (allPowerAtoms l).head?, τ.toLinearMap x.1 = 0 := by
  induction l with
  | nil => simp [allPowerAtoms]
  | cons y l ih =>
    by_cases hy : powerAtoms y.1 y.2 = []
    · simpa only [allPowerAtoms, List.flatMap_cons, hy, List.nil_append] using
        ih (fun z hz' => hz z (List.mem_cons_of_mem _ hz'))
    · intro x hx
      have hx' : x ∈ (powerAtoms y.1 y.2).head? := by
        simpa only [allPowerAtoms, List.flatMap_cons, List.head?_append_of_ne_nil _ hy] using hx
      rw [powerAtoms_head _ _ x hx']
      exact hz y List.mem_cons_self

private theorem allPowerAtoms_chain (l : List (B × ℤ))
    (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0) :
    (allPowerAtoms l).IsChain (fun x y => x.2 ≠ y.2 → τ.toLinearMap y.1 = 0) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons x l ih =>
    apply (powerAtoms_chain x.1 x.2).append (ih (fun y hy => hz y (List.mem_cons_of_mem _ hy)))
    intro a ha b hb _
    exact allPowerAtoms_head l (fun y hy => hz y (List.mem_cons_of_mem _ hy)) b hb

private theorem allPowerAtoms_word (v : unitary B) (l : List (B × ℤ))
    (hk : ∀ x ∈ l, x.2 ≠ 0) :
    ((allPowerAtoms l).map (fun x => x.1 * haarPower v (signPower x.2))).prod =
      rightHaarWord v l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [allPowerAtoms, List.flatMap_cons, List.map_append, List.prod_append]
    rw [powerAtoms_word v x.1 x.2 (hk x List.mem_cons_self)]
    change (x.1 * haarPower v x.2) *
      ((allPowerAtoms l).map (fun x => x.1 * haarPower v (signPower x.2))).prod = _
    rw [ih (fun y hy => hk y (List.mem_cons_of_mem _ hy))]
    rfl

private theorem trace_nonzero_twisted_powers (h : FreeHaarMoments τ A s)
    (U : unitary B) (hU : (U : B) ∈ A) (l : List (B × ℤ)) (hl : l ≠ [])
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hk : ∀ x ∈ l, x.2 ≠ 0) (b : B) (hb : b ∈ A) :
    τ.toLinearMap (b * rightHaarWord (s * U) l) = 0 := by
  have hne : allPowerAtoms l ≠ [] := by
    cases l with
    | nil => exact (hl rfl).elim
    | cons x l =>
      intro hnil
      have he : powerAtoms x.1 x.2 = [] := (List.append_eq_nil_iff.mp hnil).1
      exact powerAtoms_ne_nil x.1 x.2 (hk x List.mem_cons_self) he
  have hm : ∀ x ∈ allPowerAtoms l, x.1 ∈ A := by
    intro x hx
    obtain ⟨y, hy, hx⟩ := List.mem_flatMap.mp hx
    exact powerAtoms_mem y.1 y.2 (hmem y hy) x hx
  have htrace := h.trace_signed_atoms U hU (allPowerAtoms l) hne hm
    (allPowerAtoms_chain l hz) b hb
  rwa [allPowerAtoms_word (s * U) l hk] at htrace

private theorem trace_twisted_power (h : FreeHaarMoments τ A s)
    (U : unitary B) (hU : (U : B) ∈ A) (k : ℤ) (hk : k ≠ 0) :
    τ.toLinearMap (haarPower (s * U) k) = 0 := by
  have ht := h.trace_signed_atoms U hU (powerAtoms 1 k) (powerAtoms_ne_nil 1 k hk)
    (powerAtoms_mem 1 k A.one_mem) (powerAtoms_chain 1 k) 1 A.one_mem
  simpa only [powerAtoms_word (s * U) 1 k hk, one_mul] using ht

omit [CStarAlgebra B] in
private theorem nonzero_before_last (l : List (B × ℤ)) (x : B × ℤ)
    (hl : (l ++ [x]).IsChain (fun a _ => a.2 ≠ 0)) : ∀ y ∈ l, y.2 ≠ 0 := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have hy : y.2 ≠ 0 := by
      cases l with
      | nil => exact (List.isChain_cons_cons.mp hl).1
      | cons z l => exact (List.isChain_cons_cons.mp hl).1
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · exact ih hl.tail z hz

private theorem trace_alternating_twist_list (h : FreeHaarMoments τ A s)
    (U : unitary B) (hU : (U : B) ∈ A) (l : List (B × ℤ)) (hl : l ≠ [])
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hk : l.IsChain (fun x _ => x.2 ≠ 0)) :
    τ.toLinearMap (rightHaarWord (s * U) l) = 0 := by
  rcases List.eq_nil_or_concat' l with hnil | ⟨l, x, rfl⟩
  · exact (hl hnil).elim
  have hki := nonzero_before_last l x hk
  by_cases hx : x.2 = 0
  · have he : rightHaarWord (s * U) (l ++ [x]) = rightHaarWord (s * U) l * x.1 := by
      simp only [rightHaarWord, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, hx, haarPower_zero, mul_one]
    rw [he]
    by_cases hlnil : l = []
    · subst l
      simpa only [rightHaarWord, List.map_nil, List.prod_nil, one_mul] using hz x (by simp)
    · rw [τ.tracial]
      exact h.trace_nonzero_twisted_powers U hU l hlnil
        (fun y hy => hmem y (List.mem_append_left _ hy))
        (fun y hy => hz y (List.mem_append_left _ hy)) hki x.1 (hmem x (by simp))
  · have hkall : ∀ y ∈ l ++ [x], y.2 ≠ 0 := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hki y hy
      · simpa only [List.mem_singleton.mp hy] using hx
    simpa only [one_mul] using
      h.trace_nonzero_twisted_powers U hU (l ++ [x]) hl hmem hz hkall 1 A.one_mem

/-- Multiplying a free Haar unitary on the right by any unitary of the
base algebra preserves its Haar and alternating centered moments. -/
theorem mul_right (h : FreeHaarMoments τ A s) (U : unitary B) (hU : (U : B) ∈ A) :
    FreeHaarMoments τ A (s * U) where
  haar_moment k hk := h.trace_twisted_power U hU k hk
  alternating_moment n hn a k hmem hz hk := by
    let l : List (B × ℤ) := List.ofFn (fun i => (a i, k i))
    have hm : ∀ x ∈ l, x.1 ∈ A := by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hmem i
    have hc : ∀ x ∈ l, τ.toLinearMap x.1 = 0 := by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hz i
    have hi : l.IsChain (fun x _ => x.2 ≠ 0) := by
      apply List.isChain_ofFn.mpr
      intro i hi
      exact hk ⟨i, by omega⟩ hi
    have ht := h.trace_alternating_twist_list U hU l
      (by intro he; have := congrArg List.length he; simp [l] at this; omega) hm hc hi
    simpa only [l, rightHaarWord, List.map_ofFn, Function.comp_def] using ht

end FreeHaarMoments

end

end KadisonKastler

end OAI
