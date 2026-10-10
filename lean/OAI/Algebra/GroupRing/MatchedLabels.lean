import Mathlib
import OAI.Algebra.GroupRing.EntropyStages
import OAI.Algebra.GroupRing.BlockPropagation

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MatchedLabels
open scoped Classical
open OccurrenceMatching StageLabels
variable {Ω B E I A : Type*}
variable (D : Data (Ω := Ω) (B := B) (E := E)) (color : B → I)
variable (h : I → ℕ) (coordinate : ∀ b, D.positions b ≃ Fin (h (color b)))
variable (symbol : E → (A ≃ A))

def graph : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ b, color b = i ∧ color (D.matching.partner b) = j
  symm := ⟨by
    rintro i j ⟨hne,b,hi,hj⟩
    exact ⟨hne.symm,D.matching.partner b,hj,by rw [D.matching.involutive]; exact hi⟩⟩
  loopless := ⟨fun i hh => hh.1 rfl⟩

structure Witness (i j : I) where
  origin : B
  origin_color : color origin = i
  target_color : color (D.matching.partner origin) = j
  side : E
  joined : (D.positions origin).card < 2*(D.slice side origin (D.matching.partner origin)).card ∧
    (D.positions (D.matching.partner origin)).card < 2*(D.slice side origin (D.matching.partner origin)).card ∧
    (D.positions origin).card ≤ (D.slice side origin (D.matching.partner origin)).card+D.error ∧
    (D.positions (D.matching.partner origin)).card ≤
      (D.slice side origin (D.matching.partner origin)).card+D.error

theorem exists_witness {i j : I} (hadj : (graph D color).Adj i j) :
    Nonempty (Witness D color i j) := by
  obtain ⟨hne,b,hi,hj⟩ := hadj
  have hb : D.matching.partner b ≠ b := by
    intro he
    apply hne
    rw [he] at hj
    exact hi.symm.trans hj
  obtain ⟨p,hp⟩ := (D.matched_iff b).mp hb
  have he := D.partner_spec hp
  change D.matching.partner b = p at he
  obtain ⟨e,he'⟩ := hp
  exact ⟨⟨b,hi,hj,e,by simpa only [he] using he'⟩⟩

namespace Witness
variable {D color} {i j : I} (W : Witness D color i j)

def domain : Finset Ω := D.slice W.side W.origin (D.matching.partner W.origin)

def originCoordinate : D.positions W.origin ≃ Fin (h i) :=
  (coordinate W.origin).trans (finCongr (congrArg h W.origin_color))

def targetCoordinate : D.positions (D.matching.partner W.origin) ≃ Fin (h j) :=
  (coordinate (D.matching.partner W.origin)).trans (finCongr (congrArg h W.target_color))

def includeDomain : W.domain ↪ D.positions W.origin where
  toFun x := ⟨x.val,(D.slice_mem.mp x.property).1⟩
  inj' := by
    intro u v he
    apply Subtype.ext
    exact congrArg (fun z : D.positions W.origin => z.val) he

def compareTarget (x : W.domain) : D.positions (D.matching.partner W.origin) :=
  ⟨D.pairing.partner x.val,(D.slice_mem.mp x.property).2.2⟩

def known : Finset (Fin (h i)) :=
  Finset.univ.map (W.includeDomain.trans (W.originCoordinate h coordinate).toEmbedding)

theorem known_card : (W.known h coordinate).card = W.domain.card := by
  simp [known]

def recover (x : W.known h coordinate) : W.domain :=
  Classical.choose (Finset.mem_map.mp x.property)

theorem recover_spec (x : W.known h coordinate) :
    W.originCoordinate h coordinate (W.includeDomain (W.recover h coordinate x)) = x.val :=
  (Classical.choose_spec (Finset.mem_map.mp x.property)).2

def source (x : W.known h coordinate) : Fin (h j) :=
  W.targetCoordinate h coordinate (W.compareTarget (W.recover h coordinate x))

theorem deficit : h i - (W.known h coordinate).card ≤ D.error := by
  rw [W.known_card]
  have hc : h i = (D.positions W.origin).card := by
    simpa using (Fintype.card_congr (W.originCoordinate h coordinate)).symm
  rw [hc]
  exact Nat.sub_le_iff_le_add.mpr (by simpa [domain,Nat.add_comm] using W.joined.2.2.1)

end Witness

def chooseWitness {i j : I} (hadj : (graph D color).Adj i j) : Witness D color i j :=
  Classical.choice (exists_witness D color hadj)

def links : Links (T := A) h where
  graph := graph D color
  known i j := if hadj : (graph D color).Adj i j then
    (chooseWitness D color hadj).known h coordinate else ∅
  source i j x := if hadj : (graph D color).Adj i j then
    (chooseWitness D color hadj).source h coordinate ⟨x.val,by simpa only [dite_eq_left hadj] using x.property⟩
    else False.elim (by simpa only [dite_eq_right hadj,Finset.notMem_empty] using x.property)
  symbol i j := if hadj : (graph D color).Adj i j then symbol (chooseWitness D color hadj).side
    else Equiv.refl A

theorem links_deficit {i j : I} (hadj : (links D color h coordinate symbol).graph.Adj i j) :
    h i - ((links D color h coordinate symbol).known i j).card ≤ D.error := by
  change (graph D color).Adj i j at hadj
  simpa only [links,dite_eq_left hadj] using (chooseWitness D color hadj).deficit h coordinate

/-- Any actual comparison-compatible labeling induces full feasible words on
all blocks, including those not present at a chosen multiplicity stage. -/
theorem links_consistent (letters : Ω → A) (words : (i : I) → Fin (h i) → A)
    (hcompare : ∀ x e, D.side x = some e → letters x = symbol e (letters (D.pairing.partner x)))
    (hwords : ∀ b (x : D.positions b), words (color b) (coordinate b x) = letters x.val) :
    (links D color h coordinate symbol).Consistent words := by
  intro i j hadj k
  change (graph D color).Adj i j at hadj
  let W := chooseWitness D color hadj
  let k' : W.known h coordinate := ⟨k.val,by simpa only [links,dite_eq_left hadj] using k.property⟩
  let x := W.recover h coordinate k'
  have hx := (D.slice_mem.mp x.property).2.1
  have hs := W.recover_spec h coordinate k'
  have word_transport : ∀ b (i : I) (he : color b = i) (y : D.positions b),
      words i ((coordinate b).trans (finCongr (congrArg h he)) y) = letters y.val := by
    intro b i he y
    subst i
    exact hwords b y
  have ho : words i (W.originCoordinate h coordinate (W.includeDomain x)) = letters x.val :=
    word_transport W.origin i W.origin_color (W.includeDomain x)
  have ht : words j (W.targetCoordinate h coordinate (W.compareTarget x)) =
      letters (D.pairing.partner x.val) :=
    word_transport (D.matching.partner W.origin) j W.target_color (W.compareTarget x)
  simp only [links,dite_eq_left hadj]
  change words i k'.val = symbol W.side (words j (W.source h coordinate k'))
  rw [← hs,ho]
  exact (hcompare x.val W.side hx).trans (congrArg (symbol W.side) ht.symm)

end TorsionFreeZeroDivisors.MatchedLabels

namespace TorsionFreeZeroDivisors.BlockConstraints

open scoped BigOperators

/-- A partial parent map strictly decreasing the position index. -/
structure ParentMap (h : ℕ) where
  parent : Fin h → Option (Fin h)
  decreasing : ∀ j i, parent j = some i → i.val < j.val

namespace ParentMap

variable {h : ℕ} (P : ParentMap h) {T : Type*}

/-- Roots are precisely the positions not constrained to earlier positions. -/
def Root := {j : Fin h // P.parent j = none}

def Consistent (w : Fin h → T) : Prop :=
  ∀ j i, P.parent j = some i → w j = w i

/-- The letters at roots determine every consistent word. -/
theorem determined_by_roots {w v : Fin h → T}
    (hw : P.Consistent w) (hv : P.Consistent v)
    (hr : ∀ r : P.Root, w r.val = v r.val) : w = v := by
  funext j
  have aux : ∀ n : ℕ, ∀ j : Fin h, j.val = n → w j = v j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      cases hp : P.parent j with
      | none => exact hr ⟨j, hp⟩
      | some i =>
        rw [hw j i hp, hv j i hp]
        exact ih i.val (hj ▸ P.decreasing j i hp) i rfl
  exact aux j.val j rfl

/-- A forest of equality constraints costs one free letter per root. -/
theorem card_consistent_le [Fintype T] :
    Nat.card {w : Fin h → T // P.Consistent w} ≤
      (Fintype.card T) ^ Nat.card P.Root := by
  classical
  let : Fintype P.Root := inferInstanceAs (Fintype {j : Fin h // P.parent j = none})
  let restriction : {w : Fin h → T // P.Consistent w} → (P.Root → T) :=
    fun w r => w.val r.val
  have hinj : Function.Injective restriction := by
    intro w v he
    apply Subtype.ext
    exact P.determined_by_roots w.property v.property (congrFun he)
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using
    Fintype.card_le_of_injective restriction hinj

end ParentMap

/-- A set of translated positions; the integral shift is positive. -/
structure Translation (h : ℕ) where
  shift : ℕ
  positive : 0 < shift
  domain : Finset (Fin h)
  bounded : ∀ i ∈ domain, i.val + shift < h

namespace Translation

variable {h : ℕ} (D : Translation h)

/-- The image position of a prescribed comparison. -/
def target (i : D.domain) : Fin h := ⟨i.val.val + D.shift, D.bounded i.val i.property⟩

theorem target_injective : Function.Injective D.target := by
  intro i j he
  have hv := congrArg Fin.val he
  dsimp [target] at hv
  apply Subtype.ext
  apply Fin.ext
  omega

noncomputable def parents : ParentMap h where
  parent j := if hj : ∃ i : D.domain, D.target i = j then some hj.choose.val else none
  decreasing j i hp := by
    classical
    split at hp
    next hex =>
      have hei : hex.choose.val = i := Option.some.inj hp
      have he := congrArg Fin.val hex.choose_spec
      dsimp [target] at he
      have ht := D.positive
      have hlt : hex.choose.val.val < j.val :=
        lt_of_lt_of_eq (Nat.lt_add_of_pos_right ht) he
      simpa only [hei] using hlt
    next => simp at hp

theorem root_iff (j : Fin h) :
    D.parents.parent j = none ↔ j ∉ Set.range D.target := by
  classical
  simp [parents, Set.mem_range]

/-- Each distinct translated edge removes exactly one root. -/
theorem card_roots : Nat.card D.parents.Root = h - D.domain.card := by
  classical
  let e : D.parents.Root ≃ {j : Fin h // j ∉ Set.range D.target} :=
    Equiv.subtypeEquivRight (D.root_iff)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hc : Fintype.card {j : Fin h // j ∈ Set.range D.target} = D.domain.card := by
    change Fintype.card (Set.range D.target) = D.domain.card
    rw [← Fintype.card_coe D.domain]
    exact (Fintype.card_congr (Equiv.ofInjective D.target D.target_injective)).symm
  simpa using congrArg (fun k => h - k) hc

/-- Equalities along a nonzero translation form a forest, even without the
additional contiguous-domain hypothesis in the manuscript. -/
theorem word_count {T : Type*} [Fintype T] :
    Nat.card {w : Fin h → T // ∀ i : D.domain, w (D.target i) = w i.val} ≤
      (Fintype.card T) ^ (h - D.domain.card) := by
  classical
  have heq : (fun w : Fin h → T => ∀ i : D.domain, w (D.target i) = w i.val) =
      D.parents.Consistent := by
    funext w
    apply propext
    constructor
    · intro hw j i hp
      dsimp [parents] at hp
      split at hp
      next hex =>
        have hi := Option.some.inj hp
        exact (congrArg w hex.choose_spec.symm).trans ((hw hex.choose).trans (congrArg w hi))
      next => simp at hp
    · intro hw i
      have hp : D.parents.parent (D.target i) = some i.val := by
        dsimp [parents]
        split
        next hex =>
          congr 1
          exact congrArg Subtype.val (D.target_injective hex.choose_spec)
        next hn => exact False.elim (hn ⟨i, rfl⟩)
      exact hw _ _ hp
  rw [heq]
  simpa [D.card_roots] using D.parents.card_consistent_le (T := T)

end Translation

/-- A reflection self-link on an overlapping interval contradicts either
fixed-point-freeness of inversion or the reduced-word condition. Indices are
integers; half-integer manuscript positions have been shifted by 1/2. -/
theorem reflection_impossible {T : Type*} (bar : T → T)
    (hbar : Function.Involutive bar) (hfree : ∀ t, bar t ≠ t)
    (w : ℤ → T) (h reducedLo reducedHi lo hi b : ℤ)
    (hlo : 0 ≤ lo) (hhi : hi < h) (_hne : lo ≤ hi)
    (himagelo : 0 ≤ b - hi) (himagehi : b - lo < h)
    (hlarge : h < 2 * (hi - lo + 1))
    (hredlo : reducedLo ≤ lo) (hredhi : hi ≤ reducedHi)
    (hred : ∀ i : ℤ, reducedLo ≤ i → i + 1 ≤ reducedHi → w (i+1) ≠ bar (w i))
    (hcompare : ∀ i : ℤ, lo ≤ i → i ≤ hi → w i = bar (w (b-i))) : False := by
  have hleft : 2 * lo ≤ b := by omega
  have hright : b ≤ 2 * hi := by omega
  let i := b / 2
  have hrem := Int.emod_nonneg b (by norm_num : (2 : ℤ) ≠ 0)
  have hrem2 := Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 2)
  by_cases heven : b % 2 = 0
  · have hiLo : lo ≤ i := by dsimp [i]; omega
    have hiHi : i ≤ hi := by dsimp [i]; omega
    have hcenter : b - i = i := by dsimp [i]; omega
    have he := hcompare i hiLo hiHi
    rw [hcenter] at he
    exact hfree (w i) he.symm
  · have hiLo : lo ≤ i := by dsimp [i]; omega
    have hiHi : i + 1 ≤ hi := by dsimp [i]; omega
    have hcenter : b - i = i + 1 := by dsimp [i]; omega
    have he := hcompare i hiLo (by omega)
    rw [hcenter] at he
    have hv : w (i+1) = bar (w i) := by
      rw [he, hbar]
    exact hred i (by omega) (by omega) hv

end TorsionFreeZeroDivisors.BlockConstraints

namespace TorsionFreeZeroDivisors.IntervalSelfLinks
open scoped Classical
open BlockConstraints

/-- The literal increasing coordinate on a contiguous block of integer edge
indices (the manuscript's half-integer centers shifted by 1/2). -/
def coordinate (lo hi : ℤ) : (Finset.Ico lo hi) ≃ Fin (hi-lo).toNat where
  toFun q := ⟨(q.val-lo).toNat,by
    have hq := Finset.mem_Ico.mp q.property
    omega⟩
  invFun k := ⟨lo+k.val,by
    apply Finset.mem_Ico.mpr
    have hk := k.isLt
    omega⟩
  left_inv q := by
    apply Subtype.ext
    have hq := Finset.mem_Ico.mp q.property
    dsimp
    omega
  right_inv k := by
    apply Fin.ext
    dsimp
    omega

theorem coordinate_val {lo hi : ℤ} (q : Finset.Ico lo hi) :
    ((coordinate lo hi q).val : ℤ) = q.val-lo := by
  have hq := Finset.mem_Ico.mp q.property
  dsimp [coordinate]
  omega

variable (lo hi a : ℤ) (D : Finset ℤ)
variable (ha : 0 < a) (hD : ∀ q ∈ D, q ∈ Finset.Ico lo hi ∧ q+a ∈ Finset.Ico lo hi)

def domainEmbedding : D ↪ Fin (hi-lo).toNat where
  toFun q := coordinate lo hi ⟨q.val,(hD q.val q.property).1⟩
  inj' := by
    intro q r he
    have hh := (coordinate lo hi).injective he
    exact Subtype.ext (congrArg (fun z : Finset.Ico lo hi => z.val) hh)

def positiveTranslation : Translation (hi-lo).toNat where
  shift := a.toNat
  positive := by omega
  domain := Finset.univ.map (domainEmbedding lo hi a D hD)
  bounded := by
    intro k hk
    obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hk
    have hq := Finset.mem_Ico.mp (hD q.val q.property).1
    have ht := Finset.mem_Ico.mp (hD q.val q.property).2
    change (q.val-lo).toNat+a.toNat < (hi-lo).toNat
    omega

theorem positive_card : (positiveTranslation lo hi a D ha hD).domain.card = D.card := by
  simp [positiveTranslation]

theorem positive_consistent {A : Type*} (w : Fin (hi-lo).toNat → A)
    (hcompare : ∀ q (hq : q ∈ D),
      w (coordinate lo hi ⟨q+a,(hD q hq).2⟩) = w (coordinate lo hi ⟨q,(hD q hq).1⟩))
    (k : (positiveTranslation lo hi a D ha hD).domain) :
    w ((positiveTranslation lo hi a D ha hD).target k) = w k.val := by
  obtain ⟨q,_,hk⟩ := Finset.mem_map.mp k.property
  have ht : (positiveTranslation lo hi a D ha hD).target k =
      coordinate lo hi ⟨q.val+a,(hD q.val q.property).2⟩ := by
    apply Fin.ext
    change k.val.val+a.toNat = (q.val+a-lo).toNat
    rw [← hk]
    change (q.val-lo).toNat+a.toNat = (q.val+a-lo).toNat
    have hh := Finset.mem_Ico.mp (hD q.val q.property).1
    omega
  rw [ht,← hk]
  exact hcompare q.val q.property

/-- Either direction of a nonzero translation yields exactly |D| distinct
forest constraints, without requiring a substring to contain the entire block. -/
theorem translation_representation (a : ℤ) (D : Finset ℤ) (ha : a ≠ 0)
    (hD : ∀ q ∈ D, q ∈ Finset.Ico lo hi ∧ q+a ∈ Finset.Ico lo hi) :
    ∃ tr : Translation (hi-lo).toNat, tr.domain.card = D.card ∧
      ∀ (A : Type*) (w : Fin (hi-lo).toNat → A),
        (∀ q (hq : q ∈ D),
          w (coordinate lo hi ⟨q+a,(hD q hq).2⟩) = w (coordinate lo hi ⟨q,(hD q hq).1⟩)) →
          ∀ k : tr.domain, w (tr.target k) = w k.val := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · let add : ℤ ↪ ℤ := ⟨fun q => q+a,fun _ _ hh => add_right_cancel hh⟩
    let D' := D.map add
    have hD' : ∀ q ∈ D', q ∈ Finset.Ico lo hi ∧ q+(-a) ∈ Finset.Ico lo hi := by
      intro q hq
      obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp hq
      change r+a ∈ Finset.Ico lo hi ∧ r+a+(-a) ∈ Finset.Ico lo hi
      simpa only [add_neg_cancel_right] using And.intro (hD r hr).2 (hD r hr).1
    refine ⟨positiveTranslation lo hi (-a) D' (by omega) hD',?_,?_⟩
    · rw [positive_card]
      exact Finset.card_map _
    · intro A w hw k
      apply positive_consistent lo hi (-a) D' (by omega) hD' w ?_ k
      intro q hq
      obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp hq
      change w (coordinate lo hi ⟨r+a+(-a),_⟩) = w (coordinate lo hi ⟨r+a,_⟩)
      simpa only [add_neg_cancel_right] using (hw r hr).symm
  · exact ⟨positiveTranslation lo hi a D ha hD,positive_card lo hi a D ha hD,
      fun _ w hw => positive_consistent lo hi a D ha hD w hw⟩

/-- Direct reflection obstruction on literal interval coordinates. The reduced
word is the actual block word; no cyclic reduction or external extension is used. -/
theorem reflection_excluded {A : Type*} (bar : A → A)
    (hbar : Function.Involutive bar) (hfree : ∀ x, bar x ≠ x)
    (w : ℤ → A) (L U l u b : ℤ)
    (hl : L ≤ l) (hu : u ≤ U) (_hne : l < u)
    (htl : L ≤ b-(u-1)) (htu : b-l < U)
    (hmass : U-L < 2*(u-l))
    (hred : ∀ q, L ≤ q → q+1 < U → w (q+1) ≠ bar (w q))
    (hcompare : ∀ q, l ≤ q → q < u → w q = bar (w (b-q))) : False := by
  have hleft : 2*l ≤ b := by omega
  have hright : b ≤ 2*(u-1) := by omega
  let i := b/2
  have hrem := Int.emod_nonneg b (by norm_num : (2 : ℤ) ≠ 0)
  have hrem2 := Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 2)
  by_cases heven : b%2 = 0
  · have hi : l ≤ i ∧ i < u := by dsimp [i]; omega
    have hb : b-i=i := by dsimp [i]; omega
    have hh := hcompare i hi.1 hi.2
    rw [hb] at hh
    exact hfree (w i) hh.symm
  · have hi : l ≤ i ∧ i+1 < u := by dsimp [i]; omega
    have hb : b-i=i+1 := by dsimp [i]; omega
    have hh := hcompare i hi.1 (by omega)
    rw [hb] at hh
    apply hred i (by omega) (by omega)
    rw [hh,hbar]

end TorsionFreeZeroDivisors.IntervalSelfLinks

end

end OAI
