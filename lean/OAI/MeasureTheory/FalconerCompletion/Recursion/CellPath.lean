import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Recursion.BlockDepth

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
abbrev CellPath (d : ℕ) := List (Fin d → Bool)
variable {d : ℕ}

def dyadicPaths {d : ℕ} : ℕ → Finset (CellPath d)
  | 0 => {[]}
  | n+1 => Finset.univ.biUnion fun a : Fin d → Bool =>
      (dyadicPaths n).image (List.cons a)

@[simp] theorem mem_dyadicPaths (n : ℕ) (p : CellPath d) :
    p ∈ dyadicPaths n ↔ p.length = n := by
  induction n generalizing p with
  | zero => simp [dyadicPaths]
  | succ n ih =>
    cases p with
    | nil => simp [dyadicPaths]
    | cons a p => simp [dyadicPaths, ih]

lemma dyadicPaths_card_le (N : ℕ) : (dyadicPaths (d := d) N).card ≤ (2^d)^N := by
  classical
  induction N with
  | zero => simp [dyadicPaths]
  | succ N ih =>
    calc
      _ ≤ ∑ a ∈ (Finset.univ : Finset (Fin d → Bool)),
        ((dyadicPaths N).image (List.cons a)).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ (Finset.univ : Finset (Fin d → Bool)), (2^d)^N :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le.trans ih)
      _ = _ := by simp [pow_succ,Nat.mul_comm]

noncomputable def classLeaves (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (T : List ℕ) : Finset (CellPath d) := by
  classical
  exact L.filter (F · =T)

noncomputable def labeledChildren (L : Finset (CellPath d)) (f : (CellPath d) → List ℕ)
    (a b : ℕ) (p : (CellPath d)) : Finset (CellPath d) := by
  classical
  exact (L.filter fun q => q.take a = p.take a ∧ f q = f p).image (List.take b)

noncomputable def extendLabel (L : Finset (CellPath d)) (a b : ℕ)
    (f : (CellPath d) → List ℕ) (p : (CellPath d)) : List ℕ :=
  Nat.log 2 (labeledChildren L f a b p).card :: f p

noncomputable def upwardLabels (L : Finset (CellPath d)) :
    List (ℕ × ℕ) → ((CellPath d) → List ℕ) → (CellPath d) → List ℕ
  | [], f => f
  | (a,b) :: steps, f => upwardLabels L steps (extendLabel L a b f)

theorem take_eq_of_take_eq {p q : (CellPath d)} {a c : ℕ}
    (hc : c ≤ a) (h : p.take a = q.take a) : p.take c = q.take c := by
  have := congrArg (List.take c) h
  simpa only [List.take_take, Nat.min_eq_left hc] using this

theorem labeledChildren_eq {L : Finset (CellPath d)} {f : (CellPath d) → List ℕ}
    {a b : ℕ} {p q : (CellPath d)} (ha : p.take a = q.take a) (hf : f p = f q) :
    labeledChildren L f a b p = labeledChildren L f a b q := by
  classical
  simp only [labeledChildren, ha, hf]

theorem labeledChildren_nonempty {L : Finset (CellPath d)} (f : (CellPath d) → List ℕ)
    (a b : ℕ) {p : (CellPath d)} (hp : p ∈ L) :
    (labeledChildren L f a b p).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr ⟨p, by simp [hp]⟩

theorem extendLabel_old {L : Finset (CellPath d)} {f : (CellPath d) → List ℕ}
    {a b : ℕ} {p q : (CellPath d)} (h : extendLabel L a b f p = extendLabel L a b f q) :
    f p = f q := (List.cons.inj h).2

theorem extendLabel_local {L : Finset (CellPath d)} {f : (CellPath d) → List ℕ}
    {a b : ℕ} {p q : (CellPath d)} (ha : p.take a = q.take a) :
    extendLabel L a b f p = extendLabel L a b f q ↔ f p = f q := by
  constructor
  · exact extendLabel_old
  · intro hf
    simp only [extendLabel, labeledChildren_eq ha hf, hf]

theorem upwardLabels_old (L : Finset (CellPath d)) (steps : List (ℕ × ℕ))
    (f : (CellPath d) → List ℕ) {p q : (CellPath d)}
    (h : upwardLabels L steps f p = upwardLabels L steps f q) : f p = f q := by
  induction steps generalizing f with
  | nil => exact h
  | cons s steps ih => exact extendLabel_old (ih _ h)

theorem upwardLabels_local (L : Finset (CellPath d)) (steps : List (ℕ × ℕ))
    (f : (CellPath d) → List ℕ) {a : ℕ} (hsteps : ∀ s ∈ steps, s.1 ≤ a)
    {p q : (CellPath d)} (ha : p.take a = q.take a) :
    upwardLabels L steps f p = upwardLabels L steps f q ↔ f p = f q := by
  induction steps generalizing f with
  | nil => rfl
  | cons s steps ih =>
    rw [upwardLabels, ih _ (fun t ht => hsteps t (by simp [ht]))]
    exact extendLabel_local (take_eq_of_take_eq (hsteps s (by simp)) ha)

theorem final_labeledChildren_eq (L : Finset (CellPath d)) (f : (CellPath d) → List ℕ)
    (a b : ℕ) (steps : List (ℕ × ℕ)) (hsteps : ∀ s ∈ steps, s.1 ≤ a)
    (p : (CellPath d)) :
    labeledChildren L (upwardLabels L steps (extendLabel L a b f)) a b p =
      labeledChildren L f a b p := by
  classical
  apply congrArg (Finset.image (List.take b))
  apply Finset.filter_congr
  intro q _
  constructor
  · rintro ⟨ha,hf⟩
    exact ⟨ha, extendLabel_old (upwardLabels_old L steps _ hf)⟩
  · rintro ⟨ha,hf⟩
    exact ⟨ha,(upwardLabels_local L steps _ hsteps ha).mpr
      ((extendLabel_local ha).mpr hf)⟩

theorem final_child_count_bin (L : Finset (CellPath d)) (f : (CellPath d) → List ℕ)
    (a b : ℕ) (steps : List (ℕ × ℕ)) (hsteps : ∀ s ∈ steps, s.1 ≤ a)
    {p q : (CellPath d)}
    (hclass : upwardLabels L steps (extendLabel L a b f) p =
      upwardLabels L steps (extendLabel L a b f) q) :
    Nat.log 2 (labeledChildren L (upwardLabels L steps (extendLabel L a b f)) a b p).card =
      Nat.log 2 (labeledChildren L (upwardLabels L steps (extendLabel L a b f)) a b q).card := by
  rw [final_labeledChildren_eq L f a b steps hsteps,
    final_labeledChildren_eq L f a b steps hsteps]
  exact (List.cons.inj (upwardLabels_old L steps _ hclass)).1

theorem final_child_count_bounds (L : Finset (CellPath d)) (f : (CellPath d) → List ℕ)
    (a b : ℕ) (steps : List (ℕ × ℕ)) (hsteps : ∀ s ∈ steps, s.1 ≤ a)
    {p q : (CellPath d)} (hq : q ∈ L)
    (hclass : upwardLabels L steps (extendLabel L a b f) p =
      upwardLabels L steps (extendLabel L a b f) q) :
    let F := upwardLabels L steps (extendLabel L a b f)
    let B := 2 ^ Nat.log 2 (labeledChildren L F a b p).card
    0 < B ∧ B ≤ (labeledChildren L F a b q).card ∧
      (labeledChildren L F a b q).card < 2 * B := by
  dsimp only
  rw [final_child_count_bin L f a b steps hsteps hclass]
  have hp := Finset.card_pos.mpr (labeledChildren_nonempty
    (upwardLabels L steps (extendLabel L a b f)) a b hq)
  refine ⟨by positivity, Nat.pow_log_le_self 2 (by omega), ?_⟩
  simpa only [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by omega : 1 < 2)
    (labeledChildren L (upwardLabels L steps (extendLabel L a b f)) a b q).card

theorem labeledChildren_subset_extensions {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ dyadicPaths N) (f : (CellPath d) → List ℕ)
    (p : (CellPath d)) :
    labeledChildren L f a b p ⊆ (dyadicPaths (b-a)).image (fun q => p.take a ++ q) := by
  classical
  intro c hc
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hq,ha,_⟩ := Finset.mem_filter.mp hq
  have hlen : q.length = N := (mem_dyadicPaths N q).mp (hL hq)
  refine Finset.mem_image.mpr ⟨(q.take b).drop a, ?_, ?_⟩
  · simp only [mem_dyadicPaths, List.length_drop, List.length_take, hlen,
      Nat.min_eq_left hbN]
  · have he := List.take_append_drop a (q.take b)
    simpa only [List.take_take, Nat.min_eq_left hab, ha] using he

theorem labeledChildren_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ dyadicPaths N) (f : (CellPath d) → List ℕ)
    (p : (CellPath d)) : (labeledChildren L f a b p).card ≤ (2^d) ^ (b-a) :=
  (Finset.card_le_card (labeledChildren_subset_extensions hab hbN hL f p)).trans
    (Finset.card_image_le.trans (dyadicPaths_card_le (b-a)))

theorem child_bin_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ dyadicPaths N) (f : (CellPath d) → List ℕ)
    (p : (CellPath d)) : Nat.log 2 (labeledChildren L f a b p).card ≤ d*(b-a) := by
  have hc := labeledChildren_card_le hab hbN hL f p
  have hpow : (2^d) ^ (b-a) = 2 ^ (d*(b-a)) := by rw [pow_mul]
  rw [hpow] at hc
  have := Nat.log_mono_right (b := 2) hc
  simpa only [Nat.log_pow (by omega : 1 < 2)] using this

theorem extendLabel_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ dyadicPaths N) (f : (CellPath d) → List ℕ) :
    (L.image (extendLabel L a b f)).card ≤ (d*(b-a)+1) * (L.image f).card := by
  classical
  let S := (Finset.range (d*(b-a)+1)).product (L.image f)
  have hs : L.image (extendLabel L a b f) ⊆ S.image (fun z => z.1 :: z.2) := by
    intro T hT
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_image.mpr ⟨(Nat.log 2 (labeledChildren L f a b p).card, f p),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by
        have := child_bin_le hab hbN hL f p; omega),Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩,rfl⟩
  calc
    _ ≤ (S.image (fun z => z.1 :: z.2)).card := Finset.card_le_card hs
    _ ≤ S.card := Finset.card_image_le
    _ = _ := by simp [S]

theorem upwardLabels_card_le {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ dyadicPaths N)
    (steps : List (ℕ × ℕ)) (hsteps : ∀ s ∈ steps, s.1 ≤ s.2 ∧ s.2 ≤ N)
    (f : (CellPath d) → List ℕ) :
    (L.image (upwardLabels L steps f)).card ≤ (d*N+1)^steps.length * (L.image f).card := by
  classical
  induction steps generalizing f with
  | nil => simp [upwardLabels]
  | cons s steps ih =>
    have hs := hsteps s (by simp)
    have htail := ih (fun t ht => hsteps t (by simp [ht])) (extendLabel L s.1 s.2 f)
    have hone := extendLabel_card_le hs.1 hs.2 hL f
    have hbound : d*(s.2-s.1)+1 ≤ d*N+1 := Nat.add_le_add_right (Nat.mul_le_mul_left d ((Nat.sub_le _ _).trans hs.2)) 1
    calc
      _ ≤ (d*N+1)^steps.length * (L.image (extendLabel L s.1 s.2 f)).card := htail
      _ ≤ (d*N+1)^steps.length * ((d*N+1)*(L.image f).card) :=
        Nat.mul_le_mul_left _ (hone.trans (Nat.mul_le_mul_right _ hbound))
      _ = _ := by simp only [List.length_cons, pow_succ, Nat.mul_assoc]

abbrev blockDepth (N B i : ℕ) : ℕ := N-i*B

noncomputable def blockLabel (L : Finset (CellPath d)) (N B : ℕ)
    (f : (CellPath d) → List ℕ) : ℕ → (CellPath d) → List ℕ
  | 0 => f
  | i+1 => extendLabel L (blockDepth N B (i+1)) (blockDepth N B i) (blockLabel L N B f i)

theorem blockDepth_antitone (N B : ℕ) : Antitone (blockDepth N B) := by
  intro i j hij
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_right B hij) N

theorem blockDepth_gap (N B i : ℕ) : blockDepth N B i - blockDepth N B (i+1) ≤ B := by
  dsimp only [blockDepth]
  rw [Nat.add_mul, one_mul]
  omega

theorem blockDepth_terminal (N : ℕ) {B : ℕ} (hB : 0 < B) :
    blockDepth N B (N/B+1) = 0 := by
  have h := Nat.lt_mul_div_succ N hB
  simp only [blockDepth]
  rw [Nat.mul_comm] at h
  omega

theorem blockLabel_old (L : Finset (CellPath d)) (N B : ℕ) (f : (CellPath d) → List ℕ)
    {i j : ℕ} (hij : i ≤ j) {p q : (CellPath d)}
    (he : blockLabel L N B f j p = blockLabel L N B f j q) :
    blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact he
  | succ j ih =>
    by_cases heq : i = j+1
    · simpa only [heq] using he
    · exact ih (by omega) (extendLabel_old he)

theorem blockLabel_local (L : Finset (CellPath d)) (N B : ℕ) (f : (CellPath d) → List ℕ)
    {i j a : ℕ} (hij : i ≤ j) (ha : blockDepth N B i ≤ a)
    {p q : (CellPath d)} (hpq : p.take a = q.take a) :
    blockLabel L N B f j p = blockLabel L N B f j q ↔
      blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases heq : i = j+1
    · subst i; rfl
    · have hji : i ≤ j := by omega
      rw [blockLabel, extendLabel_local (take_eq_of_take_eq
        ((blockDepth_antitone N B (by omega : i ≤ j+1)).trans ha) hpq)]
      exact ih hji

theorem block_final_children (L : Finset (CellPath d)) (N B : ℕ) (f : (CellPath d) → List ℕ)
    {i K : ℕ} (hi : i < K) (p : (CellPath d)) :
    labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p =
    labeledChildren L (blockLabel L N B f i)
      (blockDepth N B (i+1)) (blockDepth N B i) p := by
  classical
  apply congrArg (Finset.image (List.take (blockDepth N B i)))
  apply Finset.filter_congr
  intro q _
  constructor
  · rintro ⟨ha,hf⟩
    exact ⟨ha,blockLabel_old L N B f (by omega) hf⟩
  · rintro ⟨ha,hf⟩
    refine ⟨ha,(blockLabel_local L N B f (by omega : i+1 ≤ K) le_rfl ha).mpr ?_⟩
    exact (extendLabel_local ha).mpr hf

theorem block_final_bin_eq (L : Finset (CellPath d)) (N B : ℕ) (f : (CellPath d) → List ℕ)
    {i K : ℕ} (hi : i < K) {p q : (CellPath d)}
    (hclass : blockLabel L N B f K p = blockLabel L N B f K q) :
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p).card =
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) q).card := by
  rw [block_final_children L N B f hi,block_final_children L N B f hi]
  exact (List.cons.inj (blockLabel_old L N B f (by omega : i+1 ≤ K) hclass)).1

theorem blockLabel_card_le {L : Finset (CellPath d)} {N : ℕ} (hL : L ⊆ dyadicPaths N)
    (B : ℕ) (f : (CellPath d) → List ℕ) (K : ℕ) :
    (L.image (blockLabel L N B f K)).card ≤ (d*N+1)^K * (L.image f).card := by
  classical
  induction K with
  | zero => simp [blockLabel]
  | succ K ih =>
    have hs := extendLabel_card_le (blockDepth_antitone N B (Nat.le_succ K))
      (Nat.sub_le N (K*B)) hL (blockLabel L N B f K)
    have hb : d*(blockDepth N B K-blockDepth N B (K+1))+1 ≤ d*N+1 := by
      have : blockDepth N B K ≤ N := Nat.sub_le _ _
      exact Nat.add_le_add_right (Nat.mul_le_mul_left d ((Nat.sub_le _ _).trans this)) 1
    calc
      _ ≤ (d*N+1) * (L.image (blockLabel L N B f K)).card :=
        hs.trans (Nat.mul_le_mul_right _ hb)
      _ ≤ (d*N+1)*((d*N+1)^K*(L.image f).card) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ac_rfl

noncomputable def prefixFiber (C : Finset (CellPath d)) (a : ℕ) (P : (CellPath d)) : Finset (CellPath d) := by
  classical
  exact C.filter fun q => q.take a = P

noncomputable def prefixChildren (C : Finset (CellPath d)) (a b : ℕ) (P : (CellPath d)) :
    Finset (CellPath d) := (prefixFiber C a P).image (List.take b)

theorem prefixFiber_zero (C : Finset (CellPath d)) : prefixFiber C 0 [] = C := by
  classical
  simp [prefixFiber]

theorem prefixFiber_leaf {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ dyadicPaths N)
    {p : (CellPath d)} (hp : p ∈ C) : prefixFiber C N p = {p} := by
  classical
  ext q
  have hlen {q} (hq : q ∈ C) : q.length = N := (mem_dyadicPaths N q).mp (hC hq)
  simp only [prefixFiber, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hq,he⟩
    simpa only [← hlen hq, List.take_length] using he
  · intro he; subst q
    exact ⟨hp,by rw [← hlen hp,List.take_length]⟩

theorem prefixFiber_nonempty {C : Finset (CellPath d)} {a : ℕ} {P : (CellPath d)}
    (hP : P ∈ C.image (List.take a)) : (prefixFiber C a P).Nonempty := by
  classical
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  exact ⟨q,by simp [prefixFiber,hq]⟩

theorem prefixChildren_mem_image {C : Finset (CellPath d)} {a b : ℕ} {P q : (CellPath d)}
    (hq : q ∈ prefixChildren C a b P) : q ∈ C.image (List.take b) := by
  classical
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨r,(Finset.mem_filter.mp hr).1,rfl⟩

theorem prefixFiber_parent_filter {C : Finset (CellPath d)} {a b : ℕ} (hab : a ≤ b)
    {P c : (CellPath d)} (hc : c ∈ prefixChildren C a b P) :
    (prefixFiber C a P).filter (fun q => q.take b = c) = prefixFiber C b c := by
  classical
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
  have hr := (Finset.mem_filter.mp hr).2
  ext q
  simp only [prefixFiber, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hq,he⟩
    exact ⟨⟨hq,(take_eq_of_take_eq hab he).trans hr⟩,he⟩

theorem prefixFiber_card_sum {C : Finset (CellPath d)} {a b : ℕ} (hab : a ≤ b)
    (P : (CellPath d)) :
    (prefixFiber C a P).card =
      ∑ c ∈ prefixChildren C a b P, (prefixFiber C b c).card := by
  classical
  rw [Finset.card_eq_sum_card_image (List.take b) (prefixFiber C a P)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [prefixFiber_parent_filter hab hc]

theorem prefixFiber_count_bounds {C : Finset (CellPath d)} {a b lo hi B : ℕ}
    (hab : a ≤ b) (P : (CellPath d))
    (hbranch : B ≤ (prefixChildren C a b P).card ∧ (prefixChildren C a b P).card ≤ 2*B)
    (hchild : ∀ c ∈ prefixChildren C a b P,
      lo ≤ (prefixFiber C b c).card ∧ (prefixFiber C b c).card ≤ hi) :
    B*lo ≤ (prefixFiber C a P).card ∧ (prefixFiber C a P).card ≤ 2*B*hi := by
  classical
  rw [prefixFiber_card_sum hab]
  constructor
  · calc
      B*lo ≤ (prefixChildren C a b P).card*lo := Nat.mul_le_mul_right _ hbranch.1
      _ = ∑ _c ∈ prefixChildren C a b P, lo := by simp
      _ ≤ _ := Finset.sum_le_sum (fun c hc => (hchild c hc).1)
  · calc
      _ ≤ ∑ _c ∈ prefixChildren C a b P, hi := Finset.sum_le_sum (fun c hc => (hchild c hc).2)
      _ = (prefixChildren C a b P).card*hi := by simp
      _ ≤ 2*B*hi := Nat.mul_le_mul_right _ hbranch.2

theorem prefixChildren_class_eq (L : Finset (CellPath d)) (F : (CellPath d) → List ℕ)
    (a b : ℕ) {T : List ℕ} {p : (CellPath d)} (hp : p ∈ classLeaves L F T) :
    prefixChildren (classLeaves L F T) a b (p.take a) = labeledChildren L F a b p := by
  classical
  have hFp := (Finset.mem_filter.mp hp).2
  apply congrArg (Finset.image (List.take b))
  ext q
  simp only [prefixFiber, classLeaves, Finset.mem_filter, hFp]
  tauto

noncomputable def blockBin (L : Finset (CellPath d)) (F : (CellPath d) → List ℕ)
    (N B i : ℕ) (p : (CellPath d)) : ℕ :=
  2 ^ Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card

noncomputable def blockProduct (L : Finset (CellPath d)) (F : (CellPath d) → List ℕ)
    (N B i : ℕ) (p : (CellPath d)) : ℕ := ∏ j ∈ Finset.range i, blockBin L F N B j p

theorem blockBin_pos (L : Finset (CellPath d)) (F : (CellPath d) → List ℕ)
    (N B i : ℕ) (p : (CellPath d)) : 0 < blockBin L F N B i p := by
  unfold blockBin; positivity

theorem blockProduct_pos (L : Finset (CellPath d)) (F : (CellPath d) → List ℕ)
    (N B i : ℕ) (p : (CellPath d)) : 0 < blockProduct L F N B i p := by
  exact Finset.prod_pos (fun j _ => blockBin_pos L F N B j p)

theorem blockBin_le {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ dyadicPaths N)
    (F : (CellPath d) → List ℕ) (B i : ℕ) (p : (CellPath d)) :
    blockBin L F N B i p ≤ (2^d) ^ (blockDepth N B i-blockDepth N B (i+1)) := by
  have hlog := child_bin_le (blockDepth_antitone N B (Nat.le_succ i)) (Nat.sub_le _ _) hL F p
  have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hlog
  simpa only [pow_mul, blockBin] using hp

theorem blockClass_child_bounds (L : Finset (CellPath d)) (N B : ℕ) (f : (CellPath d) → List ℕ)
    {K i : ℕ} (hi : i < K) (p : (CellPath d))
    {P : (CellPath d)}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B (i+1)))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockBin L F N B i p ≤ (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ∧
      (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ≤ 2*blockBin L F N B i p := by
  classical
  dsimp only
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  rw [prefixChildren_class_eq L _ _ _ hq]
  have hqL := (Finset.mem_filter.mp hq).1
  have hclass := (Finset.mem_filter.mp hq).2
  unfold blockBin
  rw [block_final_bin_eq L N B f hi hclass.symm]
  have hpos := Finset.card_pos.mpr (labeledChildren_nonempty
    (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) hqL)
  refine ⟨Nat.pow_log_le_self 2 (by omega), ?_⟩
  have hu := Nat.lt_pow_succ_log_self (by omega : 1 < 2)
    (labeledChildren L (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) q).card
  simpa only [pow_succ, Nat.mul_comm] using hu.le

theorem blockClass_leaf_count {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ dyadicPaths N)
    (B : ℕ) (f : (CellPath d) → List ℕ) (K : ℕ) (p : (CellPath d))
    {i : ℕ} (hi : i ≤ K) {P : (CellPath d)}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
      (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p := by
  classical
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  have hC : C ⊆ dyadicPaths N := fun q hq => hL (Finset.mem_filter.mp hq).1
  change blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p
  change P ∈ C.image (List.take (blockDepth N B i)) at hP
  induction i generalizing P with
  | zero =>
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
    have hlen : q.length = N := (mem_dyadicPaths _ _).mp (hC hq)
    simp only [blockDepth, Nat.zero_mul, Nat.sub_zero, ← hlen, List.take_length]
    rw [show q.length = N from hlen, prefixFiber_leaf hC hq]
    simp [blockProduct]
  | succ i ih =>
    have hb := blockClass_child_bounds L N B f (by omega : i < K) p hP
    have hc := prefixFiber_count_bounds (blockDepth_antitone N B (Nat.le_succ i)) P hb
      (fun c hc => ih (by omega) (prefixChildren_mem_image hc))
    dsimp only [blockProduct] at hc ⊢
    rw [Finset.prod_range_succ]
    constructor
    · simpa only [Nat.mul_comm] using hc.1
    · have hh := hc.2
      convert hh using 1; ring

theorem blockClass_root_count {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ dyadicPaths N)
    {B : ℕ} (hB : 0 < B) (f : (CellPath d) → List ℕ) {p : (CellPath d)} (hp : p ∈ L) :
    let K := N/B+1
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B K p ≤ C.card ∧ C.card ≤ 2^K * blockProduct L F N B K p := by
  classical
  have hpC : p ∈ classLeaves L (blockLabel L N B f (N/B+1)) (blockLabel L N B f (N/B+1) p) := by
    simp [classLeaves,hp]
  have hc := blockClass_leaf_count hL B f (N/B+1) p (le_refl (N/B+1))
    (P := []) (by rw [blockDepth_terminal N hB]; exact Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  simpa only [blockDepth_terminal N hB, prefixFiber_zero] using hc

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
