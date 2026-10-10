import Mathlib

namespace OAI

namespace MatchingFPRAS.Cells

open SimpleGraph

variable {L : Type*} {G : SimpleGraph L}

lemma exists_walk_on_trace (a : ℕ → L) (n : ℕ)
    (ha : ∀ i < n, a i = a (i + 1) ∨ G.Adj (a i) (a (i + 1))) :
    ∃ w : G.Walk (a 0) (a n), ∀ v ∈ w.support, ∃ i ≤ n, a i = v := by
  induction n with
  | zero =>
    refine ⟨.nil, ?_⟩
    intro v hv
    have hv' : v = a 0 := by simpa using hv
    exact ⟨0, le_rfl, hv'.symm⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih (fun i hi => ha i (by omega))
    rcases ha n (by omega) with heq | hadj
    · refine ⟨w.copy rfl heq, ?_⟩
      intro v hv
      obtain ⟨i, hi, hiv⟩ := hw v (by simpa using hv)
      exact ⟨i, by omega, hiv⟩
    · refine ⟨w.concat hadj, ?_⟩
      intro v hv
      have hv' : v ∈ w.support ∨ v = a (n + 1) := by simpa using hv
      rcases hv' with hv' | hv'
      · obtain ⟨i, hi, hiv⟩ := hw v hv'
        exact ⟨i, by omega, hiv⟩
      · exact ⟨n + 1, le_rfl, hv'.symm⟩

lemma neighbor_return (hG : G.IsAcyclic) (a : ℕ → L) (n : ℕ) (P : L)
    (ha : ∀ i < n, a i = a (i + 1) ∨ G.Adj (a i) (a (i + 1)))
    (havoid : ∀ i ≤ n, a i ≠ P) (hfirst : G.Adj P (a 0))
    (hlast : G.Adj P (a n)) : a 0 = a n := by
  classical
  obtain ⟨w, hw⟩ := exists_walk_on_trace a n ha
  have hnot : P ∉ w.toPath.val.support := by
    intro hP
    obtain ⟨i, hi, hiP⟩ := hw P (w.support_toPath_subset_support hP)
    exact havoid i hi hiP
  have hp : (Walk.cons hfirst w.toPath.val).IsPath := w.toPath.isPath.cons hnot
  have hv := hG.eq_snd_of_adj_start hp hlast (Walk.cons hfirst w.toPath.val).end_mem_support
  simpa using hv.symm

structure ArcData (G : SimpleGraph L) (s : ℕ) where
  labels : ℕ → L
  sets : ℕ → Finset L
  left_mem : ∀ i < s, labels i ∈ sets i
  right_mem : ∀ i < s, labels i ∈ sets (i + 1)
  clique : ∀ i ≤ s, ∀ u ∈ sets i, ∀ v ∈ sets i, u = v ∨ G.Adj u v

namespace ArcData

variable {s : ℕ} (A : ArcData G s)

def Admissible (x y : ℕ) : Prop := ∃ l, l ∈ A.sets x ∧ l ∈ A.sets y

def Good (x y : ℕ) : Prop := y = x + 1 ∨ A.Admissible (x + 1) (y - 1)

structure Split (exteriorGood : Prop) where
  p₁ : ℕ
  p₂ : ℕ
  positive : 0 < p₁
  ordered : p₁ < p₂
  inside : p₂ < s
  odd₁ : p₁ % 2 = 1
  even₂ : p₂ % 2 = 0
  first : A.Admissible 0 p₁
  middle : A.Admissible p₁ p₂
  third : A.Admissible p₂ s
  some_good : (A.Good 0 p₁ ∧ A.Good p₂ s) ∨ (A.Good p₁ p₂ ∧ exteriorGood)
  outer_long : 1 < p₁ → 1 < s - p₂ → A.Good p₁ p₂ ∧ exteriorGood
  middle_long : 1 < p₂ - p₁ → A.Good 0 p₁ ∧ A.Good p₂ s

lemma trace (i : ℕ) (hi : i + 1 < s) :
    A.labels i = A.labels (i + 1) ∨ G.Adj (A.labels i) (A.labels (i + 1)) :=
  A.clique (i + 1) (by omega) _ (A.right_mem i (by omega)) _ (A.left_mem (i + 1) hi)

lemma edge_admissible (i : ℕ) (hi : i < s) : A.Admissible i (i + 1) :=
  ⟨A.labels i, A.left_mem i hi, A.right_mem i hi⟩

lemma last_mem (hs : 0 < s) : A.labels (s - 1) ∈ A.sets s := by
  convert A.right_mem (s - 1) (by omega) using 1
  congr 1
  omega

lemma good_of_same_boundary (x y : ℕ) (hxy : x < y) (hy : y ≤ s)
    (heq : A.labels x = A.labels (y - 1)) : A.Good x y := by
  right
  refine ⟨A.labels x, A.right_mem x (by omega), ?_⟩
  rw [heq]
  exact A.left_mem (y - 1) (by omega)

lemma neighbor_return_between (hG : G.IsAcyclic) (P : L)
    (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi < s)
    (havoid : ∀ i, lo ≤ i → i ≤ hi → A.labels i ≠ P)
    (hfirst : G.Adj P (A.labels lo)) (hlast : G.Adj P (A.labels hi)) :
    A.labels lo = A.labels hi := by
  have hf : G.Adj P ((fun i => A.labels (lo + i)) 0) := by simpa using hfirst
  have hl : G.Adj P ((fun i => A.labels (lo + i)) (hi - lo)) := by
    simpa only [Nat.add_sub_of_le hlo] using hlast
  have h := neighbor_return hG (fun i => A.labels (lo + i)) (hi - lo) P
    (fun i hi' => by
      have := A.trace (lo + i) (by omega)
      simpa only [Nat.add_assoc] using this)
    (fun i hi' => havoid (lo + i) (by omega) (by omega)) hf hl
  simpa only [Nat.add_zero, Nat.add_sub_of_le hlo] using h

lemma split_short_middle {exteriorGood : Prop} (hext : exteriorGood)
    (p : ℕ) (hp : 0 < p) (hps : p + 1 < s) (hodd : p % 2 = 1)
    (hfirst : A.Admissible 0 p) (hthird : A.Admissible (p + 1) s) :
    Nonempty (A.Split exteriorGood) := by
  refine ⟨⟨p, p + 1, hp, by omega, hps, hodd, by omega,
    hfirst, A.edge_admissible p (by omega), hthird, ?_, ?_, ?_⟩⟩
  · exact Or.inr ⟨Or.inl rfl, hext⟩
  · exact fun _ _ => ⟨Or.inl rfl, hext⟩
  · intro h
    omega

lemma split_short_outer (exteriorGood : Prop) (hs : 3 ≤ s) (hsodd : s % 2 = 1)
    (heq : A.labels 0 = A.labels (s - 1)) : Nonempty (A.Split exteriorGood) := by
  have hg₁ : A.Good 0 1 := Or.inl rfl
  have hg₃ : A.Good (s - 1) s := Or.inl (by omega)
  have ha₃ : A.Admissible (s - 1) s :=
    ⟨A.labels (s - 1), A.left_mem (s - 1) (by omega), A.last_mem (by omega)⟩
  have ha₂ : A.Admissible 1 (s - 1) := by
    refine ⟨A.labels 0, A.right_mem 0 (by omega), ?_⟩
    rw [heq]
    exact A.left_mem (s - 1) (by omega)
  refine ⟨⟨1, s - 1, by omega, by omega, by omega, by omega, by omega,
    A.edge_admissible 0 (by omega), ha₂, ha₃, Or.inl ⟨hg₁, hg₃⟩,
    ?_, fun _ => ⟨hg₁, hg₃⟩⟩⟩
  intro h
  omega

lemma split_good_exterior (hG : G.IsAcyclic) {exteriorGood : Prop} (hext : exteriorGood)
    (hs : 3 ≤ s) (hsodd : s % 2 = 1) (P : L)
    (hP₀ : P ∈ A.sets 0) (hPₛ : P ∈ A.sets s) : Nonempty (A.Split exteriorGood) := by
  classical
  by_cases hboundary : A.labels 0 = A.labels (s - 1)
  · exact A.split_short_outer exteriorGood hs hsodd hboundary
  by_cases hodd : ∃ i, i < s ∧ i % 2 = 1 ∧ A.labels i = P
  · obtain ⟨i, his, hi, hiP⟩ := hodd
    refine A.split_short_middle hext i (by omega) (by omega) hi ?_ ?_
    · exact ⟨P, hP₀, by simpa only [hiP] using A.left_mem i his⟩
    · exact ⟨P, by simpa only [hiP] using A.right_mem i his, hPₛ⟩
  have heven : ∀ i < s, A.labels i = P → i % 2 = 0 := by
    intro i his hiP
    have hm := Nat.mod_lt i (by omega : 0 < 2)
    by_contra hn
    exact hodd ⟨i, his, by omega, hiP⟩
  have hex : ∃ i, i < s ∧ A.labels i = P := by
    by_contra hnone
    push Not at hnone
    have hav : ∀ i, 0 ≤ i → i ≤ s - 1 → A.labels i ≠ P :=
      fun i _ hi => hnone i (by omega)
    have hadj₀ : G.Adj P (A.labels 0) :=
      (A.clique 0 (by omega) P hP₀ _ (A.left_mem 0 (by omega))).resolve_left
        (fun h => hnone 0 (by omega) h.symm)
    have hadjₛ : G.Adj P (A.labels (s - 1)) :=
      (A.clique s le_rfl P hPₛ _ (A.last_mem (by omega))).resolve_left
        (fun h => hnone (s - 1) (by omega) h.symm)
    exact hboundary (A.neighbor_return_between hG P 0 (s - 1) (by omega) (by omega)
      hav hadj₀ hadjₛ)
  by_cases hzero : A.labels 0 = P
  · let j := Nat.findGreatest (fun i => A.labels i = P) (s - 1)
    have hjle : j ≤ s - 1 := Nat.findGreatest_le _
    have hjP : A.labels j = P := Nat.findGreatest_spec (P := fun i => A.labels i = P) (by omega : 0 ≤ s - 1) hzero
    have hlast : A.labels (s - 1) ≠ P := fun h => hboundary (hzero.trans h.symm)
    have hjlt : j < s - 1 := by
      by_contra h
      have : j = s - 1 := by omega
      exact hlast (this ▸ hjP)
    have hjEven : j % 2 = 0 := heven j (by omega) hjP
    have hav : ∀ i, j + 1 ≤ i → i ≤ s - 1 → A.labels i ≠ P := by
      intro i hi his
      exact Nat.findGreatest_is_greatest (P := fun k => A.labels k = P) (by omega : j < i) his
    have hPa : P ∈ A.sets (j + 1) := by
      simpa only [hjP] using A.right_mem j (by omega)
    have hadjFirst : G.Adj P (A.labels (j + 1)) :=
      (A.clique (j + 1) (by omega) P hPa _ (A.left_mem (j + 1) (by omega))).resolve_left
        (fun h => hav (j + 1) le_rfl (by omega) h.symm)
    have hadjLast : G.Adj P (A.labels (s - 1)) :=
      (A.clique s le_rfl P hPₛ _ (A.last_mem (by omega))).resolve_left
        (fun h => hlast h.symm)
    have hQ := A.neighbor_return_between hG P (j + 1) (s - 1)
      (by omega) (by omega) hav hadjFirst hadjLast
    refine A.split_short_middle hext (j + 1) (by omega) (by omega) (by omega)
      ⟨P, hP₀, hPa⟩ ?_
    refine ⟨A.labels (j + 1), A.right_mem (j + 1) (by omega), ?_⟩
    rw [hQ]
    exact A.last_mem (by omega)
  · let i := Nat.find hex
    have hi : i < s := (Nat.find_spec hex).1
    have hiP : A.labels i = P := (Nat.find_spec hex).2
    have hiPos : 0 < i := by
      by_contra h
      have hi0 : i = 0 := by omega
      exact hzero (hi0 ▸ hiP)
    have hiEven : i % 2 = 0 := heven i hi hiP
    have hia : i - 1 + 1 = i := by omega
    have hav : ∀ k, 0 ≤ k → k ≤ i - 1 → A.labels k ≠ P := by
      intro k _ hk hkP
      have hkmin := Nat.find_min' hex (show k < s ∧ A.labels k = P from ⟨by omega, hkP⟩)
      change i ≤ k at hkmin
      omega
    have hPi : P ∈ A.sets i := by simpa only [hiP] using A.left_mem i hi
    have hprev : A.labels (i - 1) ∈ A.sets i := by
      simpa only [hia] using A.right_mem (i - 1) (by omega)
    have hadjFirst : G.Adj P (A.labels 0) :=
      (A.clique 0 (by omega) P hP₀ _ (A.left_mem 0 (by omega))).resolve_left
        (fun h => hzero h.symm)
    have hadjLast : G.Adj P (A.labels (i - 1)) :=
      (A.clique i (by omega) P hPi _ hprev).resolve_left
        (fun h => hav (i - 1) (by omega) le_rfl h.symm)
    have hQ := A.neighbor_return_between hG P 0 (i - 1) (by omega) (by omega)
      hav hadjFirst hadjLast
    refine A.split_short_middle hext (i - 1) (by omega) (by omega) (by omega) ?_ ?_
    · refine ⟨A.labels 0, A.left_mem 0 (by omega), ?_⟩
      rw [hQ]
      exact A.left_mem (i - 1) (by omega)
    · rw [hia]
      exact ⟨P, hPi, hPₛ⟩

lemma split_left_boundary (hG : G.IsAcyclic) (exteriorGood : Prop)
    (hs : 3 ≤ s) (hsodd : s % 2 = 1) (P : L)
    (hP₀ : P ∈ A.sets 0) (hPₛ : P ∈ A.sets s) (hzero : A.labels 0 = P) :
    Nonempty (A.Split exteriorGood) := by
  classical
  by_cases hlast : A.labels (s - 1) = P
  · exact A.split_short_outer exteriorGood hs hsodd (hzero.trans hlast.symm)
  let j := Nat.findGreatest (fun i => A.labels i = P) (s - 1)
  have hjle : j ≤ s - 1 := Nat.findGreatest_le _
  have hjP : A.labels j = P :=
    Nat.findGreatest_spec (P := fun i => A.labels i = P) (by omega : 0 ≤ s - 1) hzero
  have hjlt : j < s - 1 := by
    by_contra h
    have : j = s - 1 := by omega
    exact hlast (this ▸ hjP)
  have hav : ∀ i, j + 1 ≤ i → i ≤ s - 1 → A.labels i ≠ P := by
    intro i hi his
    exact Nat.findGreatest_is_greatest (P := fun k => A.labels k = P) (by omega : j < i) his
  have hPt : P ∈ A.sets (j + 1) := by
    simpa only [hjP] using A.right_mem j (by omega)
  have hadjFirst : G.Adj P (A.labels (j + 1)) :=
    (A.clique (j + 1) (by omega) P hPt _ (A.left_mem (j + 1) (by omega))).resolve_left
      (fun h => hav (j + 1) le_rfl (by omega) h.symm)
  have hadjLast : G.Adj P (A.labels (s - 1)) :=
    (A.clique s le_rfl P hPₛ _ (A.last_mem (by omega))).resolve_left
      (fun h => hlast h.symm)
  have hQ := A.neighbor_return_between hG P (j + 1) (s - 1)
    (by omega) (by omega) hav hadjFirst hadjLast
  by_cases htEven : (j + 1) % 2 = 0
  · have hg₁ : A.Good 0 1 := Or.inl rfl
    have hg₃ : A.Good (j + 1) s := A.good_of_same_boundary _ _ (by omega) le_rfl hQ
    have ha₂ : A.Admissible 1 (j + 1) :=
      ⟨P, by simpa only [hzero] using A.right_mem 0 (by omega), hPt⟩
    have ha₃ : A.Admissible (j + 1) s := by
      refine ⟨A.labels (j + 1), A.left_mem (j + 1) (by omega), ?_⟩
      rw [hQ]
      exact A.last_mem (by omega)
    refine ⟨⟨1, j + 1, by omega, by omega, by omega, by omega, htEven,
      A.edge_admissible 0 (by omega), ha₂, ha₃, Or.inl ⟨hg₁, hg₃⟩,
      ?_, fun _ => ⟨hg₁, hg₃⟩⟩⟩
    intro h
    omega
  · have htOdd : (j + 1) % 2 = 1 := by omega
    have hg₁ : A.Good 0 (j + 1) := by
      apply A.good_of_same_boundary _ _ (by omega) (by omega)
      simpa only [Nat.add_sub_cancel, hzero] using hjP.symm
    have hg₃ : A.Good (s - 1) s := Or.inl (by omega)
    have ha₁ : A.Admissible 0 (j + 1) := ⟨P, hP₀, hPt⟩
    have ha₂ : A.Admissible (j + 1) (s - 1) := by
      refine ⟨A.labels (j + 1), A.left_mem (j + 1) (by omega), ?_⟩
      rw [hQ]
      exact A.left_mem (s - 1) (by omega)
    have ha₃ : A.Admissible (s - 1) s :=
      ⟨A.labels (s - 1), A.left_mem (s - 1) (by omega), A.last_mem (by omega)⟩
    refine ⟨⟨j + 1, s - 1, by omega, by omega, by omega, htOdd, by omega,
      ha₁, ha₂, ha₃, Or.inl ⟨hg₁, hg₃⟩, ?_, fun _ => ⟨hg₁, hg₃⟩⟩⟩
    intro _ h
    omega

def reverse : ArcData G s where
  labels i := A.labels (s - 1 - i)
  sets i := A.sets (s - i)
  left_mem i hi := by
    have hj : s - 1 - i < s := by omega
    have heq : s - 1 - i + 1 = s - i := by omega
    simpa only [heq] using A.right_mem (s - 1 - i) hj
  right_mem i hi := by
    have hj : s - 1 - i < s := by omega
    have heq : s - 1 - i = s - (i + 1) := by omega
    simpa only [← heq] using A.left_mem (s - 1 - i) hj
  clique i hi := A.clique (s - i) (by omega)

lemma admissible_symm {x y : ℕ} (h : A.Admissible x y) : A.Admissible y x := by
  obtain ⟨l, hl₁, hl₂⟩ := h
  exact ⟨l, hl₂, hl₁⟩

lemma good_reverse {x y : ℕ} (hxy : x < y) (hy : y ≤ s)
    (h : A.reverse.Good x y) : A.Good (s - y) (s - x) := by
  rcases h with hshort | ⟨l, hl₁, hl₂⟩
  · left
    omega
  · right
    change l ∈ A.sets (s - (x + 1)) at hl₁
    change l ∈ A.sets (s - (y - 1)) at hl₂
    have h₁ : s - (x + 1) = s - x - 1 := by omega
    have h₂ : s - (y - 1) = s - y + 1 := by omega
    exact ⟨l, by simpa only [h₂] using hl₂, by simpa only [h₁] using hl₁⟩

def Split.unreverse {exteriorGood : Prop} (hsodd : s % 2 = 1)
    (T : A.reverse.Split exteriorGood) : A.Split exteriorGood := by
  have h₁ := T.positive
  have h₂ := T.ordered
  have h₃ := T.inside
  have ho := T.odd₁
  have he := T.even₂
  have ha₁ : A.Admissible 0 (s - T.p₂) := by
    have h := A.admissible_symm T.third
    simpa only [reverse, Nat.sub_self] using h
  have ha₂ : A.Admissible (s - T.p₂) (s - T.p₁) := A.admissible_symm T.middle
  have ha₃ : A.Admissible (s - T.p₁) s := by
    have h := A.admissible_symm T.first
    simpa only [reverse, Nat.sub_zero] using h
  have g₁ : A.reverse.Good T.p₂ s → A.Good 0 (s - T.p₂) := by
    intro h
    simpa only [Nat.sub_self] using A.good_reverse h₃ le_rfl h
  have g₂ : A.reverse.Good T.p₁ T.p₂ → A.Good (s - T.p₂) (s - T.p₁) :=
    A.good_reverse h₂ (by omega)
  have g₃ : A.reverse.Good 0 T.p₁ → A.Good (s - T.p₁) s := by
    intro h
    simpa only [Nat.sub_zero] using A.good_reverse h₁ (by omega) h
  refine ⟨s - T.p₂, s - T.p₁, by omega, by omega, by omega, by omega, by omega,
    ha₁, ha₂, ha₃, ?_, ?_, ?_⟩
  · rcases T.some_good with ⟨hf, ht⟩ | ⟨hm, hg⟩
    · exact Or.inl ⟨g₁ ht, g₃ hf⟩
    · exact Or.inr ⟨g₂ hm, hg⟩
  · intro hf ht
    obtain ⟨hm, hg⟩ := T.outer_long (by omega) (by omega)
    exact ⟨g₂ hm, hg⟩
  · intro hm
    obtain ⟨hf, ht⟩ := T.middle_long (by omega)
    exact ⟨g₁ ht, g₃ hf⟩

theorem split (hG : G.IsAcyclic) (exteriorGood : Prop)
    (hs : 3 ≤ s) (hsodd : s % 2 = 1) (P : L)
    (hP₀ : P ∈ A.sets 0) (hPₛ : P ∈ A.sets s)
    (hbad : ¬exteriorGood → A.labels 0 = P ∨ A.labels (s - 1) = P) :
    Nonempty (A.Split exteriorGood) := by
  classical
  by_cases hext : exteriorGood
  · exact A.split_good_exterior hG hext hs hsodd P hP₀ hPₛ
  rcases hbad hext with hleft | hright
  · exact A.split_left_boundary hG exteriorGood hs hsodd P hP₀ hPₛ hleft
  · have hP₀' : P ∈ A.reverse.sets 0 := by simpa only [reverse, Nat.sub_zero] using hPₛ
    have hPₛ' : P ∈ A.reverse.sets s := by simpa only [reverse, Nat.sub_self] using hP₀
    have hzero : A.reverse.labels 0 = P := by simpa only [reverse, Nat.sub_zero] using hright
    obtain ⟨T⟩ := A.reverse.split_left_boundary hG exteriorGood hs hsodd P hP₀' hPₛ' hzero
    exact ⟨T.unreverse A hsodd⟩

end ArcData

structure CycleData (G : SimpleGraph L) (m : ℕ) where
  labels : ℤ → L
  periodic : ∀ i, labels (i + m) = labels i
  adjacent : ∀ i, labels (i - 1) = labels i ∨ G.Adj (labels (i - 1)) (labels i)

end MatchingFPRAS.Cells

end OAI
