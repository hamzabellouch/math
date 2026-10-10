import OAI.Combinatorics.PerfectMatching.CountCorrect

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma count_zero_vertices (G : Input) (hn : G.n=0) : count G=1 := by
  classical
  let M : (completeGraph G.n).Matching := ⟨∅,fun v => by have := v.isLt; omega⟩
  have hM (N : (completeGraph G.n).Matching) : N=M := by
    apply Subtype.ext
    apply Finset.eq_empty_of_forall_notMem
    intro e _
    have := e.val.1.isLt
    omega
  unfold count
  rw [sum_eq_single M]
  · simp [M]
  · intro N _ hne
    exact (hne (hM N)).elim
  · simp

lemma count_odd_vertices (G : Input) (hn : Odd G.n) : count G=0 := by
  classical
  have hempty : IsEmpty (completeGraph G.n).Matching := ⟨fun M => by
    have hh := (completeGraph G.n).matching_card_twice M
    simp only [Fintype.card_fin] at hh
    obtain ⟨r,hr⟩ := hn
    omega⟩
  simp [count]

lemma count_two_vertices (G : Input) (hn : G.n=2) : count G=rawMultiplicity G 0 1 := by
  classical
  let e : Pair G.n := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by simp⟩
  have heq (f : Pair G.n) : f=e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · have hh := f.property; have h1 := f.val.1.isLt; have h2 := f.val.2.isLt
      dsimp [e] at hh ⊢; omega
    · have hh := f.property; have h1 := f.val.1.isLt; have h2 := f.val.2.isLt
      dsimp [e] at hh ⊢; omega
  have heinc (v : Fin G.n) : (completeGraph G.n).Incident v e := by
    have hv := v.isLt
    change e.val.1=v ∨ e.val.2=v
    by_cases hz : v.val=0
    · left; apply Fin.ext; exact hz.symm
    · right; apply Fin.ext; dsimp [e]; omega
  let M : (completeGraph G.n).Matching := ⟨{e},fun v => ⟨e,⟨by simp,heinc v⟩,
    fun _ h => by simpa only [mem_singleton] using h.1⟩⟩
  have hM (N : (completeGraph G.n).Matching) : N=M := by
    apply Subtype.ext
    apply Finset.ext
    intro f
    have hfn := heq f
    obtain ⟨g,hg,_⟩ := N.property e.val.1
    have hgn := heq g
    have hmem : e∈N.val := hgn ▸ hg.1
    simp only [M,mem_singleton,hfn]
    exact iff_true_intro hmem
  unfold count
  rw [sum_eq_single M]
  · simp only [M,prod_singleton]
    unfold multiplicity rawMultiplicity
    dsimp [e]
    cases G.records.find? (fun r => r.left=0 && r.right=1) <;> rfl
  · intro N _ hne
    exact (hne (hM N)).elim
  · simp

lemma present_endpoints_covered (G : Input) (e : Pair G.n) (he : 0 < multiplicity G e) :
    e.val.1.val∈covered G ∧ e.val.2.val∈covered G := by
  unfold multiplicity at he
  cases hf : G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
  | none => simp only [hf] at he; omega
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hp
    simp only [hf] at he
    have hr' : r∈G.records.filter (fun r => 0 < r.multiplicity) := by simp [hr,he]
    constructor
    · simp only [covered,List.mem_toFinset,List.mem_flatMap]
      refine ⟨r,hr',?_⟩
      simp [hp.1]
    · simp only [covered,List.mem_toFinset,List.mem_flatMap]
      refine ⟨r,hr',?_⟩
      simp [hp.2]

lemma positive_count_covered (G : Input) (hN : 0 < count G) : G.n ≤ (covered G).card := by
  obtain ⟨M,hM⟩ := positive_count_valid G hN
  have hsub : range G.n ⊆ covered G := by
    intro v hv
    let w : Fin G.n := ⟨v,mem_range.mp hv⟩
    obtain ⟨e,⟨he,hinc⟩,_⟩ := M.property w
    have hep := present_endpoints_covered G e (hM e he)
    rcases hinc with h|h
    · have hh : e.val.1.val=v := congrArg Fin.val h
      simpa only [hh] using hep.1
    · have hh : e.val.2.val=v := congrArg Fin.val h
      simpa only [hh] using hep.2
  simpa only [card_range] using card_le_card hsub

lemma count_zero_of_uncovered (G : Input) (hu : (covered G).card < G.n) : count G=0 := by
  by_contra hN
  have := positive_count_covered G (Nat.pos_of_ne_zero hN)
  omega

theorem approximate_correct (G : Input) :
    approximate G ≤ count G ∧ count G ≤ 2^(9*G.n)*approximate G ∧
      (approximate G=0 ↔ count G=0) := by
  unfold approximate
  split_ifs with hn0 hodd hn2 hcover
  · rw [count_zero_vertices G hn0,hn0]
    norm_num
  · rw [count_odd_vertices G hodd]
    simp
  · rw [count_two_vertices G hn2]
    refine ⟨le_rfl,?_,Iff.rfl⟩
    exact Nat.le_mul_of_pos_left _ (by positivity)
  · rw [count_zero_of_uncovered G hcover]
    simp
  · have heven : Even G.n := Nat.not_odd_iff_even.mp hodd
    have hn : 4 ≤ G.n := by
      obtain ⟨r,hr⟩ := heven
      omega
    exact estimate_correct G hn heven

end
end BinaryMatching.Algorithm
end

end OAI
