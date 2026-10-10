import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.HoleBlocks

namespace OAI

namespace MatchingFPRAS.Subdivision

section

open Finset

lemma first_hole_of_sorted_cons {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (j : Fin m) (xs : List (Fin m)) (he : U.sort (· ≤ ·)=j::xs) :
    b 0=true ↔ j.val%2=1 := by
  apply first_hole_terminal hb j
  · exact (Finset.mem_sort (· ≤ ·)).mp (he ▸ List.mem_cons_self)
  · intro i hi
    have hmem : i ∈ j::xs := he ▸ (Finset.mem_sort (· ≤ ·)).mpr hi
    have hsort := U.pairwise_sort (· ≤ ·)
    rw [he] at hsort
    rcases List.mem_cons.mp hmem with rfl | hmem
    · rfl
    · exact (List.pairwise_cons.mp hsort).1 i hmem

lemma last_hole_of_sorted_append {m : ℕ} (hm : Even m) {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (j : Fin m) (xs : List (Fin m)) (he : U.sort (· ≤ ·)=xs++[j]) :
    b (Fin.last m)=true ↔ j.val%2=0 := by
  apply last_hole_terminal hm hb j
  · exact (Finset.mem_sort (· ≤ ·)).mp (he ▸ (by simp))
  · intro i hi
    have hmem : i ∈ xs++[j] := he ▸ (Finset.mem_sort (· ≤ ·)).mpr hi
    have hsort := U.pairwise_sort (· ≤ ·)
    rw [he] at hsort
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact (List.pairwise_append.mp hsort).2.2 i hmem j (by simp)
    · have hij : i=j := by simpa using hmem
      exact hij.le

theorem HoleBlocks.left_uses {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (hU : U.Nonempty) (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) (hp : d.Parity) :
    b 0=true ↔ d.left.isSome := by
  cases hl : d.left with
  | some j =>
    have hs : U.sort (· ≤ ·)=j::(d.neutral.flatMap (fun q => [q.1,q.2])++d.right.toList) := by
      simpa [HoleBlocks.flatten,hl,List.append_assoc] using he.symm
    have hj := hp.1 j (by simp [hl])
    simpa [hl,hj] using first_hole_of_sorted_cons hb j _ hs
  | none =>
    cases hn : d.neutral with
    | cons q xs =>
      have hs : U.sort (· ≤ ·)=q.1::(q.2::(xs.flatMap (fun q => [q.1,q.2])++d.right.toList)) := by
        simpa [HoleBlocks.flatten,hl,hn,List.append_assoc] using he.symm
      have hj := (hp.2.1 q (by simp [hn])).1
      simpa [hl,hj] using first_hole_of_sorted_cons hb q.1 _ hs
    | nil =>
      cases hr : d.right with
      | some j =>
        have hs : U.sort (· ≤ ·)=[j] := by simpa [HoleBlocks.flatten,hl,hn,hr] using he.symm
        have hj := hp.2.2 j (by simp [hr])
        simpa [hl,hj] using first_hole_of_sorted_cons hb j [] hs
      | none =>
        have hs : U.sort (· ≤ ·)=[] := by simpa [HoleBlocks.flatten,hl,hn,hr] using he.symm
        obtain ⟨j,hj⟩ := hU
        have : j ∈ U.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hj
        simp [hs] at this

theorem HoleBlocks.right_uses {m : ℕ} (hm : Even m) {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (hU : U.Nonempty) (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) (hp : d.Parity) :
    b (Fin.last m)=true ↔ d.right.isSome := by
  cases hr : d.right with
  | some j =>
    have hs : U.sort (· ≤ ·)=(d.left.toList++d.neutral.flatMap (fun q => [q.1,q.2]))++[j] := by
      simpa [HoleBlocks.flatten,hr] using he.symm
    have hj := hp.2.2 j (by simp [hr])
    simpa [hr,hj] using last_hole_of_sorted_append hm hb j _ hs
  | none =>
    generalize hn : d.neutral=xs at hp he
    cases xs using List.reverseRecOn with
    | nil =>
      cases hl : d.left with
      | some j =>
        have hs : U.sort (· ≤ ·)=[]++[j] := by simpa [HoleBlocks.flatten,hl,hn,hr] using he.symm
        have hj := hp.1 j (by simp [hl])
        simpa [hr,hj] using last_hole_of_sorted_append hm hb j [] hs
      | none =>
        have hs : U.sort (· ≤ ·)=[] := by simpa [HoleBlocks.flatten,hl,hn,hr] using he.symm
        obtain ⟨j,hj⟩ := hU
        have : j ∈ U.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hj
        simp [hs] at this
    | append_singleton xs q =>
      have hs : U.sort (· ≤ ·)=(d.left.toList++xs.flatMap (fun q => [q.1,q.2])++[q.1])++[q.2] := by
        simpa [HoleBlocks.flatten,hr,hn,List.flatMap_append,List.append_assoc] using he.symm
      have hj := (hp.2.1 q (by simp [hn])).2
      simpa [hr,hj] using last_hole_of_sorted_append hm hb q.2 _ hs

theorem HoleBlocks.neutral_lt {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) (q : Fin m × Fin m) (hq : q ∈ d.neutral) :
    q.1.val < q.2.val := by
  have hp : d.flatten.Pairwise (· < ·) := he ▸ U.sortedLT_sort.pairwise
  have hn : (d.neutral.flatMap (fun q => [q.1,q.2])).Pairwise (· < ·) :=
    (List.pairwise_append.mp (List.pairwise_append.mp hp).1).2.1
  have hq' := (List.pairwise_flatMap.mp hn).1 q hq
  simpa using hq'

lemma HoleBlocks.flatten_nodup {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) : d.flatten.Nodup := he ▸ U.sort_nodup (· ≤ ·)

lemma HoleBlocks.left_mem {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) {j : Fin m} (hj : j ∈ d.left) : j ∈ U := by
  apply (Finset.mem_sort (· ≤ ·)).mp
  rw [← he]
  simp only [HoleBlocks.flatten,List.mem_append,Option.mem_toList]
  exact Or.inl (Or.inl hj)

lemma HoleBlocks.right_mem {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) {j : Fin m} (hj : j ∈ d.right) : j ∈ U := by
  apply (Finset.mem_sort (· ≤ ·)).mp
  rw [← he]
  simp only [HoleBlocks.flatten,List.mem_append,Option.mem_toList]
  exact Or.inr hj

lemma HoleBlocks.neutral_mem {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) {q : Fin m × Fin m} (hq : q ∈ d.neutral) :
    q.1 ∈ U ∧ q.2 ∈ U := by
  have h (j : Fin m) (hj : j ∈ [q.1,q.2]) : j ∈ U := by
    apply (Finset.mem_sort (· ≤ ·)).mp
    rw [← he]
    have hn : j ∈ d.neutral.flatMap (fun q => [q.1,q.2]) := List.mem_flatMap.mpr ⟨q,hq,hj⟩
    simp only [HoleBlocks.flatten,List.mem_append]
    tauto
  exact ⟨h _ (by simp),h _ (by simp)⟩

lemma HoleBlocks.reorder {m : ℕ} (d : HoleBlocks m) :
    d.flatten.Perm (d.neutral.flatMap (fun q => [q.1,q.2]) ++ (d.left.toList++d.right.toList)) := by
  unfold HoleBlocks.flatten
  exact (List.perm_append_comm.append_right _).trans (by rw [List.append_assoc])

lemma HoleBlocks.reordered_nodup {m : ℕ} {U : Finset (Fin m)} (d : HoleBlocks m)
    (he : d.flatten=U.sort (· ≤ ·)) :
    (d.neutral.flatMap (fun q => [q.1,q.2]) ++ (d.left.toList++d.right.toList)).Nodup :=
  d.reorder.nodup_iff.mp (d.flatten_nodup he)

end

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
lemma uses_not_hole [Fintype V] [Fintype E]
    {m : ℕ} {u v : E → V} {R₀ : Finset V} {U : E → Finset (Fin m)}
    {b : E → Selection m} (hb : FamilyHoles u v m R₀ U b) {e : E} {x : V}
    (he : Uses u v b e x) : x ∉ R₀ := fun hx => hb.2.1 x hx e he

lemma uses_unique {m : ℕ} {u v : E → V} {R₀ : Finset V} {U : E → Finset (Fin m)}
    {b : E → Selection m} (hb : FamilyHoles u v m R₀ U b) {e e' : E} {x : V}
    (he : Uses u v b e x) (he' : Uses u v b e' x) : e=e' :=
  (hb.2.2 x (uses_not_hole hb he)).unique he he'

omit [Fintype V] [Fintype E] in
lemma left_consumes [Fintype V] [Fintype E]
    {m : ℕ} {u v : E → V} {R₀ : Finset V} {U : E → Finset (Fin m)}
    {b : E → Selection m} (hb : FamilyHoles u v m R₀ U b)
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hp : ∀ e, (d e).Parity) (e : E) {j : Fin m} (hj : j ∈ (d e).left) :
    Uses u v b e (u e) := by
  have hU : (U e).Nonempty := ⟨j,(d e).left_mem (he e) hj⟩
  have hs : (d e).left.isSome := by cases h : (d e).left <;> simp [h] at hj ⊢
  exact Or.inl ⟨((d e).left_uses (hb.1 e) hU (he e) (hp e)).mpr hs,rfl⟩

omit [Fintype V] [Fintype E] in
lemma right_consumes [Fintype V] [Fintype E]
    {m : ℕ} (hm : Even m) {u v : E → V} {R₀ : Finset V} {U : E → Finset (Fin m)}
    {b : E → Selection m} (hb : FamilyHoles u v m R₀ U b)
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·))
    (hp : ∀ e, (d e).Parity) (e : E) {j : Fin m} (hj : j ∈ (d e).right) :
    Uses u v b e (v e) := by
  have hU : (U e).Nonempty := ⟨j,(d e).right_mem (he e) hj⟩
  have hs : (d e).right.isSome := by cases h : (d e).right <;> simp [h] at hj ⊢
  exact Or.inr ⟨((d e).right_uses hm (hb.1 e) hU (he e) (hp e)).mpr hs,rfl⟩

lemma internalStrength_le_twice_incident (p : ℕ) (hp : 1≤p) (B Hu Hv : ℝ)
    (hB : 0≤B) (hHu : 0≤Hu) (hHv : 0≤Hv)
    (hinnerL : max B (Hu/2^(p-1))=B) (hinnerR : max B (Hv/2^(p-1))=B)
    (j : Fin (4*p)) :
    internalStrength p B Hu Hv j ≤ 2*profileActivity p B Hu Hv B j.castSucc ∧
    internalStrength p B Hu Hv j ≤ 2*profileActivity p B Hu Hv B j.succ := by
  have two_self (x : ℝ) (hx : B≤x) : x≤2*x := by linarith
  by_cases hj : j.val<2*p
  · rw [internalStrength,ite_eq_left hj]
    constructor
    · rw [profile_left _ _ _ _ _ _ hj]
      exact two_self _ (le_max_left _ _)
    · by_cases hk : j.val+1<2*p
      · rw [profile_left _ _ _ _ _ _ hk]
        calc
          _ ≤ 2*max B (Hu/2^(j.val/2+1)) := legValue_step B Hu hB _
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (legValue_antitone B Hu hHu (by simp only [Fin.val_succ]; omega)) (by norm_num)
      · have he : j.succ=⟨2*p,by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
        rw [he,profile_center,show j.val/2=p-1 by omega,hinnerL]
        exact two_self _ le_rfl
  · rw [internalStrength,ite_eq_right hj]
    constructor
    · by_cases hk : 2*p<j.val
      · rw [profile_right _ _ _ _ _ _ hk]
        calc
          _ ≤ 2*max B (Hv/2^((4*p-(j.val+1))/2+1)) := legValue_step B Hv hB _
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (legValue_antitone B Hv hHv (by simp only [Fin.val_castSucc]; omega)) (by norm_num)
      · have he : j.castSucc=⟨2*p,by omega⟩ := Fin.ext (by simp only [Fin.val_castSucc]; omega)
        rw [he,profile_center,show (4*p-(j.val+1))/2=p-1 by omega,hinnerR]
        exact two_self _ le_rfl
    · rw [profile_right _ _ _ _ _ _ (by simp only [Fin.val_succ]; omega)]
      exact two_self _ (le_max_left _ _)

lemma profile_adjacent_near (p : ℕ) (hp : 1≤p) (B Hu Hv : ℝ)
    (hB : 0≤B) (hHu : 0≤Hu) (hHv : 0≤Hv)
    (hinnerL : max B (Hu/2^(p-1))=B) (hinnerR : max B (Hv/2^(p-1))=B)
    (j : Fin (4*p)) :
    profileActivity p B Hu Hv B j.castSucc ≤ 2*profileActivity p B Hu Hv B j.succ ∧
    profileActivity p B Hu Hv B j.succ ≤ 2*profileActivity p B Hu Hv B j.castSucc := by
  have h₁ := internalStrength_incident p B Hu Hv B hHu hHv le_rfl j
  have h₂ := internalStrength_le_twice_incident p hp B Hu Hv hB hHu hHv hinnerL hinnerR j
  exact ⟨h₁.1.trans h₂.2,h₁.2.trans h₂.1⟩

end MatchingFPRAS.Subdivision

end OAI
