import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalIncrementProfiles
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawReplacementProfiles
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OutsidePathRules

namespace OAI

/-! A short representative replacement cannot absorb any old assigned path.
Consequently its two targets start two different oriented chains. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

private theorem mul_length_le_sum {d : ℕ} {w : List ℕ} (h : ∀ b ∈ w, d ≤ b) :
    d * w.length ≤ w.sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.length_cons, Nat.mul_succ, List.sum_cons]
    omega

theorem IsOptimal.terminal_different_chain_starts {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (U : RawPathSystem G Q) (hUa : U.amount = S.amount)
    (hUe : U.assignedCount = S.assignedCount)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {P M R : List (List V)} {A B C D : List V} {x y : V}
    (hsys : U.chains = P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q)
    (h : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d) :
    S.amount = k - Q.card ∧ A = [] ∧ C = [] ∧ d * S.assignedCount ≤ S.amount := by
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hpos : J ≠ [] := by intro he; simp only [he, List.length_nil] at hJlen; omega
  have hdis : J.Disjoint U.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzU
    exact hJout z hz (hUvertices z (List.mem_toFinset.mpr hzU))
  obtain ⟨T, original, output, kept, removed, hT, hTa, ho, hout, hp, hq⟩ :=
    U.replace_different_chains_profiled hsys hA hC hJ hJQ hpos hdis hpath
  obtain ⟨hL, _, hkept, _, hweights⟩ := hopt.terminal_increment_profiles ht hQk hkQ hQ hcycle
    hd hd' U T hUa hUe ho hout hp hq (by omega)
  have hTcount : T.assignedCount = S.assignedCount + 1 := by
    have he := hq.length_eq
    rw [hout.length_eq, List.length_cons, hkept] at he
    change T.assignedCount = S.assignedCount + 1 at he
    exact he
  have hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q := by
    intro v hv
    apply (U.endpoints _ (show A ++ x :: B ∈ U.chains by simp [hsys])).2 v
    have he := List.getLast?_eq_some_getLast (show x :: B ≠ [] by simp)
    simpa only [List.getLast?_append, he, Option.or] using hv
  have hD : ∀ v ∈ (y :: D).getLast?, v ∈ Q := by
    intro v hv
    apply (U.endpoints _ (show C ++ y :: D ∈ U.chains by simp [hsys])).2 v
    have he := List.getLast?_eq_some_getLast (show y :: D ≠ [] by simp)
    simpa only [List.getLast?_append, he, Option.or] using hv
  have hcount := RawPathSystem.different_chain_count (P := P) (M := M) (R := R) hA hC hB hD hJQ
  have hcount' : T.assignedCount + (if A = [] then 0 else 1) +
      (if C = [] then 0 else 1) = U.assignedCount + 1 := by
    simpa only [RawPathSystem.assignedCount, hT, hsys] using hcount
  rw [hTcount, hUe] at hcount'
  have hAnil : A = [] := by
    by_contra hn
    simp only [hn, ↓reduceIte] at hcount'
    omega
  have hCnil : C = [] := by
    by_contra hn
    simp only [hn, ↓reduceIte] at hcount'
    omega
  have hsum : original.sum = S.amount := by
    rw [ho.sum_eq, ← U.amount_eq_outside_count, hUa]
  have hlen : original.length = S.assignedCount := ho.length_eq.trans hUe
  have hbound := mul_length_le_sum hweights
  rw [hlen, hsum] at hbound
  exact ⟨hL, hAnil, hCnil, hbound⟩

theorem IsOptimal.terminal_same_chain_exclusion {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (U : RawPathSystem G Q) (hUa : U.amount = S.amount)
    (hUe : U.assignedCount = S.assignedCount)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {P R : List (List V)} {A B D : List V} {x y : V}
    (hsys : U.chains = P ++ (A ++ (x :: B) ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d := by
  intro h
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hpos : J ≠ [] := by intro he; simp only [he, List.length_nil] at hJlen; omega
  have hdis : J.Disjoint U.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzU
    exact hJout z hz (hUvertices z (List.mem_toFinset.mpr hzU))
  obtain ⟨T, original, output, kept, removed, hT, hTa, ho, hout, hp, hq⟩ :=
    U.replace_same_chain_profiled hsys hA hB hJ hJQ hpos hdis hpath
  obtain ⟨_, _, hkept, _, _⟩ := hopt.terminal_increment_profiles ht hQk hkQ hQ hcycle
    hd hd' U T hUa hUe ho hout hp hq (by omega)
  have hTcount : T.assignedCount = S.assignedCount + 1 := by
    have he := hq.length_eq
    rw [hout.length_eq, List.length_cons, hkept] at he
    change T.assignedCount = S.assignedCount + 1 at he
    exact he
  have hD : ∀ v ∈ (y :: D).getLast?, v ∈ Q := by
    intro v hv
    apply (U.endpoints _ (show A ++ (x :: B) ++ y :: D ∈ U.chains by simp [hsys])).2 v
    have he := List.getLast?_eq_some_getLast (show y :: D ≠ [] by simp)
    simpa only [List.getLast?_append, he, Option.or] using hv
  have hcount := RawPathSystem.same_chain_count (P := P) (R := R) hA hB hD hJQ
  have hcount' : T.assignedCount + (if A = [] then 0 else 1) = U.assignedCount := by
    simpa only [RawPathSystem.assignedCount, hT, hsys] using hcount
  rw [hTcount, hUe] at hcount'
  omega

end CycleClique.Construction.ExpandedPathSystem

end OAI
