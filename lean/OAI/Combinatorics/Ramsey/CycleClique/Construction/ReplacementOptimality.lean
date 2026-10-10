import OAI.Combinatorics.Ramsey.CycleClique.Construction.SameChainReplacement
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawCliqueCompletion
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OptimalPathSystem
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OutsidePathRules

namespace OAI

/-! One-vertex representative exclusions from the concrete chain surgery. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

theorem IsOptimal.no_one_vertex_raw {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (T : RawPathSystem G Q)
    (hinc : T.amount = S.amount + 1) : False :=
  hopt.no_one_vertex_increase hk hQk hQ hcycle T.normalize (by simpa using hinc)

theorem IsOptimal.forbidden_different_chain_one {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (U : RawPathSystem G Q)
    (hUamount : U.amount = S.amount)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {P M R : List (List V)} {A B C D : List V} {x y : V}
    (hsys : U.chains = P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y 1 := by
  intro h
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hpos : J ≠ [] := by intro he; simp [he] at hJlen
  have hdis : J.Disjoint U.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzU
    exact hJout z hz (hUvertices z (List.mem_toFinset.mpr hzU))
  obtain ⟨T, _, hamount⟩ := U.replace_different_chains hsys hA hC hJ hJQ hpos hdis hpath
  exact hopt.no_one_vertex_raw hk hQk hQ hcycle T (by omega)

theorem IsOptimal.forbidden_same_chain_one {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (U : RawPathSystem G Q)
    (hUamount : U.amount = S.amount)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {P R : List (List V)} {A B D : List V} {x y : V}
    (hsys : U.chains = P ++ (A ++ (x :: B) ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q)
    (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y 1 := by
  intro h
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hpos : J ≠ [] := by intro he; simp [he] at hJlen
  have hdis : J.Disjoint U.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzU
    exact hJout z hz (hUvertices z (List.mem_toFinset.mpr hzU))
  obtain ⟨T, _, hamount⟩ := U.replace_same_chain hsys hA hB hJ hJQ hpos hdis hpath
  exact hopt.no_one_vertex_raw hk hQk hQ hcycle T (by omega)

end CycleClique.Construction.ExpandedPathSystem

end OAI
