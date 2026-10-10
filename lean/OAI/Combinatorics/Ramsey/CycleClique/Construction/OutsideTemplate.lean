import OAI.Combinatorics.Ramsey.CycleClique.Construction.OutsideChainTemplate
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OptimalPathSystem

namespace OAI

/-! A certificate for one use of the initial extension rule consists of
old disjoint chains and two tails joined by the proposed outside path. -/

namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

structure OutsideTemplate (G : SimpleGraph V) (Q : Finset V) (x y : V) where
  rest : RawPathSystem G Q
  left : List V
  right : List V
  nodup : (rest.chains.flatten ++ (left ++ x :: y :: right)).Nodup
  left_path : (left ++ [x]).IsChain G.Adj
  right_path : (y :: right).IsChain G.Adj
  start : ∀ v ∈ (left ++ [x]).head?, v ∈ Q
  finish : ∀ v ∈ (y :: right).getLast?, v ∈ Q
  left_steps : (left ++ [x]).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q))
  right_steps : (y :: right).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q))

namespace OutsideTemplate

variable {x y : V}

def oldVertices (T : OutsideTemplate G Q x y) : List V :=
  T.rest.chains.flatten ++ (T.left ++ x :: y :: T.right)

noncomputable def amount (T : OutsideTemplate G Q x y) : ℕ :=
  chainOutsideCount Q T.oldVertices

noncomputable def assignedCount (T : OutsideTemplate G Q x y) : ℕ :=
  T.rest.assignedCount + (chainCliqueCount Q (T.left ++ x :: y :: T.right) - 1)

noncomputable def incidentBound (T : OutsideTemplate G Q x y) : ℕ :=
  chainCliqueCount Q T.oldVertices

theorem forbids {S : ExpandedPathSystem G Q} {k d : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (T : OutsideTemplate G Q x y)
    (hin : ∀ v ∈ T.oldVertices, v ∈ Q ∨ v ∈ S.vertices) (hd : 1 ≤ d)
    (hlow : S.amount + (if S.assignedCount ≤ T.assignedCount then 1 else 0) ≤ T.amount + d)
    (hhigh : T.amount + d + T.incidentBound ≤ k + 1) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d := by
  intro h
  obtain ⟨J, hJ, hlen, hout, hpath⟩ := h.interior
  have hJne : J ≠ [] := by intro he; simp only [he, List.length_nil] at hlen; omega
  have hdis : J.Disjoint T.oldVertices := by
    apply List.disjoint_left.mpr
    intro v hv ho
    exact hout v hv (hin v ho)
  obtain ⟨U, _, hUa, hUe, hUi⟩ := T.rest.expand_outside_template T.nodup
    T.left_path T.right_path T.start T.finish T.left_steps T.right_steps hJ hJne
    (fun v hv hQv => hout v hv (Or.inl hQv)) hdis hpath
  have ha : U.normalize.amount = T.amount + d := by
    rw [RawPathSystem.normalize_amount, hUa, hlen]
    rfl
  have he : U.normalize.assignedCount = T.assignedCount := by
    rw [RawPathSystem.normalize_assignedCount, hUe]
    rfl
  apply hopt.criterion hk hQk hQ hcycle U.normalize
  · simpa only [ha, he] using hlow
  · change U.normalize.incident ≤ T.incidentBound at hUi
    omega

end OutsideTemplate
end CycleClique.Construction

end OAI
