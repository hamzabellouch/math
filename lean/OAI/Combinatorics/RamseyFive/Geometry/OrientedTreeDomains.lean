import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.TreeWeights
import OAI.Combinatorics.RamseyFive.Geometry.OrientedNodeProcess
import OAI.Combinatorics.RamseyFive.Geometry.TreeShape
import OAI.Combinatorics.RamseyFive.Geometry.TargetCaps
import OAI.Combinatorics.RamseyFive.Entropy.TargetLoss

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type}

def flagRectangle (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V))) :
    Finset ((ℙ K V)×(ℙ K (Dual K V))) := (A×ˢB).filter fun z=>Incident z.1 z.2

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
  [Fintype (ℙ K (Dual K V))] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma mem_flagRectangle (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V)))
    (z : (ℙ K V)×(ℙ K (Dual K V))) :
    z∈flagRectangle A B ↔ z.1∈A ∧ z.2∈B ∧ Incident z.1 z.2 := by
  simp only [flagRectangle,Finset.mem_filter,Finset.mem_product,and_assoc]

def orientedNodeDomain (C : PivotContext K V) (t : OrientedPivotTape f r C)
    (m : OrientedPivotMessage f r C t) :=
  let d:=orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t m
  flagRectangle (C.1∩d.2) (C.2∩d.1)

def orientedPublicDomain (tree : BinaryTree I) (ω : OrientedPivotTreeTape f r tree)
    (C : PivotContext K V) (m : OrientedPivotTreeMessage f r tree ω C) (j : Address tree) :=
  (decodedAt (fun _ : I=>OrientedPivotTape f r) (fun _ : I=>OrientedPivotMessage f r)
    (fun _=>orientedPivotLeft f r) (fun _=>orientedPivotRight f r)
    (fun _=>orientedNodeDomain f r) tree ω C m j).getD ∅

theorem orientedPublicDomain_card
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5)
    (A₀ : I→Finset (ℙ K V)) (B₀ : I→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i,(A₀ i).Nonempty) (hB₀ : ∀ i,(B₀ i).Nonempty)
    (c τ P b : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hb : 0≤b)
    (hp : ∀ i,(Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀ i).card*(B₀ i).card)
    (tree : BinaryTree I) (ω : OrientedPivotTreeTape f r tree) (C : PivotContext K V)
    (j : Address tree) :
    ((orientedPublicDomain f r tree ω C
      (orientedPivotTreeEncoded f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c (9/10) τ P
        (by norm_num) tree ω C) j).card:ℝ)≤
      2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp (b+1) := by
  let enc:=fun i C t=>orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c (9/10) τ P (by norm_num) t
  let obs:=observe (fun _ : I=>OrientedPivotTape f r) (fun _ : I=>OrientedPivotMessage f r)
    (fun _=>orientedPivotLeft f r) (fun _=>orientedPivotRight f r) enc
    (fun _=>orientedNodeDomain f r) tree ω C j
  have he : orientedPublicDomain f r tree ω C
      (orientedPivotTreeEncoded f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c (9/10) τ P
        (by norm_num) tree ω C) j=obs.getD ∅ := by
    exact congrArg (fun d=>d.getD ∅) (decodedAt_encoded _ _ _ _ enc
      (fun _=>orientedNodeDomain f r) tree ω C j)
  rw [he]
  cases ho:obs with
  | none => simp only [Option.getD_none,Finset.card_empty,Nat.cast_zero]; positivity
  | some d =>
    simp only [Option.getD_some]
    exact observe_invariant _ _ _ _ enc (fun _=>orientedNodeDomain f r)
      (fun _=>True) (fun _ d=>(d.card:ℝ)≤2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp (b+1))
      (fun _ _ _ _ _ _=>True.intro) (fun _ _ _ _ _ _=>True.intro)
      (fun i C t m _ hm=>orientedGuardedNode_flags (f C) (r C) σ hσ hq hd
        (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c τ P b hc hc9 hb (hp i) t m hm)
      tree ω C True.intro j d ho

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
  [Fintype (ℙ K (Dual K V))] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma targetCovered_some (C : PivotContext K V)
    (D : Finset (ℙ K (Dual K V))×Finset (ℙ K V)) (a : ℙ K V) (b : ℙ K (Dual K V)) :
    TargetCovered (some C) (some D) a b ↔ a∈C.1 ∧ b∈C.2 ∧ a∈D.2 ∧ b∈D.1 := by
  constructor
  · rintro ⟨C',D',hC,hD,h⟩
    cases Option.some.inj hC
    cases Option.some.inj hD
    exact h
  · intro h
    exact ⟨C,D,rfl,rfl,h⟩

theorem orientedPublicDomain_coverage
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : I→Finset (ℙ K V)) (B₀ : I→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i,(A₀ i).Nonempty) (hB₀ : ∀ i,(B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ)
    (tree : BinaryTree I) (ω : OrientedPivotTreeTape f r tree) (C : PivotContext K V)
    (j : Address tree) (z : (ℙ K V)×(ℙ K (Dual K V))) :
    z∈orientedPublicDomain f r tree ω C
      (orientedPivotTreeEncoded f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C) j ↔
    TargetCovered (orientedPivotContextAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j)
      (orientedPivotCapsAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ tree ω C j) z.1 z.2 ∧
      Incident z.1 z.2 := by
  induction tree generalizing C with
  | nil => exact nomatch j
  | node i lt rt ihl ihr =>
    rcases j with j | (j | j)
    · cases he:orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
        (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ (ω.1 C) <;>
        simp [orientedPublicDomain,orientedPivotTreeEncoded,encoded,decodedAt,
          orientedPivotContextAt,contextAt,orientedPivotCapsAt,observe,probe,he,
          targetCovered_some,orientedNodeDomain,mem_flagRectangle,Finset.mem_inter,and_left_comm,and_assoc]
      ; simp [TargetCovered]
    · cases he:orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
        (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ (ω.1 C) with
      | none => simp [orientedPublicDomain,orientedPivotTreeEncoded,encoded,decodedAt,
          orientedPivotContextAt,contextAt,orientedPivotCapsAt,observe,probe,he,TargetCovered]
      | some m =>
        simpa only [orientedPublicDomain,orientedPivotTreeEncoded,encoded,decodedAt,
          orientedPivotContextAt,contextAt,orientedPivotCapsAt,observe,probe,he,
          Option.map_some,Option.elim_some]
          using ihl ω.2.1 (orientedPivotLeft f r C (ω.1 C) m) j
    · cases he:orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd
        (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c δ τ P hδ (ω.1 C) with
      | none => simp [orientedPublicDomain,orientedPivotTreeEncoded,encoded,decodedAt,
          orientedPivotContextAt,contextAt,orientedPivotCapsAt,observe,probe,he,TargetCovered]
      | some m =>
        simpa only [orientedPublicDomain,orientedPivotTreeEncoded,encoded,decodedAt,
          orientedPivotContextAt,contextAt,orientedPivotCapsAt,observe,probe,he,
          Option.map_some,Option.elim_some]
          using ihr ω.2.2 (orientedPivotRight f r C (ω.1 C) m) j

end
end

open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

abbrev VariableTreeTape (w : ℕ) := ∀ m : Fin (w+1),OrientedPivotTreeTape f r (finiteBalanced m.val)

def variableTreeLaw (w : ℕ) : Law (VariableTreeTape f r w) :=
  piLaw (fun m : Fin (w+1)=>orientedPivotTreeLaw f r (finiteBalanced m.val))

omit [Finite K] [FiniteDimensional K V] in
lemma variableTreeLaw_eval (w : ℕ) (m : Fin (w+1)) :
    map (variableTreeLaw f r w) (fun t=>t m)=orientedPivotTreeLaw f r (finiteBalanced m.val) :=
  piLaw_eval _ _

abbrev VariableTreeMessage {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V) :=
  (m : Fin (w+1)) × OrientedPivotTreeMessage f r (finiteBalanced m.val) (t m) C

def variableTreeCost {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (a : VariableTreeMessage f r t C) : ℝ :=
  Real.log (w+1)+orientedPivotSlotCost f r (finiteBalanced a.1.val) (t a.1) C a.2

omit [Finite K] in
lemma variableTree_weight {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (hf : ∀ C,(f C).Normalized) (hr : ∀ C,(r C).Normalized) :
    (∑ a : VariableTreeMessage f r t C,Real.exp (-variableTreeCost f r t C a)) ≤ 1 := by
  simpa only [variableTreeCost,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    sigma_header_weight (Fin (w+1))
      (fun m=>OrientedPivotTreeMessage f r (finiteBalanced m.val) (t m) C)
      (fun m=>orientedPivotSlotCost f r (finiteBalanced m.val) (t m) C)
      (fun _=>orientedPivotTree_weight f r hf hr _ _ _)

def variableTreeDomain {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (a : VariableTreeMessage f r t C) (j : Fin (w+1)) : Finset ((ℙ K V)×(ℙ K (Dual K V))) :=
  if h : j.val<a.1.val then
    orientedPublicDomain f r (finiteBalanced a.1.val) (t a.1) C a.2
      ((finiteRankEquiv a.1.val).symm ⟨j.val,h⟩)
  else ∅

omit [Finite K] in
lemma variableTreeDomain_valid {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (a : VariableTreeMessage f r t C) (j : Fin a.1.val) :
    variableTreeDomain f r t C a ⟨j.val,lt_trans j.isLt a.1.isLt⟩=
      orientedPublicDomain f r _ (t a.1) C a.2 ((finiteRankEquiv a.1.val).symm j) := by
  simp only [variableTreeDomain,dite_eq_left j.isLt]

def variableTreeEncoded {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (m : Fin (w+1)) (σ : ℝ) (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V ≤ 5)
    (A₀ : Fin (m.val+1)→Finset (ℙ K V)) (B₀ : Fin (m.val+1)→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i,(A₀ i).Nonempty) (hB₀ : ∀ i,(B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) : VariableTreeMessage f r t C :=
  ⟨m,orientedPivotTreeEncoded f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ
    (finiteBalanced m.val) (t m) C⟩

lemma variableTreeDomain_card {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (m : Fin (w+1)) (σ : ℝ) (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V=5)
    (A₀ : Fin (m.val+1)→Finset (ℙ K V)) (B₀ : Fin (m.val+1)→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i,(A₀ i).Nonempty) (hB₀ : ∀ i,(B₀ i).Nonempty)
    (c τ P b : ℝ) (hc : 0<c) (hc9 : c ≤ 9/10) (hb : 0 ≤ b)
    (hp : ∀ i,(Nat.card K:ℝ)^5*Real.exp (-b) ≤ (A₀ i).card*(B₀ i).card)
    (j : Fin (w+1)) :
    ((variableTreeDomain f r t C
      (variableTreeEncoded f r t C m σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c (9/10) τ P (by norm_num)) j).card:ℝ) ≤
      2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp (b+1) := by
  unfold variableTreeDomain variableTreeEncoded
  dsimp only
  split_ifs with h
  · exact orientedPublicDomain_card f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c τ P b hc hc9 hb hp
      _ _ C _
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity

lemma variableTreeDomain_coverage {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (m : Fin (w+1)) (σ : ℝ) (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V ≤ 5)
    (A₀ : Fin (m.val+1)→Finset (ℙ K V)) (B₀ : Fin (m.val+1)→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i,(A₀ i).Nonempty) (hB₀ : ∀ i,(B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (j : Fin m.val) (a : ℙ K V) (b : ℙ K (Dual K V)) :
    (a,b)∈variableTreeDomain f r t C
      (variableTreeEncoded f r t C m σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ)
      ⟨j.val,lt_trans j.isLt m.isLt⟩ ↔
    Incident a b ∧ TargetCovered
      (orientedPivotContextAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ
        (finiteBalanced m.val) (t m) C ((finiteRankEquiv m.val).symm j))
      (orientedPivotCapsAt f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ
        (finiteBalanced m.val) (t m) C ((finiteRankEquiv m.val).symm j)) a b := by
  unfold variableTreeEncoded
  rw [variableTreeDomain_valid]
  exact (orientedPublicDomain_coverage f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c δ τ P hδ
    (finiteBalanced m.val) (t m) C _ (a,b)).trans and_comm

end

end SharpRamseyFive.ProjectiveIncidence

end OAI
