import OAI.Combinatorics.Ramsey.CycleClique.Construction.TemplateEmbedding
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiniteConstraints

namespace OAI

/-! Computable validation of explicit initial-rule templates. Validation
checks paths and disjointness directly rather than trusting a forest search. -/

namespace CycleClique.Construction
variable {W V : Type*}

theorem chainCliqueCount_filter [DecidableEq W] (Q₀ : Finset W) (l : List W) :
    chainCliqueCount Q₀ l = (l.filter (fun v => decide (v ∈ Q₀))).length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [chainCliqueCount_cons, ih]
    by_cases hx : x ∈ Q₀ <;> simp [hx, Nat.add_comm]

theorem chainOutsideCount_filter [DecidableEq W] (Q₀ : Finset W) (l : List W) :
    chainOutsideCount Q₀ l = (l.filter (fun v => decide (v ∉ Q₀))).length := by
  classical
  unfold chainOutsideCount
  congr 1
  apply List.filter_congr
  intro v hv
  exact congrArg (fun h => @decide (v ∉ Q₀) h) (Subsingleton.elim _ _)

def RawChainsValid (H : SimpleGraph W) (Q₀ : Finset W) (C : List (List W)) : Prop :=
  C.flatten.Nodup ∧ ∀ l ∈ C,
    l.IsChain H.Adj ∧
    (∀ v ∈ l.head?, v ∈ Q₀) ∧ (∀ v ∈ l.getLast?, v ∈ Q₀) ∧
    l.IsChain (fun x y => ¬ (x ∈ Q₀ ∧ y ∈ Q₀))

instance [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (Q₀ : Finset W) (C : List (List W)) : Decidable (RawChainsValid H Q₀ C) :=
  inferInstanceAs (Decidable (_ ∧ _))

def RawPathSystem.ofValid {H : SimpleGraph W} {Q₀ : Finset W} {C : List (List W)}
    (h : RawChainsValid H Q₀ C) : RawPathSystem H Q₀ where
  chains := C
  paths := fun l hl => ⟨(List.nodup_flatten.mp h.1).1 l hl, (h.2 l hl).1⟩
  disjoint := (List.nodup_flatten.mp h.1).2
  endpoints := fun l hl => ⟨(h.2 l hl).2.1, (h.2 l hl).2.2.1⟩
  no_clique_steps := fun l hl => (h.2 l hl).2.2.2

structure TemplateData (W : Type*) where
  x : W
  y : W
  rest : List (List W)
  left : List W
  right : List W
  lo : ℕ
  hi : ℕ
  deriving DecidableEq, Repr

namespace TemplateData

variable [DecidableEq W]

def oldVertices (T : TemplateData W) : List W :=
  T.rest.flatten ++ (T.left ++ T.x :: T.y :: T.right)

def amount (Q₀ : Finset W) (T : TemplateData W) : ℕ :=
  (T.oldVertices.filter (fun v => decide (v ∉ Q₀))).length

def assignedCount (Q₀ : Finset W) (T : TemplateData W) : ℕ :=
  (T.rest.map (fun l => (l.filter (fun v => decide (v ∈ Q₀))).length - 1)).sum +
    (((T.left ++ T.x :: T.y :: T.right).filter (fun v => decide (v ∈ Q₀))).length - 1)

def incidentBound (Q₀ : Finset W) (T : TemplateData W) : ℕ :=
  (T.oldVertices.filter (fun v => decide (v ∈ Q₀))).length

def Valid (H : SimpleGraph W) (Q₀ : Finset W) (T : TemplateData W) : Prop :=
  RawChainsValid H Q₀ T.rest ∧ T.oldVertices.Nodup ∧
  (T.left ++ [T.x]).IsChain H.Adj ∧ (T.y :: T.right).IsChain H.Adj ∧
  (∀ v ∈ (T.left ++ [T.x]).head?, v ∈ Q₀) ∧
  (∀ v ∈ (T.y :: T.right).getLast?, v ∈ Q₀) ∧
  (T.left ++ [T.x]).IsChain (fun a b => ¬ (a ∈ Q₀ ∧ b ∈ Q₀)) ∧
  (T.y :: T.right).IsChain (fun a b => ¬ (a ∈ Q₀ ∧ b ∈ Q₀))

instance (H : SimpleGraph W) [DecidableRel H.Adj] (Q₀ : Finset W) (T : TemplateData W) :
    Decidable (T.Valid H Q₀) := inferInstanceAs (Decidable (_ ∧ _))

def toTemplate {H : SimpleGraph W} {Q₀ : Finset W} (T : TemplateData W)
    (h : T.Valid H Q₀) : OutsideTemplate H Q₀ T.x T.y where
  rest := RawPathSystem.ofValid h.1
  left := T.left
  right := T.right
  nodup := h.2.1
  left_path := h.2.2.1
  right_path := h.2.2.2.1
  start := h.2.2.2.2.1
  finish := h.2.2.2.2.2.1
  left_steps := h.2.2.2.2.2.2.1
  right_steps := h.2.2.2.2.2.2.2

@[simp] theorem toTemplate_amount {H : SimpleGraph W} {Q₀ : Finset W}
    (T : TemplateData W) (h : T.Valid H Q₀) : (T.toTemplate h).amount = T.amount Q₀ := by
  exact chainOutsideCount_filter Q₀ T.oldVertices

@[simp] theorem toTemplate_incidentBound {H : SimpleGraph W} {Q₀ : Finset W}
    (T : TemplateData W) (h : T.Valid H Q₀) :
    (T.toTemplate h).incidentBound = T.incidentBound Q₀ := by
  exact chainCliqueCount_filter Q₀ T.oldVertices

@[simp] theorem toTemplate_assignedCount {H : SimpleGraph W} {Q₀ : Finset W}
    (T : TemplateData W) (h : T.Valid H Q₀) :
    (T.toTemplate h).assignedCount = T.assignedCount Q₀ := by
  change rawAssignedCount Q₀ T.rest + (chainCliqueCount Q₀ _ - 1) = _
  simp only [rawAssignedCount, chainCliqueCount_filter, assignedCount]
  rfl

def Check (H : SimpleGraph W) (Q₀ : Finset W) (k L e : ℕ) (T : TemplateData W) : Prop :=
  T.Valid H Q₀ ∧ 1 ≤ T.lo ∧
    L + (if e ≤ T.assignedCount Q₀ then 1 else 0) ≤ T.amount Q₀ + T.lo ∧
    T.amount Q₀ + T.hi + T.incidentBound Q₀ ≤ k + 1

instance (H : SimpleGraph W) [DecidableRel H.Adj] (Q₀ : Finset W)
    (k L e : ℕ) (T : TemplateData W) : Decidable (T.Check H Q₀ k L e) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {G : SimpleGraph V} {Q : Finset V} {H : SimpleGraph W} {Q₀ : Finset W}

theorem forbids {S : ExpandedPathSystem G Q} {k L e d : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (ha : S.amount = L) (he : S.assignedCount = e)
    (f : W → V) (hf : Function.Injective f) (hfQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hfG : ∀ {i j}, H.Adj i j → G.Adj (f i) (f j))
    (hfX : ∀ i, f i ∈ Q ∨ f i ∈ S.vertices)
    (T : TemplateData W) (hc : T.Check H Q₀ k L e) (hd : d ∈ Finset.Icc T.lo T.hi) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) (f T.x) (f T.y) d := by
  have hl := (Finset.mem_Icc.mp hd).1
  have hu := (Finset.mem_Icc.mp hd).2
  let U := (T.toTemplate hc.1).embed f hf hfQ hfG
  have hUa : U.amount = T.amount Q₀ := by simp [U]
  have hUe : U.assignedCount = T.assignedCount Q₀ := by simp [U]
  have hUi : U.incidentBound = T.incidentBound Q₀ := by simp [U]
  apply U.forbids hopt hk hQk hQ hcycle
  · intro v hv
    rw [OutsideTemplate.embed_oldVertices] at hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact hfX i
  · exact hc.2.1.trans hl
  · rw [ha, he, hUa, hUe]
    exact hc.2.2.1.trans (Nat.add_le_add_left hl _)
  · rw [hUa, hUi]
    have hh := hc.2.2.2
    omega

end TemplateData
end CycleClique.Construction

end OAI
