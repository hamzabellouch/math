import OAI.Computability.PerfectCompleteness.Foundations.WholeArraySubtreeSplit
import OAI.Computability.PerfectCompleteness.Sampling.WholeArrayInteriorHiddenLaw

namespace OAI


namespace PerfectCompleteness.WholeArrayInteriorExterior

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays WholeArraySampler
open WholeArraySubtreeSplit
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {N n m t : Nat}

def upperNode : {N n : Nat} → Path branch N (n + 1) → Nodes branch N
  | _, _, .refl _ => .inl ()
  | _, _, .step j p => .inr (j, upperNode p)

@[simp] theorem upperNode_refl :
    upperNode (DescendantSpaces.Path.refl (n + 1) : Path branch (n + 1) (n + 1)) =
      (Sum.inl () : Nodes branch (n + 1)) := rfl

@[simp] theorem upperNode_step (j : Fin (branch N)) (p : Path branch N (n + 1)) :
    upperNode (.step j p) = .inr (j, upperNode p) := rfl

@[simp] theorem upperNode_height :
    {N n : Nat} → (p : Path branch N (n + 1)) → Nodes.height (upperNode p) = n + 1
  | _, _, .refl _ => rfl
  | _, _, .step _ p => upperNode_height p

theorem upperNode_spec :
    {N n : Nat} → (p : Path branch N (n + 1)) →
      (⟨Nodes.height (upperNode p), Nodes.path (upperNode p)⟩ :
        Σ h, Path branch N h) = ⟨n + 1, p⟩
  | _, _, .refl _ => rfl
  | N + 1, _, .step j p =>
      congrArg (fun z : Σ h, Path branch N h =>
        (⟨z.1, Path.step j z.2⟩ : Σ h, Path branch (N + 1) h)) (upperNode_spec p)

theorem upperNode_path_heq (p : Path branch N (n + 1)) :
    HEq (Nodes.path (upperNode p)) p :=
  (Sigma.mk.inj (upperNode_spec p)).2

def selectedNode : {N h : Nat} → (p : Path branch N h) → 0 < h → Nodes branch N
  | _, 0, _, hpos => False.elim (Nat.not_lt_zero _ hpos)
  | _, _ + 1, p, _ => upperNode p

@[simp] theorem selectedNode_succ (p : Path branch N (n + 1)) (hpos : 0 < n + 1) :
    selectedNode p hpos = upperNode p := rfl

theorem selectedNode_step {h : Nat} (j : Fin (branch N)) (p : Path branch N h)
    (hpos : 0 < h) :
    selectedNode (.step j p) hpos = .inr (j, selectedNode p hpos) := by
  cases h with
  | zero => exact False.elim (Nat.not_lt_zero _ hpos)
  | succ h => rfl

@[simp] theorem selectedNode_nodePath :
    {N : Nat} → (node : Nodes branch N) → (hpos : 0 < Nodes.height node) →
      selectedNode (Nodes.path node) hpos = node
  | 0, node, _ => nomatch node
  | _ + 1, .inl u, _ => by cases u; rfl
  | N + 1, .inr (j, node), hpos =>
      (selectedNode_step j (Nodes.path node) hpos).trans
        (congrArg (fun a : Nodes branch N => (Sum.inr (j, a) : Nodes branch (N + 1)))
          (selectedNode_nodePath node hpos))

def upperTape (rows repeats : Nat → Nat) (i : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rest : WholeArrayHiddenLaw.RestTape rows repeats i q slots) :
    Tape rows repeats (.step i q) slots := fun field =>
  match field with
  | .inl _ => fun _ => RecursiveSampler.zeroTape F2 repeats (.step i q) (LeafDomain slots)
  | .inr (.inl _) => rest ⟨.inr (.inl ()), by simp⟩
  | .inr (.inr j) => rest ⟨.inr (.inr j), by simp⟩

def read (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (p.append (.step i q)) slots) :
    WholeArrayInteriorHiddenLaw.Exterior rows repeats p i q slots :=
  let subtree := splitEquiv rows repeats p (.step i q) slots ω
  (subtree.1, fun field => subtree.2 field.val)

theorem read_split (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (ω : Tape rows repeats (p.append (.step i q)) slots) :
    (WholeArrayInteriorHiddenLaw.split rows repeats p i q slots W ω).2.2 =
      read rows repeats p i q slots ω := rfl

def rebuild (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (external : WholeArrayInteriorHiddenLaw.Exterior rows repeats p i q slots) :
    Tape rows repeats (p.append (.step i q)) slots :=
  (splitEquiv rows repeats p (.step i q) slots).symm
    (external.1, upperTape rows repeats i q (subtreeSlots p slots) external.2)

theorem evaluate_rebuild_read (rows repeats : Nat → Nat) (p : Path branch N (n + 1)) :
    ∀ {m : Nat} (i : Fin (branch n)) (q : Path branch n m)
      (slots : Slots branch N → Fin t → MixedSupport.Slot)
      (ω : Tape rows repeats (p.append (.step i q)) slots)
      (node : Nodes branch N), node ≠ upperNode p →
      WholeArraySampler.evaluate rows repeats (p.append (.step i q)) slots
          (rebuild rows repeats p i q slots (read rows repeats p i q slots ω)) node =
        WholeArraySampler.evaluate rows repeats (p.append (.step i q)) slots ω node := by
  induction N generalizing n with
  | zero =>
      have h := p.height_le
      omega
  | succ N ih =>
      cases p with
      | refl =>
          intro m i q slots ω node hnode
          cases node with
          | inl u =>
              cases u
              exact False.elim (hnode rfl)
          | inr pair =>
              rcases pair with ⟨j, node⟩
              rfl
      | step j p =>
          intro m i q slots ω node hnode
          cases node with
          | inl u =>
              cases u
              rfl
          | inr pair =>
              rcases pair with ⟨l, node⟩
              by_cases hlj : l = j
              · subst l
                have hchild : node ≠ upperNode p := by
                  intro h
                  exact hnode (congrArg (fun a => Sum.inr (j, a)) h)
                exact (WholeArraySampler.evaluate_selected rows repeats j
                  (p.append (.step i q)) slots
                  (rebuild rows repeats (.step j p) i q slots
                    (read rows repeats (.step j p) i q slots ω)) node).trans
                  ((ih p i q (childSlots slots j) (ω (.inr (.inl ()))) node hchild).trans
                    (WholeArraySampler.evaluate_selected rows repeats j
                      (p.append (.step i q)) slots ω node).symm)
              · exact (WholeArraySampler.evaluate_ordinary rows repeats j
                  (p.append (.step i q)) slots
                  (rebuild rows repeats (.step j p) i q slots
                    (read rows repeats (.step j p) i q slots ω)) ⟨l, hlj⟩ node).trans
                  (WholeArraySampler.evaluate_ordinary rows repeats j
                    (p.append (.step i q)) slots ω ⟨l, hlj⟩ node).symm

theorem evaluate_rebuild_split (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (ω : Tape rows repeats (p.append (.step i q)) slots)
    (node : Nodes branch N) (hnode : node ≠ upperNode p) :
    WholeArraySampler.evaluate rows repeats (p.append (.step i q)) slots
        (rebuild rows repeats p i q slots
          (WholeArrayInteriorHiddenLaw.split rows repeats p i q slots W ω).2.2) node =
      WholeArraySampler.evaluate rows repeats (p.append (.step i q)) slots ω node :=
  evaluate_rebuild_read rows repeats p i q slots ω node hnode

abbrev NonUpper (p : Path branch N (n + 1)) :=
  {node : Nodes branch N // node ≠ upperNode p}

def nodeArray (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (external : WholeArrayInteriorHiddenLaw.Exterior rows repeats p i q slots)
    (node : NonUpper p) :
    Fin (rows (Nodes.height node.val)) → H (nodeSlots slots node.val) :=
  WholeArraySampler.evaluate rows repeats (p.append (.step i q)) slots
    (rebuild rows repeats p i q slots external) node.val

theorem nodeArray_read (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (p.append (.step i q)) slots) (node : NonUpper p) :
    nodeArray rows repeats p i q slots (read rows repeats p i q slots ω) node =
      WholeArraySampler.evaluate rows repeats (p.append (.step i q)) slots ω node.val :=
  evaluate_rebuild_read rows repeats p i q slots ω node.val node.property

theorem nodeArray_split (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (ω : Tape rows repeats (p.append (.step i q)) slots) (node : NonUpper p) :
    nodeArray rows repeats p i q slots
        (WholeArrayInteriorHiddenLaw.split rows repeats p i q slots W ω).2.2 node =
      WholeArraySampler.evaluate rows repeats (p.append (.step i q)) slots ω node.val :=
  evaluate_rebuild_split rows repeats p i q slots W ω node.val node.property

end
end PerfectCompleteness.WholeArrayInteriorExterior


namespace PerfectCompleteness.SelectedArrayReplacement

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def selectedRows (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    Fin (rows (m + 1)) → H (subtreeSlots p slots) :=
  restrictArrays rows p slots arrays (.inl ())

def replace (rows : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) → Arrays slots rows →
        (Fin (rows (m + 1)) → H (subtreeSlots p slots)) → Arrays slots rows
  | _, _, .refl _, slots, arrays, fresh =>
      WholeArraySampler.assemble slots rows fresh
        (fun child node => arrays (.inr (child, node)))
  | _, _, .step i p, slots, arrays, fresh =>
      WholeArraySampler.assemble slots rows (arrays (.inl ()))
        (WholeArraySampler.childrenAt slots rows i
          (replace rows p (childSlots slots i) (fun node => arrays (.inr (i, node))) fresh)
          (fun child node => arrays (.inr (child.val, node))))

@[simp] theorem selectedRows_refl (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    selectedRows rows (.refl (m + 1)) slots arrays = arrays (.inl ()) := rfl

@[simp] theorem selectedRows_step (rows : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    selectedRows rows (.step i p) slots arrays =
      selectedRows rows p (childSlots slots i) (fun node => arrays (.inr (i, node))) := rfl

theorem replace_step (rows : Nat → Nat) (i : Fin (branch n)) (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows)
    (fresh : Fin (rows (m + 1)) → H (subtreeSlots (.step i p) slots)) :
    replace rows (.step i p) slots arrays fresh =
      WholeArraySampler.assemble slots rows (arrays (.inl ()))
        (WholeArraySampler.childrenAt slots rows i
          (replace rows p (childSlots slots i) (fun node => arrays (.inr (i, node))) fresh)
          (fun child node => arrays (.inr (child.val, node)))) := rfl

@[simp] theorem selectedRows_assemble_refl (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (root : Fin (rows (m + 1)) → H slots)
    (children : ∀ child, Arrays (childSlots slots child) rows) :
    selectedRows rows (.refl (m + 1)) slots
      (WholeArraySampler.assemble slots rows root children) = root := rfl

@[simp] theorem selectedRows_assemble_step (rows : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (root : Fin (rows (n + 1)) → H slots) (selected : Arrays (childSlots slots i) rows)
    (ordinary : ∀ child : RecursiveSampler.OffPath i, Arrays (childSlots slots child.val) rows) :
    selectedRows rows (.step i p) slots
        (WholeArraySampler.assemble slots rows root
          (WholeArraySampler.childrenAt slots rows i selected ordinary)) =
      selectedRows rows p (childSlots slots i) selected := by
  exact congrArg (selectedRows rows p (childSlots slots i))
    (WholeArraySampler.childrenAt_selected slots rows i selected ordinary)

@[simp] theorem replace_assemble_refl (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (root : Fin (rows (m + 1)) → H slots)
    (children : ∀ child, Arrays (childSlots slots child) rows)
    (fresh : Fin (rows (m + 1)) → H slots) :
    replace rows (.refl (m + 1)) slots
        (WholeArraySampler.assemble slots rows root children) fresh =
      WholeArraySampler.assemble slots rows fresh children := rfl

@[simp] theorem replace_assemble_step (rows : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (root : Fin (rows (n + 1)) → H slots) (selected : Arrays (childSlots slots i) rows)
    (ordinary : ∀ child : RecursiveSampler.OffPath i, Arrays (childSlots slots child.val) rows)
    (fresh : Fin (rows (m + 1)) → H (subtreeSlots (.step i p) slots)) :
    replace rows (.step i p) slots
        (WholeArraySampler.assemble slots rows root
          (WholeArraySampler.childrenAt slots rows i selected ordinary)) fresh =
      WholeArraySampler.assemble slots rows root
        (WholeArraySampler.childrenAt slots rows i
          (replace rows p (childSlots slots i) selected fresh) ordinary) := by
  simp only [replace_step, WholeArraySampler.assemble,
    WholeArraySampler.childrenAt_selected, WholeArraySampler.childrenAt_ordinary]

@[simp] theorem selectedRows_replace (rows : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows)
      (fresh : Fin (rows (m + 1)) → H (subtreeSlots p slots)),
      selectedRows rows p slots (replace rows p slots arrays fresh) = fresh := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro slots arrays fresh; rfl
      | step i p =>
          intro slots arrays fresh
          exact (selectedRows_assemble_step rows i p slots (arrays (.inl ()))
            (replace rows p (childSlots slots i) (fun node => arrays (.inr (i, node))) fresh)
            (fun child node => arrays (.inr (child.val, node)))).trans
              (ih p (childSlots slots i) (fun node => arrays (.inr (i, node))) fresh)

theorem replace_outside (rows : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows)
      (fresh : Fin (rows (m + 1)) → H (subtreeSlots p slots)) (node : Nodes branch n),
      node ≠ upperNode p → replace rows p slots arrays fresh node = arrays node := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro slots arrays fresh node hnode
          cases node with
          | inl u => cases u; exact False.elim (hnode rfl)
          | inr pair => rfl
      | step i p =>
          intro slots arrays fresh node hnode
          cases node with
          | inl u => cases u; rfl
          | inr pair =>
              rcases pair with ⟨child, node⟩
              by_cases hchild : child = i
              · subst child
                have hnode' : node ≠ upperNode p := by
                  intro h
                  exact hnode (congrArg (fun v => Sum.inr (i, v)) h)
                exact (congrFun (WholeArraySampler.childrenAt_selected slots rows i
                  (replace rows p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh)
                  (fun j v => arrays (.inr (j.val, v)))) node).trans
                    (ih p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh node hnode')
              · exact congrFun (WholeArraySampler.childrenAt_ordinary slots rows i
                    (replace rows p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh)
                    (fun j v => arrays (.inr (j.val, v))) ⟨child, hchild⟩) node

@[simp] theorem replace_same (rows : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows),
      replace rows p slots arrays (selectedRows rows p slots arrays) = arrays := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro slots arrays
          funext node
          rcases node with u | ⟨child, node⟩
          · cases u
            rfl
          · rfl
      | step i p =>
          intro slots arrays
          rw [replace_step, selectedRows_step,
            ih p (childSlots slots i) (fun v => arrays (.inr (i, v)))]
          funext node
          rcases node with u | ⟨child, node⟩
          · cases u
            rfl
          · by_cases hchild : child = i
            · subst child
              exact congrFun (WholeArraySampler.childrenAt_selected slots rows i
                (fun v => arrays (.inr (i, v))) (fun j v => arrays (.inr (j.val, v)))) node
            · exact congrFun (WholeArraySampler.childrenAt_ordinary slots rows i
                (fun v => arrays (.inr (i, v))) (fun j v => arrays (.inr (j.val, v)))
                ⟨child, hchild⟩) node

end
end PerfectCompleteness.SelectedArrayReplacement

end OAI
