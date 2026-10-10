import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialExact
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.OrdinarySelection

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldInitialHash

open MatrixMultiplication.Foundation AllFieldFiniteFamily AllFieldInitialStep
open JointPopulation JointCoarseHashing
open scoped BigOperators Classical

variable {K : ℕ} (counts : Fin K → Shape → ℕ)

def xKeep (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Position counts) k) (w : CoarseWord counts) : Prop :=
  JointHashing.xHash s (castWord k w) ∈ U

def yKeep (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Position counts) k) (w : CoarseWord counts) : Prop :=
  JointHashing.yHash s (castWord k w) ∈ U

def zKeep (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Position counts) k) (w : CoarseWord counts) : Prop :=
  JointHashing.zHash (twoUnit k) s (fun _ => (16 : ZMod (37 ^ k))) (castWord k w) ∈ U

theorem ambient_support {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ) (f : Triple (Position counts))
    (hf : f ∈ ambientSet counts (fun _ => 16)) :
    HasSupportSum (fun _ => 16) f :=
  (Finset.mem_filter.mp hf).2.1

theorem target_mem_ambient
    (hsupport : ∀ h u, 0 < counts h u → u.1.val + u.2.1.val + u.2.2.val = 16)
    (e : Target counts) : triple counts e ∈ ambientSet counts (fun _ => 16) :=
  targetSet_subset_ambient counts (fun _ => 16) hsupport
    (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)

theorem side_survival_iff (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample (Position counts) k) (e : Triple (Position counts))
    (he : HasSupportSum (fun _ => 16) e) :
    JointCoarseAssignment.survives (xKeep counts k U s) (yKeep counts k U s)
      (zKeep counts k U s) e ↔ Survives k U e s :=
  full_survival_iff k U hAP (fun _ => 16) e he s

theorem isolated_of_good
    (hsupport : ∀ h u, 0 < counts h u → u.1.val + u.2.1.val + u.2.2.val = 16)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample (Position counts) k) (e : Target counts)
    (hgood : JointOrdinarySelection.Good k U (ambientSet counts (fun _ => 16))
      (triple counts e) s) :
    AllFieldInitialExact.Isolated counts (xKeep counts k U s) (yKeep counts k U s)
      (zKeep counts k U s) e := by
  constructor
  · exact (side_survival_iff counts k U hAP s (triple counts e)
      (triple_support counts (fun _ => 16) hsupport e)).mpr hgood.1
  · intro f hf hsurvives hshare
    by_contra hne
    have hs := (side_survival_iff counts k U hAP s f (ambient_support counts f hf)).mp
      hsurvives
    exact JointOrdinarySelection.good_excludes_neighbor k U
      (ambientSet counts (fun _ => 16)) (triple counts e) f s hgood hf hne hshare hs

abbrev SelectedTargets (G : Finset (Target counts)) := {e : Target counts // e ∈ G}

def toTarget (G : Finset (Target counts)) : SelectedTargets counts G → Target counts :=
  Subtype.val

theorem toTarget_injective (G : Finset (Target counts)) :
    Function.Injective (toTarget counts G) := Subtype.val_injective

@[simp] theorem selectedTargets_card (G : Finset (Target counts)) :
    Fintype.card (SelectedTargets counts G) = G.card := Fintype.card_coe G

section Execution

variable {F : Type*} [Field F] {N : ℕ}

def selectedExecution (total : ∀ h, ∑ u, counts h u = N)
    (hsupport : ∀ h u, 0 < counts h u → u.1.val + u.2.1.val + u.2.2.val = 16)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample (Position counts) k) (G : Finset (Target counts))
    (hgood : ∀ e ∈ G, JointOrdinarySelection.Good k U
      (ambientSet counts (fun _ => 16)) (triple counts e) s) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : SelectedTargets counts G => JointCanonicalInitial.canonical counts)) :=
  AllFieldInitialExact.selectedExecution counts
    (xKeep counts k U s) (yKeep counts k U s) (zKeep counts k U s)
    total (toTarget counts G) (toTarget_injective counts G)
    (fun e => target_mem_ambient counts hsupport e.val)
    (fun e => isolated_of_good counts hsupport k U hAP s e.val (hgood e.val e.property))

@[simp] theorem selectedExecution_copies (total : ∀ h, ∑ u, counts h u = N)
    (hsupport : ∀ h u, 0 < counts h u → u.1.val + u.2.1.val + u.2.2.val = 16)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample (Position counts) k) (G : Finset (Target counts))
    (hgood : ∀ e ∈ G, JointOrdinarySelection.Good k U
      (ambientSet counts (fun _ => 16)) (triple counts e) s) :
    Fintype.card (selectedExecution (F := F) counts total hsupport k U hAP s G hgood).Copies = 1 :=
  rfl

theorem exists_selectedExecution (total : ∀ h, ∑ u, counts h u = N)
    (hsupport : ∀ h u, 0 < counts h u → u.1.val + u.2.1.val + u.2.2.val = 16)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (D : ℕ)
    (hdegree : ∀ e : Target counts,
      (JointOrdinarySelection.neighbors (ambientSet counts (fun _ => 16))
        (triple counts e)).card ≤ D)
    (hsmall : (D : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2)
    (n : ℕ) (hn : (n : ℝ) ≤ (Fintype.card (Target counts) : ℝ) *
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2)) :
    ∃ (s : Sample (Position counts) k) (G : Finset (Target counts)),
      G.card = n ∧
      (∀ e ∈ G, JointOrdinarySelection.Good k U
        (ambientSet counts (fun _ => 16)) (triple counts e) s) ∧
      ∃ E : Execution (cwSource F K N)
          (Tensor.directSum (fun _ : SelectedTargets counts G =>
            JointCanonicalInitial.canonical counts)),
        Fintype.card E.Copies = 1 := by
  obtain ⟨s, G, hcard, hgood, _hpairwise⟩ :=
    JointOrdinarySelection.exists_selection_of_degree_bound k U
      (ambientSet counts (fun _ => 16)) (fun _ => 16) (triple counts)
      (triple_injective counts) (fun f hf => ambient_support counts f hf)
      (target_mem_ambient counts hsupport) D hdegree hsmall n hn
  exact ⟨s, G, hcard, hgood,
    selectedExecution (F := F) counts total hsupport k U hAP s G hgood,
    selectedExecution_copies (F := F) counts total hsupport k U hAP s G hgood⟩

end Execution

end MatrixMultiplication.AllFieldInitialHash

end

end OAI
