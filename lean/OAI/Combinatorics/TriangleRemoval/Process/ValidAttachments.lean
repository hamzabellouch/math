import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PathForest
import OAI.Combinatorics.TriangleRemoval.Process.LocalChoiceRank

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def ValidAttachments {R s : ℕ} (E : Finset (Finset (Fin (R+s))))
    (F : PathForest s) (f : Fin s → Finset (Fin (R+s))) : Prop :=
  (∀ i, (f i).card ≤ 2) ∧ ∀ i,
    match F.parent i with
    | none => f i ∈ E
    | some p => ∃ u ∈ f p, f i = {⟨R+p.val,by omega⟩,u}

noncomputable def attachmentFamily {R s : ℕ} (E : Finset (Finset (Fin (R+s))))
    (F : PathForest s) : Finset (Fin s → Finset (Fin (R+s))) := by
  classical
  exact Finset.univ.filter (ValidAttachments E F)

@[simp] lemma mem_attachmentFamily {R s : ℕ} (E : Finset (Finset (Fin (R+s))))
    (F : PathForest s) (f : Fin s → Finset (Fin (R+s))) :
    f ∈ attachmentFamily E F ↔ ValidAttachments E F f := by
  classical
  simp only [attachmentFamily,Finset.mem_filter,Finset.mem_univ,true_and]

lemma mem_prefixChoiceValues {n : ℕ} {α : Type*}
    (S : Finset (Fin n → α)) (f : Fin n → α) (i : Fin n) (a : α) :
    a ∈ prefixChoiceValues S f i ↔ ∃ g ∈ S, (∀ j, j < i → g j = f j) ∧ g i = a := by
  classical
  simp only [prefixChoiceValues,Finset.mem_image,Finset.mem_filter]
  aesop

lemma attachment_choices_le_two {R s : ℕ} (E : Finset (Finset (Fin (R+s))))
    (hE : E.card ≤ 2) (F : PathForest s) (f : Fin s → Finset (Fin (R+s)))
    (hf : f ∈ attachmentFamily E F) (i : Fin s) :
    (prefixChoiceValues (attachmentFamily E F) f i).card ≤ 2 := by
  classical
  have hf' : ValidAttachments E F f := (mem_attachmentFamily _ _ _).mp hf
  cases hp : F.parent i with
  | none =>
    apply (Finset.card_le_card (t := E) ?_).trans hE
    intro e he
    obtain ⟨g,hg,_,rfl⟩ := (mem_prefixChoiceValues _ _ _ _).mp he
    have hvalid : ValidAttachments E F g := (mem_attachmentFamily _ _ _).mp hg
    simpa only [hp] using hvalid.2 i
  | some p =>
    let C : Finset (Finset (Fin (R+s))) :=
      (f p).image (fun u => {⟨R+p.val,by omega⟩,u})
    have hsub : prefixChoiceValues (attachmentFamily E F) f i ⊆ C := by
      intro e he
      obtain ⟨g,hgS,hprev,rfl⟩ := (mem_prefixChoiceValues _ _ _ _).mp he
      have hvalid : ValidAttachments E F g := (mem_attachmentFamily _ _ _).mp hgS
      have hgp : g p = f p := hprev p (F.property i p hp)
      have hgi := hvalid.2 i
      rw [hp] at hgi
      obtain ⟨u,hu,heq⟩ := hgi
      exact Finset.mem_image.mpr ⟨u,by simpa only [hgp] using hu,heq.symm⟩
    exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (hf'.1 p))

theorem fixed_forest_attachment_count {R s : ℕ} (E : Finset (Finset (Fin (R+s))))
    (hE : E.card ≤ 2) (F : PathForest s) : (attachmentFamily E F).card ≤ 2^s :=
  finite_branching_family_bound _ 2 (attachment_choices_le_two E hE F)

open Classical in

theorem marked_attachment_pattern_count {R s : ℕ}
    (E : Finset (Finset (Fin (R+s)))) (hE : E.card ≤ 2) (a b : Option (Fin s)) :
    Fintype.card (Σ F : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v},
      {f // f ∈ attachmentFamily E F.val}) ≤ 6^s := by
  classical
  rw [Fintype.card_sigma]
  calc
    ∑ F : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v},
        Fintype.card {f // f ∈ attachmentFamily E F.val}
      ≤ ∑ _F : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v}, 2^s := by
        apply Finset.sum_le_sum
        intro F _
        simpa only [Fintype.card_coe] using fixed_forest_attachment_count E hE F.val
    _ = Fintype.card {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v} * 2^s := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    _ ≤ 3^s * 2^s := Nat.mul_le_mul_right _ (PathForest.two_path_forest_count a b)
    _ = 6^s := by rw [← Nat.mul_pow]

open Classical in

theorem all_marked_attachment_pattern_count {R s : ℕ} {M : Type*} [Fintype M]
    (E : Finset (Finset (Fin (R+s)))) (hE : E.card ≤ 2) (mark : M → Option (Fin s)) :
    Fintype.card (Σ ab : M × M,
      Σ F : {F : PathForest s // ∀ v, F.OnPath (mark ab.1) v ∨ F.OnPath (mark ab.2) v},
        {f // f ∈ attachmentFamily E F.val}) ≤ (Fintype.card M)^2 * 6^s := by
  classical
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ab : M × M, 6^s := by
      apply Finset.sum_le_sum
      intro ab _
      exact marked_attachment_pattern_count E hE _ _
    _ = (Fintype.card M)^2 * 6^s := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,smul_eq_mul,pow_two]

end SharpTerminalLeave

end

end OAI
