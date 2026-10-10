import Mathlib
import OAI.Combinatorics.KMedian.Expanders.ExpanderIndex
import OAI.Combinatorics.KMedian.Machines.OrderedLists
import OAI.Combinatorics.KMedian.PCP.GlobalRegularization

namespace OAI

section Inline_PCPCloudOrder
namespace MetricKMedian.PCP.Compiler.CloudOrder
open scoped Classical

variable {V E A : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
variable (C : BinaryCSP V E A) (vo : Ordered V) (eo : Ordered E)
def boolOrder : Ordered Bool := ⟨[false,true],by simp,by decide⟩
noncomputable def dartOrder : Ordered (CloudCopies.Dart (E := E)) := eo.prod boolOrder
noncomputable def activeOrder : Ordered (CloudCopies.Active C) := by
  classical
  exact @Ordered.filter V vo (fun v => v ∈ Set.range (CloudCopies.endpoint C)) (Classical.decPred _)
noncomputable def incidentOrder (v : CloudCopies.Active C) : Ordered (CloudCopies.Incident C v) :=
  (dartOrder eo).filter (fun d => CloudCopies.owner C d=v)
noncomputable def copyOrder (v : CloudCopies.Active C) : Ordered (CloudCopies.Copy C v) :=
  (Ordered.fin _).map (ExpanderFamily.vertexEquiv (CloudCopies.depth C v)).symm
noncomputable def nodeOrder : Ordered (CloudCopies.Node C) :=
  (activeOrder C vo).sigma (copyOrder C)
lemma copy_index_bound (v : CloudCopies.Active C) : (incidentOrder C eo v).entries.length ≤
    (Fintype.card ExpanderFamily.Branch)^(CloudCopies.depth C v) := by
  rw [Ordered.length_card]
  have h := CloudCopies.copy_card_lower C v
  have he := Fintype.card_congr (ExpanderFamily.vertexEquiv (CloudCopies.depth C v))
  simp only [Fintype.card_fin] at he
  simp only [← Nat.card_eq_fintype_card] at h he ⊢
  exact h.trans_eq he
noncomputable def cloudEmbed (v : CloudCopies.Active C) : CloudCopies.Incident C v ↪ CloudCopies.Copy C v :=
  (incidentOrder C eo v).equiv.toEmbedding.trans
    ((Fin.castLEEmb (copy_index_bound C eo v)).trans (ExpanderFamily.vertexEquiv _).symm.toEmbedding)
@[simp] lemma cloudEmbed_index (v : CloudCopies.Active C) (d : CloudCopies.Incident C v) :
    (ExpanderFamily.vertexEquiv _ (cloudEmbed C eo v d)).val=(incidentOrder C eo v).entries.idxOf d := by
  simp only [cloudEmbed,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply,Fin.castLEEmb_apply,Fin.val_castLE,Ordered.equiv_val]
  simp only [List.idxOf]
  congr 1
  funext x
  simp only [Bool.beq_eq_decide_eq]
noncomputable def nodeCode (p : CloudCopies.Node C) : ℕ × ℕ :=
  ((vo.equiv p.1.val).val,(ExpanderFamily.vertexEquiv _ p.2).val)
lemma sigmaCode_injective {U : Type} {W : U → Type} (f : U → ℕ) (g : ∀ u, W u → ℕ)
    (hf : Function.Injective f) (hg : ∀ u, Function.Injective (g u)) :
    Function.Injective (fun p : Sigma W => (f p.1,g p.1 p.2)) := by
  rintro ⟨u,x⟩ ⟨v,y⟩ h
  have hu : u=v := hf (congrArg Prod.fst h)
  subst v
  have hx : x=y := hg u (congrArg Prod.snd h)
  subst y
  rfl
omit [DecidableEq E] in
lemma nodeCode_injective : Function.Injective (nodeCode C vo) := by
  apply sigmaCode_injective (fun v : CloudCopies.Active C => (vo.equiv v.val).val)
    (fun v w => (ExpanderFamily.vertexEquiv (CloudCopies.depth C v) w).val)
  · exact Fin.val_injective.comp (vo.equiv.injective.comp Subtype.val_injective)
  · intro v
    exact Fin.val_injective.comp (ExpanderFamily.vertexEquiv (CloudCopies.depth C v)).injective
variable [Nonempty E]
omit [DecidableEq E] in
lemma pad_index_bound : (nodeOrder C vo).entries.length ≤
    (Fintype.card ExpanderFamily.Branch)^(GlobalRegularization.depth C) := by
  rw [Ordered.length_card]
  have h := GlobalRegularization.node_lower C
  have he := Fintype.card_congr (ExpanderFamily.vertexEquiv (GlobalRegularization.depth C))
  simp only [Fintype.card_fin] at he
  simp only [← Nat.card_eq_fintype_card] at h he ⊢
  exact h.trans_eq he
noncomputable def padEmbed : CloudCopies.Node C ↪ GlobalRegularization.Node C :=
  (nodeOrder C vo).equiv.toEmbedding.trans
    ((Fin.castLEEmb (pad_index_bound C vo)).trans (ExpanderFamily.vertexEquiv _).symm.toEmbedding)
omit [DecidableEq E] in
lemma padEmbed_index (p : CloudCopies.Node C) :
    (ExpanderFamily.vertexEquiv _ (padEmbed C vo p)).val=
      ((nodeOrder C vo).entries.map (nodeCode C vo)).findIdx (fun q => decide (q=nodeCode C vo p)) := by
  simp only [padEmbed,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply,Fin.castLEEmb_apply,Fin.val_castLE]
  exact Ordered.index_coded _ _ (nodeCode_injective C vo) p
end MetricKMedian.PCP.Compiler.CloudOrder

end Inline_PCPCloudOrder

end OAI
