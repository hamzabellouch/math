import OAI.NumberTheory.Ostmann.Construction.AssignmentSlots

namespace OAI

noncomputable section
namespace Ostmann.Construction

def RestoringSplit (sources : SourceFamily) (j : ℕ) (T : List SourceSlot) :=
  {e : WeightEquiv (assignmentWeight sources T)
    (fun x : SourceAssignment sources (Template.extracted j T) ×
      SourceAssignment sources (Template.remainder j T) =>
        assignmentWeight sources (Template.extracted j T) x.1 *
        assignmentWeight sources (Template.remainder j T) x.2) //
    ∀ x,assignedSlots sources T x=Template.reinsert j T
      (assignedSlots sources (Template.extracted j T) (e.equiv x).1)
      (assignedSlots sources (Template.remainder j T) (e.equiv x).2)}

def restoringSplit (sources : SourceFamily) (j : ℕ) (T : List SourceSlot) :
    RestoringSplit sources j T := by
  induction T with
  | nil =>
    exact ⟨assignmentSplitWeightEquiv sources j [],fun _ => rfl⟩
  | cons q T ih =>
    unfold RestoringSplit
    by_cases hq : q.role=.compensation j
    · have he : Template.extracted j (q::T)=q::Template.extracted j T := by simp [Template.extracted,hq]
      have hr : Template.remainder j (q::T)=Template.remainder j T := by simp [Template.remainder,hq]
      rw [he,hr]
      let e := (assignmentConsWeightEquiv sources q T).trans
        (((WeightEquiv.refl (sources q.origin).law.mass).prod ih.val).trans
          ((WeightEquiv.assoc _ _ _).symm.trans
            ((assignmentConsWeightEquiv sources q (Template.extracted j T)).symm.prod
              (WeightEquiv.refl _))))
      refine ⟨e,?_⟩
      intro x
      rw [assignedSlots_cons]
      rw [ih.property (assignmentConsEquiv sources q T x).2]
      simp only [e,WeightEquiv.trans,WeightEquiv.prod,WeightEquiv.refl,WeightEquiv.assoc,
        WeightEquiv.symm,assignmentConsWeightEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,
        Equiv.prodAssoc_symm_apply]
      rw [assignedSlots_cons]
      simp [Template.reinsert,hq,Prod.map]
    · have he : Template.extracted j (q::T)=Template.extracted j T := by simp [Template.extracted,hq]
      have hr : Template.remainder j (q::T)=q::Template.remainder j T := by simp [Template.remainder,hq]
      rw [he,hr]
      let e := (assignmentConsWeightEquiv sources q T).trans
        (((WeightEquiv.refl (sources q.origin).law.mass).prod ih.val).trans
          ((WeightEquiv.swap _ _ _).trans
            ((WeightEquiv.refl _).prod
              (assignmentConsWeightEquiv sources q (Template.remainder j T)).symm)))
      refine ⟨e,?_⟩
      intro x
      rw [assignedSlots_cons]
      rw [ih.property (assignmentConsEquiv sources q T x).2]
      simp only [e,WeightEquiv.trans,WeightEquiv.prod,WeightEquiv.refl,WeightEquiv.swap,
        WeightEquiv.symm,assignmentConsWeightEquiv,Equiv.trans_apply,Equiv.prodCongr_apply]
      rw [assignedSlots_cons]
      simp [Template.reinsert,hq,Prod.map]

end Ostmann.Construction

end

end OAI
