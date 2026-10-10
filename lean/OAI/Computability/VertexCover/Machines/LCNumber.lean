import Mathlib
import OAI.Computability.VertexCover.Reduction.GridBudget
import OAI.Computability.VertexCover.Analysis.PowerValueRepetition

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover.LabelCover

structure Iso (Φ Ψ : LabelCover) where
  u : Fin Φ.u ≃ Fin Ψ.u
  v : Fin Φ.v ≃ Fin Ψ.v
  a : Fin Φ.qU ≃ Fin Ψ.qU
  b : Fin Φ.qV ≃ Fin Ψ.qV
  e : Fin Φ.M ≃ Fin Ψ.M
  left : ∀ c, Ψ.left (e c) = u (Φ.left c)
  right : ∀ c, Ψ.right (e c) = v (Φ.right c)
  projection : ∀ c s, Ψ.projection (e c) (a s) = b (Φ.projection c s)

namespace Iso
variable {Φ Ψ : LabelCover} (E : Iso Φ Ψ)
def labeling (A : Φ.Labeling) : Ψ.Labeling :=
  (fun x => E.a (A.1 (E.u.symm x)),fun y => E.b (A.2 (E.v.symm y)))
 theorem satisfies (A : Φ.Labeling) (c : Fin Φ.M) :
    Ψ.Satisfies (E.labeling A) (E.e c) ↔ Φ.Satisfies A c := by
  simp only [Satisfies,labeling,E.left,E.right,Equiv.symm_apply_apply,E.projection,Equiv.apply_eq_iff_eq]
 theorem count (A : Φ.Labeling) : Ψ.satisfiedCount (E.labeling A) = Φ.satisfiedCount A := by
  classical
  have h := Fintype.card_congr (E.e.subtypeEquiv (fun c => (E.satisfies A c).symm))
  simpa only [Fintype.card_subtype,satisfiedCount] using h.symm
 include E
 theorem value_le : Φ.value ≤ Ψ.value := by
  have hM : Φ.M = Ψ.M := by simpa using Fintype.card_congr E.e
  apply value_le_of_counts
  intro A
  rw [← E.count A,hM]
  exact Ψ.count_le_of_value_le le_rfl (E.labeling A)
 def symm : Iso Ψ Φ where
  u := E.u.symm
  v := E.v.symm
  a := E.a.symm
  b := E.b.symm
  e := E.e.symm
  left c := by
    apply E.u.injective
    simpa only [Equiv.apply_symm_apply] using (E.left (E.e.symm c)).symm
  right c := by
    apply E.v.injective
    simpa only [Equiv.apply_symm_apply] using (E.right (E.e.symm c)).symm
  projection c s := by
    apply E.b.injective
    simpa only [Equiv.apply_symm_apply] using (E.projection (E.e.symm c) (E.a.symm s)).symm
 theorem value_eq : Φ.value = Ψ.value := le_antisymm E.value_le E.symm.value_le
 theorem perfect (A : Φ.Labeling) (hA : ∀ c, Φ.Satisfies A c) :
    ∀ c, Ψ.Satisfies (E.labeling A) c := by
  intro c
  rw [← E.e.apply_symm_apply c]
  exact (E.satisfies A _).mpr (hA _)
end Iso

def numberedPower (Φ : LabelCover) (n : ℕ) : LabelCover where
  u := Φ.u^n
  v := Φ.v^n
  qU := Φ.qU^n
  qV := Φ.qV^n
  M := Φ.M^n
  qU_pos := pow_pos Φ.qU_pos _
  qV_pos := pow_pos Φ.qV_pos _
  M_pos := pow_pos Φ.M_pos _
  left c := finFunctionFinEquiv (fun i => Φ.left (finFunctionFinEquiv.symm c i))
  right c := finFunctionFinEquiv (fun i => Φ.right (finFunctionFinEquiv.symm c i))
  projection c s := finFunctionFinEquiv
    (fun i => Φ.projection (finFunctionFinEquiv.symm c i) (finFunctionFinEquiv.symm s i))
noncomputable def numberIso (Φ : LabelCover) (n : ℕ) : Iso (Φ.numberedPower n) (Φ.parallelPower n) where
  u := finFunctionFinEquiv.symm.trans (tupleEquiv Φ.u n)
  v := finFunctionFinEquiv.symm.trans (tupleEquiv Φ.v n)
  a := finFunctionFinEquiv.symm.trans (tupleEquiv Φ.qU n)
  b := finFunctionFinEquiv.symm.trans (tupleEquiv Φ.qV n)
  e := finFunctionFinEquiv.symm.trans (tupleEquiv Φ.M n)
  left c := by
    change (tupleEquiv Φ.u n) (fun i => Φ.left ((tupleEquiv Φ.M n).symm
      ((tupleEquiv Φ.M n) (finFunctionFinEquiv.symm c)) i)) =
      (tupleEquiv Φ.u n) (finFunctionFinEquiv.symm (finFunctionFinEquiv
        (fun i => Φ.left (finFunctionFinEquiv.symm c i))))
    simp only [Equiv.symm_apply_apply]
  right c := by
    change (tupleEquiv Φ.v n) (fun i => Φ.right ((tupleEquiv Φ.M n).symm
      ((tupleEquiv Φ.M n) (finFunctionFinEquiv.symm c)) i)) =
      (tupleEquiv Φ.v n) (finFunctionFinEquiv.symm (finFunctionFinEquiv
        (fun i => Φ.right (finFunctionFinEquiv.symm c i))))
    simp only [Equiv.symm_apply_apply]
  projection c s := by
    change (tupleEquiv Φ.qV n) (fun i => Φ.projection
      ((tupleEquiv Φ.M n).symm ((tupleEquiv Φ.M n) (finFunctionFinEquiv.symm c)) i)
      ((tupleEquiv Φ.qU n).symm ((tupleEquiv Φ.qU n) (finFunctionFinEquiv.symm s)) i)) =
      (tupleEquiv Φ.qV n) (finFunctionFinEquiv.symm (finFunctionFinEquiv
        (fun i => Φ.projection (finFunctionFinEquiv.symm c i) (finFunctionFinEquiv.symm s i))))
    simp only [Equiv.symm_apply_apply]
end VertexCover.LabelCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
