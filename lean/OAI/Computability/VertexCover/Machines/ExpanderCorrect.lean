import Mathlib
import OAI.Computability.VertexCover.Machines.ExpanderStep

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

namespace VertexCover.Machine.ExpandMachine
open UniqueGames.Foundations.PCP

@[simp] theorem lookup_fst_val {q v : ℕ} (T : ExpanderTables.Table v q) (x : Fin v × Fin q) :
    (ExpanderTables.lookup T x).1.val = (lookup q (T.rows.toList.map Fin.val,(x.1.val,x.2.val))).1 :=
  (congrArg Prod.fst (lookup_erase T x)).symm
@[simp] theorem lookup_snd_val {q v : ℕ} (T : ExpanderTables.Table v q) (x : Fin v × Fin q) :
    (ExpanderTables.lookup T x).2.val = (lookup q (T.rows.toList.map Fin.val,(x.1.val,x.2.val))).2 :=
  (congrArg Prod.snd (lookup_erase T x)).symm

@[simp] theorem index_val {v q : ℕ} (x : Fin v × Fin q) :
    (ExpanderTables.rowIndex v q x).val=x.2.val+q*x.1.val := rfl
@[simp] theorem index_inv_fst {v q : ℕ} (i : Fin (v*q)) :
    ((ExpanderTables.rowIndex v q).symm i).1.val=i.val/q := rfl
@[simp] theorem index_inv_snd {v q : ℕ} (i : Fin (v*q)) :
    ((ExpanderTables.rowIndex v q).symm i).2.val=i.val%q := rfl

 theorem stepRow_lookup {v d : ℕ} (T : ExpanderTables.Table v (d*d))
    (H : ExpanderTables.Table ((d*d)*(d*d)) d) (i : Fin ((v*((d*d)*(d*d)))*(d*d))) :
    stepRow d (H.rows.toList.map Fin.val) (erase ⟨v,T⟩,i.val) =
      (ExpanderTables.rowIndex _ _ (ExpanderTables.stepLookup T H
        ((ExpanderTables.rowIndex _ _).symm i))).val := by
  simp only [ExpanderTables.stepLookup,index_val,index_inv_fst,index_inv_snd,
    lookup_fst_val,lookup_snd_val]
  rfl

 theorem stepRow_source {v d : ℕ} (T : ExpanderTables.Table v (d*d))
    (H : ExpanderTables.Table ((d*d)*(d*d)) d) (i : Fin ((v*((d*d)*(d*d)))*(d*d))) :
    stepRow d (H.rows.toList.map Fin.val) (erase ⟨v,T⟩,i.val) =
      (ExpanderTables.step T H).rows[i].val := by
  rw [stepRow_lookup,← ExpanderTables.lookup_step]
  simp only [ExpanderTables.lookup,Equiv.apply_symm_apply,ExpanderTables.reverseIndex]

 def step {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) (T : Input (d*d)) : Input (d*d) :=
  ⟨T.1*((d*d)*(d*d)),ExpanderTables.step T.2 H⟩

 theorem stepData_source {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) (T : Input (d*d)) :
    stepData d (H.rows.toList.map Fin.val) (erase T)=erase (step H T) := by
  apply Prod.ext
  · rfl
  · apply List.ext_getElem
    · simp [stepData,erase,step]
    · intro i h₁ h₂
      simp only [stepData,List.getElem_map,List.getElem_range,erase,step,Vector.getElem_toList]
      exact stepRow_source T.2 H ⟨i, by simpa [stepData,erase] using h₁⟩

noncomputable def stepPoly {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) :
    Poly (code (q := d*d)) code (step H) :=
  (stepDataPoly d (H.rows.toList.map Fin.val)).encodeCongr erase (fun _ => rfl) (fun T => by
    change dataCode _ = dataCode _
    rw [stepData_source])

end VertexCover.Machine.ExpandMachine
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
