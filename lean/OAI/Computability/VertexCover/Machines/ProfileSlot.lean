import Mathlib
import OAI.Computability.VertexCover.Machines.Profile
import OAI.Computability.VertexCover.Reduction.HonestLargeSumIndependent

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

namespace VertexCover.LabelCover.Query

variable {Φ : LabelCover} {d : ℕ}
noncomputable def profileLabels (i : Φ.Query d) : List (Profile Φ.qU Φ.qV d) := by
  classical
  exact Finset.univ.toList.filter (fun P => decide (i.ProfileValid P))
@[simp] theorem mem_profileLabels (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) :
    P ∈ i.profileLabels ↔ i.ProfileValid P := by
  classical
  simp [profileLabels]
 theorem profileLabels_nodup (i : Φ.Query d) : i.profileLabels.Nodup := by
  classical
  exact (Finset.nodup_toList _).filter _
 theorem profileLabels_length (i : Φ.Query d) : i.profileLabels.length=Fintype.card i.LocalLabel := by
  classical
  have hp : i.profileLabels.Perm (i.labels.map i.encode) := by
    apply (List.perm_ext_iff_of_nodup (i.profileLabels_nodup) ((by simp [labels] : i.labels.Nodup).map i.encode_injective)).mpr
    intro P
    simp only [mem_profileLabels,List.mem_map,mem_labels,true_and,i.valid_iff]
  simpa using hp.length_eq
noncomputable def profileSlot (i : Φ.Query d) (A : i.LocalLabel) : Fin (Φ.WeightDimension d) :=
  ⟨i.profileLabels.idxOf (i.encode A),lt_of_lt_of_le
    (by simpa only [profileLabels_length] using (List.idxOf_lt_length_iff.mpr ((i.mem_profileLabels _).mpr (i.encode_valid A)))) i.localLabel_card_le⟩
 theorem profileSlot_injective (i : Φ.Query d) : Function.Injective i.profileSlot := by
  classical
  intro A B h
  apply i.encode_injective
  exact (List.idxOf_inj ((i.mem_profileLabels _).mpr (i.encode_valid A))).mp (congrArg Fin.val h)
noncomputable def slotPermutation (i : Φ.Query d) : Equiv.Perm (Fin (Φ.WeightDimension d)) :=
  (Equiv.Perm.exists_extending_pair i.slot i.profileSlot i.slot_injective i.profileSlot_injective).choose
 theorem slotPermutation_apply (i : Φ.Query d) (A : i.LocalLabel) :
    i.slotPermutation (i.slot A)=i.profileSlot A :=
  (Equiv.Perm.exists_extending_pair i.slot i.profileSlot i.slot_injective i.profileSlot_injective).choose_spec A
end VertexCover.LabelCover.Query

namespace VertexCover.LabelCover

noncomputable def profileVertexEquiv (Φ : LabelCover) (d : ℕ) : Φ.Vertex d ≃ Φ.Vertex d where
  toFun v := (v.1,fun j k => v.2 j ((Φ.query v.1 j).slotPermutation k))
  invFun v := (v.1,fun j k => v.2 j ((Φ.query v.1 j).slotPermutation.symm k))
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
noncomputable def profileGraph (Φ : LabelCover) (d : ℕ) (t : ℝ) : SimpleGraph (Φ.Vertex d) :=
  (Φ.graph d t).comap (Φ.profileVertexEquiv d)
noncomputable def profileGraphIso (Φ : LabelCover) (d : ℕ) (t : ℝ) : Φ.profileGraph d t ≃g Φ.graph d t where
  toEquiv := Φ.profileVertexEquiv d
  map_rel_iff' := by intro a b; rfl
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
