import OAI.MathematicalPhysics.Heisenberg.MatrixWeights

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open SlotTensor TensorMatrix
variable {d ℓ : ℕ}

def totalZ (Λ : Finset (Site d)) : QuasiLocal d ℓ:=∑ x∈Λ,spinZ d ℓ x

lemma totalZ_selfAdjoint (Λ : Finset (Site d)) : IsSelfAdjoint (totalZ (ℓ:=ℓ) Λ) := by
  change star (totalZ Λ)=totalZ Λ
  simp only [totalZ,star_sum,star_spinZ]

lemma finiteRepresentation_totalZ (Λ : Finset (Site d)) :
    finiteRepresentation (ℓ:=ℓ) (fun x : Λ=>x.val) Subtype.val_injective
      (Matrix.diagonal (physicalMagnetization (X:=Λ) ℓ))=totalZ Λ := by
  have he : Matrix.diagonal (physicalMagnetization (X:=Λ) ℓ)=
      ∑ x : Λ,onsite x (SpinSlots.physicalZ ℓ) := by
    simp only [SpinSlots.physicalZ,local_diagonal,diagonal_fintype_sum]
    rfl
  rw [he,map_sum]
  simp only [finiteRepresentation_z,totalZ]
  exact Finset.sum_coe_sort Λ _

def shiftedField (Λ : Finset (Site d)) (h : ℝ) : QuasiLocal d ℓ:=
  hamiltonian d ℓ Λ+
    (((Fintype.card (SiteEdges (fun x y : Λ=>NearestNeighbor x.val y.val)):ℝ)*(ℓ:ℝ)^2/8)) • 1-
      h • totalZ (ℓ:=ℓ) Λ

lemma shiftedField_selfAdjoint (Λ : Finset (Site d)) (h : ℝ) :
    IsSelfAdjoint (shiftedField (ℓ:=ℓ) Λ h) := by
  change star (shiftedField Λ h)=shiftedField Λ h
  simp only [shiftedField,star_sub,star_add,star_smul,star_trivial,star_one,
    (hamiltonian_selfAdjoint d ℓ Λ).star_eq,(totalZ_selfAdjoint (ℓ:=ℓ) Λ).star_eq]

lemma finiteRepresentation_field (Λ : Finset (Site d)) (h : ℝ) :
    finiteRepresentation (ℓ:=ℓ) (fun x : Λ=>x.val) Subtype.val_injective
      ((-1/2:ℝ) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ-
        h • Matrix.diagonal (physicalMagnetization (X:=Λ) ℓ))=shiftedField Λ h := by
  rw [map_sub,map_smul,map_smul,finiteRepresentation_generator,finiteRepresentation_totalZ,shiftedField]
  module

lemma field_commute (Λ : Finset (Site d)) : Commute (hamiltonian d ℓ Λ) (totalZ Λ) := by
  have hh:=(spinGenerator_mag (fun x y : Λ=>NearestNeighbor x.val y.val)
    (fun x y h he=>nearestNeighbor_ne h (congrArg Subtype.val he)) ℓ).map
      (finiteRepresentation (ℓ:=ℓ) (fun x : Λ=>x.val) Subtype.val_injective)
  rw [finiteRepresentation_generator,finiteRepresentation_totalZ] at hh
  change ((-2:ℝ) • hamiltonian d ℓ Λ-_) * totalZ Λ=totalZ Λ*((-2:ℝ) • hamiltonian d ℓ Λ-_) at hh
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one] at hh
  have he : (-2:ℝ) • (hamiltonian d ℓ Λ*totalZ Λ)=(-2:ℝ) • (totalZ Λ*hamiltonian d ℓ Λ):=sub_left_injective hh
  have he':=congrArg (fun A : QuasiLocal d ℓ=>(-1/2:ℝ) • A) he
  norm_num only [smul_smul,neg_div,neg_mul_neg,div_mul_cancel₀ _ (by norm_num : (2:ℝ)≠0),one_smul] at he'
  exact he'

lemma shiftedField_gibbs_totalZ (Λ : Finset (Site d)) (τ : State d ℓ)
    (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A)) (β h : ℝ) :
    ((gibbsState τ (shiftedField Λ h) β).functional (totalZ Λ)).re=
      (∑ k : Λ → SpinSlots.Level ℓ,
        NormedSpace.exp ((β/2) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ) k k *
          Real.exp ((β*h)*physicalMagnetization ℓ k)*physicalMagnetization ℓ k)/
      Selection.tiltPartition (fun k : Λ → SpinSlots.Level ℓ=>
        NormedSpace.exp ((β/2) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ) k k)
        (physicalMagnetization ℓ) (β*h) := by
  rw [←finiteRepresentation_field Λ h,←finiteRepresentation_totalZ Λ]
  rw [finiteRepresentation_gibbs_re _ _ τ hτ _ _ (by rw [finiteRepresentation_field]; exact shiftedField_selfAdjoint Λ h)]
  have he : (-β) • ((-1/2:ℝ) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ-
      h • Matrix.diagonal (physicalMagnetization (X:=Λ) ℓ))=
      (β/2) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ+
      (β*h) • Matrix.diagonal (physicalMagnetization (X:=Λ) ℓ) := by module
  rw [he]
  have hc:=(spinGenerator_mag (fun x y : Λ=>NearestNeighbor x.val y.val)
    (fun x y h he=>nearestNeighbor_ne h (congrArg Subtype.val he)) ℓ).smul_left (β/2)
  rw [Selection.trace_exp_tilt _ _ _ hc,Selection.trace_exp_tilt_mag _ _ _ hc]

lemma nearestNeighbor_iff_step {x y : Site d} : NearestNeighbor x y ↔ Geometry.Step x y := by
  constructor
  · intro h
    obtain ⟨i,hi,hj⟩:=nearestNeighbor_coordinate h
    exact ⟨i,by omega,hj⟩
  · rintro ⟨i,hi,hj⟩
    change ∑ j : Fin d,|x j-y j|=(1:ℤ)
    rw [Finset.sum_eq_single i]
    · rcases hi with hi | hi <;> rw [hi] <;> simp
    · intro j _ hji
      rw [hj j hji,sub_self,abs_zero]
    · exact fun h=>False.elim (h (Finset.mem_univ i))

end Heisenberg
end
end

end OAI
