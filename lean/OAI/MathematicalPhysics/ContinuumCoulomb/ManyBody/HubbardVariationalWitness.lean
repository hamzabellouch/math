import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardEnergyLower
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorOccupationSector

namespace OAI

/-! Near-minimizers of the actual half-filled Hubbard Rayleigh quotient
are represented by antisymmetric tensors, with no restriction to spin product
states or a proper subspace of the occupation sector. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
variable {Edge : Type*} [Fintype Edge]

theorem exists_halfFilled_unit_mass (m : ℕ) :
    ∃ x : Space (2*m+1), IsHalfFilled m x ∧ fockMass x=1 := by
  let s : SourceSpinBasis (m+1) := fun _ => 0
  refine ⟨spinWedge m s,isHalfFilled_of_totalNumber m _ (totalNumber_spinWedge m s),?_⟩
  rw [spinWedge_eq_fockBasis]
  simp [fockMass,Module.Basis.repr_self,Finsupp.single_apply]

theorem hubbardFermionBottom_approximate (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : Space (2*m+1), IsHalfFilled m x ∧ 0 < fockMass x ∧
      hubbardFermionForm m U V left right t x <
        (hubbardFermionBottom m U V left right t+ε)*fockMass x := by
  have hs : Set.Nonempty {e | ∃ x : Space (2*m+1), IsHalfFilled m x ∧ 0 < fockMass x ∧
      e = hubbardFermionForm m U V left right t x/fockMass x} := by
    obtain ⟨x,hx,hm⟩ := exists_halfFilled_unit_mass m
    exact ⟨_,x,hx,by rw [hm]; norm_num,rfl⟩
  obtain ⟨e,⟨x,hx,hm,rfl⟩,he⟩ := exists_lt_of_csInf_lt hs
    (show hubbardFermionBottom m U V left right t <
      hubbardFermionBottom m U V left right t+ε by linarith)
  exact ⟨x,hx,hm,(div_lt_iff₀ hm).mp he⟩

theorem halfFilled_exists_tensor (m : ℕ) (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    ∃ c : Laughlin.State (m+1) (2*m+1), Laughlin.Antisymmetric c ∧
      normalizedTensorExterior (m+1) (2*m+1) c=x := by
  obtain ⟨a,ha⟩ := OccupationFock.exists_vector_of_support x hx
  exact ⟨FockSlaterTensor.occupationTensor a,
    FockSlaterTensor.occupationTensor_antisymmetric a,
    (OccupationFock.vector_normalizedTensorExterior a).symm.trans ha⟩

theorem hubbardFermionBottom_tensor_approximate (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : Laughlin.State (m+1) (2*m+1), Laughlin.Antisymmetric c ∧
      let x := normalizedTensorExterior (m+1) (2*m+1) c
      0 < fockMass x ∧ hubbardFermionForm m U V left right t x <
        (hubbardFermionBottom m U V left right t+ε)*fockMass x := by
  obtain ⟨x,hx,hm,he⟩ := hubbardFermionBottom_approximate m U V left right t hε
  obtain ⟨c,hc,rfl⟩ := halfFilled_exists_tensor m x hx
  exact ⟨c,hc,hm,he⟩

end ContinuumCoulomb.HubbardGlobal

end

end OAI
