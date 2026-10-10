import OAI.Algebra.Finitistic.Dimension.PDResidueSemisimple
import OAI.Algebra.Finitistic.Dimension.PDSimpleTensor
import OAI.Algebra.Finitistic.Dimension.PDLowerBound
import OAI.Algebra.Finitistic.Tensor.BalancedTensorMaps

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- A nonzero finite module is detected by tensor with an actual simple right
submodule of A/rad A. This is an existence proof, not an assumed simple detector. -/
theorem exists_simple_tensor_nonzero
    (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [Module.Finite A N] [Nontrivial N] :
    ∃ S : Submodule Aᵐᵒᵖ (Residue (A := A)), IsSimpleModule Aᵐᵒᵖ S ∧
      ¬ Subsingleton (BalancedTensor.Tensor k A S N) := by
  have := residue_semisimple (k := k) (A := A)
  by_contra h
  have hS (S : Submodule Aᵐᵒᵖ (Residue (A := A))) (hs : IsSimpleModule Aᵐᵒᵖ S) :
      Subsingleton (BalancedTensor.Tensor k A S N) := by
    by_contra hn
    exact h ⟨S, hs, hn⟩
  let K : Submodule Aᵐᵒᵖ (Residue (A := A)) :=
    { carrier := {u | ∀ n : N, BalancedTensor.mk k A (Residue (A := A)) N u n=0}
      zero_mem' := fun n => LinearMap.congr_fun (map_zero (BalancedTensor.mk k A (Residue (A := A)) N)) n
      add_mem' := fun hu hv n => by
        change (BalancedTensor.mk k A (Residue (A := A)) N ( _ + _)) n=0
        rw [map_add, LinearMap.add_apply, hu, hv, add_zero]
      smul_mem' := fun a u hu n => by
        rw [show a = MulOpposite.op a.unop from rfl, BalancedTensor.balance]
        exact hu _ }
  have hK : (⊤ : Submodule Aᵐᵒᵖ (Residue (A := A))) ≤ K := by
    rw [← IsSemisimpleModule.sSup_simples_eq_top Aᵐᵒᵖ (Residue (A := A))]
    apply sSup_le
    intro S hs u hu n
    let f := BalancedTensor.mapLeft (k := k) N S.subtype
    have hz : BalancedTensor.mk k A S N ⟨u,hu⟩ n = 0 := (hS S hs).elim _ _
    have hz' := congrArg f hz
    simpa [f] using hz'
  have hz (z : BalancedTensor.Tensor k A (Residue (A := A)) N) : z=0 := by
    induction z using BalancedTensor.induction_on with
    | hz => rfl
    | ht u n => exact hK mem_top n
    | ha x y hx hy => rw [hx,hy,add_zero]
  have := residueTensor_nontrivial (k := k) (A := A) N
  obtain ⟨x,y,hxy⟩ := exists_pair_ne (BalancedTensor.Tensor k A (Residue (A := A)) N)
  exact hxy ((hz x).trans (hz y).symm)

variable (M : PDMinimal.FiniteModule k A)

/-- The exact simple-module form of projective-dimension detection. The test
modules here are actual simple right submodules of the fixed radical quotient. -/
theorem pdLE_iff_simpleTor_zero (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔
      ∀ S : Submodule Aᵐᵒᵖ (Residue (A := A)), IsSimpleModule Aᵐᵒᵖ S →
        IsZero (Tor (k := k) S M.cat (n+1)) := by
  constructor
  · intro h S _
    exact tor_zero_of_pdLT S M (n+1) h
  · intro h
    apply (PDMinimal.pdLE_iff_term_zero M n).mpr
    by_contra ht
    have : Nontrivial (PDMinimal.term M (n+1)) := not_subsingleton_iff_nontrivial.mp ht
    have : Nontrivial (ScalarModule k A (PDMinimal.term M (n+1)).cat) :=
      show Nontrivial (PDMinimal.term M (n+1)) from inferInstance
    have : Module.Finite A (ScalarModule k A (PDMinimal.term M (n+1)).cat) :=
      show Module.Finite A (PDMinimal.term M (n+1)) from inferInstance
    obtain ⟨S, hS, hnonzero⟩ := exists_simple_tensor_nonzero (k := k) (A := A)
      (ScalarModule k A (PDMinimal.term M (n+1)).cat)
    have := hS
    have hz := (h S hS).of_iso (simpleTorIsoTerm S M (n+1)).symm
    exact hnonzero (ModuleCat.isZero_iff_subsingleton.mp hz)
end LittleFinitistic.PDTensor

end

end OAI
