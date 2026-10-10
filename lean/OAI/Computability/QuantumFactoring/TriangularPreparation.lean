import Mathlib
import OAI.Computability.QuantumFactoring.TriangularCircuit
import OAI.Computability.QuantumFactoring.TriangularKernel

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

def phaseRegister (b : ℕ) : Register b (width b) where
  toFun i := ⟨b+i.val,by dsimp [width,work]; have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    change b+i.val=b+j.val at hh
    omega

lemma encode_phase {b : ℕ} (u : Bits b × ZMod (2^b)) :
    encode b u ∘ phaseRegister b = (basisResidue b).symm u.2 := by
  funext i
  change packed (work b) (Fin.append u.1 ((basisResidue b).symm u.2)) (fun _ => false)
    (⟨(Fin.natAdd b i).val,by dsimp [width,work]; omega⟩ : Fin (width b)) = _
  rw [packed_input, Fin.append_right]

lemma encode_outside_phase {b : ℕ} (x : Bits b) (z z' : ZMod (2^b))
    (i : (phaseRegister b).Unused) : encode b (x,z) i.val = encode b (x,z') i.val := by
  by_cases hi : i.val.val < b+b
  · have hlo : i.val.val < b := by
      by_contra hn
      have hv : phaseRegister b ⟨i.val.val-b,by omega⟩ = i.val := by
        apply Fin.ext
        change b+(i.val.val-b) = i.val.val
        omega
      exact i.property _ hv
    have he : i.val = (⟨(Fin.castAdd b (⟨i.val.val,hlo⟩ : Fin b)).val,
        by dsimp [width,work]; omega⟩ : Fin (width b)) := Fin.ext rfl
    rw [he]
    simp only [encode, packed_input, Fin.append_left]
  · simp [encode, packed, hi]

lemma encode_replace_phase {b : ℕ} (x : Bits b) (z : ZMod (2^b)) (v : Basis b) :
    (phaseRegister b).replace (encode b (x,z)) v = encode b (x,basisResidue b v) := by
  apply (phaseRegister b).split.injective
  apply Prod.ext
  · rw [Register.replace, Equiv.apply_symm_apply]
    change v = encode b (x,basisResidue b v) ∘ phaseRegister b
    rw [encode_phase, Equiv.symm_apply_apply]
  · funext i
    change (phaseRegister b).replace (encode b (x,z)) v i.val = _
    rw [Register.replace_outside]
    exact encode_outside_phase x z _ i

def preparation (a : ℕ) : List (Instruction (width (a+2))) :=
  (preparePhase (a+2) (by omega)).map (Instruction.place (phaseRegister (a+2)))

lemma preparation_length (a : ℕ) : (preparation a).length = a+5 := by
  simp [preparation, preparePhase_length]

lemma preparation_basis (a : ℕ) (x : Bits (a+2)) :
    (programMatrix (preparation a)).mulVec (basisVector (encode (a+2) (x,0))) =
      encodeState (encode (a+2)) (fun u => if u.1=x then residuePhase a u.2 else 0) := by
  classical
  rw [preparation, Register.placed_basis_state, encode_phase]
  have hz : (basisResidue (a+2)).symm 0 = (fun _ => false) := by
    apply (basisResidue (a+2)).injective
    rw [Equiv.apply_symm_apply, basisResidue_zero]
  rw [hz]
  unfold encodeState
  simp only [preparePhase_label, encode_replace_phase, Fintype.sum_prod_type,
    ite_smul, zero_smul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Equiv.sum_comp (basisResidue (a+2))]
  apply Finset.sum_congr rfl
  intro v _
  rw [residuePhase, basisResidue_val]

/-- Preparation, actual clean triangular gate program, inverse preparation.
The success event is the all-zero phase and scratch register; it is not enforced. -/
def transform (a : ℕ) : List (Instruction (width (a+2))) :=
  preparation a ++ triPrefix (a+2) (a+2) le_rfl ++
    (preparation a).reverse.map Instruction.reverse

lemma transform_length (a : ℕ) :
    (transform a).length ≤ (a+2)*(998*(a+2)+49)+2*(a+5) := by
  have h := triPrefix_length (a+2) (a+2) le_rfl
  simp only [transform, List.length_append, List.length_map, List.length_reverse,
    preparation_length]
  omega

/-- The exact selected matrix entry of an actual fixed-gate circuit. -/
theorem transform_selected (a : ℕ) (x y : Bits (a+2)) :
    (programMatrix (transform a)).mulVec (basisVector (encode (a+2) (x,0)))
      (encode (a+2) (y,0)) =
      (Real.sqrt ((2:ℝ)^(a+2)) : ℂ)⁻¹ *
        OrderTrial.phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(a+2)) := by
  classical
  rw [transform, programMatrix_append, programMatrix_append,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    preparation_basis, triPrefix_apply, programMatrix_reverse]
  change (programMatrix (preparation a)).conjTranspose.mulVec _ _ = _
  rw [encoded_adjoint_test (encode (a+2)) (encode_injective (a+2)) _ _ _ _
    (preparation_basis a y)]
  simp only [Fintype.sum_prod_type, apply_ite, star_zero, zero_mul, ite_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact selected_kernel a x y

end ExactQuantumFactoring.Triangular


end

end OAI
