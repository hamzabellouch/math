import Mathlib
import OAI.Analysis.Commutator.FreeBlockTensor

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap) {i j : ι} (hij : i≠j)

include hij in
lemma blockReadPre_mem_tail (n : ℕ) (x : blockTensor t S i j n) :
    (blockReadPre t S n x : t.functional.GNS) ∈ tailSpace t S i := by
  have hx : x ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [span_blockPure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    rw [blockReadPre_pure]
    exact blockVector_mem_tail t S hij _ (paramEnd t S n v).property
  | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
  | add x y _ _ hx hy => simpa only [map_add, Completion.coe_add] using
      (tailSpace t S i).add_mem hx hy
  | smul c x _ hx => simpa only [map_smul, Completion.coe_smul] using
      (tailSpace t S i).smul_mem c hx

include hfree hij in
lemma inner_blockReadPre_ne {n m : ℕ} (hnm : n≠m)
    (x : blockTensor t S i j n) (y : blockTensor t S i j m) :
    inner ℂ (blockReadPre t S n x) (blockReadPre t S m y)=0 := by
  have hx : x ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [span_blockPure]; trivial
  have hy : y ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) m)) := by rw [span_blockPure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w,rfl⟩ := hy
      rw [←Completion.inner_coe, blockReadPre_pure, blockReadPre_pure]
      exact blockVector_orthogonal t S hfree hij _ _
        (by simpa only [paramLetters_length] using hnm)
        (paramEnd t S n v).property (paramEnd t S m w).property
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, inner_add_right, hx, hy, add_zero]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx, mul_zero]

def endpointTensor (i j : ι) (n : ℕ) : Space :=
  spaceTensor ⟨factorSpace t S i⟩ (blockTensor t S i j n)

def endpointRead (n : ℕ) : endpointTensor t S i j n →ₗ[ℂ] preSpace t :=
  t.functional.toPreGNS.toLinearMap.comp
    ((TensorProduct.lift (LinearMap.mul ℂ A)).comp
      (TensorProduct.map (factorValue t S i) (blockRead t S n)))

lemma endpointRead_tmul (n : ℕ) (a : factorSpace t S i) (x : blockTensor t S i j n) :
    (endpointRead t S n (a ⊗ₜ[ℂ] x) : t.functional.GNS) =
      t.functional.gnsStarAlgHom (factorValue t S i a)
        (blockReadPre t S n x : t.functional.GNS) := by
  change (t.functional.toPreGNS (factorValue t S i a * blockRead t S n x) :
    t.functional.GNS) = _
  simp [blockReadPre, PositiveLinearMap.gnsStarAlgHom]

lemma endpointTensor_induction_on (n : ℕ) {P : endpointTensor t S i j n → Prop}
    (x : endpointTensor t S i j n) (h0 : P 0)
    (ht : ∀ a : factorSpace t S i, ∀ b : blockTensor t S i j n, P (a ⊗ₜ[ℂ] b))
    (ha : ∀ x y : endpointTensor t S i j n, P x → P y → P (x+y)) : P x := by
  by_cases hx : x = 0
  · simpa only [hx] using h0
  · exact TensorProduct.inductionOn x ht ha

include hfree hij in
lemma inner_endpointRead_tmul (n : ℕ) (a b : factorSpace t S i)
    (x y : blockTensor t S i j n) :
    inner ℂ (endpointRead t S n (a ⊗ₜ[ℂ] x)) (endpointRead t S n (b ⊗ₜ[ℂ] y)) =
      inner ℂ (a ⊗ₜ[ℂ] x) (b ⊗ₜ[ℂ] y) := by
  rw [←Completion.inner_coe, endpointRead_tmul, endpointRead_tmul,
    inner_mul_two_tailSpace t S hfree i (a := factorValue t S i a)
      (b := factorValue t S i b) a.property b.property
      (blockReadPre_mem_tail t S hij n x) (blockReadPre_mem_tail t S hij n y),
    Completion.inner_coe, inner_blockReadPre t S hfree hij]
  rw [TensorProduct.inner_tmul]
  rfl

include hfree hij in
lemma inner_endpointRead (n : ℕ) (x y : endpointTensor t S i j n) :
    inner ℂ (endpointRead t S n x) (endpointRead t S n y)=inner ℂ x y := by
  induction x using endpointTensor_induction_on t S n with
  | h0 => simp
  | ha x z hx hz => simpa only [map_add, inner_add_left] using congrArg₂ (·+·) hx hz
  | ht a x =>
    change inner ℂ (endpointRead t S n (a ⊗ₜ[ℂ] x)) (endpointRead t S n y) =
      inner ℂ (a ⊗ₜ[ℂ] x : endpointTensor t S i j n) y
    induction y using endpointTensor_induction_on t S n with
    | h0 =>
      rw [map_zero, inner_zero_right]
      exact (inner_zero_right (𝕜 := ℂ) (E := endpointTensor t S i j n) (a ⊗ₜ[ℂ] x)).symm
    | ha y z hy hz =>
      rw [map_add, inner_add_right]
      exact (congrArg₂ (·+·) hy hz).trans
        (inner_add_right (𝕜 := ℂ) (E := endpointTensor t S i j n) (a ⊗ₜ[ℂ] x) y z).symm
    | ht b y => exact inner_endpointRead_tmul t S hfree hij n a b x y

include hfree hij in
lemma inner_endpointRead_ne {n m : ℕ} (hnm : n≠m)
    (x : endpointTensor t S i j n) (y : endpointTensor t S i j m) :
    inner ℂ (endpointRead t S n x) (endpointRead t S m y)=0 := by
  induction x using endpointTensor_induction_on t S n with
  | h0 => simp
  | ha x z hx hz => simp only [map_add, inner_add_left, hx, hz, add_zero]
  | ht a x =>
    induction y using endpointTensor_induction_on t S m with
    | h0 => simp
    | ha y z hy hz => simp only [map_add, inner_add_right, hy, hz, add_zero]
    | ht b y =>
      rw [←Completion.inner_coe, endpointRead_tmul, endpointRead_tmul,
        inner_mul_two_tailSpace t S hfree i (a := factorValue t S i a)
          (b := factorValue t S i b) a.property b.property
          (blockReadPre_mem_tail t S hij n x) (blockReadPre_mem_tail t S hij m y),
        Completion.inner_coe, inner_blockReadPre_ne t S hfree hij hnm, mul_zero]

def endpointIsometry (n : ℕ) : endpointTensor t S i j n →ₗᵢ[ℂ] preSpace t :=
  (endpointRead t S n).isometryOfInner (inner_endpointRead t S hfree hij n)

def levelEmbedding (n : ℕ) : Completion (endpointTensor t S i j n) →ₗᵢ[ℂ] t.functional.GNS where
  toLinearMap := (endpointIsometry t S hfree hij n).toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

@[simp] lemma levelEmbedding_coe (n : ℕ) (x : endpointTensor t S i j n) :
    levelEmbedding t S hfree hij n (x : Completion (endpointTensor t S i j n)) =
      (endpointRead t S n x : t.functional.GNS) := by
  change (endpointIsometry t S hfree hij n).toContinuousLinearMap.completion _ = _
  simp [endpointIsometry]

lemma levelEmbedding_orthogonal {n m : ℕ} (hnm : n≠m)
    (x : Completion (endpointTensor t S i j n)) (y : Completion (endpointTensor t S i j m)) :
    inner ℂ (levelEmbedding t S hfree hij n x) (levelEmbedding t S hfree hij m y) = 0 := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [levelEmbedding_coe, levelEmbedding_coe, Completion.inner_coe]
    exact inner_endpointRead_ne t S hfree hij hnm x y

lemma levelFamily_orthogonal :
    OrthogonalFamily ℂ (fun n => Completion (endpointTensor t S i j n))
      (levelEmbedding t S hfree hij) := by
  intro n m hnm x y
  exact levelEmbedding_orthogonal t S hfree hij hnm x y

end Kadison.FreeBlocks
end

end OAI
