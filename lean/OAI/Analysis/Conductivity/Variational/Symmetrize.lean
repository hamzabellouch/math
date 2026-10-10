import Mathlib
import OAI.Analysis.Conductivity.Variational.SymmetricCorrection
import OAI.Analysis.Conductivity.Variational.PreliminaryQ

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

def symmetrize {n : Type*} [Fintype n] (M : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (M + Mᵀ)

lemma symmetrize_isSymm {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    (symmetrize M).IsSymm := by
  unfold Matrix.IsSymm symmetrize
  simp only [transpose_smul, transpose_add, transpose_transpose, add_comm]

lemma symmetrize_eq {n : Type*} [Fintype n] {M : Matrix n n ℝ} (hM : M.IsSymm) :
    symmetrize M = M := by
  unfold symmetrize
  rw [hM]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
  ring

def repairError {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (E R : Matrix (Fin 3) m ℝ) : Symmetric3 :=
  ⟨A.val + symmetrize (symmetricCorrection E R ((Eᵀ * E)⁻¹ * Eᵀ)), by
    rw [Matrix.isHermitian_iff_isSymm]
    exact (Matrix.isHermitian_iff_isSymm.mp A.property).add (symmetrize_isSymm _)⟩

lemma repairError_zero {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (E : Matrix (Fin 3) m ℝ) : repairError A E 0 = A := by
  apply Subtype.ext
  simp [repairError, symmetricCorrection, symmetrize]

lemma repairError_mul {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (E R : Matrix (Fin 3) m ℝ)
    (hE : LinearIndependent ℝ E.col) (hER : (Eᵀ * R).IsSymm) :
    (repairError A E R).val * E = A.val * E + R := by
  change (A.val + symmetrize _) * E = _
  rw [symmetrize_eq (symmetricCorrection_isSymm E R _ hER), Matrix.add_mul,
    symmetricCorrection_mul E R _ (gram_leftInverse E hE) hER]

lemma gram_det_ne_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (E : Matrix m n ℝ) (hE : LinearIndependent ℝ E.col) : (Eᵀ * E).det ≠ 0 := by
  have hinj : Function.Injective E.mulVec := Matrix.mulVec_injective_iff.mpr hE
  have hker : LinearMap.ker (Eᵀ * E).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hinj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hker)))

lemma matrix_mul_contAt {X m n p : Type*} [TopologicalSpace X]
    [Fintype n] {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ} {x : X}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) :
    ContinuousAt (fun y => A y * B y) x :=
  (continuous_fst.matrix_mul continuous_snd).continuousAt.comp (hA.prodMk hB)

lemma matrix_transpose_contAt {X m n : Type*} [TopologicalSpace X]
    {A : X → Matrix m n ℝ} {x : X} (hA : ContinuousAt A x) :
    ContinuousAt (fun y => (A y)ᵀ) x :=
  continuous_id.matrix_transpose.continuousAt.comp hA

lemma continuousAt_gramInverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (E : Matrix m n ℝ) (hE : LinearIndependent ℝ E.col) :
    ContinuousAt (fun F : Matrix m n ℝ => (Fᵀ * F)⁻¹ * Fᵀ) E := by
  have hi : ContinuousAt (fun M : Matrix n n ℝ => M⁻¹) (Eᵀ * E) :=
    continuousAt_matrix_inv _ (by
      convert continuousAt_inv₀ (gram_det_ne_zero E hE) using 1
      ext x
      exact Ring.inverse_eq_inv x)
  have hG : Continuous (fun F : Matrix m n ℝ => Fᵀ * F) :=
    (continuous_id : Continuous (id : Matrix m n ℝ → Matrix m n ℝ)).matrix_transpose.matrix_mul
      continuous_id
  have hT : Continuous (fun F : Matrix m n ℝ => Fᵀ) :=
    (continuous_id : Continuous (id : Matrix m n ℝ → Matrix m n ℝ)).matrix_transpose
  have hGi : ContinuousAt (fun F : Matrix m n ℝ => (Fᵀ * F)⁻¹) E := by
    exact ContinuousAt.comp (f := fun F : Matrix m n ℝ => Fᵀ * F)
      (g := fun M : Matrix n n ℝ => M⁻¹) hi hG.continuousAt
  exact matrix_mul_contAt hGi hT.continuousAt

lemma continuousAt_repairError {m X : Type*} [Fintype m] [DecidableEq m]
    [TopologicalSpace X] (A : X → Symmetric3) (E R : X → Matrix (Fin 3) m ℝ)
    {x : X} (hA : ContinuousAt A x) (hE : ContinuousAt E x) (hR : ContinuousAt R x)
    (hi : LinearIndependent ℝ (E x).col) :
    ContinuousAt (fun y => repairError (A y) (E y) (R y)) x := by
  apply IsInducing.subtypeVal.continuousAt_iff.mpr
  have hL := (continuousAt_gramInverse (E x) hi).comp hE
  have hC : ContinuousAt (fun y =>
      symmetricCorrection (E y) (R y) (((E y)ᵀ * E y)⁻¹ * (E y)ᵀ)) x := by
    unfold symmetricCorrection
    exact ((matrix_mul_contAt hR hL).add
      (matrix_mul_contAt (matrix_transpose_contAt hL) (matrix_transpose_contAt hR))).sub
      (matrix_mul_contAt (matrix_mul_contAt (matrix_transpose_contAt hL)
        (matrix_mul_contAt (matrix_transpose_contAt hE) hR)) hL)
  exact (continuousAt_subtype_val.comp hA).add
    ((hC.add (matrix_transpose_contAt hC)).const_smul (1 / 2 : ℝ))

lemma compact_zero_stability {P V W : Type*} [TopologicalSpace P]
    [SeminormedAddCommGroup V] [TopologicalSpace W]
    {K : Set P} (hK : IsCompact K) (f : P × V → W)
    (hf : ∀ p ∈ K, ContinuousAt f (p, 0))
    {U : Set W} (hU : IsOpen U) (hmem : ∀ p ∈ K, f (p, 0) ∈ U) :
    ∃ O : Set P, IsOpen O ∧ K ⊆ O ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ O, ∀ v : V, ‖v‖ < ε → f (p, v) ∈ U := by
  let N := interior (f ⁻¹' U)
  have hKN : K ×ˢ ({0} : Set V) ⊆ N := by
    rintro ⟨p, v⟩ ⟨hp, hv⟩
    have hv0 : v = 0 := hv
    subst v
    exact mem_interior_iff_mem_nhds.mpr ((hf p hp).preimage_mem_nhds (hU.mem_nhds (hmem p hp)))
  obtain ⟨O, Z, hO, hZ, hKO, h0Z, hOZ⟩ :=
    generalized_tube_lemma hK isCompact_singleton isOpen_interior hKN
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp hZ 0 (h0Z (mem_singleton 0))
  refine ⟨O, hO, hKO, ε, hε, ?_⟩
  intro p hp v hv
  have hvZ : v ∈ Z := he (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  have hm : (p, v) ∈ interior (f ⁻¹' U) := hOZ ⟨hp, hvZ⟩
  exact (interior_subset : interior (f ⁻¹' U) ⊆ f ⁻¹' U) hm

theorem repairError_open_stability {m : Type*} [Fintype m] [DecidableEq m]
    {K : Set (Symmetric3 × Matrix (Fin 3) m ℝ)} (hK : IsCompact K)
    (hE : ∀ p ∈ K, LinearIndependent ℝ p.2.col)
    {U : Set Symmetric3} (hU : IsOpen U) (hA : ∀ p ∈ K, p.1 ∈ U) :
    ∃ O : Set (Symmetric3 × Matrix (Fin 3) m ℝ), IsOpen O ∧ K ⊆ O ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ O, ∀ R : Matrix (Fin 3) m ℝ,
        ‖R‖ < ε → repairError p.1 p.2 R ∈ U := by
  let f : (Symmetric3 × Matrix (Fin 3) m ℝ) × Matrix (Fin 3) m ℝ → Symmetric3 :=
    fun p => repairError p.1.1 p.1.2 p.2
  have hf : ∀ p ∈ K, ContinuousAt f (p, 0) := by
    intro p hp
    have h₁ : Continuous (fun q : (Symmetric3 × Matrix (Fin 3) m ℝ) ×
      Matrix (Fin 3) m ℝ => q.1.1) := continuous_fst.fst
    have h₂ : Continuous (fun q : (Symmetric3 × Matrix (Fin 3) m ℝ) ×
      Matrix (Fin 3) m ℝ => q.1.2) := continuous_fst.snd
    exact continuousAt_repairError _ _ _ h₁.continuousAt h₂.continuousAt
      continuous_snd.continuousAt (hE p hp)
  apply compact_zero_stability hK f hf hU
  intro p hp
  simpa only [f, repairError_zero] using hA p hp

end ScalarConductivity

end

end OAI
