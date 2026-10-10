import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicCanonicalAllowedStatement

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set
namespace PrimeDegreePackets.Adelic

def realPGLToSL {n : ℕ} (hodd : Odd n) : PGL(Fin n, ℝ) → G n :=
  Quotient.lift (realSLNormalize hodd) (by
    intro a b hab
    apply specialLinear_toPGL_injective_odd hodd
    rw [realSLNormalize_projective,realSLNormalize_projective]
    exact Quotient.sound hab)

lemma realPGLToSL_projective {n : ℕ} (hodd : Odd n) (h : PGL(Fin n, ℝ)) :
    SpecialLinearGroup.toPGL (realPGLToSL hodd h) = h := by
  induction h using Quotient.inductionOn with
  | h a => exact realSLNormalize_projective hodd a

lemma realPGLToSL_toPGL {n : ℕ} (hodd : Odd n) (h : G n) :
    realPGLToSL hodd (SpecialLinearGroup.toPGL h) = h := by
  apply specialLinear_toPGL_injective_odd hodd
  exact realPGLToSL_projective hodd _

lemma continuous_realPGLToSL {n : ℕ} (hodd : Odd n) : Continuous (realPGLToSL hodd) :=
  (continuous_realSLNormalize hodd).quotient_lift _

lemma real_torus_diagonal {n : ℕ} (hodd : Odd n) {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (t : realTorus b) :
    ∀ i j, i ≠ j →
      (realPGLToSL hodd ((ProjGenLinGroup.mk (realBasisGL hn b σ))⁻¹ * t.val *
        ProjGenLinGroup.mk (realBasisGL hn b σ))).val i j = 0 := by
  obtain ⟨u,hu⟩ := t.property
  let z := Units.map (realTensorEquiv σ hn).toMonoidHom u
  have hre : rowRegularUnits (b.baseChange ℝ) u * realBasisGL hn b σ =
      realBasisGL hn b σ * diagonalUnits n z := by
    have he := regular_realTensorEquiv_symm hn b σ z
    have hu' : Units.map (realTensorEquiv σ hn).symm.toMonoidHom z = u := by
      apply Units.ext
      exact (realTensorEquiv σ hn).symm_apply_apply u.val
    rwa [hu'] at he
  have ht : (ProjGenLinGroup.mk (realBasisGL hn b σ))⁻¹ * t.val *
        ProjGenLinGroup.mk (realBasisGL hn b σ) = ProjGenLinGroup.mk (diagonalUnits n z) := by
    change ProjGenLinGroup.mk (rowRegularUnits (b.baseChange ℝ) u) = t.val at hu
    rw [← hu,← map_inv,← map_mul,← map_mul]
    congr 1
    rw [mul_assoc,hre,← mul_assoc,inv_mul_cancel,one_mul]
  obtain ⟨D,hD,heD⟩ := specialLinear_diagonal_preimage hodd z
  rw [ht,← heD,realPGLToSL_toPGL]
  exact hD

lemma real_torus_identity_positive {n : ℕ} (hodd : Odd n) {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (t : realTorus b) (ht : t ∈ connectedComponent (1 : realTorus b)) :
    realPGLToSL hodd ((ProjGenLinGroup.mk (realBasisGL hn b σ))⁻¹ * t.val *
      ProjGenLinGroup.mk (realBasisGL hn b σ)) ∈ positiveDiagonal n := by
  let F : realTorus b → G n := fun s => realPGLToSL hodd
    ((ProjGenLinGroup.mk (realBasisGL hn b σ))⁻¹ * s.val * ProjGenLinGroup.mk (realBasisGL hn b σ))
  have hF : Continuous F := (continuous_realPGLToSL hodd).comp
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hF1 : F 1 = 1 := by
    dsimp [F]
    simp only [mul_one,inv_mul_cancel]
    simpa using realPGLToSL_toPGL hodd (1 : G n)
  refine ⟨real_torus_diagonal hodd hn b σ t,?_⟩
  intro i
  have hne (s : realTorus b) : (F s).val i i ≠ 0 := by
    obtain ⟨z,hz⟩ := diagonalUnits_of_SL (F s) (real_torus_diagonal hodd hn b σ s)
    have hh := congrArg (fun A : GL (Fin n) ℝ => A.val i i) hz
    change (F s).val i i = Matrix.diagonal z.val i i at hh
    rw [Matrix.diagonal_apply_eq] at hh
    rw [hh]
    exact Units.ne_zero (Units.map (Pi.evalMonoidHom (fun _ : Fin n => ℝ) i) z)
  by_contra hp
  have hc : Continuous (fun s : realTorus b => (F s).val i i) :=
    ((continuous_apply i).comp ((continuous_apply i).comp (SpecialLinearGroup.isClosedEmbedding_val.continuous.comp hF)))
  obtain ⟨s,hs,he⟩ := isPreconnected_connectedComponent.intermediate_value ht
    (mem_connectedComponent (x := (1 : realTorus b))) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc ((F t).val i i) ((F 1).val i i) from
      ⟨not_lt.mp hp,by simp [hF1]⟩)
  exact hne s he

theorem canonical_real_diagonalizer_allowed {n : ℕ} (hodd : Odd n)
    {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K) :
    CanonicalRealDiagonalizerAllowed hn b σ := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,⟨t,ht,rfl⟩,rfl⟩
    exact ⟨_,real_torus_identity_positive hodd hn b σ t ht,realPGLToSL_projective hodd _⟩
  · rintro x ⟨D,hD,rfl⟩
    obtain ⟨z,hz⟩ := diagonalUnits_of_SL D hD.1
    have hzp (i : Fin n) : 0 < z.val i := by
      have he := congrArg (fun A : GL (Fin n) ℝ => A.val i i) hz
      change D.val i i = Matrix.diagonal z.val i i at he
      rw [Matrix.diagonal_apply_eq] at he
      rw [← he]
      exact hD.2 i
    let w : Fin n → ℝ := fun i => Real.log (z.val i)
    have hw : signedExpUnit n 1 w = z := by
      apply Units.ext
      ext i
      simp [signedExpUnit,signValue,w,Real.exp_log (hzp i)]
    refine ⟨realExpTorus hn b σ w,realExpTorus_mem_identity hn b σ w,?_⟩
    change (ProjGenLinGroup.mk (realBasisGL hn b σ))⁻¹ *
      ProjGenLinGroup.mk (rowRegularUnits (b.baseChange ℝ)
        (Units.map (realTensorEquiv σ hn).symm.toMonoidHom (signedExpUnit n 1 w))) *
      ProjGenLinGroup.mk (realBasisGL hn b σ) = ProjGenLinGroup.mk D.toGL
    rw [hw,hz,← map_inv,← map_mul,← map_mul]
    congr 1
    rw [mul_assoc,regular_realTensorEquiv_symm,← mul_assoc,inv_mul_cancel,one_mul]

end PrimeDegreePackets.Adelic

end

end OAI
