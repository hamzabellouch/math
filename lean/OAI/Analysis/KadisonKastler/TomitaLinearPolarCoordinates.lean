import OAI.Analysis.KadisonKastler.TomitaComplementaryRoot
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace OAI

/-! # Linear polar coordinates for the closed Tomita graph -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

/-- The linear unitary part of the Tomita operator in the chosen conjugate coordinates. -/
def tomitaLinearPolarUnitary : H ≃ₗᵢ[ℂ] H where
  toFun a := J (tomitaPolarConjugation J Ω hsep hcyc a)
  invFun a := tomitaPolarConjugation J Ω hsep hcyc (J.symm a)
  left_inv a := by dsimp only; rw [J.symm_apply_apply, tomitaPolarConjugation_involutive]
  right_inv a := by dsimp only; rw [tomitaPolarConjugation_involutive, J.apply_symm_apply]
  map_add' a b := by rw [map_add, map_add]
  map_smul' z a := by
    rw [map_smulₛₗ, map_smulₛₗ]
    simp only [RingHomCompTriple.comp_apply]
  norm_map' a := (J.norm_map _).trans ((tomitaPolarConjugation J Ω hsep hcyc).norm_map a)

@[simp] theorem tomitaLinearPolarUnitary_apply (a : H) :
    tomitaLinearPolarUnitary J Ω hsep hcyc a = J (tomitaPolarConjugation J Ω hsep hcyc a) := rfl

@[simp] theorem tomitaLinearPolarUnitary_symm_apply (a : H) :
    (tomitaLinearPolarUnitary J Ω hsep hcyc).symm a =
      tomitaPolarConjugation J Ω hsep hcyc (J.symm a) := rfl

theorem tomitaGraphRoot_polar_symm (a : H) :
    tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a) =
      tomitaPolarConjugation J Ω hsep hcyc (tomitaGraphComplementRoot (M := M) J Ω a) := by
  have h := congrArg (tomitaPolarConjugation J Ω hsep hcyc)
    (tomitaGraphRoot_polar_apply J Ω hsep hcyc (tomitaPolarConjugation J Ω hsep hcyc a))
  rw [tomitaPolarConjugation_involutive J Ω hsep hcyc
    (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a)),
    tomitaPolarConjugation_involutive J Ω hsep hcyc a] at h
  exact h

/-- Both positive coordinates are functions of the same positive contraction. -/
theorem tomitaGraphRoots_commute :
    Commute (tomitaGraphRoot (M := M) J Ω) (tomitaGraphComplementRoot (M := M) J Ω) := by
  have h : Commute (graphResolvent M J Ω 1) (1 - graphResolvent M J Ω 1) :=
    (Commute.one_right _).sub_right (Commute.refl _)
  rw [tomitaGraphRoot, tomitaGraphComplementRoot, CFC.sqrt_eq_cfc, CFC.sqrt_eq_cfc]
  exact ((h.cfc_nnreal NNReal.sqrt).symm.cfc_nnreal NNReal.sqrt).symm

theorem tomitaClosedLinearOperator_positive_graph_iff (x y : H) :
    (x, y) ∈ (tomitaClosedLinearOperator M J Ω 1).graph ↔
      ∃ a : H, tomitaGraphRoot (M := M) J Ω a = x ∧
        tomitaLinearPolarUnitary J Ω hsep hcyc (tomitaGraphComplementRoot (M := M) J Ω a) = y := by
  rw [tomitaClosedLinearOperator_graph_iff J Ω hsep hcyc]
  constructor <;> rintro ⟨a, ha, hb⟩ <;> refine ⟨a, ha, ?_⟩
  · rw [tomitaGraphRoot_polar_symm J Ω hsep hcyc] at hb
    exact hb
  · rw [tomitaGraphRoot_polar_symm J Ω hsep hcyc]
    exact hb

end

end KadisonKastler

end OAI
