import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicBasisRepresentation

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set MeasureTheory
namespace PrimeDegreePackets.Adelic

lemma ambientEquiv_basis_independent {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b m : Basis (Fin n) ℚ K) :
    ambientEquiv hodd hn m = ambientEquiv hodd hn b := by
  ext x
  induction x using Quotient.inductionOn with | h g =>
  rw [ambientEquiv_mk,ambientEquiv_mk]

theorem generalAdelicOrbit_basis_independent {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b m : Basis (Fin n) ℚ K) (h : PGL(Fin n, ℝ))
    (g : GL (Fin n) RationalFiniteAdeles) (t : (TensorAdeles K)ˣ) :
    generalAdelicOrbit m
      (ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap ℚ ℝ) (rowBasisChange m b)) * h)
      (GeneralLinearGroup.map rationalFiniteEmbedding (rowBasisChange m b) * g) t =
      generalAdelicOrbit b h g t := by
  let c := rowBasisChange m b
  let q := rationalProjectiveEmbedding n (ProjGenLinGroup.mk c)
  have hb : (ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap ℚ ℝ) c) * h,
      ProjGenLinGroup.mk (GeneralLinearGroup.map rationalFiniteEmbedding c * g)) =
        q * (h,ProjGenLinGroup.mk g) := by
    apply Prod.ext
    · rfl
    · exact map_mul _ _ _
  apply Eq.symm
  apply DoubleCoset.eq.mpr
  refine ⟨q,⟨ProjGenLinGroup.mk c,rfl⟩,1,Subgroup.one_mem _,?_⟩
  change adelicRegular m t * _ = q * (adelicRegular b t * _) * 1
  rw [hb,mul_one,← mul_assoc,adelicRegular_basisChange,mul_assoc]

theorem generalAdelicOrbit_projective_lift_independent {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (h : PGL(Fin n, ℝ))
    (g g' : GL (Fin n) RationalFiniteAdeles)
    (he : ProjGenLinGroup.mk g = ProjGenLinGroup.mk g') (t : (TensorAdeles K)ˣ) :
    generalAdelicOrbit b h g t = generalAdelicOrbit b h g' t := by
  simp only [generalAdelicOrbit,he]

 

lemma native_projection_unique {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b m : Basis (Fin n) ℚ K)
    (p p' : TorusQuotient K → X n) (F F' : (TensorAdeles K)ˣ → AmbientQuotient n)
    (hp : ∀ t, ambientEquiv hodd hn b (p (QuotientGroup.mk t)) = F t)
    (hp' : ∀ t, ambientEquiv hodd hn m (p' (QuotientGroup.mk t)) = F' t)
    (hF : F = F') : p = p' := by
  funext x
  induction x using QuotientGroup.induction_on with | H t =>
  apply (ambientEquiv hodd hn b).injective
  rw [hp,← ambientEquiv_basis_independent hodd hn b m,hp',hF]

end PrimeDegreePackets.Adelic

end

end OAI
