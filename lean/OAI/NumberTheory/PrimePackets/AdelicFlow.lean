import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicFibers

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise MatrixGroups
open Matrix Module Filter Set MeasureTheory
namespace PrimeDegreePackets.Adelic

def splitFlow {d : ℕ} (u : LogCoordinates d) : (Fin (d+1) → ℝ)ˣ :=
  signedExpUnit (d+1) 1 (fullLog d u)

lemma continuous_splitFlow (d : ℕ) : Continuous (splitFlow (d := d)) :=
  (continuous_signedExpUnit (d+1)).comp (continuous_const.prodMk (continuous_fullLog d))

lemma diagonalUnits_splitFlow {d : ℕ} (u : LogCoordinates d) :
    diagonalUnits (d+1) (splitFlow u) = (diagonalFlow u).toGL := by
  apply Units.ext
  change Matrix.diagonal (splitFlow u).val = Matrix.diagonal _
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [splitFlow,signedExpUnit,fullLog,signValue]

def flowIdele {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) (u : LogCoordinates d) :
    (TensorAdeles K)ˣ := (ideleEquiv σ hn).symm (splitFlow u,1)

def flowTorus {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) (u : LogCoordinates d) :
    TorusQuotient K := QuotientGroup.mk (flowIdele σ hn u)

lemma continuous_flowTorus {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) : Continuous (flowTorus σ hn) :=
  QuotientGroup.continuous_mk.comp ((continuous_ideleEquiv_symm σ hn).comp
    ((continuous_splitFlow d).prodMk continuous_const))

lemma adelicIdelePoint_flow {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd (d+1)) (hn : finrank ℚ K = d+1) (b : Basis (Fin (d+1)) ℚ K)
    (σ : OrderedEmbeddings (d+1) K) (g : GL (Fin (d+1)) RationalFiniteAdeles)
    (t : (TensorAdeles K)ˣ) (u : LogCoordinates d) :
    adelicIdelePoint hodd hn b σ g (t * flowIdele σ hn u) =
      orbitMap (adelicIdelePoint hodd hn b σ g t) u := by
  obtain ⟨D,hD,hDz⟩ := specialLinear_diagonal_preimage hodd ((ideleEquiv σ hn t).1)
  have ht := adelic_translate_eq_latticePoint hodd hn b σ g t D hDz
  have he : ideleEquiv σ hn (t * flowIdele σ hn u) =
      (ideleEquiv σ hn t) * (splitFlow u,1) := by
    rw [map_mul]
    exact congrArg (fun x => ideleEquiv σ hn t * x) ((ideleEquiv σ hn).apply_symm_apply _)
  have hDu : SpecialLinearGroup.toPGL (D * diagonalFlow u) =
      ProjGenLinGroup.mk (diagonalUnits (d+1) ((ideleEquiv σ hn (t * flowIdele σ hn u)).1)) := by
    rw [he,Prod.fst_mul,map_mul,map_mul,diagonalUnits_splitFlow,hDz]
    rfl
  have ht' := adelic_translate_eq_latticePoint hodd hn b σ g (t * flowIdele σ hn u) (D * diagonalFlow u) hDu
  rw [he,Prod.snd_mul,mul_one] at ht'
  apply (ambientEquiv hodd hn b).injective
  simp only [adelicIdelePoint,Equiv.apply_symm_apply]
  rw [ht',ht,Equiv.symm_apply_apply]
  simp only [orbitMap,rightAction_mul]

lemma adelicTorusPoint_flow {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd (d+1)) (hn : finrank ℚ K = d+1) (b : Basis (Fin (d+1)) ℚ K)
    (σ : OrderedEmbeddings (d+1) K) (g : GL (Fin (d+1)) RationalFiniteAdeles)
    (t : TorusQuotient K) (u : LogCoordinates d) :
    adelicTorusPoint hodd hn b σ g (t * flowTorus σ hn u) =
      orbitMap (adelicTorusPoint hodd hn b σ g t) u := by
  induction t using QuotientGroup.induction_on with | H t =>
  exact adelicIdelePoint_flow hodd hn b σ g t u

end PrimeDegreePackets.Adelic

end

end OAI
