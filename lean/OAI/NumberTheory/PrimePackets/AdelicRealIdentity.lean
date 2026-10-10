import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicDiagonalizerDefinitions

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set
namespace PrimeDegreePackets.Adelic

lemma continuous_projectivization (n : ℕ) :
    Continuous (ProjGenLinGroup.mk : GL (Fin n) ℝ → PGL(Fin n, ℝ)) :=
  QuotientGroup.continuous_mk

 
def realExpTorus {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (v : Fin n → ℝ) : realTorus b :=
  ⟨ProjGenLinGroup.mk (rowRegularUnits (b.baseChange ℝ)
      (Units.map (realTensorEquiv σ hn).symm.toMonoidHom (signedExpUnit n 1 v))),
    ⟨Units.map (realTensorEquiv σ hn).symm.toMonoidHom (signedExpUnit n 1 v),rfl⟩⟩

lemma continuous_realExpTorus {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K) :
    Continuous (realExpTorus hn b σ) := by
  apply Continuous.subtype_mk
  exact (continuous_projectivization n).comp ((continuous_rowRegularUnits (b.baseChange ℝ)).comp
    ((continuous_realTensorEquiv_symm σ hn).units_map.comp
      ((continuous_signedExpUnit n).comp (continuous_const.prodMk continuous_id))))

lemma realExpTorus_zero {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K) :
    realExpTorus hn b σ 0 = 1 := by
  have he : signedExpUnit n 1 0 = 1 := by
    apply Units.ext
    ext i
    simp [signedExpUnit,signValue]
  apply Subtype.ext
  change ProjGenLinGroup.mk (rowRegularUnits (b.baseChange ℝ)
      (Units.map (realTensorEquiv σ hn).symm.toMonoidHom (signedExpUnit n 1 0))) = 1
  rw [he,map_one,map_one,map_one]

lemma realExpTorus_mem_identity {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (v : Fin n → ℝ) : (realExpTorus hn b σ v : PGL(Fin n, ℝ)) ∈ realTorusIdentity b := by
  refine ⟨realExpTorus hn b σ v,?_,rfl⟩
  apply (isConnected_range (continuous_realExpTorus hn b σ)).subset_connectedComponent
    (x := (1 : realTorus b)) ?_ (Set.mem_range_self v)
  exact ⟨0,realExpTorus_zero hn b σ⟩

lemma regular_realTensorEquiv_symm {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (z : (Fin n → ℝ)ˣ) :
    rowRegularUnits (b.baseChange ℝ) (Units.map (realTensorEquiv σ hn).symm.toMonoidHom z) *
      realBasisGL hn b σ = realBasisGL hn b σ * diagonalUnits n z := by
  apply Units.ext
  change rowRegular (b.baseChange ℝ) ((realTensorEquiv σ hn).symm z.val) *
    (realBasisGL hn b σ).val = (realBasisGL hn b σ).val * Matrix.diagonal z.val
  rw [real_regular_diagonalization]
  congr 2
  exact (realTensorEquiv σ hn).apply_symm_apply z.val

end PrimeDegreePackets.Adelic

end

end OAI
