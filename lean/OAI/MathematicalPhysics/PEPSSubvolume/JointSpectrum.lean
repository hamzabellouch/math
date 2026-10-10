import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators

namespace OAI

/-! Common eigenbases for positive commuting matrices. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open PolynomialPEPS.PinnedEntropy

open scoped BigOperators Matrix.Norms.L2Operator
namespace PolynomialPEPS.Subvolume.JointDiagonalization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_subordinate {κ E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (V : κ → Submodule ℂ E)
    (horth : OrthogonalFamily ℂ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (htop : (⨆ i, V i) = ⊤) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (idx : Fin (Module.finrank ℂ E) → κ), ∀ i, b i ∈ V (idx i) := by
  classical
  let : Fintype {i : κ // V i ≠ ⊥} := horth.independent.fintypeNeBotOfFiniteDimensional
  let W : {i : κ // V i ≠ ⊥} → Submodule ℂ E := fun i => V i.val
  have horthW := horth.comp (f := fun i : {i : κ // V i ≠ ⊥} => i.val) Subtype.val_injective
  have htopW : (⨆ i, W i) = ⊤ := (iSup_ne_bot_subtype V).trans htop
  have hV : DirectSum.IsInternal W := horthW.isInternal_iff.mpr
    (by rw [htopW,Submodule.top_orthogonal_eq_bot])
  refine ⟨hV.subordinateOrthonormalBasis rfl horthW,
    (fun i => (hV.subordinateOrthonormalBasisIndex rfl i horthW).val),?_⟩
  exact fun i => hV.subordinateOrthonormalBasis_subordinate rfl i horthW

theorem exists_basis (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (d e : ι → ℂ),
      (∀ i, A.toEuclideanLin (b i) = d i • b i) ∧
      (∀ i, B.toEuclideanLin (b i) = e i • b i) := by
  classical
  have hA' := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hB' := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hAB' : Commute A.toEuclideanLin B.toEuclideanLin := by
    change (Matrix.toLpLin 2 2 A).comp (Matrix.toLpLin 2 2 B) =
      (Matrix.toLpLin 2 2 B).comp (Matrix.toLpLin 2 2 A)
    rw [← Matrix.toLpLin_mul_same,← Matrix.toLpLin_mul_same,hAB.eq]
  let V : (ℂ × ℂ) → Submodule ℂ (EuclideanSpace ℂ ι) :=
    fun i => Module.End.eigenspace A.toEuclideanLin i.2 ⊓
      Module.End.eigenspace B.toEuclideanLin i.1
  have horth := hA'.orthogonalFamily_eigenspace_inf_eigenspace hB'
  have htop : (⨆ i, V i) = ⊤ := by
    rw [iSup_prod]
    change (⨆ i : ℂ, ⨆ j : ℂ, Module.End.eigenspace A.toEuclideanLin j ⊓
      Module.End.eigenspace B.toEuclideanLin i) = ⊤
    rw [iSup_comm]
    exact hA'.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hB' hAB'
  obtain ⟨b₀,idx,hm⟩ := exists_subordinate V horth htop
  let eι : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)) ≃ ι :=
    Fintype.equivOfCardEq (by simp)
  refine ⟨b₀.reindex eι,(fun i => (idx (eι.symm i)).2),
    (fun i => (idx (eι.symm i)).1),?_,?_⟩
  · intro i
    have h := Module.End.mem_eigenspace_iff.mp (hm (eι.symm i)).1
    simpa only [OrthonormalBasis.reindex_apply] using h
  · intro i
    have h := Module.End.mem_eigenspace_iff.mp (hm (eι.symm i)).2
    simpa only [OrthonormalBasis.reindex_apply] using h

def basisUnitary (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) :
    unitary (Matrix ι ι ℂ) :=
  ⟨(EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

theorem conjugate_eq_diagonal (A : Matrix ι ι ℂ)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (d : ι → ℂ)
    (hd : ∀ i, A.toEuclideanLin (b i) = d i • b i) :
    A = (basisUnitary b : Matrix ι ι ℂ) * Matrix.diagonal d * star (basisUnitary b : Matrix ι ι ℂ) := by
  let U := basisUnitary b
  have hAU : A*(U : Matrix ι ι ℂ) = (U : Matrix ι ι ℂ)*Matrix.diagonal d := by
    ext i j
    have h := congrArg (fun v : EuclideanSpace ℂ ι => v i) (hd j)
    rw [Matrix.mul_diagonal]
    change (∑ k, A i k * (b j) k) = (b j) i * d j
    simpa [Matrix.toLpLin_apply,Matrix.mulVec,dotProduct,smul_eq_mul,mul_comm] using h
  have hright := congrArg (fun M : Matrix ι ι ℂ => M*star (U : Matrix ι ι ℂ)) hAU
  have hu : (U : Matrix ι ι ℂ)*star (U : Matrix ι ι ℂ) = 1 := Unitary.coe_mul_star_self U
  rw [mul_assoc,hu,mul_one] at hright
  exact hright

theorem exists_unitary (A B : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ (U : unitary (Matrix ι ι ℂ)) (d e : ι → ℂ),
      A = (U : Matrix ι ι ℂ)*Matrix.diagonal d*star (U : Matrix ι ι ℂ) ∧
      B = (U : Matrix ι ι ℂ)*Matrix.diagonal e*star (U : Matrix ι ι ℂ) := by
  obtain ⟨b,d,e,hd,he⟩ := exists_basis A B hA hB hAB
  exact ⟨basisUnitary b,d,e,conjugate_eq_diagonal A b d hd,conjugate_eq_diagonal B b e he⟩

open scoped ComplexOrder

theorem diagonal_nonneg (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (U : unitary (Matrix ι ι ℂ)) (d : ι → ℂ)
    (hd : A = (U : Matrix ι ι ℂ)*Matrix.diagonal d*star (U : Matrix ι ι ℂ)) :
    ∀ i, 0 ≤ d i := by
  have hp := hA.conjTranspose_mul_mul_same (U : Matrix ι ι ℂ)
  rw [hd] at hp
  have hu : star (U : Matrix ι ι ℂ)*(U : Matrix ι ι ℂ)=1 := Unitary.coe_star_mul_self U
  rw [← Matrix.star_eq_conjTranspose,← mul_assoc,← mul_assoc,hu,one_mul,
    mul_assoc,hu,mul_one] at hp
  exact Matrix.posSemidef_diagonal_iff.mp hp

theorem exists_positive_unitary (A B : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hAB : Commute A B) :
    ∃ (U : unitary (Matrix ι ι ℂ)) (d e : ι → ℝ),
      (∀ i, 0 ≤ d i) ∧ (∀ i, 0 ≤ e i) ∧
      A = (U : Matrix ι ι ℂ)*Matrix.diagonal (fun i => (d i:ℂ))*star (U : Matrix ι ι ℂ) ∧
      B = (U : Matrix ι ι ℂ)*Matrix.diagonal (fun i => (e i:ℂ))*star (U : Matrix ι ι ℂ) := by
  obtain ⟨U,d,e,hd,he⟩ := exists_unitary A B hA.isHermitian hB.isHermitian hAB
  have hd0 := diagonal_nonneg A hA U d hd
  have he0 := diagonal_nonneg B hB U e he
  have hdr (i : ι) : ((d i).re:ℂ) = d i := by
    exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp (hd0 i)).2)
  have her (i : ι) : ((e i).re:ℂ) = e i := by
    exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp (he0 i)).2)
  refine ⟨U,(fun i => (d i).re),(fun i => (e i).re),
    (fun i => (Complex.nonneg_iff.mp (hd0 i)).1),
    (fun i => (Complex.nonneg_iff.mp (he0 i)).1),?_,?_⟩
  · simpa only [hdr] using hd
  · simpa only [her] using he

end PolynomialPEPS.Subvolume.JointDiagonalization

end

end OAI
