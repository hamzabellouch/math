import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicPacket

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise MatrixGroups
open Matrix Module Filter Set
namespace PrimeDegreePackets.Adelic

def diagonalUnits (n : ℕ) : (Fin n → ℝ)ˣ →* GL (Fin n) ℝ :=
  Units.map (Matrix.diagonalRingHom (Fin n) ℝ).toMonoidHom

def adelicMatrixPoint {n : ℕ} (h : GL (Fin n) ℝ) (g : GL (Fin n) RationalFiniteAdeles) :
    AmbientQuotient n := DoubleCoset.mk (rationalProjectiveGroup n) (finiteProjectiveIntegral n)
      (ProjGenLinGroup.mk h,ProjGenLinGroup.mk g)

def realMatrixPoint {n : ℕ} (h : GL (Fin n) ℝ) : AmbientQuotient n := adelicMatrixPoint h 1

lemma realMatrixPoint_eq_of_projective_eq {n : ℕ} {g h : GL (Fin n) ℝ}
    (he : ProjGenLinGroup.mk g = ProjGenLinGroup.mk h) : realMatrixPoint g = realMatrixPoint h := by
  simp only [realMatrixPoint,adelicMatrixPoint,he]

lemma realBasisGL_basisChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b m : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (rowBasisChange m b) * realBasisGL hn b σ =
      realBasisGL hn m σ := by
  apply Units.ext
  ext i j
  have H := congrFun (realTensorMap_coordinates hn b σ (1 ⊗ₜ[ℚ] m i)) j
  have hc : (b.baseChange ℝ).equivFun (1 ⊗ₜ[ℚ] m i) =
      fun k => ((b.repr (m i) k : ℚ) : ℝ) := by
    funext k
    simp [Basis.baseChange_repr_tmul,Algebra.smul_def]
  rw [hc] at H
  simpa [rowBasisChange,Basis.toMatrix_apply,Matrix.mul_apply,Matrix.vecMul,dotProduct] using H

lemma realBasisGL_latticeBasis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (M : FullLattice n K) (σ : OrderedEmbeddings n K) :
    (realBasisGL hn (fullLatticeRatBasis M hn) σ).val = embeddingMatrix M σ := by
  ext i j
  simp [embeddingMatrix,fullLatticeRatBasis_apply]

lemma exists_SL_normalizedLattice_projective {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n)
    (hodd : Odd n) : ∃ h : G n, rowLattice h.val = normalizedLattice M σ ∧
      SpecialLinearGroup.toPGL h = ProjGenLinGroup.mk (realBasisGL hn (fullLatticeRatBasis M hn) σ) := by
  let B := embeddingMatrix M σ
  let r := |B.det| ^ (-(1 : ℝ) / n)
  have hr : r ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.mpr (embeddingMatrix_det_ne_zero M σ hn)) _).ne'
  let A := r • B
  have hd : |A.det| = 1 := normalizedMatrix_abs_det B hodd.pos (embeddingMatrix_det_ne_zero M σ hn)
  have hproj (c : ℝ) (hc : c ≠ 0) (h : G n) (hh : h.val = c • B) :
      SpecialLinearGroup.toPGL h = ProjGenLinGroup.mk (realBasisGL hn (fullLatticeRatBasis M hn) σ) := by
    apply ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨(Units.mk0 c hc)⁻¹,?_⟩
    apply Units.ext
    change h.val * Matrix.scalar (Fin n) c⁻¹ = _
    rw [hh,realBasisGL_latticeBasis]
    change (c • B) * Matrix.diagonal (fun _ => c⁻¹) = B
    rw [← Matrix.smul_one_eq_diagonal,Matrix.mul_smul,Matrix.mul_one,smul_smul]
    simp [hc]
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hd with hd | hd
  · exact ⟨⟨A,hd⟩,rfl,hproj r hr _ rfl⟩
  · have hneg : (-A).det = 1 := by
      rw [Matrix.det_neg,Fintype.card_fin,hodd.neg_one_pow,hd]
      norm_num
    refine ⟨⟨-A,hneg⟩,rowLattice_neg A,hproj (-r) (neg_ne_zero.mpr hr) _ ?_⟩
    simp only [A,neg_smul]

lemma ambientEquiv_latticePoint_rightAction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (D : G n) :
    ambientEquiv hodd hn b (rightAction (latticePoint M σ) D) =
      realMatrixPoint (realBasisGL hn (fullLatticeRatBasis M hn) σ * D.toGL) := by
  obtain ⟨h,hh,hproj⟩ := exists_SL_normalizedLattice_projective M σ hn hodd
  rw [latticePoint_eq_of_rowLattice_eq M σ h hh]
  change ambientEquiv hodd hn b (Quotient.mk _ (h * D)) = _
  rw [ambientEquiv_mk]
  unfold realAmbientPoint realMatrixPoint adelicMatrixPoint
  rw [map_mul,map_mul,hproj,map_one]
  rfl

lemma matrixFullLattice_basis_reduction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) :
    IntegralFiniteGL (GeneralLinearGroup.map rationalFiniteEmbedding
      (rowBasisChange (fullLatticeRatBasis (matrixFullLattice hn b g) hn) b) * g) := by
  let m := fullLatticeRatBasis (matrixFullLattice hn b g) hn
  let c := rowBasisChange m b
  have heq (p : Nat.Primes) :
      localMatrixLattice m (GeneralLinearGroup.map rationalFiniteEmbedding c * g) p =
        localIntegralSpan p.val m := by
    rw [localMatrixLattice_basisChange,← matrixFullLattice_completed hn b g p,
      completedLattice_integralSpan_basis]
  constructor
  · intro i j p
    exact (integralFiniteAt_of_lattice_eq m _ p (heq p)).1 i j
  · intro i j p
    have H := (integralFiniteAt_of_lattice_eq m _ p (heq p)).2 i j
    rw [← finiteMatrixAt_inv] at H
    exact H

lemma adelicMatrixPoint_reduction {n : ℕ} (h : GL (Fin n) ℝ)
    (g : GL (Fin n) RationalFiniteAdeles) (c : GL (Fin n) ℚ)
    (hc : IntegralFiniteGL (GeneralLinearGroup.map rationalFiniteEmbedding c * g)) :
    adelicMatrixPoint h g = realMatrixPoint (GeneralLinearGroup.map (algebraMap ℚ ℝ) c * h) := by
  apply DoubleCoset.eq.mpr
  let q := ProjGenLinGroup.mk c
  let k := ProjGenLinGroup.mk (GeneralLinearGroup.map rationalFiniteEmbedding c * g)
  have hk : k ∈ (integralFiniteGroup n).map ProjGenLinGroup.mk := ⟨_,hc,rfl⟩
  refine ⟨rationalProjectiveEmbedding n q,⟨q,rfl⟩,(1,k⁻¹),⟨rfl,Subgroup.inv_mem _ hk⟩,?_⟩
  apply Prod.ext
  · simp [rationalProjectiveEmbedding,q]
  · change ProjGenLinGroup.mk (1 : GL (Fin n) RationalFiniteAdeles) = _
    simp [rationalProjectiveEmbedding,q,k]

lemma adelicMatrixPoint_basis_reduction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (g : GL (Fin n) RationalFiniteAdeles) (D : GL (Fin n) ℝ) :
    adelicMatrixPoint (realBasisGL hn b σ * D) g =
      realMatrixPoint (realBasisGL hn (fullLatticeRatBasis (matrixFullLattice hn b g) hn) σ * D) := by
  rw [adelicMatrixPoint_reduction _ _ _ (matrixFullLattice_basis_reduction hn b g),
    ← mul_assoc,realBasisGL_basisChange]

lemma adelicRegular_real_matrix {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (t : (TensorAdeles K)ˣ) :
    GeneralLinearGroup.map (RingHom.fst ℝ RationalFiniteAdeles)
        (rowRegularUnits (b.baseChange RationalAdeles) t) * realBasisGL hn b σ =
      realBasisGL hn b σ * diagonalUnits n ((ideleEquiv σ hn t).1) := by
  apply Units.ext
  change (rowRegular (b.baseChange RationalAdeles) t.val).map (RingHom.fst ℝ RationalFiniteAdeles) *
    (realBasisGL hn b σ).val = (realBasisGL hn b σ).val * Matrix.diagonal ((ideleEquiv σ hn t).1).val
  rw [rowRegular_real_component,real_regular_diagonalization]
  rfl

lemma adelicRegular_finite_matrix {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (t : (TensorAdeles K)ˣ) :
    GeneralLinearGroup.map (RingHom.snd ℝ RationalFiniteAdeles)
        (rowRegularUnits (b.baseChange RationalAdeles) t) =
      finiteRegular b ((ideleEquiv σ hn t).2) := by
  apply Units.ext
  change (rowRegular (b.baseChange RationalAdeles) t.val).map (RingHom.snd ℝ RationalFiniteAdeles) =
    rowRegular (b.baseChange RationalFiniteAdeles)
      ((finiteTensorEquiv K).symm (finiteTensorEquiv K ((tensorProdEquiv K t.val).2)))
  rw [rowRegular_finite_component,AlgEquiv.symm_apply_apply]

lemma adelicRegular_translate {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (g : GL (Fin n) RationalFiniteAdeles) (t : (TensorAdeles K)ˣ) :
    adelicRegular b t * (ProjGenLinGroup.mk (realBasisGL hn b σ),ProjGenLinGroup.mk g) =
      (ProjGenLinGroup.mk (realBasisGL hn b σ * diagonalUnits n ((ideleEquiv σ hn t).1)),
        ProjGenLinGroup.mk (finiteRegular b ((ideleEquiv σ hn t).2) * g)) := by
  apply Prod.ext
  · change ProjGenLinGroup.mk (GeneralLinearGroup.map (RingHom.fst ℝ RationalFiniteAdeles)
      (rowRegularUnits (b.baseChange RationalAdeles) t)) * ProjGenLinGroup.mk (realBasisGL hn b σ) = _
    rw [← map_mul,adelicRegular_real_matrix]
  · change ProjGenLinGroup.mk (GeneralLinearGroup.map (RingHom.snd ℝ RationalFiniteAdeles)
      (rowRegularUnits (b.baseChange RationalAdeles) t)) * ProjGenLinGroup.mk g = _
    rw [adelicRegular_finite_matrix hn b σ]
    change ProjGenLinGroup.mk (finiteRegular b ((ideleEquiv σ hn t).2)) * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk (finiteRegular b ((ideleEquiv σ hn t).2) * g)
    rw [map_mul]

lemma specialLinear_diagonal_preimage {n : ℕ} (hodd : Odd n) (z : (Fin n → ℝ)ˣ) :
    ∃ D : G n, (∀ i j, i ≠ j → D.val i j = 0) ∧
      SpecialLinearGroup.toPGL D = ProjGenLinGroup.mk (diagonalUnits n z) := by
  obtain ⟨D,hD⟩ := specialLinear_toPGL_surjective_odd hodd (ProjGenLinGroup.mk (diagonalUnits n z))
  refine ⟨D,?_,hD⟩
  obtain ⟨c,hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hD
  intro i j hij
  have H := congrArg (fun A : GL (Fin n) ℝ => A.val i j) hc
  change (D.val * Matrix.diagonal (fun _ => c.val) : Matrix (Fin n) (Fin n) ℝ) i j = Matrix.diagonal z.val i j at H
  rw [Matrix.mul_diagonal,Matrix.diagonal_apply_ne _ hij] at H
  exact (mul_eq_zero.mp H).resolve_right (Units.ne_zero c)

lemma diagonalUnits_of_SL {n : ℕ} (D : G n) (hD : ∀ i j, i ≠ j → D.val i j = 0) :
    ∃ z : (Fin n → ℝ)ˣ, D.toGL = diagonalUnits n z := by
  have hd : Matrix.diagonal (Matrix.diag D.val) = D.val := Matrix.IsDiag.diagonal_diag hD
  have hp : ∏ i, D.val i i = (1 : ℝ) := by
    rw [← Matrix.det_diagonal]
    change (Matrix.diagonal (Matrix.diag D.val)).det = 1
    rw [hd]
    exact D.property
  have hz (i : Fin n) : D.val i i ≠ 0 := by
    have H : (∏ j, D.val j j) ≠ (0 : ℝ) := by rw [hp]; exact one_ne_zero
    exact (Finset.prod_ne_zero_iff.mp H) i (Finset.mem_univ i)
  let z : (Fin n → ℝ)ˣ :=
    ⟨fun i => D.val i i,fun i => (D.val i i)⁻¹,
      funext (fun i => mul_inv_cancel₀ (hz i)),funext (fun i => inv_mul_cancel₀ (hz i))⟩
  exact ⟨z,Units.ext hd.symm⟩

end PrimeDegreePackets.Adelic

end

end OAI
