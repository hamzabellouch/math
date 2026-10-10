import OAI.GroupTheory.Kervaire.SignedIncidence

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireFixed

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
def fixedDim (M : Matrix I I ℂ) := Module.finrank ℂ (LinearMap.ker (M.mulVecLin - LinearMap.id))
lemma mulVecLin_sub_one (M : Matrix I I ℂ) :
    (M-1).mulVecLin = M.mulVecLin - LinearMap.id := by
  ext v i
  simp

lemma fixedDim_reindex (e : I ≃ J) (M : Matrix I I ℂ) :
    fixedDim (Matrix.reindex e e M) = fixedDim M := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (M - 1).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker ((Matrix.reindex e e M) - 1).mulVecLin
  have hm : (Matrix.reindex e e M) - 1 = Matrix.reindex e e (M - 1) := by
    change (Matrix.reindexAlgEquiv ℂ ℂ e) M - 1 = (Matrix.reindexAlgEquiv ℂ ℂ e) (M-1)
    rw [map_sub,map_one]
  have hr := Matrix.rank_reindex e e (M-1)
  change Module.finrank ℂ (LinearMap.range ((Matrix.reindex e e (M-1)).mulVecLin)) =
    Module.finrank ℂ (LinearMap.range (M-1).mulVecLin) at hr
  rw [← hm] at hr
  rw [mulVecLin_sub_one] at h1 h2 hr
  rw [mulVecLin_sub_one] at hr
  rw [hr] at h2
  have hc := Fintype.card_congr e
  simp only [Module.finrank_fintype_fun_eq_card] at h1 h2
  unfold fixedDim
  omega
end

section
open Matrix
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
def reindexUnitary (e : I ≃ J) (P : unitary (Matrix I I ℂ)) : unitary (Matrix J J ℂ) :=
  ⟨Matrix.reindex e e (P : Matrix I I ℂ),by
    let f := Matrix.reindexAlgEquiv ℂ ℂ e
    have hs (M : Matrix I I ℂ) : star (f M) = f (star M) := by
      exact Matrix.conjTranspose_reindex e e M
    change star (f P) * f P = 1 ∧ f P * star (f P) = 1
    constructor
    · rw [hs,← map_mul,P.property.1,map_one]
    · rw [hs,← map_mul,P.property.2,map_one]⟩
end

section
open KervaireIncidenceCurrent KervaireSignPairing KervaireUnitaryHomotopy
open scoped Matrix.Norms.L2Operator
variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

lemma exists_signed_fixed_pos [Nonempty K] (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : ∑ i, s i = 1)
    (P : unitary (Mat (K × I))) :
    ∃ X : unitary (Mat K), Fintype.card K ≤ fixedDim (signedMatrix s (X : Mat K) * (P : Mat (K × I))) := by
  classical
  let e := coordinates (K := K) s (sign_count s hs hsum)
  let Q := reindexUnitary e.symm P
  obtain ⟨X,hX⟩ := exists_paired_fixed (repeatMap (K := K) (D := negative s)) Q
  refine ⟨X,?_⟩
  change Fintype.card K ≤ fixedDim ((pairedMap (repeatMap (K := K) (D := negative s))) X * (Q : Mat (K ⊕ ((K × negative s) ⊕ (K × negative s))))) at hX
  have hD : (pairedMap (repeatMap (K := K) (D := negative s))) X =
      Matrix.reindex e.symm e.symm (signedMatrix s (X : Mat K)) :=
    (signedMatrix_coordinates s hs (sign_count s hs hsum) (X : Mat K)).symm
  have hM : (pairedMap (repeatMap (K := K) (D := negative s))) X * (Q : Mat (K ⊕ ((K × negative s) ⊕ (K × negative s)))) =
      Matrix.reindex e.symm e.symm (signedMatrix s (X : Mat K) * (P : Mat (K × I))) := by
    rw [hD]
    exact (map_mul (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (signedMatrix s (X : Mat K)) P).symm
  rw [hM,fixedDim_reindex] at hX
  exact hX

omit [Fintype I] [Fintype K] [DecidableEq K] in
lemma signedMatrix_neg (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (X : Mat K) :
    signedMatrix (fun i ↦ -s i) X = signedMatrix s (star X) := by
  unfold signedMatrix
  congr 1
  funext i
  rcases hs i with h | h <;> simp [h]

lemma exists_signed_fixed [Nonempty K] (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (P : unitary (Mat (K × I))) :
    ∃ X : unitary (Mat K), Fintype.card K ≤ fixedDim (signedMatrix s (X : Mat K) * (P : Mat (K × I))) := by
  rcases hsum with hsum | hsum
  · exact exists_signed_fixed_pos s hs hsum P
  · have hs' (i : I) : -s i = 1 ∨ -s i = -1 := by
      rcases hs i with h | h <;> simp [h]
    have hsum' : ∑ i, -s i = 1 := by rw [Finset.sum_neg_distrib,hsum]; norm_num
    obtain ⟨X,hX⟩ := exists_signed_fixed_pos (fun i ↦ -s i) hs' hsum' P
    refine ⟨star X,?_⟩
    rw [signedMatrix_neg s hs] at hX
    exact hX
end

open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev fixedSpace (M : Matrix I I ℂ) := LinearMap.ker (M.mulVecLin - LinearMap.id)
omit [DecidableEq I] in
@[simp] lemma mem_fixedSpace (M : Matrix I I ℂ) (v : I → ℂ) :
    v ∈ fixedSpace M ↔ M.mulVec v = v := by
  simp [fixedSpace, LinearMap.mem_ker, sub_eq_zero]

lemma fixed_star {M : Matrix I I ℂ} (hM : M ∈ unitary (Matrix I I ℂ))
    {v : I → ℂ} (hv : M.mulVec v = v) : (star M).mulVec v = v := by
  calc
    (star M).mulVec v = (star M).mulVec (M.mulVec v) := congrArg _ hv.symm
    _ = v := by rw [mulVec_mulVec, hM.1, one_mulVec]

/-- Both traversal blocks have the same fixed space dimension, without a
spectral-theorem assumption or a nonzero complement assumption. -/
def doubleFixedMap (D P : unitary (Matrix I I ℂ)) :
    (fixedSpace ((D : Matrix I I ℂ) * (P : Matrix I I ℂ)) × fixedSpace ((D : Matrix I I ℂ) * (P : Matrix I I ℂ))) →ₗ[ℂ]
      fixedSpace ((fromBlocks 0 (D : Matrix I I ℂ) (star D : Matrix I I ℂ) 0) *
        (fromBlocks 0 (star P : Matrix I I ℂ) (P : Matrix I I ℂ) 0)) where
  toFun v := ⟨Sum.elim (v.1 : I → ℂ) ((star D : Matrix I I ℂ).mulVec v.2),by
    rw [mem_fixedSpace]
    have h1 := (mem_fixedSpace _ _).mp v.1.property
    have h2 := fixed_star (mul_mem D.property P.property) ((mem_fixedSpace _ _).mp v.2.property)
    simp only [star_mul] at h2
    rw [fromBlocks_multiply]
    simp only [zero_mul,mul_zero,zero_add,add_zero]
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec,add_zero,zero_add]
    funext i
    cases i with
    | inl i => simpa using congrFun h1 i
    | inr i =>
      change ((star D : Matrix I I ℂ) * (star P : Matrix I I ℂ)).mulVec
        ((star D : Matrix I I ℂ).mulVec v.2) i = ((star D : Matrix I I ℂ).mulVec v.2) i
      have hh := congrArg ((star D : Matrix I I ℂ).mulVec) h2
      simpa only [mulVec_mulVec, mul_assoc] using congrFun hh i⟩
  map_add' v w := by
    apply Subtype.ext
    funext i
    cases i <;> simp [mulVec_add]
  map_smul' c v := by
    apply Subtype.ext
    funext i
    cases i <;> simp [mulVec_smul]

lemma doubleFixedMap_injective (D P : unitary (Matrix I I ℂ)) :
    Function.Injective (doubleFixedMap D P) := by
  intro v w h
  have hh := congrArg Subtype.val h
  have h1 : (v.1 : I → ℂ) = w.1 := funext fun i ↦ congrFun hh (Sum.inl i)
  have h2 : (star D : Matrix I I ℂ).mulVec v.2 = (star D : Matrix I I ℂ).mulVec w.2 :=
    funext fun i ↦ congrFun hh (Sum.inr i)
  have hi := congrArg (D : Matrix I I ℂ).mulVec h2
  simp only [mulVec_mulVec] at hi
  exact Prod.ext (Subtype.ext h1) (Subtype.ext (by simpa [D.property.2] using hi))

lemma two_mul_fixedDim_le (D P : unitary (Matrix I I ℂ)) :
    2 * fixedDim ((D : Matrix I I ℂ) * (P : Matrix I I ℂ)) ≤
      fixedDim ((fromBlocks 0 (D : Matrix I I ℂ) (star D : Matrix I I ℂ) 0) *
        (fromBlocks 0 (star P : Matrix I I ℂ) (P : Matrix I I ℂ) 0)) := by
  have h := LinearMap.finrank_le_finrank_of_injective (doubleFixedMap_injective D P)
  simpa only [Module.finrank_prod, ← two_mul, fixedDim, fixedSpace] using h
end KervaireFixed

namespace KervaireMatrix
open KervaireFixed KervaireSpectral KervaireRegular
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

/-- Scalar phase bound from the literal complex fixed-space dimension. -/
lemma phase_scalar_le_codim (M Q : Matrix D D ℂ)
    (hM : M ∈ unitary (Matrix D D ℂ)) (hQ : Q ∈ unitary (Matrix D D ℂ))
    (hc : Q * M * star Q = star M) :
    let _ := isStarNormal_of_mem_unitary (scalarTensor_mem_unitary (A := A) hM)
    KervaireMatrix.phase (scalarTensor (A := A) M) ≤
      ((Fintype.card D : ℝ) - fixedDim M) / 2 := by
  let L := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  let e := (WithLp.linearEquiv 2 ℂ (D → ℂ)).symm
  let E := (fixedSpace M).map (e : (D → ℂ) →ₗ[ℂ] EuclideanSpace ℂ D)
  have hE (v : E) : L M (v : EuclideanSpace ℂ D) = v := by
    obtain ⟨w,hw,he⟩ := v.property
    rw [← he]
    change WithLp.toLp 2 (M.mulVec w) = WithLp.toLp 2 w
    rw [(mem_fixedSpace M w).mp hw]
  have hML := Unitary.map_mem L hM
  have hQL := Unitary.map_mem L hQ
  have hcL : L Q * L M * star (L Q) = star (L M) := by
    rw [← map_star, ← map_mul, ← map_mul,hc,map_star]
  let _ := isStarNormal_of_mem_unitary hML
  let _ := isStarNormal_of_mem_unitary (scalarTensor_mem_unitary (A := A) hM)
  change KervaireMatrix.phase (scalarTensor (A := A) M) ≤ _
  rw [phase_scalarTensor M hM]
  have h := sumPhase_le_half_codim (L M) (L Q) hML hQL hcL
    (EuclideanSpace.basisFun D ℂ) E hE
  have hd : Module.finrank ℂ E = fixedDim M := e.finrank_map_eq (fixedSpace M)
  rw [hd] at h
  simpa only [finrank_euclideanSpace] using h
end KervaireMatrix

end

end OAI
