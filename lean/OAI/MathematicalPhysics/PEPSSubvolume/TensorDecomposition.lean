import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.PhysicalModular
import OAI.MathematicalPhysics.PEPSSubvolume.LocalBlocks
import OAI.MathematicalPhysics.PEPSSubvolume.Pinning

namespace OAI

/-! Bounded decomposition of local support across a contour. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.LocalTensorDecomposition
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.PhysicalModular PolynomialPEPS.Subvolume.Pinning PolynomialPEPS.Subvolume.LocalBlocks
variable {L q : ℕ}

theorem lift_split_tensor (C S : Finset (Vertex L)) (hCS : C ⊆ S)
    (a : Matrix (RegionConfiguration q C) (RegionConfiguration q C) ℂ)
    (b : Matrix (RegionConfiguration q (S\C)) (RegionConfiguration q (S\C)) ℂ) :
    Matrix.reindex (splitEquiv C S hCS) (splitEquiv C S hCS) (Matrix.kronecker a b) =
      liftBetween hCS a * liftBetween (Finset.sdiff_subset : S\C ⊆ S) b := by
  classical
  ext x y
  obtain ⟨⟨u,z⟩,rfl⟩ := (splitEquiv (q := q) C S hCS).surjective x
  obtain ⟨⟨v,w⟩,rfl⟩ := (splitEquiv (q := q) C S hCS).surjective y
  simp only [Matrix.reindex_apply,Matrix.kronecker,Matrix.kroneckerMap]
  rw [Matrix.mul_apply,← Equiv.sum_comp (splitEquiv (q := q) C S hCS)]
  simp only [splitEquiv,Equiv.coe_fn_mk,Fintype.sum_prod_type,
    liftBetween_core_join,liftBetween_shell_join C S hCS]
  simp

theorem liftLocal_compl_join (X : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ)
    (x y : RegionConfiguration q X) (z w : RegionConfiguration q Xᶜ) :
    liftLocal Xᶜ B (joinConfigurations X x z) (joinConfigurations X y w) =
      if x=y then B z w else 0 := by
  classical
  have heq : (∀ v, v∉Xᶜ → joinConfigurations X x z v = joinConfigurations X y w v) ↔ x=y := by
    constructor
    · intro h
      funext v
      simpa [joinConfigurations,v.property] using h v.val (by simp)
    · rintro rfl v hv
      have hvX : v∈X := by simpa using hv
      simp [joinConfigurations,hvX]
  have hz : (fun v : {v : Vertex L // v∈Xᶜ} => joinConfigurations X x z v.val)=z := by
    funext v
    simp [joinConfigurations,Finset.mem_compl.mp v.property]
  have hw : (fun v : {v : Vertex L // v∈Xᶜ} => joinConfigurations X y w v.val)=w := by
    funext v
    simp [joinConfigurations,Finset.mem_compl.mp v.property]
  simp only [liftLocal,heq,hz,hw]

theorem tensorAcross_one_left (X : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    tensorAcross X 1 B = liftLocal Xᶜ B := by
  classical
  ext x y
  obtain ⟨⟨u,z⟩,rfl⟩ := (joinEquiv (q := q) X).surjective x
  obtain ⟨⟨v,w⟩,rfl⟩ := (joinEquiv (q := q) X).surjective y
  simp only [joinEquiv_apply,tensorAcross_join,liftLocal_compl_join,Matrix.one_apply]
  split_ifs <;> simp

theorem tensorAcross_eq_product (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    tensorAcross X A B = liftLocal X A * liftLocal Xᶜ B := by
  classical
  calc
    _ = tensorAcross X (A*1) (1*B) := by simp
    _ = _ := by rw [tensorAcross_mul,tensorAcross_one,tensorAcross_one_left]

theorem liftBetween_norm_le (hq : 0<q) {S X : Finset (Vertex L)} (hSX : S ⊆ X)
    (A : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ) :
    ‖liftBetween hSX A‖ ≤ ‖A‖ :=
  NonUnitalStarAlgHom.norm_apply_le (liftBetweenHom hq hSX) A

theorem opNorm_liftLocal (hq : 0<q) (S : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ) :
    opNorm (liftLocal S A) = ‖A‖ := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (liftLocal S A)‖ = _
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  exact NonUnitalStarAlgHom.norm_map (localLiftHom S) (liftLocal_injective hq S) A

theorem exists_local_tensor_decomposition (hq : 0<q)
    (S X C : Finset (Vertex L)) (hCS : C ⊆ S) (hCX : C ⊆ X) (hT : S\C ⊆ Xᶜ)
    (H : Operator L q) (hH : SupportedOn H S) :
    ∃ (A : (RegionConfiguration q C × RegionConfiguration q C) →
        Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
      (B : (RegionConfiguration q C × RegionConfiguration q C) →
        Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ),
      H = ∑ i, tensorAcross X (A i) (B i) ∧
      (∑ i, ‖A i‖*‖B i‖) ≤ (Fintype.card (RegionConfiguration q C):ℝ)^2 * opNorm H := by
  classical
  obtain ⟨h,rfl⟩ := hH
  let e := splitEquiv (q := q) C S hCS
  let h' := Matrix.reindex e.symm e.symm h
  let A := fun i : RegionConfiguration q C × RegionConfiguration q C =>
    liftBetween hCX (Matrix.single i.1 i.2 (1:ℂ))
  let B := fun i : RegionConfiguration q C × RegionConfiguration q C =>
    liftBetween hT (block h' i.1 i.2)
  refine ⟨A,B,?_,?_⟩
  · have hd := block_decomposition h'
    have he : Matrix.reindex e e h' = h := by
      ext x y
      simp [h',Matrix.reindex_apply]
    rw [← he,hd]
    change localLiftHom S ((reindexStarAlgEquiv e) (∑ i, ∑ j,
      Matrix.kronecker (Matrix.single i j (1:ℂ)) (block h' i j))) = _
    simp only [map_sum,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    change liftLocal S (Matrix.reindex e e (Matrix.kronecker (Matrix.single i j (1:ℂ))
      (block h' i j))) = tensorAcross X (A (i,j)) (B (i,j))
    rw [lift_split_tensor,liftLocal_mul,liftLocal_liftBetween,liftLocal_liftBetween,
      tensorAcross_eq_product]
    simp only [A,B,liftLocal_liftBetween]
  · have hc := decomposition_cost h'
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ i, ∑ j, ‖(Matrix.single i j (1:ℂ):Matrix (RegionConfiguration q C) _ ℂ)‖ * ‖block h' i j‖ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul (liftBetween_norm_le hq hCX _) (liftBetween_norm_le hq hT _)
          (norm_nonneg _) (norm_nonneg _)
      _ ≤ _ := by
        convert hc using 1
        rw [opNorm_liftLocal hq S h]
        exact congrArg (fun t => (Fintype.card (RegionConfiguration q C):ℝ)^2*t) (norm_reindex e.symm h).symm

end PolynomialPEPS.Subvolume.LocalTensorDecomposition

end

end OAI
