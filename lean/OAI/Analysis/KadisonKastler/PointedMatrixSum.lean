import OAI.Analysis.KadisonKastler.PublishedPointedOperations
import OAI.Analysis.KadisonKastler.SpatialAssociatorAlgebra
import OAI.Analysis.KadisonKastler.SpatialProductSeparating
import OAI.Analysis.KadisonKastler.KaplanskyDensity
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

/-! # Tensor products of pointed matrix-site systems

The two site families act in the two tensor legs. Finite words split into
their two subwords, and their vector moments multiply. Cyclicity follows
from the dense tensor-product orbit; separation follows by the same
argument for the commutants. No modular or infinite-product input is used.
-/

namespace KadisonKastler

open Generator UnitalTomsWinter
open scoped TensorProduct

noncomputable section

universe u

private def sumLeftList {I J : Type*} (l : List (I ⊕ J)) : List I :=
  l.filterMap (fun x => match x with | .inl i => some i | .inr _ => none)

private def sumRightList {I J : Type*} (l : List (I ⊕ J)) : List J :=
  l.filterMap (fun x => match x with | .inl _ => none | .inr j => some j)

private theorem sumLeftList_nodup {I J : Type*} {l : List (I ⊕ J)}
    (h : l.Nodup) : (sumLeftList l).Nodup := by
  apply List.Nodup.filterMap _ h
  intro a b i ha hb
  cases a <;> cases b <;> simp_all

private theorem sumRightList_nodup {I J : Type*} {l : List (I ⊕ J)}
    (h : l.Nodup) : (sumRightList l).Nodup := by
  apply List.Nodup.filterMap _ h
  intro a b i ha hb
  cases a <;> cases b <;> simp_all

private theorem sumList_scalar_prod {I J : Type*} (a : I → ℂ) (b : J → ℂ)
    (l : List (I ⊕ J)) :
    (l.map (Sum.elim a b)).prod =
      ((sumLeftList l).map a).prod * ((sumRightList l).map b).prod := by
  induction l with
  | nil => simp [sumLeftList, sumRightList]
  | cons x l ih =>
    cases x <;> simp [sumLeftList, sumRightList] at ih ⊢
    all_goals rw [ih]; ring

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem sumList_operator_prod {I J : Type*}
    (a : I → H →L[ℂ] H) (b : J → K →L[ℂ] K) (l : List (I ⊕ J)) :
    (l.map (Sum.elim (fun i => spatialLeft (K := K) (a i))
      (fun j => spatialRight (H := H) (b j)))).prod =
      spatialTensorOp (((sumLeftList l).map a).prod) (((sumRightList l).map b).prod) := by
  induction l with
  | nil => simpa [sumLeftList, sumRightList] using Pureness.spatialTensorOp_one.symm
  | cons x l ih =>
    cases x with
    | inl i =>
      simp only [List.map_cons, List.prod_cons, Sum.elim_inl]
      rw [ih]
      change spatialTensorOp (a i) 1 * spatialTensorOp _ _ = spatialTensorOp _ _
      rw [← spatialTensorOp_mul]
      simp [sumLeftList, sumRightList]
    | inr j =>
      simp only [List.map_cons, List.prod_cons, Sum.elim_inr]
      rw [ih]
      change spatialTensorOp 1 (b j) * spatialTensorOp _ _ = spatialTensorOp _ _
      rw [← spatialTensorOp_mul]
      simp [sumLeftList, sumRightList]

/-- Separation in each tensor leg implies separation of the product
vector, without requiring supplied modular conjugations. -/
theorem separating_spatialProduct_vector_of_separating
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (Ω : H) (ξ : K)
    (hM : Function.Injective (algebraVectorMap M Ω))
    (hN : Function.Injective (algebraVectorMap N ξ)) :
    Function.Injective (algebraVectorMap (spatialProductAlgebra M N) (tensorVector ξ Ω)) := by
  have hcM : DenseRange (algebraVectorMap M.commutant Ω) := by
    apply Generator.commutant_orbit_dense M Ω
    intro a ha
    apply hM
    change a.val Ω = (0 : H →L[ℂ] H) Ω
    simpa only [zero_apply] using ha
  have hcN : DenseRange (algebraVectorMap N.commutant ξ) := by
    apply Generator.commutant_orbit_dense N ξ
    intro a ha
    apply hN
    change a.val ξ = (0 : K →L[ℂ] K) ξ
    simpa only [zero_apply] using ha
  have hsmall := denseRange_spatialProduct_vector M.commutant N.commutant Ω ξ hcM hcN
  have hlarge : DenseRange (algebraVectorMap (spatialProductAlgebra M N).commutant
      (tensorVector ξ Ω)) := by
    apply Dense.mono _ hsmall
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a.val, spatialProduct_commutants_le M N a.property⟩, rfl⟩
  intro a b hab
  apply Subtype.ext
  apply operator_eq_of_mem_commutant_of_eq_on_cyclicVector
    (spatialProductAlgebra M N).commutant (tensorVector ξ Ω) hlarge a.val b.val
  · rw [VonNeumannAlgebra.commutant_commutant]
    exact a.property
  · rw [VonNeumannAlgebra.commutant_commutant]
    exact b.property
  · exact hab

namespace PointedMatrixSites

variable {I J : Type*} {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  {Ω : H} {ξ : K} {ν : I → ℝ} {η : J → ℝ}

/-- The actual site family on the two tensor legs. -/
def sumSite (S : PointedMatrixSites M Ω ν) (T : PointedMatrixSites N ξ η) :
    I ⊕ J → MatrixUnitSystem (Fin 2) (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  Sum.elim (fun i => (S.site i).map (spatialLeft (K := K)))
    (fun j => (T.site j).map (spatialRight (H := H)))

private theorem site_mem (S : PointedMatrixSites M Ω ν) (i : I) (a b : Fin 2) :
    (S.site i).entry a b ∈ M := by
  apply Eq.mpr (congrArg (fun P : VonNeumannAlgebra H => (S.site i).entry a b ∈ P) S.generates)
  exact subset_generatedVonNeumannAlgebra _
    ((le_iSup (fun i => (S.site i).algebra) i) ((S.site i).entry_mem a b))

private theorem sumSite_generates (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) :
    spatialProductAlgebra M N = generatedVonNeumannAlgebra (⨆ i, (S.sumSite T i).algebra) := by
  let Q := generatedVonNeumannAlgebra (⨆ i, (S.sumSite T i).algebra)
  have hentry (i : I ⊕ J) (a b : Fin 2) : (S.sumSite T i).entry a b ∈ Q :=
    subset_generatedVonNeumannAlgebra _
      ((le_iSup (fun i => (S.sumSite T i).algebra) i) ((S.sumSite T i).entry_mem a b))
  have hleft : ∀ x ∈ M, spatialLeft (K := K) x ∈ Q := by
    intro x hx
    rw [S.generates] at hx
    apply spatialLeft_mem_of_generated publishedKaplanskyDensity _ Q _ hx
    have hle : (⨆ i, (S.site i).algebra) ≤ Q.toStarSubalgebra.comap (spatialLeft (K := K)) := by
      apply iSup_le
      intro i
      apply ((S.site i).algebra_le_iff _).mpr
      intro a b
      exact hentry (.inl i) a b
    exact fun _ h => hle h
  have hright : ∀ x ∈ N, spatialRight (H := H) x ∈ Q := by
    intro x hx
    rw [T.generates] at hx
    apply spatialRight_mem_of_generated publishedKaplanskyDensity _ Q _ hx
    have hle : (⨆ i, (T.site i).algebra) ≤ Q.toStarSubalgebra.comap (spatialRight (H := H)) := by
      apply iSup_le
      intro i
      apply ((T.site i).algebra_le_iff _).mpr
      intro a b
      exact hentry (.inr i) a b
    exact fun _ h => hle h
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    apply sup_le
    · rintro x ⟨a, ha, rfl⟩
      exact hleft a ha
    · rintro x ⟨a, ha, rfl⟩
      exact hright a ha
  · apply generatedVonNeumannAlgebra_le_of_le
    apply iSup_le
    intro i
    apply ((S.sumSite T i).algebra_le_iff _).mpr
    intro a b
    cases i with
    | inl i => exact spatialLeft_mem_product M N (S.site_mem i a b)
    | inr j => exact spatialRight_mem_product M N (T.site_mem j a b)

private theorem sumSite_moments (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (l : List (I ⊕ J)) (hl : l.Nodup)
    (r c : I ⊕ J → Fin 2) :
    inner ℂ (tensorVector ξ Ω)
      (((l.map fun i => (S.sumSite T i).entry (r i) (c i)).prod) (tensorVector ξ Ω)) =
      (l.map fun i => if r i = c i then (twoSiteWeight (Sum.elim ν η i) (r i) : ℂ) else 0).prod := by
  let a : I → H →L[ℂ] H := fun i => (S.site i).entry (r (.inl i)) (c (.inl i))
  let b : J → K →L[ℂ] K := fun j => (T.site j).entry (r (.inr j)) (c (.inr j))
  have hword : (l.map fun i => (S.sumSite T i).entry (r i) (c i)).prod =
      spatialTensorOp (((sumLeftList l).map a).prod) (((sumRightList l).map b).prod) := by
    convert sumList_operator_prod a b l using 1
    congr 2
    funext i
    cases i <;> rfl
  rw [hword]
  have hstate (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
      inner ℂ (tensorVector ξ Ω) (spatialTensorOp A B (tensorVector ξ Ω)) =
        inner ℂ Ω (A Ω) * inner ℂ ξ (B ξ) := by
    simp only [tensorVector_apply, spatialTensorOp_coe, TensorProduct.mapL_tmul,
      UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]
  rw [hstate, S.moments (sumLeftList l) (sumLeftList_nodup hl),
    T.moments (sumRightList l) (sumRightList_nodup hl)]
  symm
  convert sumList_scalar_prod
    (fun i => if r (.inl i) = c (.inl i) then (twoSiteWeight (ν i) (r (.inl i)) : ℂ) else 0)
    (fun j => if r (.inr j) = c (.inr j) then (twoSiteWeight (η j) (r (.inr j)) : ℂ) else 0) l using 1
  congr 2
  funext i
  cases i <;> rfl

/-- Tensoring two pointed systems constructs their sum-indexed system. -/
def sum (S : PointedMatrixSites M Ω ν) (T : PointedMatrixSites N ξ η) :
    PointedMatrixSites (spatialProductAlgebra M N) (tensorVector ξ Ω) (Sum.elim ν η) where
  valid i := by cases i with | inl i => exact S.valid i | inr j => exact T.valid j
  site := S.sumSite T
  commuting i j hij a b c d := by
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change spatialLeft (K := K) ((S.site i).entry a b) * spatialLeft ((S.site j).entry c d) =
          spatialLeft ((S.site j).entry c d) * spatialLeft ((S.site i).entry a b)
        rw [← map_mul, ← map_mul, (S.commuting i j (fun h => hij (congrArg Sum.inl h)) a b c d).eq]
      | inr j =>
        change spatialTensorOp ((S.site i).entry a b) 1 * spatialTensorOp 1 ((T.site j).entry c d) =
          spatialTensorOp 1 ((T.site j).entry c d) * spatialTensorOp ((S.site i).entry a b) 1
        rw [← spatialTensorOp_mul, ← spatialTensorOp_mul]
        simp only [mul_one, one_mul]
    | inr i =>
      cases j with
      | inl j =>
        change spatialTensorOp 1 ((T.site i).entry a b) * spatialTensorOp ((S.site j).entry c d) 1 =
          spatialTensorOp ((S.site j).entry c d) 1 * spatialTensorOp 1 ((T.site i).entry a b)
        rw [← spatialTensorOp_mul, ← spatialTensorOp_mul]
        simp only [mul_one, one_mul]
      | inr j =>
        change spatialRight (H := H) ((T.site i).entry a b) * spatialRight ((T.site j).entry c d) =
          spatialRight ((T.site j).entry c d) * spatialRight ((T.site i).entry a b)
        rw [← map_mul, ← map_mul, (T.commuting i j (fun h => hij (congrArg Sum.inr h)) a b c d).eq]
  generates := S.sumSite_generates T
  unit_vector := by rw [norm_tensorVector_apply, S.unit_vector, T.unit_vector, one_mul]
  cyclic := denseRange_spatialProduct_vector M N Ω ξ S.cyclic T.cyclic
  separating := separating_spatialProduct_vector_of_separating M N Ω ξ S.separating T.separating
  moments := S.sumSite_moments T

end PointedMatrixSites

/-- The sum clause of the pointed-product input is an actual construction. -/
theorem pointedMatrixSites_sum {I J : Type*} {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    {Ω : H} {ξ : K} {ν : I → ℝ} {η : J → ℝ}
    (S : PointedMatrixSites M Ω ν) (T : PointedMatrixSites N ξ η) :
    Nonempty (PointedMatrixSites (spatialProductAlgebra M N) (tensorVector ξ Ω) (Sum.elim ν η)) :=
  ⟨S.sum T⟩

end

end KadisonKastler

end OAI
