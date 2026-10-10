import OAI.Analysis.TracialSplitting.CoefficientBounds

namespace OAI

universe uE uF


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open UniformSpace.Completion UnitalTomsWinter

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open Pureness UnitalTomsWinter

noncomputable section

open scoped Pointwise

noncomputable section

open scoped ComplexOrder

noncomputable section

open scoped ComplexOrder

namespace NuclearTrace

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

def coefficientSelfAdjMap (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (k : Fin n → K) (a : Fin n → A) : selfAdjoint A →ₗ[ℝ] selfAdjoint A where
  toFun x := ⟨coefficientMap α k a x,coefficientMap_selfAdjoint α k a _ x.property⟩
  map_add' left right := Subtype.ext ((coefficientMap α k a).map_add left right)
  map_smul' scalar value :=
    Subtype.ext ((coefficientMap α k a).map_smul_of_tower scalar (value : A))

def coefficientCone (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ConvexCone ℝ (selfAdjoint A →ₗ[ℝ] selfAdjoint A) :=
  ConvexCone.hull ℝ {L | ∃ (n : ℕ) (k : Fin n → K) (a : Fin n → A),
    L = coefficientSelfAdjMap α k a}

omit [PartialOrder A] [StarOrderedRing A] in
lemma coefficientCone_zero (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    (0 : selfAdjoint A →ₗ[ℝ] selfAdjoint A) ∈ coefficientCone α := by
  apply ConvexCone.subset_hull
  refine ⟨0,Fin.elim0,Fin.elim0,?_⟩
  ext x
  simp [coefficientSelfAdjMap,coefficientMap]

def evalTuple (x : I → selfAdjoint A) :
    (selfAdjoint A →ₗ[ℝ] selfAdjoint A) →ₗ[ℝ] (I → selfAdjoint A) where
  toFun L i := L (x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tracialTupleSeminorm (τ : Pureness.TracialState A) :
    Seminorm ℝ (I → selfAdjoint A) :=
  ∑ i, (CurrentMain.tracialOneSeminorm τ).comp (LinearMap.proj i)

@[simp] lemma tracialTupleSeminorm_apply (τ : Pureness.TracialState A)
    (x : I → selfAdjoint A) :
    tracialTupleSeminorm τ x = ∑ i, CurrentMain.traceOneNorm τ (x i) := by
  simp [tracialTupleSeminorm]

lemma tracialTupleSeminorm_continuous (τ : Pureness.TracialState A) :
    Continuous (tracialTupleSeminorm (I := I) τ) := by
  simp only [funext (tracialTupleSeminorm_apply (I := I) τ)]
  apply continuous_finsetSum
  intro i _
  exact (CurrentMain.tracialOneSeminorm_continuous τ).comp (continuous_apply i)

lemma tracialTupleSeminorm_single [DecidableEq I] (τ : Pureness.TracialState A)
    (i : I) (a : selfAdjoint A) :
    tracialTupleSeminorm τ (Pi.single i a) = CurrentMain.tracialOneSeminorm τ a := by
  simp [tracialTupleSeminorm_apply,Pi.single_apply,apply_ite,CurrentMain.traceOneNorm]

theorem nuclear_tracial_coefficient_approximation (hA : Pureness.IsNuclear.{0,0} A)
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hα : Function.Injective α)
    (τ : Pureness.TracialState A) (x : I → selfAdjoint A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L ∈ coefficientCone α,
      ∑ i, CurrentMain.traceOneNorm τ ((x i : A) - L (x i)) < ε := by
  classical
  let C := (coefficientCone α).map (evalTuple x)
  have h0 : (0 : I → selfAdjoint A) ∈ C := by
    exact ⟨0,coefficientCone_zero α,by ext i; rfl⟩
  have hs : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ C, t • s ∈ C := by
    intro t ht s hs
    obtain rfl | ht := ht.eq_or_lt
    · simpa using h0
    · exact C.smul_mem ht hs
  have hdual (f : (I → selfAdjoint A) →L[ℝ] ℝ)
      (hf : ∃ c : ℝ, 0 ≤ c ∧ ∀ y, |f y| ≤ c * tracialTupleSeminorm τ y)
      (hfc : ∀ s ∈ C, f s ≤ 0) : f x ≤ 0 := by
    obtain ⟨c,hc,hf⟩ := hf
    let l (i : I) : selfAdjoint A →ₗ[ℝ] ℝ :=
      f.toLinearMap.comp (LinearMap.single ℝ (fun _ : I => selfAdjoint A) i)
    have hl (i : I) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
        |l i a| ≤ c * (τ.functional a).re := by
      have hh := hf (Pi.single i a)
      rw [tracialTupleSeminorm_single,CurrentMain.tracialOneSeminorm_of_nonneg τ a ha] at hh
      exact hh
    have he (y : I → selfAdjoint A) : (∑ i, l i (y i)) = f y := by
      change (∑ i, f (Pi.single i (y i))) = f y
      rw [← map_sum]
      congr 1
      exact Finset.univ_sum_single y
    rw [← he x]
    apply nuclear_coefficient_dual_bound hA α hα τ.functional τ.normalized x l hc hl
    intro n k a
    rw [he]
    apply hfc
    refine ⟨coefficientSelfAdjMap α k a,?_,rfl⟩
    exact ConvexCone.subset_hull ⟨n,k,a,rfl⟩
  obtain ⟨s,hs,hclose⟩ := seminorm_cone_approximation_of_dual
    (tracialTupleSeminorm τ) (tracialTupleSeminorm_continuous τ)
    C C.convex h0 hs x hdual hε
  obtain ⟨L,hL,rfl⟩ := hs
  refine ⟨L,hL,?_⟩
  simpa only [tracialTupleSeminorm_apply,Pi.sub_apply,evalTuple,
    LinearMap.coe_mk,AddHom.coe_mk,(selfAdjoint A).coe_sub] using hclose

end NuclearTrace

noncomputable section

namespace NuclearTrace

open Set

variable {E : Type uE} {F : Type uF}

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

theorem compact_convex_uniform_cost {X : Set E} {Y : Set F}
    (hXne : X.Nonempty) (hX : IsCompact X) (hXconv : Convex ℝ X)
    (hYconv : Convex ℝ Y) (c : E → F → ℝ)
    (hcX : ∀ y ∈ Y, Continuous (fun x => c x y))
    (hcXconc : ∀ y ∈ Y, ConcaveOn ℝ X (fun x => c x y))
    (hcY : ∀ x ∈ X, ContinuousOn (c x) Y)
    (hcYconv : ∀ x ∈ X, ConvexOn ℝ Y (c x))
    {ε : ℝ} (hpoint : ∀ x ∈ X, ∃ y ∈ Y, c x y < ε) :
    ∃ y ∈ Y, ∀ x ∈ X, c x y < ε := by
  classical
  let U (y : Y) : Set E := {x | c x y < ε}
  have hUopen (y : Y) : IsOpen (U y) := (hcX y y.property).isOpen_preimage _ isOpen_Iio
  have hcover : X ⊆ ⋃ y : Y, U y := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hpoint x hx
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hxy⟩
  obtain ⟨s,hs⟩ := hX.elim_finite_subcover U hUopen hcover
  have hfinitePoint : ∀ x ∈ X, ∃ y ∈ Subtype.val '' (s : Set Y), -ε < -c x y := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact ⟨y,⟨y,hy,rfl⟩,neg_lt_neg hxy⟩
  obtain ⟨y,hy,hyall⟩ := Sion.exists_lt_iInf_of_lt_iInf_of_finite
    (f := fun x y => -c x y) hXne hX
    (fun y hy => (hcX y hy).neg.continuousOn.lowerSemicontinuousOn)
    (fun y hy => (hcXconc y hy).neg.quasiconvexOn)
    hYconv
    (fun x hx => (hcY x hx).neg.upperSemicontinuousOn)
    (fun x hx => (hcYconv x hx).neg.quasiconcaveOn)
    hXconv (s.finite_toSet.image Subtype.val)
    (fun _ hy => by obtain ⟨y,_,rfl⟩ := hy; exact y.property) hfinitePoint
  exact ⟨y,hy,fun x hx => neg_lt_neg_iff.mp (hyall x hx)⟩

end NuclearTrace

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end OAI
