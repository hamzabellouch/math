import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.AffineCurves

namespace OAI

/-! Exceptional Fibers. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {X : Scheme.{u}} [IsIntegral X]

theorem smooth_proper_curve_through_point_avoiding
    (sX : X ⟶ Spec (.of k)) [IsProper sX]
    (x : X) (hx : IsClosed {x}) (Z : Set X) (hZ : IsClosed Z)
    (hne : Z ≠ Set.univ) (hxZ : x ∈ Z) :
    ∃ (N : Scheme.{u}) (i : N ⟶ X), IsIntegral N ∧ Nontrivial N ∧
      SmoothOfRelativeDimension 1 (i ≫ sX) ∧ IsProper (i ≫ sX) ∧
      x ∈ Set.range i ∧ ¬ Set.range i ⊆ Z := by
  obtain ⟨C,j,hj,hI,hN,hD,hxC,hCZ⟩ := closed_curve_through_point_avoiding sX x hx Z hZ hne hxZ
  have := hj
  have := hI
  have := hN
  let sC := j ≫ sX
  have : IsProper sC := inferInstance
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated sC
  let f := C.fromSpecStalk (genericPoint C)
  let N := f.normalization
  let ν : N ⟶ C := f.fromNormalization
  have hNi : IsIntegral N := integral_genericNormalization
  have hsurj : Surjective ν := surjective_genericNormalization
  have hNt : Nontrivial N := ν.surjective.nontrivial
  have hsm : SmoothOfRelativeDimension 1 (ν ≫ sC) := smooth_genericNormalization sC hD
  have hpr : IsProper (ν ≫ sC) := proper_genericNormalization sC
  refine ⟨N,ν ≫ j,hNi,hNt,?_,?_,?_,?_⟩
  · simpa only [Category.assoc] using hsm
  · simpa only [Category.assoc] using hpr
  · obtain ⟨c,hc⟩ := hxC
    obtain ⟨n,hn⟩ := ν.surjective c
    exact ⟨n,by simpa only [Scheme.Hom.comp_apply,hn] using hc⟩
  · intro hsub
    apply hCZ
    rintro _ ⟨c,rfl⟩
    obtain ⟨n,hn⟩ := ν.surjective c
    exact hsub ⟨n,by simp only [Scheme.Hom.comp_apply,hn]⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

theorem dominant_of_nonconstant_to_curve {C Y : Scheme.{u}} [IsIntegral C]
    [IsIntegral Y] (f : C ⟶ Y) (hd : ∀ y : Y, Order.coheight y ≤ 1)
    (hn : ∃ a b : C, f a ≠ f b) : IsDominant f := by
  have hg : f (genericPoint C) = genericPoint Y := by
    by_contra hne
    have hc := isClosed_point_of_curve_coheight hd hne
    have heq (c : C) : f c = f (genericPoint C) := by
      have hs := (genericPoint_specializes c).map f.continuous
      have hm := specializes_iff_mem_closure.mp hs
      rwa [hc.closure_eq, Set.mem_singleton_iff] at hm
    obtain ⟨a,b,hab⟩ := hn
    exact hab ((heq a).trans (heq b).symm)
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← genericPoint_spec Y]
  apply closure_mono
  rintro y rfl
  exact ⟨genericPoint C,hg⟩

theorem finite_dominant_of_nonconstant_smooth_curve
    {k : Type u} [Field k] {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    [NoetherianSpace C] (sC : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 sC]
    (f : C ⟶ Y) [IsProper f] (hd : ∀ y : Y, Order.coheight y ≤ 1)
    (hn : ∃ a b : C, f a ≠ f b) : IsFinite f ∧ IsDominant f := by
  have : IsDominant f := dominant_of_nonconstant_to_curve f hd hn
  have : Nontrivial Y := by
    obtain ⟨a,b,hab⟩ := hn
    exact ⟨⟨f a,f b,hab⟩⟩
  exact ⟨finite_of_proper_dominant_from_smooth_curve sC f,inferInstance⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {A C : Scheme.{u}} [IsIntegral A] [IsIntegral C] [Nontrivial C]

theorem finite_curve_through_point
    (sA : A ⟶ Spec (.of k)) [IsProper sA]
    (sC : C ⟶ Spec (.of k)) [IsSeparated sC]
    (f : A ⟶ C) [Surjective f] (hover : f ≫ sC = sA)
    (hd : ∀ c : C, Order.coheight c ≤ 1)
    (z : A) (hz : IsClosed {z}) (hfx : IsClosed {f z}) :
    ∃ (N : Scheme.{u}) (i : N ⟶ A), IsIntegral N ∧ Nontrivial N ∧
      SmoothOfRelativeDimension 1 (i ≫ sA) ∧ IsProper (i ≫ sA) ∧
      z ∈ Set.range i ∧ IsFinite (i ≫ f) ∧ IsDominant (i ≫ f) := by
  let Z : Set A := f ⁻¹' {f z}
  have hZ : IsClosed Z := hfx.preimage f.continuous
  have hne : Z ≠ Set.univ := by
    intro heq
    obtain ⟨c,hc⟩ := exists_ne (f z)
    obtain ⟨a,ha⟩ := f.surjective c
    have : a ∈ Z := heq.symm ▸ Set.mem_univ a
    exact hc (ha.symm.trans this)
  obtain ⟨N,i,hI,hN,hsm,hpr,hzi,hnZ⟩ :=
    smooth_proper_curve_through_point_avoiding sA z hz Z hZ hne rfl
  have := hI
  have := hN
  have := hsm
  have := hpr
  have : IsNoetherian N := {
    __ := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sA)
    __ := QuasiCompact.compactSpace_of_compactSpace (i ≫ sA) }
  have : IsProper ((i ≫ f) ≫ sC) := by
    rw [Category.assoc,hover]
    infer_instance
  have : IsProper (i ≫ f) := IsProper.of_comp (i ≫ f) sC
  have hn : ∃ a b : N, (i ≫ f) a ≠ (i ≫ f) b := by
    obtain ⟨a,ha⟩ := hzi
    have hnot : ∃ b : N, i b ∉ Z := by
      by_contra! h
      exact hnZ (by rintro y ⟨b,rfl⟩; exact h b)
    obtain ⟨b,hb⟩ := hnot
    refine ⟨a,b,?_⟩
    intro heq
    apply hb
    change f (i b) = f z
    exact heq.symm.trans (congrArg f ha)
  obtain ⟨hfin,hdom⟩ := finite_dominant_of_nonconstant_smooth_curve (i ≫ sA) (i ≫ f) hd hn
  exact ⟨N,i,hI,hN,hsm,hpr,hzi,hfin,hdom⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {A C : Scheme} [IsIntegral A] [IsIntegral C] [Nontrivial C]

theorem projective_finite_curve_through_point
    (sA : A ⟶ Spec (.of ℂ)) [IsProper sA]
    (sC : C ⟶ Spec (.of ℂ)) [IsSeparated sC]
    (f : A ⟶ C) [Surjective f] (hover : f ≫ sC = sA)
    (hd : ∀ c : C, Order.coheight c ≤ 1)
    (z : A) (hz : IsClosed {z}) (hfx : IsClosed {f z}) :
    ∃ (N : ComplexProjectiveVariety) (i : N.scheme ⟶ A),
      IsSmoothNfold N 1 ∧ i ≫ sA = N.structureMap ∧
      z ∈ Set.range i ∧ IsFinite (i ≫ f) ∧ IsDominant (i ≫ f) := by
  obtain ⟨N,i,hI,_,hsm,hpr,hzi,hfin,hdom⟩ :=
    finite_curve_through_point sA sC f hover hd z hz hfx
  have := hI
  have := hsm
  have := hpr
  let NC : ComplexProjectiveVariety := {
    scheme := N
    structureMap := i ≫ sA
    integral := hI
    connected := inferInstance
    projective := exists_closedImmersion_of_smooth_proper_curve (i ≫ sA) }
  exact ⟨NC,i,hsm,rfl,hzi,hfin,hdom⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem positive_curve_in_closed_subvariety
    (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    (D : cartierDivisors (X := X.scheme)) (heff : ∀ p, 0 ≤ D.1 p)
    {T : Scheme} [IsIntegral T] (i : T ⟶ X.scheme) [IsClosedImmersion i]
    (hmeet : (Set.range i ∩ divisorSupport D.1).Nonempty)
    (hnot : ¬ Set.range i ⊆ divisorSupport D.1) :
    ∃ C : CurveOn X, Set.range C.morphism ⊆ Set.range i ∧
      0 < cartierCurveDegree D C := by
  let sT := i ≫ X.structureMap
  have : IsProper sT := inferInstance
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  let Z : Set T := i ⁻¹' divisorSupport D.1
  have hZ : IsClosed Z := (isClosed_divisorSupport D.1).preimage i.continuous
  have hZn : Z.Nonempty := by
    obtain ⟨_,⟨t,rfl⟩,ht⟩ := hmeet
    exact ⟨t,ht⟩
  obtain ⟨x,hxZ,hx⟩ := hZ.exists_closed_singleton hZn
  have hZu : Z ≠ Set.univ := by
    intro heq
    apply hnot
    rintro _ ⟨t,rfl⟩
    change t ∈ Z
    rw [heq]
    exact Set.mem_univ t
  obtain ⟨N,j,hI,_,hsm,hpr,hxj,hjZ⟩ :=
    smooth_proper_curve_through_point_avoiding sT x hx Z hZ hZu hxZ
  have := hI
  have := hsm
  have := hpr
  let NC : ComplexProjectiveVariety := {
    scheme := N
    structureMap := j ≫ sT
    integral := hI
    connected := inferInstance
    projective := exists_closedImmersion_of_smooth_proper_curve (j ≫ sT) }
  let C : CurveOn X := {
    curve := NC
    smooth := hsm
    morphism := j ≫ i
    overComplex := Category.assoc _ _ _ }
  have hη : C.morphism (genericPoint N) ∉ divisorSupport D.1 := by
    intro hm
    apply hjZ
    rintro _ ⟨u,rfl⟩
    exact ((genericPoint_specializes u).map j.continuous).mem_closed hZ hm
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace (j ≫ sT)
  have hpre : (j ⁻¹' {x}).Nonempty := by
    obtain ⟨u,hu⟩ := hxj
    exact ⟨u,hu⟩
  obtain ⟨u,hu,huc⟩ := (hx.preimage j.continuous).exists_closed_singleton hpre
  let p : PrimeDivisor N := ⟨u,coheight_eq_of_smooth_closed (j ≫ sT) 1 u huc⟩
  refine ⟨C,?_,cartierCurveDegree_positive_of_effective_meeting D C heff hη p ?_⟩
  · rintro _ ⟨v,rfl⟩
    exact ⟨j v,rfl⟩
  · change i (j u) ∈ divisorSupport D.1
    rw [show j u = x from hu]
    exact hxZ
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

theorem height_eq_of_closedImmersion {X Y : Scheme} (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) : Order.height x = Order.height (f x) := by
  have hle (a b : X) : f a ≤ f b ↔ a ≤ b :=
    f.isEmbedding.isInducing.specializes_iff
  have hlt (a b : X) : f a < f b ↔ a < b := by
    simp only [lt_iff_le_not_ge, hle]
  apply Order.height_eq_of_strictMono f (fun a b h => (hlt a b).mpr h)
  intro a b h
  have hb : b ∈ Set.range f :=
    (show f a ⤳ b from h.le).mem_closed
      f.isClosedEmbedding.isClosed_range (Set.mem_range_self a)
  obtain ⟨a',rfl⟩ := hb
  exact ⟨a',(hlt a' a).mp h,rfl⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

theorem integral_closed_closure (X : Scheme) (q : X) :
    ∃ (T : Scheme) (i : T ⟶ X), IsIntegral T ∧ IsClosedImmersion i ∧
      Set.range i = closure {q} ∧
      ∃ t : T, i t = q ∧ Order.height t = Order.height q := by
  let f := X.fromSpecResidueField q
  have : QuasiCompact f := quasiCompact_of_noetherianSpace_source f
  have hI := integral_image f
  have hr : Set.range f.imageι = closure {q} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
    rw [Scheme.range_fromSpecResidueField]
  obtain ⟨t,ht⟩ : q ∈ Set.range f.imageι := by
    rw [hr]
    exact subset_closure (Set.mem_singleton q)
  refine ⟨f.image,f.imageι,hI,inferInstance,hr,t,ht,?_⟩
  simpa only [ht] using height_eq_of_closedImmersion f.imageι t
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem effective_antinef_irreducible_dichotomy
    (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    (D : cartierDivisors (X := X.scheme)) (heff : ∀ p, 0 ≤ D.1 p)
    {Y : Scheme} (f : X.scheme ⟶ Y)
    (hanti : ∀ C : CurveOn X, (∃ y, ∀ c, f (C.morphism c) = y) →
      cartierCurveDegree D C ≤ 0)
    {Z : Set X.scheme} (hZ : IsClosed Z) (hI : IsIrreducible Z)
    (hconst : ∃ y, ∀ z ∈ Z, f z = y) :
    Z ⊆ divisorSupport D.1 ∨ Disjoint Z (divisorSupport D.1) := by
  classical
  by_cases hsub : Z ⊆ divisorSupport D.1
  · exact Or.inl hsub
  right
  by_contra hdisj
  have hmeet : (Z ∩ divisorSupport D.1).Nonempty :=
    Set.not_disjoint_iff_nonempty_inter.mp hdisj
  obtain ⟨T,i,hT,hi,hr,_⟩ := integral_closed_closure X.scheme hI.genericPoint
  have := hT
  have := hi
  have hir : Set.range i = Z := hr.trans (hI.closure_genericPoint hZ)
  obtain ⟨C,hC,hCpos⟩ := positive_curve_in_closed_subvariety X D heff i
    (hir.symm ▸ hmeet) (hir.symm ▸ hsub)
  obtain ⟨y,hy⟩ := hconst
  have hCnonpos := hanti C ⟨y,fun c => hy (C.morphism c)
    (hir ▸ hC (Set.mem_range_self c))⟩
  exact (not_lt_of_ge hCnonpos) hCpos
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open TopologicalSpace

theorem connected_closed_dichotomy_of_irreducible
    {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    {F A : Set α} (hF : IsClosed F) (hFc : IsPreconnected F) (hA : IsClosed A)
    (hcomp : ∀ Z, IsClosed Z → IsIrreducible Z → Z ⊆ F →
      Z ⊆ A ∨ Disjoint Z A) : F ⊆ A ∨ Disjoint F A := by
  classical
  obtain ⟨S,hSf,hSc,hSi,hFS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  let S' : Set (Set α) := {T | T ∈ S ∧ Disjoint T A}
  let B := ⋃₀ S'
  have hS'f : S'.Finite := hSf.subset (fun _ h => h.1)
  have hBc : IsClosed B := by
    rw [show B = ⋃ T ∈ S', T from Set.sUnion_eq_biUnion]
    exact hS'f.isClosed_biUnion fun T hT => hSc T hT.1
  have hBd : Disjoint B A := by
    apply Set.disjoint_left.mpr
    rintro x ⟨T,hT,hxT⟩ hxA
    exact Set.disjoint_left.mp hT.2 hxT hxA
  have hcov : F ⊆ A ∪ B := by
    intro x hx
    obtain ⟨T,hT,hxT⟩ := Set.mem_sUnion.mp (hFS ▸ hx)
    have hTF : T ⊆ F := by
      intro y hy
      rw [hFS]
      exact Set.mem_sUnion.mpr ⟨T,hT,hy⟩
    rcases hcomp T (hSc T hT) (hSi T hT) hTF with hTA | hTA
    · exact Or.inl (hTA hxT)
    · exact Or.inr (Set.mem_sUnion.mpr ⟨T,⟨hT,hTA⟩,hxT⟩)
  by_cases hFA : Disjoint F A
  · exact Or.inr hFA
  left
  intro x hx
  by_contra hxA
  have hxB := (hcov hx).resolve_left hxA
  obtain ⟨y,_,hyA,hyB⟩ := isPreconnected_closed_iff.mp hFc A B hA hBc hcov
    (Set.not_disjoint_iff_nonempty_inter.mp hFA) ⟨x,hx,hxB⟩
  exact Set.disjoint_left.mp hBd hyB hyA
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem effective_antinef_connected_fiber
    (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    (D : cartierDivisors (X := X.scheme)) (heff : ∀ p, 0 ≤ D.1 p)
    {Y : Scheme} (f : X.scheme ⟶ Y)
    (hanti : ∀ C : CurveOn X, (∃ y, ∀ c, f (C.morphism c) = y) →
      cartierCurveDegree D C ≤ 0)
    (y : Y) (hy : IsClosed {y}) (hcon : _root_.IsPreconnected (f ⁻¹' {y})) :
    f ⁻¹' {y} ⊆ divisorSupport D.1 ∨ Disjoint (f ⁻¹' {y}) (divisorSupport D.1) := by
  have : IsNoetherian X.scheme := ⟨⟩
  apply connected_closed_dichotomy_of_irreducible (hy.preimage f.continuous) hcon
    (isClosed_divisorSupport D.1)
  intro Z hZ hI hZF
  exact effective_antinef_irreducible_dichotomy X D heff f hanti hZ hI
    ⟨y,fun z hz => hZF hz⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

def qDivisorSupport {X : Scheme} (D : QWeilDivisor X) : Set X :=
  ⋃ p ∈ D.support, closure ({p.1} : Set X)
lemma CartierMultiple.support_eq {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {D : QWeilDivisor X} (M : CartierMultiple D) : M.divisor.1.support = D.support := by
  ext p
  rw [Finsupp.mem_support_iff,Finsupp.mem_support_iff]
  have he : (M.denominator : ℚ) * D p = (M.divisor.1 p : ℚ) :=
    DFunLike.congr_fun M.equation p
  have hm : (M.denominator : ℚ) ≠ 0 := by exact_mod_cast M.positive.ne'
  apply not_congr
  constructor
  · intro hz
    rw [hz,Int.cast_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hm
  · intro hz
    have he' : (M.divisor.1 p : ℚ) = 0 := by rw [← he,hz,mul_zero]
    exact_mod_cast he'
lemma CartierMultiple.divisorSupport_eq {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {D : QWeilDivisor X} (M : CartierMultiple D) :
    divisorSupport M.divisor.1 = qDivisorSupport D := by
  unfold divisorSupport qDivisorSupport
  rw [M.support_eq]
lemma CartierMultiple.coeff_nonneg_iff {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {D : QWeilDivisor X} (M : CartierMultiple D) (p : PrimeDivisor X) :
    0 ≤ M.divisor.1 p ↔ 0 ≤ D p := by
  have he : (M.denominator : ℚ) * D p = (M.divisor.1 p : ℚ) :=
    DFunLike.congr_fun M.equation p
  have hm : (0 : ℚ) < M.denominator := by exact_mod_cast M.positive
  constructor
  · intro h
    have h' : (0 : ℚ) ≤ M.divisor.1 p := by exact_mod_cast h
    rw [← he] at h'
    exact nonneg_of_mul_nonneg_right h' hm
  · intro h
    have h' := mul_nonneg hm.le h
    rw [he] at h'
    exact_mod_cast h'
lemma CartierMultiple.degree_nonpos_of_qDegree_nonpos
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    {D : QWeilDivisor X.scheme} (hD : IsQCartierDivisor D) (M : CartierMultiple D)
    (C : CurveOn X) (hC : qCartierCurveDegree D hD C ≤ 0) :
    cartierCurveDegree M.divisor C ≤ 0 := by
  rw [qCartierCurveDegree_eq_multiple _ M] at hC
  change (cartierCurveDegree M.divisor C : ℚ) / M.denominator ≤ 0 at hC
  by_contra hn
  have hd : (0 : ℚ) < cartierCurveDegree M.divisor C := by exact_mod_cast lt_of_not_ge hn
  have hm : (0 : ℚ) < M.denominator := by exact_mod_cast M.positive
  exact (not_lt_of_ge hC) (div_pos hd hm)

theorem qSurface_negativity_of_antinef
    (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    (hX : IsSmoothNfold X 2)
    {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X.scheme ⟶ Y) [IsDominant f] [IsProper f] (hf : IsBirationalMorphism f)
    (D : QWeilDivisor X.scheme) (hD : IsQCartierDivisor D)
    (hexc : ∀ p ∈ D.support, ∀ x ∈ closure ({p.1} : Set X.scheme), f x = f p.1)
    (hanti : ∀ C : CurveOn X, (∃ y, ∀ c, f (C.morphism c) = y) → qCartierCurveDegree D hD C ≤ 0) :
    0 ≤ D := by
  let : SmoothOfRelativeDimension 2 X.structureMap := hX
  let M := chooseCartierMultiple hD
  have hex : ∀ p ∈ M.divisor.1.support, ∀ x ∈ closure ({p.1} : Set X.scheme), f x = f p.1 := by
    rw [M.support_eq]
    exact hexc
  have hpos := surface_negativity_of_antinef X hX f hf M.divisor.1 hex (by
    intro C hC
    have he : smoothSurfaceWeilCartier X.structureMap M.divisor.1 = M.divisor :=
      Subtype.ext rfl
    rw [he]
    exact M.degree_nonpos_of_qDegree_nonpos hD C (hanti C hC))
  intro p
  exact (M.coeff_nonneg_iff p).mp (hpos p)

theorem qEffective_antinef_connected_fiber
    (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    (D : QWeilDivisor X.scheme) (hD : IsQCartierDivisor D) (heff : 0 ≤ D)
    {Y : Scheme} (f : X.scheme ⟶ Y)
    (hanti : ∀ C : CurveOn X, (∃ y, ∀ c, f (C.morphism c) = y) → qCartierCurveDegree D hD C ≤ 0)
    (y : Y) (hy : IsClosed {y}) (hcon : _root_.IsPreconnected (f ⁻¹' {y})) :
    f ⁻¹' {y} ⊆ qDivisorSupport D ∨ Disjoint (f ⁻¹' {y}) (qDivisorSupport D) := by
  let M := chooseCartierMultiple hD
  rw [← M.divisorSupport_eq]
  apply effective_antinef_connected_fiber X M.divisor
    (fun p => (M.coeff_nonneg_iff p).mpr (heff p)) f ?_ y hy hcon
  intro C hC
  exact M.degree_nonpos_of_qDegree_nonpos hD C (hanti C hC)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem exceptional_prime_not_quasiFiniteAt
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f]
    (hb : IsBirationalMorphism f) (p : PrimeDivisor X)
    (hp : 1 < Order.coheight (f p.1)) (x : X)
    (hx : x ∈ closure ({p.1} : Set X)) : ¬ f.QuasiFiniteAt x := by
  intro hq
  have hpx : p.1 ⤳ x := specializes_iff_mem_closure.mpr hx
  have hqp : f.QuasiFiniteAt p.1 := hpx.mem_open f.isOpen_quasiFiniteAt hq
  let : Algebra (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) :=
    (f.stalkMap p.1).hom.toAlgebra
  have hqa : Algebra.QuasiFinite (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) :=
    RingHom.quasiFinite_algebraMap.mp hqp
  have he := birational_quasiFinite_stalk_coheight f hb p.1 hqa
  rw [p.2] at he
  exact (ne_of_gt hp) he

theorem exceptional_fiber_not_isOpen_singleton
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f]
    (hb : IsBirationalMorphism f) (p : PrimeDivisor X)
    (hp : 1 < Order.coheight (f p.1)) (x : X)
    (hx : x ∈ closure ({p.1} : Set X)) : ¬ IsOpen {f.asFiber x} := by
  rw [← Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  exact exceptional_prime_not_quasiFiniteAt f hb p hp x hx
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open TopologicalSpace

lemma nonisolated_irreducible_closed_subset
    {T : Type*} [TopologicalSpace T] [NoetherianSpace T]
    (A : Set T) (hA : IsClosed A) (x : A)
    (hx : ¬ IsOpen ({x} : Set A)) :
    ∃ Z : Set T, IsClosed Z ∧ IsIrreducible Z ∧ x.1 ∈ Z ∧ Z ⊆ A ∧ Z ≠ {x.1} := by
  let R := irreducibleComponent x
  have hR : R ≠ {x} := by
    intro he
    obtain ⟨U,hU,hUn,hUR⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent R
        (irreducibleComponent_mem_irreducibleComponents x)
    rw [he] at hUR
    obtain ⟨u,hu⟩ := hUn
    have hux : u = x := hUR hu
    have hEq : U = {x} := Set.Subset.antisymm hUR (by
      rw [Set.singleton_subset_iff]
      exact hux ▸ hu)
    exact hx (hEq ▸ hU)
  refine ⟨Subtype.val '' R, hA.isClosedEmbedding_subtypeVal.isClosedMap R
    isClosed_irreducibleComponent,
    isIrreducible_irreducibleComponent.image _ continuous_subtype_val.continuousOn,
    ⟨x,mem_irreducibleComponent,rfl⟩, ?_, ?_⟩
  · rintro _ ⟨z,_,rfl⟩
    exact z.2
  · intro he
    apply hR
    apply Set.Subset.antisymm
    · intro z hz
      have hm : z.1 ∈ Subtype.val '' R := Set.mem_image_of_mem Subtype.val hz
      rw [he] at hm
      exact Subtype.ext hm
    · exact Set.singleton_subset_iff.mpr mem_irreducibleComponent
end NumericalDimensionOne

end OAI
