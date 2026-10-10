import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.SurfaceIntersection

namespace OAI

/-! Fixed Divisors. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]
variable [CompactSpace X]
lemma surfaceCartierPrimeDegree_principal (a : X.functionField) (ha : a ≠ 0)
    (p : PrimeDivisor X) :
    surfaceCartierPrimeDegree sX
        (smoothSurfaceWeilCartier sX (principalWeilDivisor a)) p = 0 := by
  let C := (pointClosure p.1).fromSpecStalk (genericPoint (pointClosure p.1))
  have : IsIntegral C.normalization := integral_genericNormalization
  have : SmoothOfRelativeDimension 1
      (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_smooth sX p.1 p.2
  have : IsProper (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_proper sX p.1
  have : IsLocallyNoetherian C.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  have : CompactSpace C.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  exact properCurveDegree_principal (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
    (C.fromNormalization ≫ pointClosureι p.1) a ha _
lemma surfaceIntersection_principal_right (a : X.functionField) (ha : a ≠ 0)
    (D : cartierDivisors (X := X)) :
    surfaceIntersection sX D (smoothSurfaceWeilCartier sX (principalWeilDivisor a)) = 0 := by
  simp only [surfaceIntersection, surfaceCartierPrimeDegree_principal sX a ha,
    mul_zero, Finsupp.sum, Finset.sum_const_zero]
lemma surfaceIntersection_principal_left (a : X.functionField) (ha : a ≠ 0)
    (D : cartierDivisors (X := X)) :
    surfaceIntersection sX (smoothSurfaceWeilCartier sX (principalWeilDivisor a)) D = 0 := by
  rw [surfaceIntersection_comm, surfaceIntersection_principal_right sX a ha]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
section ActualFixedPart
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

def sectionOrderSet (D : WeilDivisor X) (S : Set X.functionField) (p : PrimeDivisor X) : Set ℤ :=
  {z | ∃ s ∈ S, s ≠ 0 ∧ z = X.ord s p.1 + D p}

lemma sectionOrderSet_nonempty (D : WeilDivisor X) (S : Set X.functionField)
    (hne : ∃ s ∈ S, s ≠ 0) (p : PrimeDivisor X) : (sectionOrderSet D S p).Nonempty := by
  obtain ⟨s, hs, hsn⟩ := hne
  exact ⟨_, s, hs, hsn, rfl⟩

lemma sectionOrderSet_nonnegative (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (p : PrimeDivisor X) :
    ∀ z ∈ sectionOrderSet D S p, 0 ≤ z := by
  rintro z ⟨s, hs, hsn, rfl⟩
  exact (hS s hs).resolve_left hsn p

noncomputable def fixedCoefficient (D : WeilDivisor X) (S : Set X.functionField)
    (p : PrimeDivisor X) : ℤ := sInf (sectionOrderSet D S p)

lemma fixedCoefficient_nonnegative (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0)
    (p : PrimeDivisor X) : 0 ≤ fixedCoefficient D S p := by
  apply le_csInf (sectionOrderSet_nonempty D S hne p)
  exact sectionOrderSet_nonnegative D S hS p

lemma fixedCoefficient_le (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s)
    {s : X.functionField} (hs : s ∈ S) (hsn : s ≠ 0) (p : PrimeDivisor X) :
    fixedCoefficient D S p ≤ X.ord s p.1 + D p := by
  exact csInf_le ⟨0, sectionOrderSet_nonnegative D S hS p⟩ ⟨s, hs, hsn, rfl⟩

lemma exists_fixedCoefficient_eq (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0)
    (p : PrimeDivisor X) :
    ∃ s ∈ S, s ≠ 0 ∧ fixedCoefficient D S p = X.ord s p.1 + D p := by
  exact Int.csInf_mem (sectionOrderSet_nonempty D S hne p)
    ⟨0, sectionOrderSet_nonnegative D S hS p⟩

lemma fixedCoefficient_support_finite [CompactSpace X]
    (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0) :
    (Function.support (fixedCoefficient D S)).Finite := by
  classical
  obtain ⟨s, hs, hsn⟩ := hne
  apply (principalWeilDivisor s + D).support.finite_toSet.subset
  intro p hp
  apply Finsupp.mem_support_iff.mpr
  intro hz
  have hle := fixedCoefficient_le D S hS hs hsn p
  have hge := fixedCoefficient_nonnegative D S hS ⟨s, hs, hsn⟩ p
  change X.ord s p.1 + D p = 0 at hz
  exact hp (le_antisymm (hle.trans_eq hz) hge)

noncomputable def fixedPart [CompactSpace X] (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0) : WeilDivisor X :=
  Finsupp.ofSupportFinite (fixedCoefficient D S) (fixedCoefficient_support_finite D S hS hne)

lemma fixedPart_nonnegative [CompactSpace X]
    (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0) :
    0 ≤ fixedPart D S hS hne := by
  intro p
  exact fixedCoefficient_nonnegative D S hS hne p

lemma fixedPart_le_zeroDivisor [CompactSpace X]
    (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0)
    {s : X.functionField} (hs : s ∈ S) (hsn : s ≠ 0) :
    fixedPart D S hS hne ≤ principalWeilDivisor s + D := by
  intro p
  exact fixedCoefficient_le D S hS hs hsn p

lemma fixedPart_residual_no_fixed_prime [CompactSpace X]
    (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0)
    (p : PrimeDivisor X) :
    ∃ s ∈ S, s ≠ 0 ∧ (principalWeilDivisor s + D - fixedPart D S hS hne) p = 0 := by
  obtain ⟨s, hs, hsn, he⟩ := exists_fixedCoefficient_eq D S hS hne p
  refine ⟨s, hs, hsn, ?_⟩
  change X.ord s p.1 + D p - fixedCoefficient D S p = 0
  omega

lemma le_fixedPart_iff [CompactSpace X]
    (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0)
    (E : WeilDivisor X) :
    E ≤ fixedPart D S hS hne ↔ ∀ s ∈ S, s ≠ 0 → E ≤ principalWeilDivisor s + D := by
  constructor
  · intro h s hs hsn
    exact h.trans (fixedPart_le_zeroDivisor D S hS hne hs hsn)
  · intro h p
    obtain ⟨s, hs, hsn, he⟩ := exists_fixedCoefficient_eq D S hS hne p
    change E p ≤ fixedCoefficient D S p
    rw [he]
    exact h s hs hsn p
end ActualFixedPart
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u

lemma divisorSupport_mono_nonnegative {X : Scheme.{u}}
    {D E : WeilDivisor X} (hD : 0 ≤ D) (hDE : D ≤ E) :
    divisorSupport D ⊆ divisorSupport E := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := Set.mem_iUnion₂.mp hx
  refine Set.mem_iUnion₂.mpr ⟨p, ?_, hpx⟩
  apply Finsupp.mem_support_iff.mpr
  intro hz
  have hDp : D p = 0 := le_antisymm ((hDE p).trans_eq hz) (hD p)
  exact Finsupp.mem_support_iff.mp hp hDp

section FixedSupport
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [CompactSpace X]

theorem fixedPart_support_subset (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0)
    (B : Set X)
    (hgen : ∀ x ∉ B, ∃ s ∈ S, s ≠ 0 ∧ x ∈ sectionNonvanishing D s) :
    divisorSupport (fixedPart D S hS hne) ⊆ B := by
  intro x hx
  by_contra hxB
  obtain ⟨s, hs, hsn, hxnon⟩ := hgen x hxB
  have hsub := divisorSupport_mono_nonnegative (fixedPart_nonnegative D S hS hne)
    (fixedPart_le_zeroDivisor D S hS hne hs hsn)
  exact hxnon (hsub hx)

theorem fixedPart_prime_image_constant {Y : Scheme.{u}}
    (f : X ⟶ Y) (D : WeilDivisor X) (S : Set X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0)
    (Z : Set Y) (hZ : ∀ y ∈ Z, IsClosed ({y} : Set Y))
    (hgen : ∀ x : X, f x ∉ Z →
      ∃ s ∈ S, s ≠ 0 ∧ x ∈ sectionNonvanishing D s)
    (p : PrimeDivisor X) (hp : p ∈ (fixedPart D S hS hne).support) :
    f p.1 ∈ Z ∧ ∀ x ∈ closure ({p.1} : Set X), f x = f p.1 := by
  have hpSupp : p.1 ∈ divisorSupport (fixedPart D S hS hne) := by
    exact Set.mem_iUnion₂.mpr ⟨p, hp, subset_closure (Set.mem_singleton _)⟩
  have hpZ : f p.1 ∈ Z := fixedPart_support_subset D S hS hne (f ⁻¹' Z) hgen hpSupp
  refine ⟨hpZ, ?_⟩
  intro x hx
  have hsp := f.base.hom.map_specializes (specializes_iff_mem_closure.mpr hx)
  have hfx : f x ∈ closure ({f p.1} : Set Y) := specializes_iff_mem_closure.mp hsp
  simpa only [(hZ _ hpZ).closure_eq, Set.mem_singleton_iff] using hfx
end FixedSupport
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
section LinearSystemAvoidance
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ))

lemma linearSystem_avoid_finite (D : WeilDivisor X) (S : letI := schemeFieldAlgebra (.of ℂ) sX; Submodule ℂ X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0)
    (hmov : ∀ p : PrimeDivisor X, ∃ s ∈ S, s ≠ 0 ∧ X.ord s p.1 + D p = 0)
    (V : Finset (PrimeDivisor X)) :
    ∃ s ∈ S, s ≠ 0 ∧ ∀ p ∈ V, X.ord s p.1 + D p = 0 := by
  let := schemeFieldAlgebra (.of ℂ) sX
  classical
  let P : Option {p // p ∈ V} → Submodule ℂ S
    | none => ⊥
    | some p => (divisorSectionsOver (.of ℂ) sX (D - Finsupp.single p.1 1)).comap S.subtype
  have hP : ∀ i, P i ≠ ⊤ := by
    intro i he
    cases i with
    | none =>
      obtain ⟨s,hs,hsn⟩ := hne
      have hm : (⟨s,hs⟩ : S) ∈ P none := by rw [he]; trivial
      exact hsn (congrArg Subtype.val (by simpa only [P,Submodule.mem_bot] using hm))
    | some p =>
      obtain ⟨s,hs,hsn,hp⟩ := hmov p.1
      have hm : (⟨s,hs⟩ : S) ∈ P (some p) := by rw [he]; trivial
      change IsDivisorSection (D - Finsupp.single p.1 1) s at hm
      have ht := hm.resolve_left hsn p.1
      simp only [Finsupp.sub_apply,Finsupp.single_eq_same] at ht
      omega
  obtain ⟨s,hs⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hP
  have hsn : (s : X.functionField) ≠ 0 := by
    intro hz
    exact hs none (by simpa only [P,Submodule.mem_bot] using (Subtype.ext hz : s = 0))
  refine ⟨s,s.2,hsn,?_⟩
  intro p hp
  by_contra hn
  have hpos : 1 ≤ X.ord (s : X.functionField) p.1 + D p := by
    have hnon := (hS s s.2).resolve_left hsn p
    omega
  apply hs (some ⟨p,hp⟩)
  change IsDivisorSection (D - Finsupp.single p 1) (s : X.functionField)
  right
  intro q
  by_cases hq : q = p
  · subst q
    simp only [Finsupp.sub_apply,Finsupp.single_eq_same]
    omega
  · simpa only [Finsupp.sub_apply,Finsupp.single_eq_of_ne hq,sub_zero] using
      (hS s s.2).resolve_left hsn q
end LinearSystemAvoidance
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]
lemma surfaceIntersection_effective_disjoint (D E : cartierDivisors (X := X))
    (hD : 0 ≤ D.1) (hE : 0 ≤ E.1) (hdis : ∀ p, D.1 p ≠ 0 → E.1 p = 0) :
    0 ≤ surfaceIntersection sX D E := by
  classical
  unfold surfaceIntersection
  apply Finset.sum_nonneg
  intro p hp
  have hP := (smoothSurfacePrimeCartier sX p).2
  have hEp := hdis p (Finsupp.mem_support_iff.mp hp)
  have hdeg : 0 ≤ surfaceCartierPrimeDegree sX E p := by
    rw [surfacePrimeDegree_eq_multiplicities sX E hE p hEp hP]
    apply finsum_nonneg
    intro z
    positivity
  exact mul_nonneg (hD p) hdeg
section MovingSystem
lemma surfaceIntersection_movable_nonneg (D : WeilDivisor X) (S : letI := schemeFieldAlgebra (.of ℂ) sX; Submodule ℂ X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0)
    (hmov : ∀ p : PrimeDivisor X, ∃ s ∈ S, s ≠ 0 ∧ X.ord s p.1 + D p = 0) :
    0 ≤ surfaceIntersection sX (smoothSurfaceWeilCartier sX D) (smoothSurfaceWeilCartier sX D) := by
  let := schemeFieldAlgebra (.of ℂ) sX
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨s,hs,hsn⟩ := hne
  let E : WeilDivisor X := principalWeilDivisor s + D
  obtain ⟨t,ht,htn,htE⟩ := linearSystem_avoid_finite sX D S hS ⟨s,hs,hsn⟩ hmov E.support
  let F : WeilDivisor X := principalWeilDivisor t + D
  let H := smoothSurfaceWeilCartier sX
  have hE : 0 ≤ E := (hS s hs).resolve_left hsn
  have hF : 0 ≤ F := (hS t ht).resolve_left htn
  have hdis : ∀ p, E p ≠ 0 → F p = 0 := by
    intro p hp
    exact htE p (Finsupp.mem_support_iff.mpr hp)
  have hh := surfaceIntersection_effective_disjoint sX (H E) (H F) hE hF hdis
  change 0 ≤ surfaceIntersection sX (H (principalWeilDivisor s + D))
    (H (principalWeilDivisor t + D)) at hh
  rw [map_add,map_add,surfaceIntersection_add_left,surfaceIntersection_principal_left sX s hsn,
    zero_add,surfaceIntersection_add_right,surfaceIntersection_principal_right sX t htn,zero_add] at hh
  exact hh
lemma surfaceIntersection_residual_nonneg [CompactSpace X]
    (D : WeilDivisor X) (S : letI := schemeFieldAlgebra (.of ℂ) sX; Submodule ℂ X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0) :
    let R := D - fixedPart D S hS hne
    0 ≤ surfaceIntersection sX (smoothSurfaceWeilCartier sX R) (smoothSurfaceWeilCartier sX R) := by
  let := schemeFieldAlgebra (.of ℂ) sX
  dsimp only
  apply surfaceIntersection_movable_nonneg sX _ S
  · intro s hs
    by_cases hsn : s = 0
    · exact Or.inl hsn
    · right
      intro p
      have hh := fixedPart_le_zeroDivisor D (S : Set X.functionField) hS hne hs hsn p
      change _ ≤ X.ord s p.1 + D p at hh
      simp only [Finsupp.sub_apply]
      omega
  · exact hne
  · intro p
    obtain ⟨s,hs,hsn,he⟩ := fixedPart_residual_no_fixed_prime D (S : Set X.functionField) hS hne p
    refine ⟨s,hs,hsn,?_⟩
    change X.ord s p.1 + D p - _ = 0 at he
    change X.ord s p.1 + (D p - _) = 0
    omega
end MovingSystem
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma isPulledCartierRepresentative_zero_of_equation {C X : Scheme}
    [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C] [IsLocallyNoetherian X]
    (g : C ⟶ X) (D : WeilDivisor X) (U : X.Opens) (hU : ∀ x : C, g x ∈ U)
    (a : X.functionField) (ha : a ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord a p.1) :
    IsPulledCartierRepresentative g D 0 := by
  obtain ⟨V,hV,hηV,hVU⟩ := exists_isAffineOpen_mem_and_subset (hU (genericPoint C))
  refine ⟨V,hV,hηV,a,ha,fun p hp => heq p (hVU hp),?_⟩
  intro x
  obtain ⟨W,hW,hxW,hWU⟩ := exists_isAffineOpen_mem_and_subset (hU x)
  refine ⟨W,hW,hxW,a,ha,fun p hp => heq p (hWU hp),1,isUnit_one,?_,?_⟩
  · simp only [map_one,div_self ha]
  · intro p _
    simp only [Finsupp.zero_apply,map_one,order_one]
lemma IsCartierPullback.zero_representative_of_constant {C X Y : Scheme}
    [IsIntegral C] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian C] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {f : X ⟶ Y} [IsDominant f] {D : WeilDivisor Y} {E : WeilDivisor X}
    (hE : IsCartierPullback f D E) (g : C ⟶ X)
    (hconst : ∀ x : C, f (g x) = f (g (genericPoint C))) :
    IsPulledCartierRepresentative g E 0 := by
  obtain ⟨U,_,hηU,a,ha,_,heq⟩ := hE (g (genericPoint C))
  apply isPulledCartierRepresentative_zero_of_equation g E (f ⁻¹ᵁ U)
    (fun x => by change f (g x) ∈ U; rw [hconst x]; exact hηU)
    (dominantFunctionFieldMap f a) ((map_ne_zero _).mpr ha)
  exact heq
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]
lemma surfaceCartierPrimeDegree_contracted {f : X ⟶ Y} [IsDominant f]
    {D : WeilDivisor Y} (E : cartierDivisors (X := X)) (hE : IsCartierPullback f D E.1)
    (p : PrimeDivisor X) (hp : ∀ x ∈ closure ({p.1} : Set X), f x = f p.1) :
    surfaceCartierPrimeDegree sX E p = 0 := by
  let C := (pointClosure p.1).fromSpecStalk (genericPoint (pointClosure p.1))
  have : IsIntegral C.normalization := integral_genericNormalization
  have : SmoothOfRelativeDimension 1
      (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_smooth sX p.1 p.2
  have : IsProper (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_proper sX p.1
  have : IsLocallyNoetherian C.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  have : CompactSpace C.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (C.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  let g := C.fromNormalization ≫ pointClosureι p.1
  have him (x : C.normalization) : g x ∈ closure ({p.1} : Set X) := by
    rw [← pointClosure_range]
    exact ⟨C.fromNormalization x,rfl⟩
  have hzero := hE.zero_representative_of_constant g
    (fun x => (hp _ (him x)).trans (hp _ (him (genericPoint C.normalization))).symm)
  change properCurveDegree g E = 0
  rw [properCurveDegree_eq (C.fromNormalization ≫ pointClosureι p.1 ≫ sX) g E 0 hzero]
  rfl
lemma surfaceIntersection_contracted {f : X ⟶ Y} [IsDominant f]
    {D : WeilDivisor Y} (E F : cartierDivisors (X := X)) (hE : IsCartierPullback f D E.1)
    (hF : ∀ p ∈ F.1.support, ∀ x ∈ closure ({p.1} : Set X), f x = f p.1) :
    surfaceIntersection sX F E = 0 := by
  unfold surfaceIntersection Finsupp.sum
  apply Finset.sum_eq_zero
  intro p hp
  change F.1 p * surfaceCartierPrimeDegree sX E p = 0
  rw [surfaceCartierPrimeDegree_contracted sX E hE p (hF p hp),mul_zero]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]
lemma surfacePrimePrime_nonneg (p q : PrimeDivisor X) (hpq : p ≠ q) :
    0 ≤ surfaceCartierPrimeDegree sX (smoothSurfacePrimeCartier sX q) p := by
  have h := surfaceIntersection_effective_disjoint sX
    (smoothSurfacePrimeCartier sX p) (smoothSurfacePrimeCartier sX q)
    (primeDivisor_effective p) (primeDivisor_effective q) ?_
  · rwa [surfaceIntersection_prime_left] at h
  · intro r hr
    have hrp : r = p := by
      by_contra hn
      exact hr (Finsupp.single_eq_of_ne hn)
    subst r
    exact Finsupp.single_eq_of_ne hpq
lemma surfacePrimePrime_zero_of_disjoint (p q : PrimeDivisor X)
    (hdis : Disjoint (closure ({p.1} : Set X)) (closure ({q.1} : Set X))) :
    surfaceCartierPrimeDegree sX (smoothSurfacePrimeCartier sX q) p = 0 := by
  classical
  let ν := (pointClosure p.1).fromSpecStalk (genericPoint (pointClosure p.1))
  have : IsIntegral ν.normalization := integral_genericNormalization
  have : SmoothOfRelativeDimension 1
      (ν.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_smooth sX p.1 p.2
  have : IsProper (ν.fromNormalization ≫ pointClosureι p.1 ≫ sX) :=
    surface_prime_normalization_proper sX p.1
  have : IsLocallyNoetherian ν.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (ν.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  have : CompactSpace ν.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (ν.fromNormalization ≫ pointClosureι p.1 ≫ sX)
  let g := ν.fromNormalization ≫ pointClosureι p.1
  let U : X.Opens := ⟨(closure ({q.1} : Set X))ᶜ,isClosed_closure.isOpen_compl⟩
  have hg : ∀ z, g z ∈ U := by
    intro z hz
    apply Set.disjoint_left.mp hdis ?_ hz
    rw [← pointClosure_range]
    exact ⟨ν.fromNormalization z,rfl⟩
  have heq (r : PrimeDivisor X) (hr : r.1 ∈ U) :
      (smoothSurfacePrimeCartier sX q).1 r = X.ord 1 r.1 := by
    have hrq : r ≠ q := by rintro rfl; exact hr (subset_closure (Set.mem_singleton _))
    change Finsupp.single q (1 : ℤ) r = X.ord 1 r.1
    rw [Finsupp.single_eq_of_ne hrq, order_one]
  have hzero := isPulledCartierRepresentative_zero_of_equation g
    (smoothSurfacePrimeCartier sX q).1 U hg 1 one_ne_zero heq
  change properCurveDegree g (smoothSurfacePrimeCartier sX q) = 0
  rw [properCurveDegree_eq (ν.fromNormalization ≫ pointClosureι p.1 ≫ sX) g _ 0 hzero]
  rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]
noncomputable def surfacePrimePair (p q : PrimeDivisor X) : ℤ :=
  surfaceCartierPrimeDegree sX (smoothSurfacePrimeCartier sX q) p
lemma surfacePrimePair_comm (p q : PrimeDivisor X) : surfacePrimePair sX p q = surfacePrimePair sX q p := by
  have hh := surfaceIntersection_comm sX (smoothSurfacePrimeCartier sX p)
    (smoothSurfacePrimeCartier sX q)
  simpa only [surfaceIntersection_prime_left, surfacePrimePair] using hh
lemma surfaceDegree_eq_pair_sum (D : WeilDivisor X) (p : PrimeDivisor X) :
    surfaceCartierPrimeDegree sX (smoothSurfaceWeilCartier sX D) p =
      D.sum (fun q n => n * surfacePrimePair sX p q) := by
  rw [← surfaceIntersection_prime_left, surfaceIntersection_comm]
  change D.sum (fun q n => n * surfacePrimePair sX q p) = _
  apply Finsupp.sum_congr
  intro q _
  rw [surfacePrimePair_comm sX q p]
lemma surfacePrimePair_nonneg (p q : PrimeDivisor X) (hpq : p ≠ q) :
    0 ≤ surfacePrimePair sX p q :=
  surfacePrimePrime_nonneg sX p q hpq
lemma surfacePrimePair_zero_of_disjoint (p q : PrimeDivisor X)
    (hdis : Disjoint (closure ({p.1} : Set X)) (closure ({q.1} : Set X))) :
    surfacePrimePair sX p q = 0 :=
  surfacePrimePrime_zero_of_disjoint sX p q hdis
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma surface_prime_contracted_of_not_prime
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (sY : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sY]
    (f : X ⟶ Y) [IsDominant f] (hf : IsBirationalMorphism f)
    (q : PrimeDivisor X) (hq : Order.coheight (f q.1) ≠ 1) :
    ∀ x ∈ closure ({q.1} : Set X), f x = f q.1 := by
  have hz : Order.coheight (f q.1) ≠ 0 := by
    intro he
    have hsp : f q.1 ⤳ genericPoint Y :=
      (Order.coheight_eq_zero.mp he) (genericPoint_specializes (f q.1))
    have heq := (hsp.antisymm (genericPoint_specializes (f q.1))).eq
    have hqη := birational_generic_fiber f hf q.1 heq
    have h0 : Order.coheight q.1 = 0 := by
      rw [hqη]
      exact Order.coheight_eq_zero.mpr (fun x _ => genericPoint_specializes x)
    rw [q.2] at h0
    exact one_ne_zero h0
  have hlt : (1 : ℕ∞) < Order.coheight (f q.1) :=
    lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr hz) (Ne.symm hq)
  have h2 : (2 : ℕ∞) ≤ Order.coheight (f q.1) := by
    simpa only [one_add_one_eq_two] using
      (ENat.add_one_le_iff (show (1 : ℕ∞) ≠ ⊤ by simp)).mpr hlt
  have hc : IsClosed ({f q.1} : Set Y) := isClosed_point_of_max_coheight
    (coheight_le_of_smooth_dimension sY 2) (f q.1)
    (le_antisymm (coheight_le_of_smooth_dimension sY 2 (f q.1)) h2)
  intro x hx
  have hs : f q.1 ⤳ f x := (specializes_iff_mem_closure.mpr hx).map f.continuous
  have hm : f x ∈ closure ({f q.1} : Set Y) := hs.mem_closure
  rw [hc.closure_eq] at hm
  exact hm
end NumericalDimensionOne

end OAI
