import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.RelativeAmpleness

namespace OAI

/-! Ample Absorption. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
section SharedFiber
variable {W X Y R : ComplexProjectiveVariety}
    [StalkwiseNormal W.scheme] [StalkwiseNormal X.scheme] [StalkwiseNormal Y.scheme]
    (p : W.scheme ⟶ X.scheme) (q : W.scheme ⟶ Y.scheme)
    [IsDominant p] [IsDominant q]
    (hp : p ≫ X.structureMap = W.structureMap) (hq : q ≫ Y.structureMap = W.structureMap)
    (f : X.scheme ⟶ R.scheme) (g : Y.scheme ⟶ R.scheme)
    [IsDominant f] [IsDominant g] (hcomm : p ≫ f = q ≫ g)
    {D : QWeilDivisor X.scheme} {E : QWeilDivisor Y.scheme}
    {P Q : QWeilDivisor W.scheme} (hD : IsQCartierDivisor D) (hE : IsQCartierDivisor E)
    (hP : IsQCartierPullback p D P) (hQ : IsQCartierPullback q E Q)
    (hs : IsQCartierDivisor (P-Q)) (hnegative : IsRelativelyAmpleQ f (-D))
    (hpositive : IsRelativelyAmpleQ g E)
    (C : CurveOn W) (hC : IsCurveContracted (p ≫ f) C)
include hp hq hcomm hD hE hP hQ hnegative hpositive hC
lemma canonical_difference_nonpos_shared_fiber :
    qCartierCurveDegree (P-Q) hs C ≤ 0 := by
  have hCp : IsCurveContracted f (C.comp p hp) := hC
  have hCq : IsCurveContracted g (C.comp q hq) := by
    obtain ⟨r,hr⟩ := hC
    refine ⟨r,?_⟩
    intro x
    change (q ≫ g) (C.morphism x) = r
    rw [← hcomm]
    exact hr x
  have hn : IsQCartierDivisor (-D) := by
    simpa only [neg_one_smul] using ((chooseCartierMultiple hD).smul (-1)).isQCartier
  have hleft := hnegative.curveDegree_nonneg f hn (C.comp p hp) hCp
  rw [qCartierCurveDegree_neg hD hn,neg_nonneg] at hleft
  have hright := hpositive.curveDegree_nonneg g hE (C.comp q hq) hCq
  rw [qCartierCurveDegree_sub hP.isQCartier hQ.isQCartier,
    qCartierCurveDegree_pullback p hp hD hP,
    qCartierCurveDegree_pullback q hq hE hQ]
  exact sub_nonpos.mpr (hleft.trans hright)
lemma canonical_difference_negative_shared_fiber
    (c : PrimeDivisor C.curve.scheme)
    (hc : p (C.morphism (genericPoint C.curve.scheme)) ≠ p (C.morphism c.1) ∨
      q (C.morphism (genericPoint C.curve.scheme)) ≠ q (C.morphism c.1)) :
    qCartierCurveDegree (P-Q) hs C < 0 := by
  have hCp : IsCurveContracted f (C.comp p hp) := hC
  have hCq : IsCurveContracted g (C.comp q hq) := by
    obtain ⟨r,hr⟩ := hC
    refine ⟨r,?_⟩
    intro x
    change (q ≫ g) (C.morphism x) = r
    rw [← hcomm]
    exact hr x
  have hn : IsQCartierDivisor (-D) := by
    simpa only [neg_one_smul] using ((chooseCartierMultiple hD).smul (-1)).isQCartier
  have hleft := hnegative.curveDegree_nonneg f hn (C.comp p hp) hCp
  rw [qCartierCurveDegree_neg hD hn,neg_nonneg] at hleft
  have hright := hpositive.curveDegree_nonneg g hE (C.comp q hq) hCq
  rw [qCartierCurveDegree_sub hP.isQCartier hQ.isQCartier,
    qCartierCurveDegree_pullback p hp hD hP,
    qCartierCurveDegree_pullback q hq hE hQ]
  rcases hc with hc | hc
  · have hlt := hnegative.curveDegree_pos f hn (C.comp p hp) hCp c hc
    rw [qCartierCurveDegree_neg hD hn,neg_pos] at hlt
    exact sub_neg.mpr (hlt.trans_le hright)
  · have hlt := hpositive.curveDegree_pos g hE (C.comp q hq) hCq c hc
    exact sub_neg.mpr (hleft.trans_lt hlt)
end SharedFiber
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
lemma surfacePrimePair_zero_outside_fiber_open {Y : Scheme} (f : X ⟶ Y)
    (p q : PrimeDivisor X) (hp : ∀ x ∈ closure ({p.1} : Set X), f x = f p.1)
    (U : Y.Opens) (hpU : f p.1 ∈ U) (hqU : f q.1 ∉ U) :
    surfacePrimePair sX p q = 0 := by
  apply surfacePrimePair_zero_of_disjoint
  apply Set.disjoint_left.mpr
  intro x hxp hxq
  apply hqU
  have hspec : f q.1 ⤳ f x := (specializes_iff_mem_closure.mpr hxq).map f.continuous
  apply hspec.mem_open U.isOpen
  rwa [hp x hxp]
lemma surfacePrimePair_zero_distinct_fibers {Y : Scheme} (f : X ⟶ Y)
    (p q : PrimeDivisor X) (hp : ∀ x ∈ closure ({p.1} : Set X), f x = f p.1)
    (hq : ∀ x ∈ closure ({q.1} : Set X), f x = f q.1) (hne : f p.1 ≠ f q.1) :
    surfacePrimePair sX p q = 0 := by
  apply surfacePrimePair_zero_of_disjoint
  apply Set.disjoint_left.mpr
  intro x hxp hxq
  exact hne ((hp x hxp).symm.trans (hq x hxq))
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
noncomputable def surfaceWeilPrimeDegreeHom (p : PrimeDivisor X) : WeilDivisor X →+ ℤ where
  toFun D := surfaceCartierPrimeDegree sX (smoothSurfaceWeilCartier sX D) p
  map_zero' := surfaceCartierPrimeDegree_zero sX p
  map_add' D E := surfaceCartierPrimeDegree_add sX
    (smoothSurfaceWeilCartier sX D) (smoothSurfaceWeilCartier sX E) p
lemma surfaceWeilDegree_local_nonneg {Y : Scheme} (f : X ⟶ Y)
    (p : PrimeDivisor X) (hp : ∀ x ∈ closure ({p.1} : Set X), f x = f p.1)
    (U : Y.Opens) (hpU : f p.1 ∈ U) (D : WeilDivisor X) (hDp : D p = 0)
    (hD : ∀ q : PrimeDivisor X, f q.1 ∈ U → 0 ≤ D q) :
    0 ≤ surfaceWeilPrimeDegreeHom sX p D := by
  classical
  change 0 ≤ surfaceCartierPrimeDegree sX (smoothSurfaceWeilCartier sX D) p
  rw [surfaceDegree_eq_pair_sum]
  apply Finset.sum_nonneg
  intro q _
  change 0 ≤ D q * surfacePrimePair sX p q
  by_cases hqp : q = p
  · subst q
    simp only [hDp,zero_mul,le_refl]
  · by_cases hqU : f q.1 ∈ U
    · exact mul_nonneg (hD q hqU) (surfacePrimePair_nonneg sX p q (Ne.symm hqp))
    · rw [surfacePrimePair_zero_outside_fiber_open sX f p q hp U hpU hqU,mul_zero]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX] [CompactSpace X]
lemma surface_exceptional_row_le {Y : Scheme} (f : X ⟶ Y)
    (V : Finset (PrimeDivisor X)) (p : PrimeDivisor X) (hpV : p ∈ V)
    (hp : ∀ x ∈ closure ({p.1} : Set X), f x = f p.1)
    (U : Y.Opens) (hpU : f p.1 ∈ U) (J : WeilDivisor X) (hJ : ∀ q ∈ V, J q = 0)
    (a : X.functionField) (ha : a ≠ 0)
    (hdom : ∀ q : PrimeDivisor X, f q.1 ∈ U → J q ≤ X.ord a q.1) :
    (∑ q ∈ V, X.ord a q.1 * surfacePrimePair sX p q) ≤
      -surfaceWeilPrimeDegreeHom sX p J := by
  classical
  let D := principalWeilDivisor a
  let E := D.filter (fun q => q ∈ V)
  let R := D-E-J
  have hRp : R p = 0 := by simp [R,E,Finsupp.sub_apply,hpV,hJ p hpV]
  have hR : ∀ q : PrimeDivisor X, f q.1 ∈ U → 0 ≤ R q := by
    intro q hqU
    by_cases hq : q ∈ V
    · simp [R,E,Finsupp.sub_apply,hq,hJ q hq]
    · simp only [R,E,Finsupp.sub_apply,Finsupp.filter_apply,ite_eq_right hq,sub_zero]
      exact sub_nonneg.mpr (hdom q hqU)
  have hn := surfaceWeilDegree_local_nonneg sX f p hp U hpU R hRp hR
  have hz : surfaceWeilPrimeDegreeHom sX p D = 0 :=
    surfaceCartierPrimeDegree_principal sX a ha p
  change 0 ≤ surfaceWeilPrimeDegreeHom sX p (D-E-J) at hn
  rw [map_sub,map_sub,hz] at hn
  have he : surfaceWeilPrimeDegreeHom sX p E =
      ∑ q ∈ V, X.ord a q.1 * surfacePrimePair sX p q := by
    change surfaceCartierPrimeDegree sX (smoothSurfaceWeilCartier sX E) p = _
    rw [surfaceDegree_eq_pair_sum]
    have hs : E.support ⊆ V := by
      intro q hq
      exact (Finset.mem_filter.mp hq).2
    rw [Finsupp.sum_of_support_subset E hs (fun q n => n * surfacePrimePair sX p q) (fun _ _ => zero_mul _)]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [E,Finsupp.filter_apply,ite_eq_left hq,D,principalWeilDivisor_apply]
  rw [he] at hn
  linarith
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma exists_primeDivisor_curve (C : ComplexProjectiveVariety) (hC : IsSmoothNfold C 1) :
    Nonempty (PrimeDivisor C.scheme) := by
  let : SmoothOfRelativeDimension 1 C.structureMap := hC
  let : JacobsonSpace C.scheme := LocallyOfFiniteType.jacobsonSpace C.structureMap
  obtain ⟨p,_,hp⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set C.scheme).Nonempty) isClosed_univ.isLocallyClosed
  exact ⟨⟨p,coheight_eq_of_smooth_closed C.structureMap 1 p hp⟩⟩
lemma surface_prime_morphism_generic (X : ComplexProjectiveVariety)
    (hX : IsSmoothNfold X 2) (p : PrimeDivisor X.scheme) :
    (surfacePrimeCurveOn X hX p).morphism
      (genericPoint (surfacePrimeCurveOn X hX p).curve.scheme) = p.1 := by
  let ν := (pointClosure p.1).fromSpecStalk (genericPoint (pointClosure p.1))
  change pointClosureι p.1 (ν.fromNormalization (genericPoint ν.normalization)) = p.1
  rw [dominant_genericPoint ν.fromNormalization,pointClosure_generic]
lemma surfaceCartierPrimeDegree_positive_of_ample (X : ComplexProjectiveVariety)
    [StalkwiseNormal X.scheme] (hX : IsSmoothNfold X 2)
    (D : cartierDivisors (X := X.scheme)) (hD : IsAmpleDivisor D.1)
    (p : PrimeDivisor X.scheme) :
    0 < @surfaceCartierPrimeDegree X.scheme _ _ _ X.structureMap hX _ D p := by
  let : SmoothOfRelativeDimension 2 X.structureMap := hX
  let C := surfacePrimeCurveOn X hX p
  obtain ⟨q⟩ := exists_primeDivisor_curve C.curve C.smooth
  rw [surfaceCartierPrimeDegree_eq_cartierCurveDegree X hX D p]
  apply cartierCurveDegree_positive_of_ample D hD C q
  intro he
  have hc := C.isClosed_prime_image q
  rw [← he,surface_prime_morphism_generic] at hc
  have hh := coheight_eq_of_smooth_closed X.structureMap 2 p.1 hc
  rw [p.2] at hh
  norm_num at hh
lemma surfaceIntersection_positive_of_ample_effective (X : ComplexProjectiveVariety)
    [StalkwiseNormal X.scheme] (hX : IsSmoothNfold X 2)
    (D E : cartierDivisors (X := X.scheme)) (hD : IsAmpleDivisor D.1)
    (hE : 0 ≤ E.1) (hne : E.1 ≠ 0) :
    0 < @surfaceIntersection X.scheme _ _ _ X.structureMap hX _ E D := by
  classical
  obtain ⟨p,hp⟩ := Finsupp.ne_iff.mp hne
  have hp0 : E.1 p ≠ 0 := by simpa using hp
  change 0 < E.1.sum (fun p n => n * _)
  apply Finset.sum_pos'
  · intro q _
    exact mul_nonneg (hE q) (surfaceCartierPrimeDegree_positive_of_ample X hX D hD q).le
  · exact ⟨p,Finsupp.mem_support_iff.mpr hp0,
      mul_pos (lt_of_le_of_ne (hE p) (Ne.symm hp0))
        (surfaceCartierPrimeDegree_positive_of_ample X hX D hD p)⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
section FiniteWitnessAvoidance
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
variable (sX : X ⟶ Spec (.of ℂ))

lemma linearSystem_avoid_finite_of_witnesses (D : WeilDivisor X) (S : letI := schemeFieldAlgebra (.of ℂ) sX; Submodule ℂ X.functionField)
    (hS : ∀ s ∈ S, IsDivisorSection D s) (hne : ∃ s ∈ S, s ≠ 0)
    (V : Finset (PrimeDivisor X))
    (hmov : ∀ p ∈ V, ∃ s ∈ S, s ≠ 0 ∧ X.ord s p.1 + D p = 0) :
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
      obtain ⟨s,hs,hsn,hp⟩ := hmov p.1 p.2
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
end FiniteWitnessAvoidance
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
section AmpleDivisorExtra
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

theorem principalWeilDivisor_mul {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    principalWeilDivisor (f * g) = principalWeilDivisor f + principalWeilDivisor g := by
  ext p
  exact X.ord_mul hf hg

@[simp] theorem principalWeilDivisor_one :
    principalWeilDivisor (1 : X.functionField) = 0 := by
  ext p
  exact order_one p.1

theorem principalWeilDivisor_inv {f : X.functionField} (hf : f ≠ 0) :
    principalWeilDivisor f⁻¹ = -principalWeilDivisor f := by
  ext p
  exact order_inv f hf p.1

theorem principalWeilDivisor_pow {f : X.functionField} (hf : f ≠ 0) (m : ℕ) :
    principalWeilDivisor (f ^ m) = m • principalWeilDivisor f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, principalWeilDivisor_mul (pow_ne_zero _ hf) hf, ih, succ_nsmul]

theorem isCartierDivisor_principal {f : X.functionField} (hf : f ≠ 0) :
    IsCartierDivisor (principalWeilDivisor f) := by
  intro x
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  exact ⟨U, isAffineOpen_opensRange _, X.affineCover.covers x, f, hf, fun _ _ => rfl⟩

end AmpleDivisorExtra
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
section AmpleLinearEquivalence
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

lemma principal_shift_identity (D : WeilDivisor X) {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) (m : ℕ) :
    principalWeilDivisor (f / g ^ m) + m • (D + principalWeilDivisor g) =
      principalWeilDivisor f + m • D := by
  rw [div_eq_mul_inv, principalWeilDivisor_mul hf (inv_ne_zero (pow_ne_zero _ hg)),
    principalWeilDivisor_inv (pow_ne_zero _ hg), principalWeilDivisor_pow hg,
    nsmul_add]
  abel

lemma divisorSection_iff_effective {D : WeilDivisor X} {f : X.functionField}
    (hf : f ≠ 0) :
    IsDivisorSection D f ↔ ∀ p, 0 ≤ (principalWeilDivisor f + D) p := by
  simp only [IsDivisorSection, hf, false_or, Finsupp.add_apply, principalWeilDivisor_apply]

lemma isAmpleDivisor_add_principal {D : WeilDivisor X} (hD : IsAmpleDivisor D)
    {g : X.functionField} (hg : g ≠ 0) :
    IsAmpleDivisor (D + principalWeilDivisor g) := by
  refine ⟨isCartierDivisor_add hD.1 (isCartierDivisor_principal hg), ?_⟩
  intro x U hx
  obtain ⟨m, hm, f, hf, hsec, haff, hxm, hsub⟩ := hD.2 x U hx
  have hfg : f / g ^ m ≠ 0 := div_ne_zero hf (pow_ne_zero _ hg)
  have heq := principal_shift_identity D hf hg m
  have hn : sectionNonvanishing (m • (D + principalWeilDivisor g)) (f / g ^ m) =
      sectionNonvanishing (m • D) f := by
    unfold sectionNonvanishing
    rw [heq]
  refine ⟨m, hm, f / g ^ m, hfg, ?_, ?_⟩
  · rw [divisorSection_iff_effective hfg, heq]
    exact (divisorSection_iff_effective hf).mp hsec
  · simpa only [hn] using And.intro haff (And.intro hxm hsub)

theorem isAmpleDivisor_add_principal_iff (D : WeilDivisor X) {g : X.functionField}
    (hg : g ≠ 0) :
    IsAmpleDivisor (D + principalWeilDivisor g) ↔ IsAmpleDivisor D := by
  refine ⟨fun h => ?_, fun h => isAmpleDivisor_add_principal h hg⟩
  have h' := isAmpleDivisor_add_principal h (inv_ne_zero hg)
  rwa [principalWeilDivisor_inv hg, add_neg_cancel_right] at h'

end AmpleLinearEquivalence
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
section AmpleAbsorption
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
  [CompactSpace X]

omit [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X] in
lemma prime_eq_of_specializes (p q : PrimeDivisor X) (hpq : q.1 ⤳ p.1) : p = q := by
  let : PartialOrder X := specializationOrder X
  apply Subtype.ext
  by_contra hne
  have hpq' : p.1 ≤ q.1 := hpq
  have h := Order.coheight_add_one_le (lt_of_le_of_ne hpq' hne)
  rw [p.2, q.2] at h
  norm_num at h

omit [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X] in
lemma prime_mem_divisorSupport_iff (D : WeilDivisor X) (p : PrimeDivisor X) :
    p.1 ∈ divisorSupport D ↔ D p ≠ 0 := by
  classical
  constructor
  · intro hp
    obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp hp
    have heq := prime_eq_of_specializes p q (specializes_iff_mem_closure.mpr hpq)
    exact heq ▸ Finsupp.mem_support_iff.mp hq
  · intro hp
    exact Set.mem_iUnion₂.mpr ⟨p, Finsupp.mem_support_iff.mpr hp,
      subset_closure (Set.mem_singleton p.1)⟩

omit [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X] in
lemma generic_not_divisorSupport (D : WeilDivisor X) : genericPoint X ∉ divisorSupport D := by
  let : PartialOrder X := specializationOrder X
  intro h
  obtain ⟨p, _, hp⟩ := Set.mem_iUnion₂.mp h
  have hpg : p.1 ⤳ genericPoint X := specializes_iff_mem_closure.mpr hp
  have heq : p.1 = (⊤ : X) := le_antisymm (genericPoint_specializes p.1) hpg
  have hco := p.2
  rw [heq] at hco
  simp at hco

omit [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X] in
lemma divisorSupport_nsmul (D : WeilDivisor X) {m : ℕ} (hm : 0 < m) :
    divisorSupport (m • D) = divisorSupport D := by
  classical
  unfold divisorSupport
  have hs : (m • D).support = D.support := by
    ext p
    simp [Nat.ne_zero_of_lt hm]
  rw [hs]

omit [StalkwiseNormal X] in
lemma sectionNonvanishing_pow (D : WeilDivisor X) {f : X.functionField}
    (hf : f ≠ 0) {m : ℕ} (hm : 0 < m) :
    sectionNonvanishing (m • D) (f ^ m) = sectionNonvanishing D f := by
  unfold sectionNonvanishing
  rw [principalWeilDivisor_pow hf, ← nsmul_add]
  ext x
  simp only [divisorComplement, divisorSupport_nsmul _ hm]

omit [StalkwiseNormal X] in
lemma isAmpleDivisor_nsmul {D : WeilDivisor X} (hD : IsAmpleDivisor D)
    {m : ℕ} (hm : 0 < m) : IsAmpleDivisor (m • D) := by
  refine ⟨(cartierDivisors (X := X)).nsmul_mem hD.1 m, ?_⟩
  intro x U hxU
  obtain ⟨r, hr, f, hf, hsection, haff, hx, hsub⟩ := hD.2 x U hxU
  have hcomm : r • m • D = m • r • D := by simp only [smul_comm r m D]
  have hn : sectionNonvanishing (r • m • D) (f ^ m) = sectionNonvanishing (r • D) f := by
    rw [hcomm, sectionNonvanishing_pow _ hf hm]
  refine ⟨r, hr, f ^ m, pow_ne_zero _ hf, ?_, ?_⟩
  · rw [divisorSection_iff_effective (pow_ne_zero _ hf), principalWeilDivisor_pow hf, hcomm,
      ← nsmul_add]
    intro p
    simpa only [Finsupp.smul_apply, nsmul_eq_mul] using
      mul_nonneg (Int.natCast_nonneg m) ((divisorSection_iff_effective hf).mp hsection p)
  · simpa only [hn] using And.intro haff (And.intro hx hsub)

omit [StalkwiseNormal X] in

theorem exists_ample_twist_dominating (B P : WeilDivisor X) (hB : IsAmpleDivisor B) :
    ∃ A : WeilDivisor X, IsAmpleDivisor A ∧
      ∃ f : X.functionField, f ≠ 0 ∧ IsDivisorSection (A - P) f := by
  classical
  obtain ⟨r, hr, f, hf, hsec, _, _, hsub⟩ :=
    hB.2 (genericPoint X) (divisorComplement P) (generic_not_divisorSupport P)
  let E := principalWeilDivisor f + r • B
  have hE : 0 ≤ E := (divisorSection_iff_effective hf).mp hsec
  have hsupport : ∀ p : PrimeDivisor X, P p ≠ 0 → E p ≠ 0 := by
    intro p hp he
    have hpE : p.1 ∈ sectionNonvanishing (r • B) f := by
      change p.1 ∉ divisorSupport E
      rw [prime_mem_divisorSupport_iff]
      exact fun h => h he
    have hpP := hsub hpE
    exact hpP ((prime_mem_divisorSupport_iff P p).mpr hp)
  let N := P.support.sup (fun p => (P p).natAbs) + 1
  have hN : 0 < N := Nat.succ_pos _
  have hPN : ∀ p : PrimeDivisor X, P p < (N : ℤ) := by
    intro p
    by_cases hp : P p = 0
    · simpa only [hp] using (Int.natCast_pos.mpr hN)
    have hs : (P p).natAbs ≤ P.support.sup (fun p => (P p).natAbs) :=
      Finset.le_sup (f := fun p => (P p).natAbs) (Finsupp.mem_support_iff.mpr hp)
    have hpa : P p ≤ ((P p).natAbs : ℤ) := Int.le_natAbs
    dsimp [N]
    omega
  refine ⟨(N * r) • B, isAmpleDivisor_nsmul hB (Nat.mul_pos hN hr), f ^ N,
    pow_ne_zero _ hf, ?_⟩
  rw [divisorSection_iff_effective (pow_ne_zero _ hf)]
  have heq : principalWeilDivisor (f ^ N) + ((N * r) • B - P) = N • E - P := by
    rw [principalWeilDivisor_pow hf]
    dsimp [E]
    simp only [nsmul_add, smul_smul]
    abel
  rw [heq]
  intro p
  change 0 ≤ (N : ℤ) * E p - P p
  by_cases hp : P p = 0
  · rw [hp, sub_zero]
    exact mul_nonneg (Int.natCast_nonneg _) (hE p)
  have hepos : 1 ≤ E p := by
    have hep : 0 ≤ E p := hE p
    have := hsupport p hp
    omega
  have hNm : (N : ℤ) ≤ (N : ℤ) * E p := by
    nlinarith [Int.natCast_nonneg N]
  have := hPN p
  omega

end AmpleAbsorption
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma exists_effective_ample_avoiding_primes {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (D : WeilDivisor X) (hD : IsAmpleDivisor D)
    (V : Finset (PrimeDivisor X)) :
    ∃ E : WeilDivisor X, IsAmpleDivisor E ∧ 0 ≤ E ∧ ∀ p ∈ V, E p = 0 := by
  classical
  let := schemeFieldAlgebra (.of ℂ) sX
  let I := Option {p // p ∈ V}
  let x : I → X | none => genericPoint X | some p => p.1.1
  choose m hm a ha hsec _ him _ using (fun i : I => hD.2 (x i) ⊤ (by trivial))
  let M := ∏ i : I, m i
  have hM : 0 < M := Finset.prod_pos (fun i _ => hm i)
  have hdiv (i : I) : m i ∣ M := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  let n (i : I) := M / m i
  have hn (i : I) : n i * m i = M := Nat.div_mul_cancel (hdiv i)
  let b (i : I) := a i ^ n i
  have hb (i : I) : b i ≠ 0 := pow_ne_zero _ (ha i)
  have he (i : I) : principalWeilDivisor (b i) + M • D =
      n i • (principalWeilDivisor (a i) + m i • D) := by
    rw [nsmul_add,smul_smul,hn]
    exact congrArg (fun E => E + M • D) (principalWeilDivisor_pow (ha i) (n i))
  have hsecB (i : I) : IsDivisorSection (M • D) (b i) := by
    rw [divisorSection_iff_effective (hb i),he]
    intro p
    change 0 ≤ (n i : ℤ) * (principalWeilDivisor (a i) + m i • D) p
    exact mul_nonneg (Int.natCast_nonneg _) ((divisorSection_iff_effective (ha i)).mp (hsec i) p)
  let S := divisorSectionsOver (.of ℂ) sX (M • D)
  have hS : ∀ s ∈ S, IsDivisorSection (M • D) s := fun _ hs => hs
  have hne : ∃ s ∈ S, s ≠ 0 := ⟨b none,hsecB none,hb none⟩
  have hmov : ∀ p ∈ V, ∃ s ∈ S, s ≠ 0 ∧ X.ord s p.1 + (M • D) p = 0 := by
    intro p hp
    let i : I := some ⟨p,hp⟩
    have hz : (principalWeilDivisor (a i) + m i • D) p = 0 := by
      by_contra hnz
      exact him i ((prime_mem_divisorSupport_iff _ p).mpr hnz)
    refine ⟨b i,hsecB i,hb i,?_⟩
    change (principalWeilDivisor (b i) + M • D) p = 0
    rw [he]
    simp only [Finsupp.smul_apply,hz,smul_zero]
  obtain ⟨s,hs,hsn,havoid⟩ := linearSystem_avoid_finite_of_witnesses sX (M • D) S hS hne V hmov
  refine ⟨M • D + principalWeilDivisor s,
    isAmpleDivisor_add_principal (isAmpleDivisor_nsmul hD hM) hsn,?_,?_⟩
  · intro p
    simpa only [add_comm,Finsupp.zero_apply] using ((divisorSection_iff_effective hsn).mp (hS s hs) p)
  · intro p hp
    change (M • D) p + X.ord s p.1 = 0
    rw [add_comm]
    exact havoid p hp
end NumericalDimensionOne

end OAI
