import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.ExceptionalFibers

namespace OAI

/-! Relative Negativity. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma nonconstant_curve_in_irreducible_closed_subset
    (X : ComplexProjectiveVariety) {Z : Set X.scheme}
    (hZ : IsClosed Z) (hI : IsIrreducible Z) (x : X.scheme)
    (hx : IsClosed {x}) (hxZ : x ∈ Z) (hZn : Z ≠ {x}) :
    ∃ C : CurveOn X, Set.range C.morphism ⊆ Z ∧ x ∈ Set.range C.morphism ∧
      ¬ Set.range C.morphism ⊆ {x} := by
  obtain ⟨T,i,hT,hi,hr,_⟩ := integral_closed_closure X.scheme hI.genericPoint
  let := hT
  let := hi
  have hir : Set.range i = Z := hr.trans (hI.closure_genericPoint hZ)
  obtain ⟨t,ht⟩ : x ∈ Set.range i := hir.symm ▸ hxZ
  let sT := i ≫ X.structureMap
  have : IsProper sT := inferInstance
  have htclosed : IsClosed {t} := by
    have he : i ⁻¹' {x} = {t} := by
      ext s
      simp only [Set.mem_preimage,Set.mem_singleton_iff,← ht]
      exact i.isClosedEmbedding.injective.eq_iff
    rw [← he]
    exact hx.preimage i.continuous
  have htne : ({t} : Set T) ≠ Set.univ := by
    intro he
    apply hZn
    rw [← hir,← Set.image_univ,← he,Set.image_singleton,ht]
  obtain ⟨N,j,hNI,_hNt,hsm,hpr,htj,hj⟩ :=
    smooth_proper_curve_through_point_avoiding sT t htclosed {t} htclosed htne rfl
  let := hNI
  let := hsm
  let := hpr
  let NC : ComplexProjectiveVariety := {
    scheme := N
    structureMap := j ≫ sT
    integral := hNI
    connected := inferInstance
    projective := exists_closedImmersion_of_smooth_proper_curve (j ≫ sT) }
  let C : CurveOn X := {
    curve := NC
    smooth := hsm
    morphism := j ≫ i
    overComplex := Category.assoc _ _ _ }
  refine ⟨C,?_,?_,?_⟩
  · rintro _ ⟨c,rfl⟩
    rw [← hir]
    exact ⟨j c,rfl⟩
  · obtain ⟨c,hc⟩ := htj
    exact ⟨c,by change i (j c) = x; rw [hc,ht]⟩
  · intro hsub
    apply hj
    rintro _ ⟨c,rfl⟩
    have hc : i (j c) = x := hsub (Set.mem_range_self c)
    change j c = t
    exact i.isClosedEmbedding.injective (hc.trans ht.symm)

theorem contracted_curve_through_exceptional_point
    (X : ComplexProjectiveVariety) (Y : NormalProjectiveVariety)
    (f : X.scheme ⟶ Y.scheme) [IsDominant f] [IsProper f]
    (hb : IsBirationalMorphism f) (p : PrimeDivisor X.scheme)
    (hp : 1 < Order.coheight (f p.1)) (x : X.scheme)
    (hx : IsClosed {x}) (hxp : x ∈ closure ({p.1} : Set X.scheme)) :
    ∃ C : CurveOn X, IsCurveContracted f C ∧ x ∈ Set.range C.morphism ∧
      ¬ Set.range C.morphism ⊆ {x} := by
  have : IsNoetherian X.scheme := ⟨⟩
  have hy : IsClosed {f x} := by
    simpa only [Set.image_singleton] using f.isClosedMap {x} hx
  have hF : IsClosed (f ⁻¹' {f x}) := hy.preimage f.continuous
  have hnon : ¬ IsOpen ({⟨x,rfl⟩} : Set (f ⁻¹' {f x})) := by
    intro ho
    have he := (f.fiberHomeo (f x)).symm.isOpenMap _ ho
    simp only [Set.image_singleton] at he
    exact exceptional_fiber_not_isOpen_singleton f hb p hp x hxp he
  obtain ⟨Z,hZ,hI,hxZ,hZF,hZn⟩ :=
    nonisolated_irreducible_closed_subset (f ⁻¹' {f x}) hF ⟨x,rfl⟩ hnon
  obtain ⟨C,hCZ,hxC,hCn⟩ :=
    nonconstant_curve_in_irreducible_closed_subset X hZ hI x hx hxZ hZn
  exact ⟨C,⟨f x,fun c => hZF (hCZ (Set.mem_range_self c))⟩,hxC,hCn⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma exists_cartierStalkEquation_of_effective_near
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
    {D : WeilDivisor X} (hD : IsCartierDivisor D)
    (V : X.Opens) (heff : ∀ p : PrimeDivisor X, p.1 ∈ V → 0 ≤ D p)
    (x : X) (hx : x ∈ V) : Nonempty (CartierStalkEquation D x) := by
  obtain ⟨U,_hU,hxU,g,hg,heq⟩ := hD x
  obtain ⟨W,hW,hxW,hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U ⊓ V from ⟨hxU,hx⟩)
  have : Nonempty W := ⟨⟨x,hxW⟩⟩
  have hEq : ∀ p : PrimeDivisor X, p.1 ∈ W → D p = X.ord g p.1 :=
    fun p hp => heq p (hWU hp).1
  have hsec : IsDivisorSectionOn D W (1 : X.functionField) :=
    Or.inr (fun p hp => by simpa only [order_one,zero_add] using heff p (hWU hp).2)
  obtain ⟨a,ha⟩ := (cartier_local_section_iff hW hg hEq 1).mp hsec
  exact ⟨⟨W,hxW,g,hg,hEq,X.presheaf.germ W x hxW a,by
    rw [X.algebraMap_germ_eq_germToFunctionField hxW a,ha,one_mul]⟩⟩

lemma cartierCurveDegree_nonneg_of_effective_near
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    (D : cartierDivisors (X := X.scheme)) (C : CurveOn X)
    (V : X.scheme.Opens) (hCV : Set.range C.morphism ⊆ V)
    (heff : ∀ p : PrimeDivisor X.scheme, p.1 ∈ V → 0 ≤ D.1 p)
    (hη : C.morphism (genericPoint C.curve.scheme) ∉ divisorSupport D.1) :
    0 ≤ cartierCurveDegree D C := by
  classical
  let E := pulledCartierRepresentative C D.1 D.2
  obtain ⟨t,ht,htord⟩ := (pulledCartierRepresentative_spec C D.1 D.2).exists_effective_local_orders
    C.morphism hη
  let F := principalWeilDivisor t + E
  have hF (q : PrimeDivisor C.curve.scheme) : 0 ≤ F q := by
    obtain ⟨b⟩ := exists_cartierStalkEquation_of_effective_near D.2 V heff
      (C.morphism q.1) (hCV (Set.mem_range_self q.1))
    obtain ⟨hb,ho⟩ := htord q b
    rw [show F q = _ from ho,NumericalDimensionOneCurveAux.scheme_order_of_stalk_element q.1 q.2 _ hb]
    positivity
  have hdeg : 0 ≤ complexWeilDegree F := Finset.sum_nonneg fun q _ => hF q
  unfold F complexWeilDegree at hdeg
  rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)] at hdeg
  change 0 ≤ complexWeilDegree (principalWeilDivisor t) + cartierCurveDegree D C at hdeg
  rwa [principal_degree_zero C.curve C.smooth t,zero_add] at hdeg
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma cartierCurveDegree_pos_of_nonconstant
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    (D : cartierDivisors (X := X.scheme)) (hD : IsAmpleDivisor D.1)
    (C : CurveOn X) (x : X.scheme) (hx : IsClosed {x})
    (hxC : x ∈ Set.range C.morphism) (hn : ¬ Set.range C.morphism ⊆ {x}) :
    0 < cartierCurveDegree D C := by
  let : SmoothOfRelativeDimension 1 C.curve.structureMap := C.smooth
  have : IsNoetherian C.curve.scheme := ⟨⟩
  have hη : C.morphism (genericPoint C.curve.scheme) ≠ x := by
    intro he
    apply hn
    rintro _ ⟨c,rfl⟩
    exact ((genericPoint_specializes c).map C.morphism.continuous).mem_closed hx he
  have hpre : (C.morphism ⁻¹' {x}).Nonempty := hxC
  obtain ⟨c,hcx,hcc⟩ := (hx.preimage C.morphism.continuous).exists_closed_singleton hpre
  let p : PrimeDivisor C.curve.scheme :=
    ⟨c,coheight_eq_of_smooth_closed C.curve.structureMap 1 c hcc⟩
  exact cartierCurveDegree_positive_of_ample D hD C p (hcx ▸ hη)

theorem projective_cartier_negativity
    (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    (Y : NormalProjectiveVariety) (f : X.scheme ⟶ Y.scheme)
    [IsDominant f] [IsProper f] (hb : IsBirationalMorphism f)
    (D : cartierDivisors (X := X.scheme))
    (hexc : ∀ p : PrimeDivisor X.scheme, D.1 p ≠ 0 → 1 < Order.coheight (f p.1))
    (hanti : ∀ C : CurveOn X, IsCurveContracted f C → cartierCurveDegree D C ≤ 0) :
    0 ≤ D.1 := by
  classical
  have : IsNoetherian X.scheme := ⟨⟩
  let : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.structureMap
  intro p₀
  by_contra hn₀
  have hn : D.1 p₀ < 0 := lt_of_not_ge hn₀
  obtain ⟨J,hJ⟩ := exists_ampleDivisor_of_projective X
  obtain ⟨E,hEa,hEe,_hEz⟩ := exists_effective_ample_avoiding_primes X.structureMap J hJ D.1.support
  let EC : cartierDivisors (X := X.scheme) := ⟨E,hEa.1⟩
  let absD : WeilDivisor X.scheme := D.1.mapRange (fun a : ℤ => |a|) (abs_zero : |(0 : ℤ)| = 0)
  have habs (p : PrimeDivisor X.scheme) : absD p = |D.1 p| := rfl
  have hJE : 0 ≤ E + absD := fun p => add_nonneg (hEe p) (abs_nonneg (D.1 p))
  obtain ⟨U,hp₀U,b,hb0,hbD⟩ := exists_birational_local_equation_dominating f hb (E+absD) hJE (f p₀.1)
  let P : cartierDivisors (X := X.scheme) := ⟨principalWeilDivisor b,isCartierDivisor_principal hb0⟩
  let B : cartierDivisors (X := X.scheme) := P - EC
  have hB (p : PrimeDivisor X.scheme) (hp : f p.1 ∈ U) : |D.1 p| ≤ B.1 p := by
    have h := hbD p hp
    change E p + |D.1 p| ≤ X.scheme.ord b p.1 at h
    change |D.1 p| ≤ X.scheme.ord b p.1 - E p
    linarith
  have hBn (p : PrimeDivisor X.scheme) (hp : f p.1 ∈ U) : 0 ≤ B.1 p :=
    (abs_nonneg _).trans (hB p hp)
  have hBp (p : PrimeDivisor X.scheme) (hp : f p.1 ∈ U) (hd : D.1 p < 0) : 0 < B.1 p := by
    have h := hB p hp
    rw [abs_of_neg hd] at h
    linarith
  let S := D.1.support.filter (fun p => D.1 p < 0 ∧ f p.1 ∈ U)
  have hS : S.Nonempty := ⟨p₀,Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hn.ne,hn,hp₀U⟩⟩
  obtain ⟨p,hp,hmax⟩ := S.exists_max_image (fun p => (-D.1 p : ℚ) / B.1 p) hS
  have hp' := (Finset.mem_filter.mp hp).2
  have hbp : 0 < B.1 p := hBp p hp'.2 hp'.1
  let A : cartierDivisors (X := X.scheme) := (B.1 p) • D + (-D.1 p) • B
  have hA (q : PrimeDivisor X.scheme) (hq : f q.1 ∈ U) : 0 ≤ A.1 q := by
    change 0 ≤ B.1 p * D.1 q + (-D.1 p) * B.1 q
    by_cases hdq : D.1 q < 0
    · have hqS : q ∈ S := Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hdq.ne,hdq,hq⟩
      have hrat := hmax q hqS
      have hpQ : (0 : ℚ) < B.1 p := by exact_mod_cast hbp
      have hqQ : (0 : ℚ) < B.1 q := by exact_mod_cast hBp q hq hdq
      have hc := (div_le_div_iff₀ hqQ hpQ).mp hrat
      have hc' : (-D.1 q) * B.1 p ≤ (-D.1 p) * B.1 q := by exact_mod_cast hc
      nlinarith
    · exact add_nonneg (mul_nonneg hbp.le (le_of_not_gt hdq))
        (mul_nonneg (neg_nonneg.mpr hp'.1.le) (hBn q hq))
  have hAp : A.1 p = 0 := by
    change B.1 p * D.1 p + (-D.1 p) * B.1 p = 0
    ring
  let V : X.scheme.Opens := (f ⁻¹ᵁ U) ⊓ divisorComplement A.1
  have hpV : p.1 ∈ V := ⟨hp'.2,by
    change p.1 ∉ divisorSupport A.1
    rw [prime_mem_divisorSupport_iff]
    exact not_ne_iff.mpr hAp⟩
  have hloc : IsLocallyClosed (closure ({p.1} : Set X.scheme) ∩ (V : Set X.scheme)) :=
    isClosed_closure.isLocallyClosed.inter V.isOpen.isLocallyClosed
  obtain ⟨x,⟨hxp,hxV⟩,hx⟩ := nonempty_inter_closedPoints
    (show (closure ({p.1} : Set X.scheme) ∩ (V : Set X.scheme)).Nonempty from
      ⟨p.1,subset_closure (Set.mem_singleton p.1),hpV⟩) hloc
  obtain ⟨C,hCf,hxC,hCn⟩ := contracted_curve_through_exceptional_point X Y f hb p
    (hexc p hp'.1.ne) x hx hxp
  have hEC : 0 < cartierCurveDegree EC C :=
    cartierCurveDegree_pos_of_nonconstant EC hEa C x hx hxC hCn
  obtain ⟨y,hy⟩ := hCf
  obtain ⟨c,hcx⟩ := hxC
  have hCV : Set.range C.morphism ⊆ (f ⁻¹ᵁ U : X.scheme.Opens) := by
    rintro _ ⟨d,rfl⟩
    change f (C.morphism d) ∈ U
    rw [hy d,← hy c,hcx]
    exact hxV.1
  have hηA : C.morphism (genericPoint C.curve.scheme) ∉ divisorSupport A.1 := by
    intro hm
    have hxc := ((genericPoint_specializes c).map C.morphism.continuous).mem_closed
      (isClosed_divisorSupport A.1) hm
    rw [hcx] at hxc
    exact hxV.2 hxc
  have hAC := cartierCurveDegree_nonneg_of_effective_near A C (f ⁻¹ᵁ U) hCV hA hηA
  have hDC := hanti C ⟨y,hy⟩
  have hPC : cartierCurveDegree P C = 0 := cartierCurveDegree_principal C b hb0 P.2
  have hBC : cartierCurveDegree B C = -cartierCurveDegree EC C := by
    change cartierCurveDegreeHom C (P-EC) = _
    rw [map_sub]
    change cartierCurveDegree P C - cartierCurveDegree EC C = _
    rw [hPC,zero_sub]
  have hAeq : cartierCurveDegree A C = B.1 p * cartierCurveDegree D C +
      (-D.1 p) * cartierCurveDegree B C := by
    change cartierCurveDegreeHom C ((B.1 p) • D + (-D.1 p) • B) = _
    rw [map_add,map_zsmul,map_zsmul,zsmul_eq_mul,zsmul_eq_mul]
    rfl
  rw [hAeq,hBC] at hAC
  have hDC' : B.1 p * cartierCurveDegree D C ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbp.le hDC
  have hEC' : 0 < (-D.1 p) * cartierCurveDegree EC C := mul_pos (neg_pos.mpr hp'.1) hEC
  nlinarith
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

theorem projective_qCartier_negativity
    (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    (Y : NormalProjectiveVariety) (f : X.scheme ⟶ Y.scheme)
    [IsDominant f] [IsProper f] (hb : IsBirationalMorphism f)
    (D : QWeilDivisor X.scheme) (hD : IsQCartierDivisor D)
    (hexc : ∀ p : PrimeDivisor X.scheme, D p ≠ 0 → 1 < Order.coheight (f p.1))
    (hanti : ∀ C : CurveOn X, IsCurveContracted f C → qCartierCurveDegree D hD C ≤ 0) :
    0 ≤ D := by
  let M := chooseCartierMultiple hD
  have hex : ∀ p : PrimeDivisor X.scheme, M.divisor.1 p ≠ 0 →
      1 < Order.coheight (f p.1) := by
    intro p hp
    apply hexc p
    have hp' : p ∈ M.divisor.1.support := Finsupp.mem_support_iff.mpr hp
    rw [M.support_eq] at hp'
    exact Finsupp.mem_support_iff.mp hp'
  have hpos := projective_cartier_negativity X Y f hb M.divisor hex (by
    intro C hC
    exact M.degree_nonpos_of_qDegree_nonpos hD C (hanti C hC))
  intro p
  exact (M.coeff_nonneg_iff p).mp (hpos p)

theorem higher_dimensional_negativity_missing {n : ℕ} (_hn : 3 ≤ n)
    (W : ComplexProjectiveVariety) [StalkwiseNormal W.scheme]
    (_hW : IsSmoothNfold W n) (Y : NormalProjectiveVariety)
    (q : W.scheme ⟶ Y.scheme) [IsDominant q] [IsProper q]
    (hbir : IsBirationalMorphism q)
    (_hbase : q ≫ Y.structureMap = W.structureMap)
    (D : QWeilDivisor W.scheme) (hD : IsQCartierDivisor D)
    (hexc : ∀ F : PrimeDivisor W.scheme, D F ≠ 0 → 1 < Order.coheight (q F.1))
    (hanti : ∀ C : CurveOn W, IsCurveContracted q C → qCartierCurveDegree D hD C ≤ 0) :
    0 ≤ D := by
  exact projective_qCartier_negativity W Y q hbir D hD hexc hanti

lemma IsCanonicalMMPStep.effective_comparison_on_common_model {n : ℕ}
    {X Y : CanonicalModel n} {φ : X.scheme.PartialIso Y.scheme}
    (hstep : IsCanonicalMMPStep X Y φ)
    (W : ComplexProjectiveVariety) [StalkwiseNormal W.scheme]
    (hW : IsSmoothNfold W n)
    (p : W.scheme ⟶ X.scheme) (q : W.scheme ⟶ Y.scheme)
    [IsDominant p] [IsDominant q] [IsProper p] [IsProper q]
    (hp : p ≫ X.structureMap = W.structureMap) (hq : q ≫ Y.structureMap = W.structureMap)
    (θ : W.scheme.PartialIso X.scheme) (hθp : θ.IsOver p (𝟙 X.scheme))
    (hθq : (θ.trans φ).IsOver q (𝟙 Y.scheme)) :
    ∃ P Q : QWeilDivisor W.scheme,
      IsQCartierPullback p (rationalWeilDivisor X.canonical) P ∧
      IsQCartierPullback q (rationalWeilDivisor Y.canonical) Q ∧
      0 ≤ P-Q ∧
      (∀ F : PrimeDivisor W.scheme, (P-Q) F ≠ 0 → 1 < Order.coheight (q F.1)) ∧
      (∀ F : PrimeDivisor W.scheme, Order.coheight (p F.1) = 1 →
        1 < Order.coheight (q F.1) → 0 < (P-Q) F) := by
  obtain ⟨P,Q,hP,hQ,hD,hex,hstrict,hanti⟩ :=
    hstep.comparison_boundary_on_common_model W hW p q hp hq θ hθp hθq
  exact ⟨P,Q,hP,hQ,projective_qCartier_negativity W Y.toNormalProjectiveVariety q
    ⟨θ.trans φ,hθq⟩ (P-Q) hD hex hanti,hex,hstrict⟩
end NumericalDimensionOne

end OAI
