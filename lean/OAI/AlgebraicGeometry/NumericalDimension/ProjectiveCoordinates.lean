import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.AmpleAbsorption

namespace OAI

/-! Projective Coordinates. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma ord_positive_of_nonunit {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [StalkwiseNormal X] (p : PrimeDivisor X) (a : X.presheaf.stalk p.1)
    (ha : a ≠ 0) (hu : ¬ IsUnit a) :
    0 < X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField a) p.1 := by
  have := dvr_at_prime_divisor p
  have ha' : algebraMap (X.presheaf.stalk p.1) X.functionField a ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective (X.presheaf.stalk p.1) X.functionField).ne ha
  have hn := (ord_nonnegative_iff_regular p _ ha').mpr ⟨a,rfl⟩
  apply lt_of_le_of_ne hn
  intro hz
  have he := (X.ord_eq_iff p.2 ha').mp hz.symm
  change Ring.ordFrac (X.presheaf.stalk p.1) _ = 1 at he
  exact hu (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing.mpr he)
lemma pullback_section_orders {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal X]
    (f : X ⟶ Y) [IsDominant f] (U : Y.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (a : Γ(Y,U)) (ha : a ≠ 0) :
    let b := dominantFunctionFieldMap f (Y.germToFunctionField U a)
    b ≠ 0 ∧ ∀ (p : PrimeDivisor X) (hp : f p.1 ∈ U),
      0 ≤ X.ord b p.1 ∧ (a ∈ (hU.primeIdealOf ⟨f p.1,hp⟩).asIdeal →
        0 < X.ord b p.1) := by
  dsimp only
  have hy : Y.germToFunctionField U a ≠ 0 := by
    simpa only [map_zero] using (Y.germToFunctionField_injective U).ne ha
  have hb := (map_ne_zero (dominantFunctionFieldMap f)).mpr hy
  refine ⟨hb,?_⟩
  intro p hp
  let r := (Y.presheaf.germ U (f p.1) hp).hom a
  let t := f.stalkMap p.1 r
  have ht : algebraMap (X.presheaf.stalk p.1) X.functionField t =
      dominantFunctionFieldMap f (Y.germToFunctionField U a) := by
    rw [← dominantFunctionFieldMap_algebraMap]
    rw [Y.algebraMap_germ_eq_germToFunctionField hp a]
  refine ⟨(ord_nonnegative_iff_regular p _ hb).mpr ⟨t,ht⟩,?_⟩
  intro ham
  have hrm : r ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (f p.1)) := by
    rw [hU.primeIdealOf_eq_map_closedPoint] at ham
    exact ham
  have htm : t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p.1) :=
    map_nonunit (f.stalkMap p.1).hom r hrm
  have htn : t ≠ 0 := by intro he; exact hb (ht.symm.trans (by rw [he,map_zero]))
  rw [← ht]
  exact ord_positive_of_nonunit p t htn htm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma exists_affine_nonzero_vanishing_section {Y : Scheme} [IsIntegral Y]
    (Z : Set Y) (hZ : IsClosed Z) (hη : genericPoint Y ∉ Z)
    (U : Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set Y).Nonempty) :
    ∃ a : Γ(Y,U), a ≠ 0 ∧ ∀ x : U, x.1 ∈ Z → a ∈ (hU.primeIdealOf x).asIdeal := by
  classical
  have hηU : genericPoint Y ∈ U :=
    (genericPoint_spec Y).mem_open_set_iff U.isOpen |>.mpr (by simpa using hne)
  let η : U := ⟨genericPoint Y,hηU⟩
  let T : Set (PrimeSpectrum Γ(Y,U)) := hU.fromSpec ⁻¹' Z
  have hT : IsClosed T := hZ.preimage hU.fromSpec.continuous
  have hnot : hU.primeIdealOf η ∉ PrimeSpectrum.zeroLocus
      (PrimeSpectrum.vanishingIdeal T) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,hT.closure_eq]
    change hU.fromSpec (hU.primeIdealOf η) ∉ Z
    rw [hU.fromSpec_primeIdealOf]
    exact hη
  rw [PrimeSpectrum.mem_zeroLocus] at hnot
  obtain ⟨a,ha,han⟩ := Set.not_subset.mp hnot
  refine ⟨a,fun he => han (he ▸ Ideal.zero_mem _),?_⟩
  intro x hx
  apply (PrimeSpectrum.mem_vanishingIdeal T a).mp ha (hU.primeIdealOf x)
  change hU.fromSpec (hU.primeIdealOf x) ∈ Z
  rwa [hU.fromSpec_primeIdealOf]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma exists_birational_local_equation {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal X] [CompactSpace X]
    (f : X ⟶ Y) [IsDominant f] [IsProper f] (hf : IsBirationalMorphism f)
    (J : WeilDivisor X) (z : Y) :
    ∃ (U : Y.Opens), z ∈ U ∧ ∃ b : X.functionField, b ≠ 0 ∧
      ∀ p : PrimeDivisor X, f p.1 ∈ U → 0 ≤ X.ord b p.1 ∧
        (J p ≠ 0 → 0 < X.ord b p.1) := by
  have hZ : IsClosed (f '' divisorSupport J) :=
    f.isClosedMap _ (isClosed_divisorSupport J)
  have hη : genericPoint Y ∉ f '' divisorSupport J := by
    rintro ⟨x,hx,hfx⟩
    have he := birational_generic_fiber f hf x hfx
    exact generic_not_divisorSupport J (he ▸ hx)
  obtain ⟨U,hU,hzU,_⟩ := exists_isAffineOpen_mem_and_subset
    (show z ∈ (⊤ : Y.Opens) from trivial)
  have : Nonempty U := ⟨⟨z,hzU⟩⟩
  obtain ⟨a,ha,hvan⟩ := exists_affine_nonzero_vanishing_section
    (f '' divisorSupport J) hZ hη U hU ⟨z,hzU⟩
  have hh := pullback_section_orders f U hU a ha
  refine ⟨U,hzU,_,hh.1,?_⟩
  intro p hp
  refine ⟨(hh.2 p hp).1,?_⟩
  intro hJ
  apply (hh.2 p hp).2
  exact hvan ⟨f p.1,hp⟩ ⟨p.1,(prime_mem_divisorSupport_iff J p).mpr hJ,rfl⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma order_pow {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (a : X.functionField) (ha : a ≠ 0) (n : ℕ) (x : X) :
    X.ord (a^n) x = (n : ℤ) * X.ord a x := by
  induction n with
  | zero => simp only [pow_zero,order_one,Nat.cast_zero,zero_mul]
  | succ n ih =>
    rw [pow_succ,X.ord_mul (pow_ne_zero n ha) ha,ih]
    push_cast
    ring
lemma exists_birational_local_equation_dominating {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal X] [CompactSpace X]
    (f : X ⟶ Y) [IsDominant f] [IsProper f] (hf : IsBirationalMorphism f)
    (J : WeilDivisor X) (hJ : 0 ≤ J) (z : Y) :
    ∃ (U : Y.Opens), z ∈ U ∧ ∃ b : X.functionField, b ≠ 0 ∧
      ∀ p : PrimeDivisor X, f p.1 ∈ U → J p ≤ X.ord b p.1 := by
  classical
  obtain ⟨U,hz,a,ha,hh⟩ := exists_birational_local_equation f hf J z
  let N := J.support.sup (fun p => (J p).toNat)
  refine ⟨U,hz,a^N,pow_ne_zero N ha,?_⟩
  intro p hp
  rw [order_pow a ha]
  by_cases hj : J p = 0
  · rw [hj]
    exact mul_nonneg (Int.natCast_nonneg N) (hh p hp).1
  · have hle : (J p).toNat ≤ N := Finset.le_sup (f := fun q => (J q).toNat) (Finsupp.mem_support_iff.mpr hj)
    have hle' : J p ≤ (N : ℤ) := by
      rw [← Int.toNat_of_nonneg (show 0 ≤ J p from hJ p)]
      exact_mod_cast hle
    have ho : 1 ≤ X.ord a p.1 := (hh p hp).2 hj
    nlinarith [Int.natCast_nonneg N]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma exists_positive_exceptional_weight (X : ComplexProjectiveVariety)
    [StalkwiseNormal X.scheme] (hX : IsSmoothNfold X 2)
    {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X.scheme ⟶ Y) [IsDominant f] [IsProper f] (hf : IsBirationalMorphism f)
    (J : WeilDivisor X.scheme) (hJ : IsAmpleDivisor J)
    (V : Finset (PrimeDivisor X.scheme))
    (hV : ∀ p ∈ V, ∀ x ∈ closure ({p.1} : Set X.scheme), f x = f p.1) :
    letI : SmoothOfRelativeDimension 2 X.structureMap := hX
    ∃ v : V → ℤ, (∀ p, 0 < v p) ∧
      ∀ p : V, (∑ q : V, surfacePrimePair X.structureMap p.1 q.1 * v q) < 0 := by
  classical
  let : SmoothOfRelativeDimension 2 X.structureMap := hX
  obtain ⟨E,hEample,hE,hEzero⟩ := exists_effective_ample_avoiding_primes X.structureMap J hJ V
  have hx (z : Y) := exists_birational_local_equation_dominating f hf E hE z
  choose U hU a ha hd using hx
  let v (p : V) : ℤ := X.scheme.ord (a (f p.1.1)) p.1.1
  have hv (p : V) : 0 ≤ v p := by
    have hh := hd (f p.1.1) p.1 (hU (f p.1.1))
    rw [hEzero p.1 p.2] at hh
    exact hh
  have hr (p : V) : (∑ q : V, surfacePrimePair X.structureMap p.1 q.1 * v q) < 0 := by
    have hh := surface_exceptional_row_le X.structureMap f V p.1 p.2 (hV p.1 p.2)
      (U (f p.1.1)) (hU (f p.1.1)) E hEzero (a (f p.1.1)) (ha (f p.1.1)) (hd (f p.1.1))
    have he : 0 < surfaceWeilPrimeDegreeHom X.structureMap p.1 E :=
      surfaceCartierPrimeDegree_positive_of_ample X hX ⟨E,hEample.1⟩ hEample p.1
    have hsum : (∑ q : V, surfacePrimePair X.structureMap p.1 q.1 * v q) =
        ∑ q ∈ V, X.scheme.ord (a (f p.1.1)) q.1 * surfacePrimePair X.structureMap p.1 q := by
      rw [Finset.sum_subtype V (fun _ => Iff.rfl)]
      apply Finset.sum_congr rfl
      intro q _
      by_cases heq : f q.1.1 = f p.1.1
      · simp only [v,heq,mul_comm]
      · rw [surfacePrimePair_zero_distinct_fibers X.structureMap f p.1 q.1
          (hV p.1 p.2) (hV q.1 q.2) (Ne.symm heq),zero_mul,mul_zero]
    rw [hsum]
    linarith
  refine ⟨v,?_,hr⟩
  intro p
  by_contra hp
  have hz : v p = 0 := le_antisymm (le_of_not_gt hp) (hv p)
  have hn : 0 ≤ ∑ q : V, surfacePrimePair X.structureMap p.1 q.1 * v q := by
    apply Finset.sum_nonneg
    intro q _
    by_cases hq : q = p
    · subst q
      rw [hz,mul_zero]
    · exact mul_nonneg (surfacePrimePair_nonneg X.structureMap p.1 q.1
        (fun hh => hq (Subtype.ext hh.symm))) (hv q)
  linarith [hr p]
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
lemma surfaceIntersection_supported_eq (V : Finset (PrimeDivisor X))
    (F : WeilDivisor X) (hF : F.support ⊆ V) :
    surfaceIntersection sX (smoothSurfaceWeilCartier sX F) (smoothSurfaceWeilCartier sX F) =
      ∑ p : V, ∑ q : V, surfacePrimePair sX p.1 q.1 * F p.1 * F q.1 := by
  classical
  change F.sum (fun p n => n * surfaceCartierPrimeDegree sX (smoothSurfaceWeilCartier sX F) p) = _
  rw [Finsupp.sum_of_support_subset F hF (fun p n => n * surfaceCartierPrimeDegree sX (smoothSurfaceWeilCartier sX F) p) (fun _ _ => zero_mul _),
    Finset.sum_subtype V (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro p _
  change F p.1 * surfaceCartierPrimeDegree sX (smoothSurfaceWeilCartier sX F) p.1 = _
  rw [surfaceDegree_eq_pair_sum,Finsupp.sum_of_support_subset F hF (fun q n => n * surfacePrimePair sX p.1 q) (fun _ _ => zero_mul _),
    Finset.sum_subtype V (fun _ => Iff.rfl),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
lemma weighted_symmetric_quadratic_le {ι : Type*} [Fintype ι]
    (B : ι → ι → ℝ) (hB : ∀ i j, B i j = B j i)
    (hpos : ∀ i j, i ≠ j → 0 ≤ B i j) (v y : ι → ℝ) (hv : ∀ i, 0 < v i) :
    (∑ i, ∑ j, B i j * v i * v j * y i * y j) ≤
      ∑ i, (v i * (y i)^2) * (∑ j, B i j * v j) := by
  have hp (i j : ι) :
      2 * (B i j * v i * v j * y i * y j) ≤
        B i j * v i * v j * ((y i)^2 + (y j)^2) := by
    by_cases he : i = j
    · subst j
      exact le_of_eq (by ring)
    · have ha := mul_nonneg (mul_nonneg (hpos i j he) (hv i).le) (hv j).le
      have hs := mul_nonneg ha (sq_nonneg (y i-y j))
      nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hp i j))
  have hleft : (∑ i, ∑ j, 2 * (B i j * v i * v j * y i * y j)) =
      2 * (∑ i, ∑ j, B i j * v i * v j * y i * y j) := by
    simp only [Finset.mul_sum]
  have hfirst : (∑ i, ∑ j, B i j * v i * v j * (y i)^2) =
      ∑ i, (v i*(y i)^2)*(∑ j, B i j*v j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsecond : (∑ i, ∑ j, B i j * v i * v j * (y j)^2) =
      ∑ i, (v i*(y i)^2)*(∑ j, B i j*v j) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ∑ j, B i j * v i * v j * (y i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hB j i]
        ring
      _ = _ := hfirst
  have hright : (∑ i, ∑ j, B i j * v i * v j * ((y i)^2+(y j)^2)) =
      2 * (∑ i, (v i*(y i)^2)*(∑ j, B i j*v j)) := by
    simp only [mul_add,Finset.sum_add_distrib]
    rw [hfirst,hsecond]
    ring
  rw [hleft,hright] at hh
  linarith
lemma negative_row_quadratic_bound {ι : Type*} [Fintype ι]
    (B : ι → ι → ℝ) (hB : ∀ i j, B i j = B j i)
    (hpos : ∀ i j, i ≠ j → 0 ≤ B i j) (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hrow : ∀ i, (∑ j, B i j * v j) < 0) (e : ι) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ι → ℝ,
      (∑ i, ∑ j, B i j * x i * x j) ≤ -ε * (x e)^2 := by
  classical
  let r (i : ι) := ∑ j, B i j * v j
  refine ⟨-r e / v e,div_pos (neg_pos.mpr (hrow e)) (hv e),?_⟩
  intro x
  have hh := weighted_symmetric_quadratic_le B hB hpos v (fun i => x i / v i) hv
  have he (i j : ι) : B i j * v i * v j * (x i / v i) * (x j / v j) =
      B i j * x i * x j := by
    field_simp [ne_of_gt (hv i),ne_of_gt (hv j)]
  simp_rw [he] at hh
  have hb : (∑ i, (v i*(x i/v i)^2)*r i) ≤ (v e*(x e/v e)^2)*r e := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
    have hn : (∑ i ∈ Finset.univ.erase e, (v i*(x i/v i)^2)*r i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hv i).le (sq_nonneg _)) (hrow i).le
    linarith
  have hend : (v e*(x e/v e)^2)*r e = -(-r e/v e)*(x e)^2 := by
    field_simp [ne_of_gt (hv e)]
  rw [hend] at hb
  exact hh.trans hb
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma partialIso_extending_injOn {X Y : Scheme} (f : X ⟶ Y)
    (φ : X.PartialIso Y) (hφ : φ.IsOver f (𝟙 Y)) :
    Set.InjOn f (φ.source : Set X) := by
  have he : φ.iso.hom ≫ φ.target.ι = φ.source.ι ≫ f := by simpa only [Scheme.PartialIso.IsOver,Category.comp_id] using hφ
  have hi : Function.Injective (φ.iso.hom ≫ φ.target.ι) :=
    (φ.iso.hom ≫ φ.target.ι).isOpenEmbedding.injective
  intro x hx y hy hxy
  have h : (⟨x,hx⟩ : φ.source) = ⟨y,hy⟩ := by
    apply hi
    change (φ.iso.hom ≫ φ.target.ι) ⟨x,hx⟩ = (φ.iso.hom ≫ φ.target.ι) ⟨y,hy⟩
    rw [he]
    exact hxy
  exact congrArg Subtype.val h

lemma finite_contracted_primes (X : ComplexProjectiveVariety) (hX : IsSmoothNfold X 2)
    {Y : Scheme} (f : X.scheme ⟶ Y) (hf : IsBirationalMorphism f) :
    {p : PrimeDivisor X.scheme | ∀ x ∈ closure ({p.1} : Set X.scheme), f x = f p.1}.Finite := by
  let : SmoothOfRelativeDimension 2 X.structureMap := hX
  let : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.structureMap
  obtain ⟨φ,hφ⟩ := hf
  have hn : (φ.source : Set X.scheme)ᶜ ≠ Set.univ := by
    intro he
    have hne := φ.dense_source.nonempty
    obtain ⟨x,hx⟩ := hne
    have hh : x ∈ (φ.source : Set X.scheme)ᶜ := by rw [he]; trivial
    exact hh hx
  apply (finite_primeDivisors_in_closed φ.source.isOpen.isClosed_compl hn).subset
  intro p hp hpin
  have hne : ((φ.source : Set X.scheme) ∩ closure ({p.1} : Set X.scheme)).Nonempty :=
    ⟨p.1,hpin,subset_closure (Set.mem_singleton p.1)⟩
  obtain ⟨q,hq,hclosed⟩ := nonempty_inter_closedPoints hne
    (φ.source.isOpen.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have hqp : q = p.1 := partialIso_extending_injOn f φ hφ hq.1 hpin (hp q hq.2)
  rw [hqp] at hclosed
  have hh := coheight_eq_of_smooth_closed X.structureMap 2 p.1 hclosed
  rw [p.2] at hh
  norm_num at hh
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma exceptional_uniform_negative_square (X : ComplexProjectiveVariety)
    [StalkwiseNormal X.scheme] (hX : IsSmoothNfold X 2)
    {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X.scheme ⟶ Y) [IsDominant f] [IsProper f] (hf : IsBirationalMorphism f)
    (J : WeilDivisor X.scheme) (hJ : IsAmpleDivisor J)
    (e : PrimeDivisor X.scheme)
    (he : ∀ x ∈ closure ({e.1} : Set X.scheme), f x = f e.1) :
    letI : SmoothOfRelativeDimension 2 X.structureMap := hX
    ∃ ε : ℝ, 0 < ε ∧ ∀ F : WeilDivisor X.scheme,
      (∀ p ∈ F.support, ∀ x ∈ closure ({p.1} : Set X.scheme), f x = f p.1) →
      (surfaceIntersection X.structureMap (smoothSurfaceWeilCartier X.structureMap F)
        (smoothSurfaceWeilCartier X.structureMap F) : ℝ) ≤ -ε * (F e : ℝ)^2 := by
  classical
  let : SmoothOfRelativeDimension 2 X.structureMap := hX
  let V := (finite_contracted_primes X hX f hf).toFinset
  have hV (p : PrimeDivisor X.scheme) : p ∈ V ↔
      ∀ x ∈ closure ({p.1} : Set X.scheme), f x = f p.1 := Set.Finite.mem_toFinset _
  obtain ⟨v,hv,hr⟩ := exists_positive_exceptional_weight X hX f hf J hJ V
    (fun p hp => (hV p).mp hp)
  let B (p q : V) : ℝ := surfacePrimePair X.structureMap p.1 q.1
  have hB (p q : V) : B p q = B q p := by
    dsimp only [B]
    exact_mod_cast surfacePrimePair_comm X.structureMap p.1 q.1
  have hpos (p q : V) (hpq : p ≠ q) : 0 ≤ B p q := by
    dsimp only [B]
    exact_mod_cast surfacePrimePair_nonneg X.structureMap p.1 q.1
      (fun hh => hpq (Subtype.ext hh))
  have hvr (p : V) : 0 < (v p : ℝ) := by exact_mod_cast hv p
  have hr' (p : V) : (∑ q : V, B p q * (v q : ℝ)) < 0 := by
    dsimp only [B]
    exact_mod_cast hr p
  obtain ⟨ε,hε,hbound⟩ := negative_row_quadratic_bound B hB hpos
    (fun p => (v p : ℝ)) hvr hr' ⟨e,(hV e).mpr he⟩
  refine ⟨ε,hε,?_⟩
  intro F hF
  have hs : F.support ⊆ V := fun p hp => (hV p).mpr (hF p hp)
  rw [surfaceIntersection_supported_eq X.structureMap V F hs]
  push_cast
  exact hbound (fun p => (F p.1 : ℝ))
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma surface_fixed_square_from_ample (X : ComplexProjectiveVariety)
    [StalkwiseNormal X.scheme] (hX : IsSmoothNfold X 2)
    {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X.scheme ⟶ Y) [IsDominant f] [IsProper f] (hf : IsBirationalMorphism f)
    (J : WeilDivisor X.scheme) (hJ : IsAmpleDivisor J)
    (e : PrimeDivisor X.scheme)
    (he : ∀ x ∈ closure ({e.1} : Set X.scheme), f x = f e.1)
    {ι : Type*} (D : ι → WeilDivisor Y) (P : ι → WeilDivisor X.scheme)
    (hP : ∀ j, IsCartierPullback f (D j) (P j)) (k : ι → ℕ) (hk : ∀ j, 0 < k j)
    (S : ι → letI := schemeFieldAlgebra (.of ℂ) X.structureMap; Submodule ℂ X.scheme.functionField)
    (hS : ∀ j, ∀ s ∈ S j, IsDivisorSection (P j) s)
    (hne : ∀ j, ∃ s ∈ S j, s ≠ 0)
    (Z : ι → Finset Y) (hZ : ∀ j z, z ∈ Z j → IsClosed ({z} : Set Y))
    (hgen : ∀ j x, f x ∉ Z j → ∃ s ∈ S j, s ≠ 0 ∧ x ∈ sectionNonvanishing (P j) s)
    (c : ℝ) (hc : 0 < c)
    (hcoeff : ∀ j, c * (k j : ℝ) ≤ (fixedPart (P j) (S j) (hS j) (hne j) e : ℝ)) :
    letI : SmoothOfRelativeDimension 2 X.structureMap := hX
    ∃ ε : ℝ, 0 < ε ∧ ∀ j,
      ε * (k j : ℝ)^2 ≤ (surfaceIntersection X.structureMap
        (smoothSurfaceWeilCartier X.structureMap (P j))
        (smoothSurfaceWeilCartier X.structureMap (P j)) : ℝ) := by
  let : SmoothOfRelativeDimension 2 X.structureMap := hX
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  let H := smoothSurfaceWeilCartier X.structureMap
  let B := surfaceIntersectionHom X.structureMap
  obtain ⟨a,ha,hneg⟩ := exceptional_uniform_negative_square X hX f hf J hJ e he
  refine ⟨a*c^2,mul_pos ha (sq_pos_of_pos hc),?_⟩
  intro j
  let F := fixedPart (P j) (S j) (hS j) (hne j)
  have hF (p : PrimeDivisor X.scheme) (hp : p ∈ F.support) :
      ∀ x ∈ closure ({p.1} : Set X.scheme), f x = f p.1 :=
    (fixedPart_prime_image_constant f (P j) (S j) (hS j) (hne j) (Z j)
      (hZ j) (hgen j) p hp).2
  have hFE : B (H F) (H (P j)) = 0 :=
    surfaceIntersection_contracted X.structureMap (H (P j)) (H F) (hP j) hF
  have hEF : B (H (P j)) (H F) = 0 := by
    change surfaceIntersection X.structureMap (H (P j)) (H F) = 0
    rw [surfaceIntersection_comm]
    exact hFE
  have hres := surfaceIntersection_residual_nonneg X.structureMap (P j) (S j) (hS j) (hne j)
  change 0 ≤ B (H (P j - F)) (H (P j - F)) at hres
  simp only [map_sub,AddMonoidHom.sub_apply,hFE,hEF,sub_zero,zero_sub,sub_neg_eq_add] at hres
  have hres' : 0 ≤ (B (H (P j)) (H (P j)) : ℝ) + (B (H F) (H F) : ℝ) := by
    have hr : 0 ≤ B (H (P j)) (H (P j)) + B (H F) (H F) := by simpa using hres
    exact_mod_cast hr
  have hn := hneg F hF
  change (B (H F) (H F) : ℝ) ≤ -a * (F e : ℝ)^2 at hn
  have hs := mul_self_le_mul_self (mul_nonneg hc.le (Nat.cast_nonneg (k j))) (hcoeff j)
  have hmul := mul_le_mul_of_nonneg_left hs ha.le
  have hkreal : 0 < (k j : ℝ) := by exact_mod_cast hk j
  have hFreal : 0 < (F e : ℝ) := lt_of_lt_of_le (mul_pos hc hkreal) (hcoeff j)
  change a*c^2*(k j : ℝ)^2 ≤ (B (H (P j)) (H (P j)) : ℝ)
  nlinarith [hFreal]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable def projectiveChartConstants {N : ℕ} (i : Fin (N+1)) : ℂ →+*
    Away (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i) :=
  (fromZeroRingHom _ _).comp (projectiveConstants N)
lemma projectiveChartRatio_self {N : ℕ} (i : Fin (N+1)) :
    projectiveChartRatio (k := ℂ) i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_one]
  change (Localization.mk (MvPolynomial.X i)
    ⟨(MvPolynomial.X i)^1, ⟨1,rfl⟩⟩ : Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N+1)) ℂ)) = 1
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_iff_eq_mul]
  simp only [pow_one,one_mul]
lemma projectiveChart_eval_homogeneous {N : ℕ} (i : Fin (N+1))
    (n : ℕ) (p : MvPolynomial (Fin (N+1)) ℂ) (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂Hom (projectiveChartConstants i) (projectiveChartRatio i) p =
      Away.mk _ (projectiveVariable_mem i) n p (by simpa using hp) := by
  let P := MvPolynomial (Fin (N+1)) ℂ
  let L := Localization.Away (MvPolynomial.X i : P)
  let v : Away (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i) →+* L :=
    { toFun := HomogeneousLocalization.val
      map_one' := HomogeneousLocalization.val_one
      map_mul' := HomogeneousLocalization.val_mul
      map_zero' := HomogeneousLocalization.val_zero
      map_add' := HomogeneousLocalization.val_add }
  let u : L := IsLocalization.Away.invSelf (S := L) (MvPolynomial.X i : P)
  have hc : v.comp (projectiveChartConstants i) =
      (algebraMap P L).comp MvPolynomial.C := by
    ext a
    change Localization.mk (MvPolynomial.C a) 1 = algebraMap P L (MvPolynomial.C a)
    rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_iff_eq_mul]
    simp only [OneMemClass.coe_one,map_one,mul_one]
    rfl
  have hr (j : Fin (N+1)) : v (projectiveChartRatio i j) =
      u * algebraMap P L (MvPolynomial.X j) := by
    change (Localization.mk (MvPolynomial.X j)
      ⟨(MvPolynomial.X i)^1, ⟨1,rfl⟩⟩ : L) = u * algebraMap P L (MvPolynomial.X j)
    rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_iff_eq_mul]
    simp only [pow_one]
    calc
      _ = algebraMap P L (MvPolynomial.X j) *
          (algebraMap P L (MvPolynomial.X i) * u) := by
        rw [IsLocalization.Away.mul_invSelf,mul_one]
      _ = _ := by ring
  have hev : MvPolynomial.eval₂Hom ((algebraMap P L).comp MvPolynomial.C)
      (fun j => algebraMap P L (MvPolynomial.X j)) = algebraMap P L := by
    ext j <;> simp
  apply HomogeneousLocalization.val_injective
  change v (MvPolynomial.eval₂Hom (projectiveChartConstants i) (projectiveChartRatio i) p) =
    v (Away.mk _ (projectiveVariable_mem i) n p (by simpa using hp))
  rw [MvPolynomial.map_eval₂Hom,hc]
  simp_rw [hr]
  rw [eval₂_homogeneous_scaling _ _ u hp,hev]
  change u ^ n * algebraMap P L p =
    (Localization.mk p ⟨(MvPolynomial.X i)^n, ⟨n,rfl⟩⟩ : L)
  rw [Localization.mk_eq_mk',IsLocalization.eq_mk'_iff_mul_eq,map_pow]
  calc
    _ = algebraMap P L p * (algebraMap P L (MvPolynomial.X i) * u)^n := by ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf]; simp only [one_pow,mul_one]; rfl
lemma projectiveChart_hom_reconstruct {N : ℕ} {R : Type} [CommRing R]
    (i : Fin (N+1))
    (ψ : Away (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i) →+* R) :
    projectiveChartRingHom (ψ.comp (projectiveChartConstants i))
      (fun j => ψ (projectiveChartRatio i j)) i
        (by rw [projectiveChartRatio_self,map_one]) = ψ := by
  apply RingHom.ext
  intro a
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective _ (projectiveVariable_mem i) a
  rw [projectiveChartRingHom_mk]
  conv_rhs => rw [← projectiveChart_eval_homogeneous i n p (by simpa using hp)]
  exact (MvPolynomial.map_eval₂Hom (projectiveChartConstants i) (projectiveChartRatio i) ψ p).symm
end NumericalDimensionOne

end OAI
