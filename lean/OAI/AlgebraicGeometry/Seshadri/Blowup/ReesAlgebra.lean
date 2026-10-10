import Mathlib

namespace OAI


                                    
section

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def piece (n : ℕ) : Submodule R (reesAlgebra I) where
  carrier := {p | (p : R[X]) = monomial n ((p : R[X]).coeff n)}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    change (p : R[X]) + q = monomial n (((p : R[X]) + q).coeff n)
    rw [coeff_add, map_add, ← hp, ← hq]
  smul_mem' a p hp := by
    change a • (p : R[X]) = monomial n ((a • (p : R[X])).coeff n)
    rw [coeff_smul, map_smul, ← hp]

lemma mem_piece (n : ℕ) (p : reesAlgebra I) :
    p ∈ piece I n ↔ (p : R[X]) = monomial n ((p : R[X]).coeff n) := Iff.rfl

def component (n : ℕ) (p : reesAlgebra I) : piece I n :=
  ⟨⟨monomial n ((p : R[X]).coeff n), reesAlgebra.monomial_mem.mpr (p.property n)⟩,
    by simp [mem_piece]⟩

@[simp] lemma component_val (n : ℕ) (p : reesAlgebra I) :
    ((component I n p : reesAlgebra I) : R[X]) = monomial n ((p : R[X]).coeff n) := rfl

def components (p : reesAlgebra I) : ⨁ n, piece I n :=
  ⟨fun n => component I n p,
    Trunc.mk ⟨(p : R[X]).support.val, fun n => by
      classical
      by_cases hn : n ∈ (p : R[X]).support
      · exact Or.inl hn
      · right
        apply Subtype.ext
        apply Subtype.ext
        have hc : (p : R[X]).coeff n = 0 := notMem_support_iff.mp hn
        simp [component_val, hc]⟩⟩

@[simp] lemma components_apply (p : reesAlgebra I) (n : ℕ) :
    components I p n = component I n p := rfl

def componentsAdd : reesAlgebra I →+ ⨁ n, piece I n where
  toFun := components I
  map_zero' := by ext n : 1; apply Subtype.ext; apply Subtype.ext; simp [component_val]
  map_add' p q := by
    ext n : 1
    apply Subtype.ext
    apply Subtype.ext
    change monomial n (((p : R[X]) + q).coeff n) =
      monomial n ((p : R[X]).coeff n) + monomial n ((q : R[X]).coeff n)
    rw [coeff_add, map_add]

lemma piece_coeff_ne {n m : ℕ} (hnm : n ≠ m) (p : piece I n) :
    ((p : reesAlgebra I) : R[X]).coeff m = 0 := by
  rw [(mem_piece I n p.val).mp p.property, coeff_monomial, ite_eq_right hnm]

lemma components_of_piece (n : ℕ) (p : piece I n) :
    components I p.val = DirectSum.of (fun n => piece I n) n p := by
  ext m : 1
  by_cases h : n = m
  · subst m
    rw [DirectSum.of_eq_same]
    apply Subtype.ext
    apply Subtype.ext
    exact ((mem_piece I n p.val).mp p.property).symm
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
    apply Subtype.ext
    apply Subtype.ext
    simp [component_val, piece_coeff_ne I h p]

lemma recompose_components (p : reesAlgebra I) :
    DirectSum.coeAddMonoidHom (piece I) (components I p) = p := by
  let f := DirectSum.coeAddMonoidHom (piece I)
  have hc (n : ℕ) :
      ((Polynomial.lcoeff R n).toAddMonoidHom.comp
        ((reesAlgebra I).val.toAddMonoidHom.comp f)) =
      ((Polynomial.lcoeff R n).toAddMonoidHom.comp
        ((reesAlgebra I).val.toAddMonoidHom.comp
          ((piece I n).subtype.toAddMonoidHom.comp (DFinsupp.evalAddMonoidHom n)))) := by
    apply DirectSum.addHom_ext
    intro m a
    dsimp only [f]
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
    change ((a : reesAlgebra I) : R[X]).coeff n =
      (((DirectSum.of (fun i => piece I i) m a) n : reesAlgebra I) : R[X]).coeff n
    by_cases h : m = n
    · subst m
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), piece_coeff_ne I h a]
      rfl
  apply Subtype.ext
  ext n
  have h := DFunLike.congr_fun (hc n) (components I p)
  change ((f (components I p) : reesAlgebra I) : R[X]).coeff n =
    ((component I n p : reesAlgebra I) : R[X]).coeff n at h
  simpa only [component_val, coeff_monomial, ite_true] using h

instance gradedMonoid : SetLike.GradedMonoid (piece I) where
  one_mem := by simp [mem_piece]
  mul_mem {i j} {a b} ha hb := by
    change (a : R[X]) * b = monomial (i+j) (((a : R[X]) * b).coeff (i+j))
    rw [(mem_piece I i a).mp ha, (mem_piece I j b).mp hb,
      monomial_mul_monomial, coeff_monomial, ite_eq_left rfl]

instance grading : GradedAlgebra (piece I) where
  toGradedMonoid := gradedMonoid I
  decompose' := components I
  left_inv := recompose_components I
  right_inv := by
    have h : (componentsAdd I).comp (DirectSum.coeAddMonoidHom (piece I)) = .id _ := by
      apply DirectSum.addHom_ext
      intro n a
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      exact components_of_piece I n a
    exact DFunLike.congr_fun h

def affineBlowup : Scheme.{u} := Proj (piece I)

def zeroEquiv : R ≃+* piece I 0 :=
  RingEquiv.ofBijective (algebraMap R (piece I 0)) (by
    constructor
    · intro a b h
      have hp := congrArg (fun p : piece I 0 => ((p : reesAlgebra I) : R[X])) h
      exact Polynomial.C_injective hp
    · intro p
      refine ⟨((p : reesAlgebra I) : R[X]).coeff 0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (show ((p : reesAlgebra I) : R[X]) =
        C (((p : reesAlgebra I) : R[X]).coeff 0) by
          simpa only [monomial_zero_left] using (mem_piece I 0 p.val).mp p.property).symm)

def zeroIso : CommRingCat.of R ≅ CommRingCat.of (piece I 0) :=
  (zeroEquiv I).toCommRingCatIso

def projection : affineBlowup I ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom

instance : IsScalarTower R (piece I 0) (reesAlgebra I) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := piece I 0) (A := reesAlgebra I)
    (fun _ => rfl)

instance [IsNoetherianRing R] : Algebra.FiniteType (piece I 0) (reesAlgebra I) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R (piece I 0) (reesAlgebra I)

instance projection_proper [IsNoetherianRing R] : IsProper (projection I) := by
  have hP : IsProper (Proj.toSpecZero (piece I)) := inferInstance
  have hS : IsIso (Spec.map (zeroIso I).hom) := inferInstance
  have hQ : IsProper (Spec.map (zeroIso I).hom) := by infer_instance
  exact MorphismProperty.comp_mem (@IsProper) _ _ hP hQ

end

noncomputable section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def generator (a : I) : reesAlgebra I :=
  ⟨monomial 1 a.val, reesAlgebra.monomial_mem.mpr (by simp [a.property])⟩

@[simp] lemma generator_val (a : I) :
    (generator I a : R[X]) = monomial 1 a.val := rfl

lemma generator_mem (a : I) : generator I a ∈ piece I 1 := by
  simp [mem_piece]

def evaluation : reesAlgebra I →+* R :=
  (Polynomial.evalRingHom 1).comp (reesAlgebra I).val.toRingHom

@[simp] lemma evaluation_generator (a : I) : evaluation I (generator I a) = a.val := by
  simp [evaluation]

lemma evaluation_piece {n : ℕ} (p : piece I n) :
    evaluation I p.val = ((p : reesAlgebra I) : R[X]).coeff n := by
  change Polynomial.eval 1 ((p : reesAlgebra I) : R[X]) = _
  conv_lhs => rw [(mem_piece I n p.val).mp p.property]
  simp

abbrev chart (a : I) := HomogeneousLocalization.Away (piece I) (generator I a)

def chartMap (a : I) : chart I a →+* Localization.Away a.val :=
  (IsLocalization.map (M := Submonoid.powers (generator I a))
    (S := Localization.Away (generator I a)) (T := Submonoid.powers a.val)
    (Localization.Away a.val) (evaluation I)
    (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩)).comp
      (algebraMap (chart I a) (Localization.Away (generator I a)))

lemma chartMap_mk (a : I) (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ piece I (n • (1 : ℕ))) :
    chartMap I a (HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) n p hp) =
      IsLocalization.mk' (M := Submonoid.powers a.val) (Localization.Away a.val)
        (evaluation I p) ⟨a.val ^ n, ⟨n, rfl⟩⟩ := by
  simp only [chartMap, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  simp

lemma chartMap_injective (a : I) : Function.Injective (chartMap I a) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply bot_unique
  intro x hx
  change x = 0
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  have hzero := RingHom.mem_ker.mp hx
  rw [chartMap_mk] at hzero
  obtain ⟨⟨b, hb⟩, hbp⟩ := (IsLocalization.mk'_eq_zero_iff (M := Submonoid.powers a.val)
    (S := Localization.Away a.val) _ _).mp hzero
  obtain ⟨j, rfl⟩ := hb
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨generator I a ^ j, ⟨j, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have hpn : p ∈ piece I n := by simpa using hp
  have he : evaluation I p = (p : R[X]).coeff n := evaluation_piece I ⟨p, hpn⟩
  change (generator I a : R[X]) ^ j * (p : R[X]) = 0
  rw [(mem_piece I n p).mp hpn, generator_val, monomial_pow, monomial_mul_monomial]
  rw [he] at hbp
  simp [hbp]

def chartBase (a : I) : R →+* chart I a :=
  (HomogeneousLocalization.fromZeroRingHom (piece I) (Submonoid.powers (generator I a))).comp
    (zeroEquiv I).toRingHom

lemma chartMap_base (a : I) (r : R) :
    chartMap I a (chartBase I a r) = algebraMap R (Localization.Away a.val) r := by
  have h0 : algebraMap R (reesAlgebra I) r ∈ piece I (0 • (1 : ℕ)) := by
    simp [mem_piece]
  refine (chartMap_mk I a 0 (algebraMap R (reesAlgebra I) r) h0).trans ?_
  have he : evaluation I (algebraMap R (reesAlgebra I) r) = r := by simp [evaluation]
  rw [he]
  convert IsLocalization.mk'_one (M := Submonoid.powers a.val)
    (Localization.Away a.val) r using 1
  congr 1
  apply Subtype.ext
  exact pow_zero a.val

def ratio (a b : I) : chart I a :=
  HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) 1
    (generator I b) (by simpa using generator_mem I b)

lemma chartMap_ratio (a b : I) :
    chartMap I a (ratio I a b) =
      IsLocalization.mk' (M := Submonoid.powers a.val) (Localization.Away a.val)
        b.val ⟨a.val, ⟨1, pow_one _⟩⟩ := by
  simp only [ratio, chartMap_mk, evaluation_generator, pow_one]

lemma base_mul_ratio (a b : I) :
    chartBase I a a.val * ratio I a b = chartBase I a b.val := by
  apply chartMap_injective I a
  rw [map_mul, chartMap_base, chartMap_ratio, chartMap_base]
  exact IsLocalization.mk'_spec' (M := Submonoid.powers a.val)
    (Localization.Away a.val) b.val ⟨a.val, ⟨1, pow_one _⟩⟩

lemma map_ideal_principal (a : I) :
    I.map (chartBase I a) = Ideal.span {chartBase I a a.val} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change chartBase I a b ∈ Ideal.span {chartBase I a a.val}
    rw [Ideal.mem_span_singleton]
    exact ⟨ratio I a ⟨b, hb⟩, (base_mul_ratio I a ⟨b, hb⟩).symm⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ a.property

lemma chart_isDomain [IsDomain R] (a : I) (ha : a.val ≠ 0) : IsDomain (chart I a) := by
  have : IsDomain (Localization.Away a.val) := IsLocalization.Away.isDomain (Localization.Away a.val) ha
  exact Function.Injective.isDomain (chartMap I a) (chartMap_injective I a)

lemma chartBase_injective [IsDomain R] (a : I) (ha : a.val ≠ 0) :
    Function.Injective (chartBase I a) := by
  intro r s h
  apply IsLocalization.injective (Localization.Away a.val)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  simpa only [chartMap_base] using congrArg (chartMap I a) h

lemma chart_generator_regular (a : I) :
    IsRegular (chartBase I a a.val) := by
  have hu : IsUnit (chartMap I a (chartBase I a a.val)) := by
    rw [chartMap_base]
    exact IsLocalization.map_units (Localization.Away a.val)
      (⟨a.val, 1, pow_one _⟩ : Submonoid.powers a.val)
  constructor
  · intro x y h
    apply chartMap_injective I a
    apply hu.isRegular.left
    simpa only [map_mul] using congrArg (chartMap I a) h
  · intro x y h
    apply chartMap_injective I a
    apply hu.isRegular.right
    simpa only [map_mul] using congrArg (chartMap I a) h

end
end MaximalSeshadri.ReesGrading


end

end OAI
