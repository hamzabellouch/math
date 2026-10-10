import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.CartierModule
import OAI.AlgebraicGeometry.Seshadri.Blowup.ReesAlgebra

namespace OAI

section
namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial HomogeneousLocalization
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable {B : Type v} [CommRing B] (f : R →+* B)

def chartToLocalization : chart I a →+* Localization.Away (f a.val) :=
  (IsLocalization.map (M := Submonoid.powers a.val)
    (T := Submonoid.powers (f a.val)) (S := Localization.Away a.val)
    (Localization.Away (f a.val)) f (by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, (map_pow f _ _).symm⟩)).comp (chartMap I a)

lemma chartToLocalization_mk (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ piece I (n • (1 : ℕ))) :
    chartToLocalization I a f
      (HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) n p hp) =
      IsLocalization.mk' (M := Submonoid.powers (f a.val))
        (Localization.Away (f a.val)) (f (evaluation I p))
          ⟨(f a.val) ^ n, ⟨n, rfl⟩⟩ := by
  simp only [chartToLocalization, RingHom.comp_apply, chartMap_mk, IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  exact map_pow f _ _

lemma chartToLocalization_base (r : R) :
    chartToLocalization I a f (chartBase I a r) =
      algebraMap B (Localization.Away (f a.val)) (f r) := by
  simp [chartToLocalization, chartMap_base]

lemma coeff_power_dvd (hI : I.map f ≤ Ideal.span {f a.val})
    (n : ℕ) {r : R} (hr : r ∈ I ^ n) : (f a.val) ^ n ∣ f r := by
  have hm : f r ∈ (I.map f) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hr
  have hm' := pow_le_pow_left' hI n hm
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm'
  exact hm'

lemma chartToLocalization_range (hI : I.map f ≤ Ideal.span {f a.val})
    (x : chart I a) :
    ∃ b : B, algebraMap B (Localization.Away (f a.val)) b =
      chartToLocalization I a f x := by
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  rw [chartToLocalization_mk]
  have hpn : p ∈ piece I n := by simpa using hp
  have he : evaluation I p = (p : R[X]).coeff n := evaluation_piece I ⟨p, hpn⟩
  obtain ⟨b, hb⟩ := coeff_power_dvd I a f hI n (p.property n)
  refine ⟨b, ?_⟩
  rw [he, hb]
  exact (IsLocalization.mk'_mul_cancel_left (M := Submonoid.powers (f a.val))
    (S := Localization.Away (f a.val)) b ⟨(f a.val) ^ n, ⟨n, rfl⟩⟩).symm

lemma localizationMap_injective (hfa : IsRegular (f a.val)) :
    Function.Injective (algebraMap B (Localization.Away (f a.val))) :=
  IsLocalization.injective _ (Submonoid.powers_le.mpr
    (isRegular_iff_mem_nonZeroDivisors.mp hfa))

def chartLift (hI : I.map f ≤ Ideal.span {f a.val}) (hfa : IsRegular (f a.val)) :
    chart I a →+* B where
  toFun x := Classical.choose (chartToLocalization_range I a f hI x)
  map_zero' := localizationMap_injective I a f hfa (by
    rw [Classical.choose_spec (chartToLocalization_range I a f hI 0), map_zero, map_zero])
  map_one' := localizationMap_injective I a f hfa (by
    rw [Classical.choose_spec (chartToLocalization_range I a f hI 1), map_one, map_one])
  map_add' x y := localizationMap_injective I a f hfa (by
    rw [Classical.choose_spec (chartToLocalization_range I a f hI (x+y)), map_add,
      map_add, Classical.choose_spec (chartToLocalization_range I a f hI x),
      Classical.choose_spec (chartToLocalization_range I a f hI y)])
  map_mul' x y := localizationMap_injective I a f hfa (by
    rw [Classical.choose_spec (chartToLocalization_range I a f hI (x*y)), map_mul,
      map_mul, Classical.choose_spec (chartToLocalization_range I a f hI x),
      Classical.choose_spec (chartToLocalization_range I a f hI y)])

lemma chartLift_spec (hI : I.map f ≤ Ideal.span {f a.val}) (hfa : IsRegular (f a.val))
    (x : chart I a) :
    algebraMap B (Localization.Away (f a.val)) (chartLift I a f hI hfa x) =
      chartToLocalization I a f x :=
  Classical.choose_spec (chartToLocalization_range I a f hI x)

lemma chartLift_base (hI : I.map f ≤ Ideal.span {f a.val}) (hfa : IsRegular (f a.val))
    (r : R) : chartLift I a f hI hfa (chartBase I a r) = f r := by
  apply localizationMap_injective I a f hfa
  rw [chartLift_spec, chartToLocalization_base]

end

noncomputable section
open Polynomial HomogeneousLocalization
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable {B : Type v} [CommRing B] (f : R →+* B)

lemma base_pow_mul_mk (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ piece I (n • (1 : ℕ))) :
    chartBase I a (a.val ^ n) *
        HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) n p hp =
      chartBase I a (evaluation I p) := by
  apply chartMap_injective I a
  rw [map_mul, chartMap_base, chartMap_base, chartMap_mk]
  exact IsLocalization.mk'_spec' (M := Submonoid.powers a.val)
    (Localization.Away a.val) (evaluation I p) ⟨a.val ^ n, n, rfl⟩

lemma chartLift_unique (hI : I.map f ≤ Ideal.span {f a.val}) (hfa : IsRegular (f a.val))
    (g : chart I a →+* B) (hg : g.comp (chartBase I a) = f) :
    g = chartLift I a f hI hfa := by
  have hb (r : R) : g (chartBase I a r) = f r := RingHom.congr_fun hg r
  ext x
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  apply (hfa.pow n).left
  have h₁ := congrArg g (base_pow_mul_mk I a n p hp)
  have h₂ := congrArg (chartLift I a f hI hfa) (base_pow_mul_mk I a n p hp)
  simp only [map_mul, hb, map_pow] at h₁
  simp only [map_mul, chartLift_base, map_pow] at h₂
  exact h₁.trans h₂.symm

theorem chart_universal (hI : I.map f ≤ Ideal.span {f a.val}) (hfa : IsRegular (f a.val)) :
    ∃! g : chart I a →+* B, g.comp (chartBase I a) = f := by
  refine ⟨chartLift I a f hI hfa, ?_, fun g hg => chartLift_unique I a f hI hfa g hg⟩
  ext r
  exact chartLift_base I a f hI hfa r

end

noncomputable section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma generators_adjoin : Algebra.adjoin R (Set.range (generator I)) = ⊤ := by
  apply (Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective)
  rw [AlgHom.map_adjoin]
  have hs : (reesAlgebra I).val '' Set.range (generator I) =
      (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) := by
    ext p
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨generator I ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  rw [hs, adjoin_monomial_eq_reesAlgebra]
  rw [Algebra.map_top, Subalgebra.range_val]

lemma generators_adjoin_zero :
    Algebra.adjoin (piece I 0) (Set.range (generator I)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  have hh : p ∈ Algebra.adjoin R (Set.range (generator I)) := by
    rw [generators_adjoin]
    trivial
  induction hh using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact (Algebra.adjoin (piece I 0) (Set.range (generator I))).algebraMap_mem (zeroEquiv I r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

lemma iSup_generator_basicOpen :
    ⨆ a : I, Proj.basicOpen (piece I) (generator I a) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (piece I) (generator I)
    (fun a => ⟨1, generator_mem I a⟩) (generators_adjoin_zero I)

def chartCover : (affineBlowup I).AffineOpenCover where
  I₀ := I
  X a := CommRingCat.of (chart I a)
  f a := Proj.awayι (m := 1) (piece I) (generator I a) (generator_mem I a) (show 0 < (1 : ℕ) from Nat.zero_lt_one)
  map_prop a := inferInstanceAs (IsOpenImmersion
    (Proj.awayι (m := 1) (piece I) (generator I a) (generator_mem I a) (show 0 < (1 : ℕ) from Nat.zero_lt_one)))
  idx x := (Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.awayι (m := 1) (piece I) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))).choose_spec

lemma chartCover_projection (a : I) :
    (chartCover I).f a ≫ projection I = Spec.map (CommRingCat.ofHom (chartBase I a)) := by
  change Proj.awayι (m := 1) (piece I) (generator I a) _ _ ≫
    (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end
end MaximalSeshadri.ReesGrading


end

end OAI
