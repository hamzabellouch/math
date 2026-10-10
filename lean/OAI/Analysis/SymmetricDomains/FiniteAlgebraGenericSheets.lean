import Mathlib
import OAI.Analysis.SymmetricDomains.IntegralPrimitive

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors


theorem primitive_polynomial_representation
    {R S K E : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field E] [Algebra R S] [Algebra R K] [IsFractionRing R K]
    [Algebra S E] [IsFractionRing S E] [Algebra R E] [Algebra K E]
    [IsScalarTower R S E] [IsScalarTower R K E]
    (t : S) (ht : Algebra.adjoin K {algebraMap S E t} = ⊤) (x : S) :
    ∃ r : R, r ≠ 0 ∧ ∃ q : R[X], r • x = aeval t q := by
  have hx : algebraMap S E x ∈ Algebra.adjoin K {algebraMap S E t} := by
    rw [ht]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, hp⟩ := hx
  obtain ⟨r, hr, hq⟩ := IsLocalization.integerNormalization_spec R⁰ p
  refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr,
    IsLocalization.integerNormalization R⁰ p, ?_⟩
  apply IsFractionRing.injective S E
  have he := congrArg (aeval (algebraMap S E t)) hq
  rw [Polynomial.aeval_map_algebraMap] at he
  rw [AlgHom.map_smul_of_tower] at he
  change (aeval (algebraMap S E t)) p = algebraMap S E x at hp
  rw [hp] at he
  rw [Polynomial.aeval_algebraMap_apply] at he
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R S E]
  simpa only [Algebra.smul_def] using he.symm

theorem finite_integral_primitive_representations
    {R S : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [Module.Finite R S] :
    ∃ t : S, ∀ x : S, ∃ r : R, r ≠ 0 ∧ ∃ q : R[X], r • x = aeval t q := by
  let := FractionRing.liftAlgebra (R := R) (K := FractionRing S)
  obtain ⟨t, ht⟩ := exists_integral_primitive (R := R) (S := S)
    (K := FractionRing R) (E := FractionRing S)
  exact ⟨t, primitive_polynomial_representation (K := FractionRing R)
    (E := FractionRing S) t ht⟩

theorem extend_algHom_of_integral
    {k A B : Type*} [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [FaithfulSMul A B] [Algebra.IsIntegral A B] [Algebra.FiniteType k B]
    (e : A →ₐ[k] k) :
    ∃ f : B →ₐ[k] k, ∀ a : A, f (algebraMap A B a) = e a := by
  let m := RingHom.ker e
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective e
    (fun x => ⟨algebraMap k A x, e.commutes x⟩)
  let := hm
  have hker : RingHom.ker (algebraMap A B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := B) m (by rw [hker]; exact bot_le)
  let := hQmax
  let : Field (B ⧸ Q) := Ideal.Quotient.field Q
  let : Module.Finite k (B ⧸ Q) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ Q)
  let f : B →ₐ[k] k := IsAlgClosed.lift.comp (Ideal.Quotient.mkₐ k Q)
  refine ⟨f, fun a => ?_⟩
  have ham : a - algebraMap k A (e a) ∈ m := by
    change e (a - algebraMap k A (e a)) = 0
    rw [map_sub, e.commutes]; simp
  have haQ : algebraMap A B (a - algebraMap k A (e a)) ∈ Q := by
    change a - algebraMap k A (e a) ∈ Q.under A
    rw [hQ]; exact ham
  have hz : f (algebraMap A B (a - algebraMap k A (e a))) = 0 := by
    change IsAlgClosed.lift (Ideal.Quotient.mk Q _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr haQ, map_zero]
  rw [map_sub, map_sub, ← IsScalarTower.algebraMap_apply k A B, f.commutes] at hz
  exact sub_eq_zero.mp hz

open Polynomial Algebra

theorem realize_specialized_minpoly_root
    {k R S : Type*} [Field k] [IsAlgClosed k]
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra k R] [Algebra k S] [Algebra R S]
    [IsScalarTower k R S] [Module.IsTorsionFree R S]
    [Algebra.IsIntegral R S] [Algebra.FiniteType k S]
    (e : R →ₐ[k] k) (t : S) (z : k)
    (hz : (minpoly R t).eval₂ e z = 0) :
    ∃ f : S →ₐ[k] k, (∀ r : R, f (algebraMap R S r) = e r) ∧ f t = z := by
  let A := Algebra.adjoin R ({t} : Set S)
  have ht : IsIntegral R t := Algebra.IsIntegral.isIntegral t
  let eqv := minpoly.equivAdjoin ht
  let l := AdjoinRoot.liftAlgHom (minpoly R t) e z hz
  let ea : A →ₐ[k] k := l.comp (eqv.symm.restrictScalars k).toAlgHom
  let : Algebra.IsIntegral A S := Algebra.IsIntegral.tower_top R
  have hinj : Function.Injective (algebraMap A S) := Subtype.val_injective
  let : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr hinj
  obtain ⟨f, hf⟩ := extend_algHom_of_integral (B := S) ea
  refine ⟨f, ?_, ?_⟩
  · intro r
    rw [IsScalarTower.algebraMap_apply R A S, hf]
    change l (eqv.symm (algebraMap R A r)) = e r
    rw [eqv.symm.commutes]
    exact AdjoinRoot.liftAlgHom_of (minpoly R t) e z hz r
  · let ta : A := ⟨t, Algebra.self_mem_adjoin_singleton R t⟩
    have hta : eqv (AdjoinRoot.root (minpoly R t)) = ta := by
      apply Subtype.ext
      simp [eqv, minpoly.equivAdjoin, AdjoinRoot.Minpoly.toAdjoin, ta]
    have hta' : eqv.symm ta = AdjoinRoot.root (minpoly R t) := by
      exact (eqv.symm_apply_eq).mpr hta.symm
    change f (algebraMap A S ta) = z
    rw [hf]
    change l (eqv.symm ta) = z
    rw [hta']
    exact AdjoinRoot.liftAlgHom_root (minpoly R t) e z hz

theorem algHom_aeval_of_base
    {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S]
    (f : S →ₐ[k] k) (e : R →+* k)
    (hf : ∀ r, f (algebraMap R S r) = e r) (t : S) (q : R[X]) :
    f (aeval t q) = q.eval₂ e (f t) := by
  have heq : f.toRingHom.comp (algebraMap R S) = e := RingHom.ext hf
  change f.toRingHom (q.eval₂ (algebraMap R S) t) = _
  rw [Polynomial.hom_eval₂, heq]
  rfl

theorem analyticAt_polynomial_substitution {d : ℕ}
    (q : Polynomial (MvPolynomial (Fin d) ℂ))
    {g : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ} (hg : AnalyticAt ℂ g a) :
    AnalyticAt ℂ (fun y => q.eval₂ (MvPolynomial.eval y) (g y)) a := by
  simp only [Polynomial.eval₂_eq_sum_range]
  exact Finset.analyticAt_fun_sum (Finset.range (q.natDegree + 1)) (fun j _ =>
    (AnalyticOnNhd.eval_mvPolynomial (q.coeff j) a (Set.mem_univ a)).mul (hg.pow j))

theorem finite_algebra_generic_sheets {d n : ℕ}
    {S : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra (MvPolynomial (Fin d) ℂ) S]
    [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) S]
    [FaithfulSMul (MvPolynomial (Fin d) ℂ) S]
    [Module.Finite (MvPolynomial (Fin d) ℂ) S]
    (x : Fin n → S) (hx : Algebra.adjoin ℂ (Set.range x) = ⊤) :
    ∃ D : MvPolynomial (Fin d) ℂ, D ≠ 0 ∧
      ∀ a : Fin d → ℂ, MvPolynomial.eval a D ≠ 0 →
      ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → (Fin n → ℂ))
        (W : Set (Fin d → ℂ)),
        I.Nonempty ∧ IsOpen W ∧ a ∈ W ∧
        (∀ i, AnalyticOnNhd ℂ (g i) W) ∧
        ∀ y ∈ W, Function.Injective (fun i => g i y) ∧
          ∀ z : Fin n → ℂ,
            (∃ f : S →ₐ[ℂ] ℂ,
              (∀ r, f (algebraMap (MvPolynomial (Fin d) ℂ) S r) = MvPolynomial.eval y r) ∧
              (∀ j, f (x j) = z j)) ↔ ∃ i, g i y = z := by
  classical
  let R := MvPolynomial (Fin d) ℂ
  have : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℂ R) (inferInstance : Algebra.FiniteType R S)
  obtain ⟨t, ht⟩ := finite_integral_primitive_representations (R := R) (S := S)
  choose r hr q hq using fun j => ht (x j)
  let p := minpoly R t
  have hi : IsIntegral R t := Algebra.IsIntegral.isIntegral t
  have hp : p.Monic := minpoly.monic hi
  have hdisc : p.resultant p.derivative ≠ 0 :=
    integral_minpoly_resultant_ne_zero (K := FractionRing R) t hi
  let D := p.resultant p.derivative * ∏ j, r j
  have hD : D ≠ 0 := mul_ne_zero hdisc (Finset.prod_ne_zero_iff.mpr (fun j _ => hr j))
  refine ⟨D, hD, fun a ha => ?_⟩
  have hda : MvPolynomial.eval a (p.resultant p.derivative) ≠ 0 := by
    exact left_ne_zero_of_mul (by simpa only [D, map_mul] using ha)
  have hra : ∀ j, MvPolynomial.eval a (r j) ≠ 0 := by
    have h := right_ne_zero_of_mul (by simpa only [D, map_mul] using ha)
    rw [map_prod] at h
    exact fun j => Finset.prod_ne_zero_iff.mp h j (Finset.mem_univ j)
  obtain ⟨I, w, W₀, hcard, hW₀, haW₀, hw, _hwa, hsheets⟩ :=
    polynomial_analytic_sheets p hp a (separable_map_of_resultant_ne_zero p hp _ hda)
  have hI : I.Nonempty := Finset.card_pos.mp (hcard ▸ minpoly.natDegree_pos hi)
  let H : Set (Fin d → ℂ) := {y | ∀ j, MvPolynomial.eval y (r j) ≠ 0}
  have hH : IsOpen H := by
    have hH : H = ⋂ j, {y | MvPolynomial.eval y (r j) ≠ 0} := by
      ext y; simp [H]
    rw [hH]
    exact isOpen_iInter_of_finite (fun j => isOpen_ne.preimage
      (MvPolynomial.continuous_eval (r j)))
  let W := W₀ ∩ H
  let g : I → (Fin d → ℂ) → (Fin n → ℂ) := fun i y j =>
    (q j).eval₂ (MvPolynomial.eval y) (w i y) / MvPolynomial.eval y (r j)
  have hformula (y : Fin d → ℂ) (hy : y ∈ W) (f : S →ₐ[ℂ] ℂ)
      (hf : ∀ b : R, f (algebraMap R S b) = MvPolynomial.eval y b) :
      ∀ j, f (x j) = (q j).eval₂ (MvPolynomial.eval y) (f t) /
        MvPolynomial.eval y (r j) := by
    intro j
    apply (eq_div_iff (hy.2 j)).mpr
    have hh := congrArg f (hq j)
    rw [Algebra.smul_def, map_mul, hf, algHom_aeval_of_base f _ hf] at hh
    simpa only [mul_comm] using hh
  have hroot (y : Fin d → ℂ) (f : S →ₐ[ℂ] ℂ)
      (hf : ∀ b : R, f (algebraMap R S b) = MvPolynomial.eval y b) :
      p.eval₂ (MvPolynomial.eval y) (f t) = 0 := by
    rw [← algHom_aeval_of_base f _ hf, minpoly.aeval, map_zero]
  have hpoint (y : Fin d → ℂ) (hy : y ∈ W) (i : I) :
      ∃ f : S →ₐ[ℂ] ℂ,
        (∀ b : R, f (algebraMap R S b) = MvPolynomial.eval y b) ∧
        f t = w i y ∧ ∀ j, f (x j) = g i y j := by
    have hwi : p.eval₂ (MvPolynomial.eval y) (w i y) = 0 :=
      ((hsheets y hy.1).2 _).mpr ⟨i, rfl⟩
    obtain ⟨f, hf, hft⟩ := realize_specialized_minpoly_root
      (S := S) (MvPolynomial.aeval y) t (w i y) hwi
    refine ⟨f, hf, hft, fun j => ?_⟩
    rw [hformula y hy f hf j, hft]
  refine ⟨I, g, W, hI, hW₀.inter hH, ⟨haW₀, hra⟩, ?_, ?_⟩
  · intro i y hy
    exact AnalyticAt.pi (fun j =>
      (analyticAt_polynomial_substitution (q j) (hw i y hy.1)).div
        (AnalyticOnNhd.eval_mvPolynomial (r j) y (Set.mem_univ y)) (hy.2 j))
  · intro y hy
    refine ⟨?_, fun z => ?_⟩
    · intro i j hij
      obtain ⟨f, _hf, hft, hfx⟩ := hpoint y hy i
      obtain ⟨f', _hf', hft', hfx'⟩ := hpoint y hy j
      have he : f = f' := AlgHom.ext_of_adjoin_eq_top hx (by
        rintro _ ⟨k, rfl⟩
        rw [hfx, hfx']
        exact congrFun hij k)
      apply (hsheets y hy.1).1
      change w i y = w j y
      rw [← hft, ← hft', he]
    · constructor
      · rintro ⟨f, hf, hfz⟩
        obtain ⟨i, hi⟩ := ((hsheets y hy.1).2 (f t)).mp (hroot y f hf)
        refine ⟨i, funext (fun j => ?_)⟩
        change (q j).eval₂ (MvPolynomial.eval y) (w i y) /
          MvPolynomial.eval y (r j) = z j
        rw [hi, ← hformula y hy f hf j, hfz]
      · rintro ⟨i, rfl⟩
        obtain ⟨f, hf, _hft, hfx⟩ := hpoint y hy i
        exact ⟨f, hf, hfx⟩

end Release061

end OAI
