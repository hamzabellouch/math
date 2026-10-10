import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialRemovableLocal

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology


theorem glue_dense_differentiable_extensions
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U D : Set E} (hD : Dense D) (f : E → ℂ) {B : ℝ}
    (hlocal : ∀ x ∈ U, ∃ A : Set E, IsOpen A ∧ x ∈ A ∧
      ∃ g : E → ℂ, DifferentiableOn ℂ g A ∧ EqOn g f (A ∩ D) ∧
        ∀ y ∈ A, ‖g y‖ ≤ B) :
    ∃ g : E → ℂ, DifferentiableOn ℂ g U ∧ EqOn g f (U ∩ D) ∧
      ∀ x ∈ U, ‖g x‖ ≤ B := by
  let g : E → ℂ := fun x => limUnder (𝓝[D] x) f
  have hvalue {A : Set E} (hA : IsOpen A) (ga : E → ℂ)
      (hga : DifferentiableOn ℂ ga A) (heq : EqOn ga f (A ∩ D))
      {x : E} (hx : x ∈ A) : g x = ga x := by
    have : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hD x)
    have ht : Tendsto ga (𝓝[D] x) (𝓝 (ga x)) :=
      (hga.differentiableAt (hA.mem_nhds hx)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hevent : ga =ᶠ[𝓝[D] x] f := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hA.mem_nhds hx), self_mem_nhdsWithin] with y hy hyD
      exact heq ⟨hy, hyD⟩
    exact (ht.congr' hevent).limUnder_eq
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨A, hA, hxA, ga, hga, heq, _⟩ := hlocal x hx
    have hh : g =ᶠ[𝓝 x] ga := Filter.Eventually.mono (hA.mem_nhds hxA) (fun y hy => hvalue hA ga hga heq hy)
    exact ((hga.differentiableAt (hA.mem_nhds hxA)).congr_of_eventuallyEq hh).differentiableWithinAt
  · intro x hx
    obtain ⟨A, hA, hxA, ga, hga, heq, _⟩ := hlocal x hx.1
    exact (hvalue hA ga hga heq hxA).trans (heq ⟨hxA, hx.2⟩)
  · intro x hx
    obtain ⟨A, hA, hxA, ga, hga, heq, hb⟩ := hlocal x hx
    rw [hvalue hA ga hga heq hxA]
    exact hb x hxA

theorem bounded_polynomial_removable {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f (U \ {x | MvPolynomial.eval x P = 0}))
    {B : ℝ} (hb : ∀ x ∈ U \ {x | MvPolynomial.eval x P = 0}, ‖f x‖ ≤ B) :
    ∃ g : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ g U ∧
      EqOn g f (U \ {x | MvPolynomial.eval x P = 0}) ∧
      ∀ x ∈ U, ‖g x‖ ≤ B := by
  apply glue_dense_differentiable_extensions (dense_polynomial_nonzero P hP) f
  intro a ha
  obtain ⟨A, hA, haA, _, g, hg, heq, hb⟩ :=
    bounded_polynomial_removable_local P hP hU f hf hb ha
  exact ⟨A, hA, haA, g, hg, heq, hb⟩

open Polynomial

theorem resultant_derivative_ne_zero_of_generic_separable
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (p : R[X])
    (hp : (p.map (algebraMap R K)).Separable) :
    p.resultant p.derivative ≠ 0 := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h := Polynomial.resultant_ne_zero (p.map (algebraMap R K))
    ((p.map (algebraMap R K)).derivative) hp
  rw [Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.resultant_map_map] at h
  exact fun hz => h (by rw [hz, map_zero])

theorem eval₂_derivative_ne_zero_of_resultant
    {R K : Type*} [CommRing R] [Field K]
    (p : R[X]) (hp : p.Monic) (e : R →+* K) (z : K)
    (hr : p.eval₂ e z = 0)
    (hd : e (p.resultant p.derivative) ≠ 0) :
    p.derivative.eval₂ e z ≠ 0 := by
  have hdeg : p.natDegree ≠ 0 := by
    intro hz
    have hpone : p = 1 := eq_one_of_monic_natDegree_zero hp hz
    simp only [hpone, eval₂_one, one_ne_zero] at hr
  obtain ⟨a, b, _, _, hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    p p.derivative le_rfl le_rfl (Or.inl hdeg)
  intro hm
  have h := congrArg (Polynomial.eval₂ e z) hab
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, hr, hm,
    zero_mul, zero_add, Polynomial.eval₂_C] at h
  exact hd h.symm

theorem separable_map_of_resultant_ne_zero
    {R K : Type*} [CommRing R] [Field K]
    (p : R[X]) (hp : p.Monic) (e : R →+* K)
    (hd : e (p.resultant p.derivative) ≠ 0) :
    (p.map e).Separable := by
  by_cases hdeg : p.natDegree = 0
  · rw [eq_one_of_monic_natDegree_zero hp hdeg, Polynomial.map_one]
    exact Polynomial.separable_one
  obtain ⟨a, b, _, _, hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    p p.derivative le_rfl le_rfl (Or.inl hdeg)
  have hh := congrArg (Polynomial.map e) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hh
  refine ⟨C ((e (p.resultant p.derivative))⁻¹) * a.map e,
    C ((e (p.resultant p.derivative))⁻¹) * b.map e, ?_⟩
  rw [Polynomial.derivative_map]
  calc
    _ = C ((e (p.resultant p.derivative))⁻¹) *
        (p.map e * a.map e + p.derivative.map e * b.map e) := by ring
    _ = 1 := by rw [hh, ← C_mul, inv_mul_cancel₀ hd, C_1]

theorem integral_minpoly_resultant_ne_zero
    {R S K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (x : S) (hx : IsIntegral R x) :
    (minpoly R x).resultant (minpoly R x).derivative ≠ 0 := by
  apply resultant_derivative_ne_zero_of_generic_separable (K := K)
  exact (((minpoly.monic hx).irreducible_iff_irreducible_map_fraction_map).mp
    (minpoly.irreducible hx)).separable

theorem polynomial_analytic_sheets {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (hP : P.Monic)
    (a : Fin d → ℂ) (ha : (P.map (MvPolynomial.eval a)).Separable) :
    ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → ℂ) (W : Set (Fin d → ℂ)),
      I.card = P.natDegree ∧ IsOpen W ∧ a ∈ W ∧
      (∀ i, AnalyticOnNhd ℂ (g i) W) ∧ (∀ i, g i a = i.val) ∧
      ∀ y ∈ W, Function.Injective (fun i => g i y) ∧
        ∀ z : ℂ, Polynomial.eval₂ (MvPolynomial.eval y) z P = 0 ↔
          ∃ i, g i y = z := by
  classical
  let I : Finset ℂ := (P.map (MvPolynomial.eval a)).roots.toFinset
  have hcard : I.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots ha),
      IsAlgClosed.card_roots_map_eq_natDegree_of_isUnit_leadingCoeff _ (hP ▸ isUnit_one)]
  have hi (i : I) : Polynomial.eval₂ (MvPolynomial.eval a) i.val P = 0 := by
    have h := Polynomial.mem_roots (hP.map (MvPolynomial.eval a)).ne_zero |>.mp
      (Multiset.mem_toFinset.mp i.property)
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using h
  have hs (i : I) : Polynomial.eval₂ (MvPolynomial.eval a) i.val P.derivative ≠ 0 := by
    simpa only [Polynomial.eval₂_id, Polynomial.derivative_map,
      Polynomial.eval_map] using
      ha.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := i.val)
        (by simpa only [Polynomial.eval₂_id, Polynomial.eval_map] using hi i)
  choose g hg hga hgr _hgu using fun i : I => polynomial_analytic_root P a i.val (hi i) (hs i)
  have hgi : ∀ᶠ y in 𝓝 a, Function.Injective (fun i => g i y) := by
    have hj : ∀ i j : I, ∀ᶠ y in 𝓝 a, i ≠ j → g i y ≠ g j y := by
      intro i j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
      · have hval : g i a ≠ g j a := by
          rw [hga, hga]
          exact fun h => hij (Subtype.ext h)
        exact ((hg i).continuousAt.ne_iff_eventually_ne (hg j).continuousAt).mp hval |>.mono
          (fun _ hh _ => hh)
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hj i))] with y hy
    intro i j hij
    by_contra h
    exact hy i j h hij
  have hall : ∀ᶠ y in 𝓝 a,
      (∀ i, AnalyticAt ℂ (g i) y) ∧
      (∀ i, Polynomial.eval₂ (MvPolynomial.eval y) (g i y) P = 0) ∧
      Function.Injective (fun i => g i y) := by
    exact (Filter.eventually_all.mpr (fun i => (hg i).eventually_analyticAt)).and
      ((Filter.eventually_all.mpr hgr).and hgi)
  obtain ⟨W, hWsub, hW, haW⟩ := _root_.mem_nhds_iff.mp hall
  refine ⟨I, g, W, hcard, hW, haW, fun i y hy => (hWsub hy).1 i, hga, ?_⟩
  intro y hy
  have hyroot := (hWsub hy).2.1
  have hyinj := (hWsub hy).2.2
  refine ⟨hyinj, ?_⟩
  let J : Finset ℂ := Finset.univ.image (fun i : I => g i y)
  let K : Finset ℂ := (P.map (MvPolynomial.eval y)).roots.toFinset
  have hJK : J ⊆ K := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hP.map _).ne_zero).mpr
      (by simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hyroot i))
  have hJcard : J.card = I.card := by
    rw [Finset.card_image_of_injective _ hyinj]
    simp
  have hKcard : K.card ≤ P.natDegree := by
    exact (Multiset.toFinset_card_le _).trans (le_of_eq
      (IsAlgClosed.card_roots_map_eq_natDegree_of_isUnit_leadingCoeff _ (hP ▸ isUnit_one)))
  have hJKeq : J = K := Finset.eq_of_subset_of_card_le hJK (by rw [hJcard, hcard]; exact hKcard)
  intro z
  constructor
  · intro hz
    have hzK : z ∈ K := Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (hP.map _).ne_zero).mpr
        (by simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hz))
    rw [← hJKeq] at hzK
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzK
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact hyroot i

open Polynomial Algebra
open scoped nonZeroDivisors

theorem exists_integral_primitive
    {R S K E : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field E] [Algebra R S] [FaithfulSMul R S]
    [Algebra R K] [IsFractionRing R K] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [Algebra K E] [IsScalarTower R S E] [IsScalarTower R K E]
    [Algebra.IsAlgebraic R S] [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    ∃ t : S, Algebra.adjoin K {algebraMap S E t} = ⊤ := by
  let b := Field.powerBasisOfFiniteOfSeparable K E
  obtain ⟨s, t, ht⟩ := IsLocalization.exists_integer_multiple
    (algebraMapSubmonoid S R⁰) b.gen
  obtain ⟨r, hr, hrs⟩ := s.property
  have hr0 : (r : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
  have hrK : algebraMap R K r ≠ 0 :=
    fun h => hr0 (IsFractionRing.injective R K (h.trans (map_zero _).symm))
  have ht' : algebraMap S E t = (algebraMap R K r) • b.gen := by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K E]
    rw [IsScalarTower.algebraMap_apply R S E, hrs]
    simpa only [Algebra.smul_def] using ht
  refine ⟨t, b.adjoin_eq_top_of_gen_mem_adjoin ?_⟩
  have hmem := (Algebra.adjoin K {algebraMap S E t}).smul_mem
    (Algebra.self_mem_adjoin_singleton K (algebraMap S E t)) (algebraMap R K r)⁻¹
  have hs : (algebraMap R K r)⁻¹ • algebraMap S E t = b.gen := by
    rw [ht', smul_smul, inv_mul_cancel₀ hrK, one_smul]
  rwa [hs] at hmem

end Release061

end OAI
