import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteAlgebraGenericSheets

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem finite_algebra_generic_sheets_constant_degree {d n : ℕ}
    {S : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra (MvPolynomial (Fin d) ℂ) S]
    [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) S]
    [FaithfulSMul (MvPolynomial (Fin d) ℂ) S]
    [Module.Finite (MvPolynomial (Fin d) ℂ) S]
    (x : Fin n → S) (hx : Algebra.adjoin ℂ (Set.range x) = ⊤) :
    ∃ (D : MvPolynomial (Fin d) ℂ) (r : ℕ), D ≠ 0 ∧ 0 < r ∧
      ∀ a : Fin d → ℂ, MvPolynomial.eval a D ≠ 0 →
      ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → (Fin n → ℂ))
        (W : Set (Fin d → ℂ)),
        I.card = r ∧ IsOpen W ∧ a ∈ W ∧
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
  refine ⟨D, p.natDegree, hD, minpoly.natDegree_pos hi, fun a ha => ?_⟩
  have hda : MvPolynomial.eval a (p.resultant p.derivative) ≠ 0 := by
    exact left_ne_zero_of_mul (by simpa only [D, map_mul] using ha)
  have hra : ∀ j, MvPolynomial.eval a (r j) ≠ 0 := by
    have h := right_ne_zero_of_mul (by simpa only [D, map_mul] using ha)
    rw [map_prod] at h
    exact fun j => Finset.prod_ne_zero_iff.mp h j (Finset.mem_univ j)
  obtain ⟨I, w, W₀, hcard, hW₀, haW₀, hw, _hwa, hsheets⟩ :=
    polynomial_analytic_sheets p hp a (separable_map_of_resultant_ne_zero p hp _ hda)
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
  refine ⟨I, g, W, hcard, hW₀.inter hH, ⟨haW₀, hra⟩, ?_, ?_⟩
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

noncomputable def quotientCoordinate {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (j : Fin n) : MvPolynomial (Fin n) ℂ ⧸ I :=
  (Ideal.Quotient.mkₐ ℂ I) (MvPolynomial.X j)

noncomputable def affineCharacter {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (z : MvPolynomial.zeroLocus ℂ I) : (MvPolynomial (Fin n) ℂ ⧸ I) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval z.val) (fun p hp => z.property p hp)

@[simp] theorem affineCharacter_mk {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (z : MvPolynomial.zeroLocus ℂ I) (p : MvPolynomial (Fin n) ℂ) :
    affineCharacter I z ((Ideal.Quotient.mkₐ ℂ I) p) = MvPolynomial.eval z.val p := rfl

@[simp] theorem affineCharacter_coordinate {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (z : MvPolynomial.zeroLocus ℂ I) (j : Fin n) :
    affineCharacter I z (quotientCoordinate I j) = z.val j := by
  change MvPolynomial.eval z.val (MvPolynomial.X j) = z.val j
  exact MvPolynomial.eval_X _

theorem character_comp_mk {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (f : (MvPolynomial (Fin n) ℂ ⧸ I) →ₐ[ℂ] ℂ) :
    f.comp (Ideal.Quotient.mkₐ ℂ I) = MvPolynomial.aeval (fun j => f (quotientCoordinate I j)) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [quotientCoordinate]

noncomputable def pointOfCharacter {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (f : (MvPolynomial (Fin n) ℂ ⧸ I) →ₐ[ℂ] ℂ) : MvPolynomial.zeroLocus ℂ I := by
  refine ⟨fun j => f (quotientCoordinate I j), fun p hp => ?_⟩
  have he := DFunLike.congr_fun (character_comp_mk I f) p
  change f (Ideal.Quotient.mk I p) = MvPolynomial.eval _ p at he
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero] at he
  exact he.symm

noncomputable def affineCharacterEquiv {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    MvPolynomial.zeroLocus ℂ I ≃ ((MvPolynomial (Fin n) ℂ ⧸ I) →ₐ[ℂ] ℂ) where
  toFun := affineCharacter I
  invFun := pointOfCharacter I
  left_inv z := by
    apply Subtype.ext
    funext j
    exact affineCharacter_coordinate I z j
  right_inv f := by
    ext t
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I t
    exact (DFunLike.congr_fun (character_comp_mk I f) p).symm

theorem continuous_affineCharacter {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (t : MvPolynomial (Fin n) ℂ ⧸ I) :
    Continuous (fun z : MvPolynomial.zeroLocus ℂ I => affineCharacter I z t) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I t
  exact (MvPolynomial.continuous_eval p).comp continuous_subtype_val

theorem adjoin_quotientCoordinate {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    Algebra.adjoin ℂ (range (quotientCoordinate I)) = ⊤ := by
  have he : range (quotientCoordinate I) =
      (Ideal.Quotient.mkₐ ℂ I) '' range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℂ) :=
    Set.range_comp _ _
  rw [he, Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top]
  exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective ℂ I)

theorem affineCharacter_normalization {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (MvPolynomial (Fin n) ℂ ⧸ I))
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (hP : ∀ j, (Ideal.Quotient.mkₐ ℂ I) (P j) = g (MvPolynomial.X j))
    (z : MvPolynomial.zeroLocus ℂ I) :
    (affineCharacter I z).comp g = MvPolynomial.aeval (fun j => MvPolynomial.eval z.val (P j)) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
  rw [← hP j, affineCharacter_mk]

theorem polynomial_root_near_of_small_eval (p : Polynomial ℂ) (hp : p.Monic)
    (b : ℂ) (ε : ℝ) (hε : 0 < ε) (hb : ‖p.eval b‖ < ε ^ p.natDegree) :
    ∃ z : ℂ, p.eval z = 0 ∧ dist z b < ε := by
  classical
  by_contra! h
  have hs : p.Splits := IsAlgClosed.splits p
  have hprod : (p.roots.map (fun _ => ε)).prod ≤
      (p.roots.map (fun z => ‖b - z‖)).prod := by
    apply Multiset.prod_map_le_prod_map₀
    · intro z _; exact hε.le
    · intro z hz
      have hr : p.eval z = 0 := (Polynomial.mem_roots hp.ne_zero).mp hz
      simpa only [dist_eq_norm, norm_sub_rev] using h z hr
  have he : (p.roots.map (fun z => ‖b - z‖)).prod = ‖p.eval b‖ := by
    rw [hs.eval_eq_prod_roots_of_monic hp]
    exact p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun z => b-z)
  rw [he, Multiset.map_const', Multiset.prod_replicate, ← hs.natDegree_eq_card_roots] at hprod
  exact (not_le_of_gt hb) hprod

theorem polynomial_eventually_exists_near_root {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (hP : P.Monic)
    (a : Fin d → ℂ) (b : ℂ)
    (hb : P.eval₂ (MvPolynomial.eval a) b = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 a, ∃ z : ℂ,
      P.eval₂ (MvPolynomial.eval y) z = 0 ∧ dist z b < ε := by
  have hc : Continuous (fun y : Fin d → ℂ => P.eval₂ (MvPolynomial.eval y) b) := by
    simp only [Polynomial.eval₂_eq_sum_range]
    exact continuous_finsetSum _ (fun j _ =>
      (MvPolynomial.continuous_eval (P.coeff j)).mul continuous_const)
  have he : ∀ᶠ y in 𝓝 a, ‖P.eval₂ (MvPolynomial.eval y) b‖ < ε ^ P.natDegree :=
    hc.norm.continuousAt.eventually (gt_mem_nhds (by
      change ‖P.eval₂ (MvPolynomial.eval a) b‖ < _
      rw [hb, _root_.norm_zero]; positivity))
  filter_upwards [he] with y hy
  obtain ⟨z, hz, hzb⟩ := polynomial_root_near_of_small_eval
    (P.map (MvPolynomial.eval y)) (hP.map _) b ε hε
      (by simpa only [Polynomial.eval_map, hP.natDegree_map] using hy)
  exact ⟨z, by simpa only [Polynomial.eval_map] using hz, hzb⟩

theorem finite_proper_map_open_at_of_root_realization
    {X : Type*} [TopologicalSpace X] {d : ℕ}
    (π : X → (Fin d → ℂ)) (hπ : IsProperMap π) (q : X)
    (hfin : Set.Finite {x : X | π x = π q})
    (s : X → ℂ) (hs : Continuous s)
    (hsep : ∀ x, π x = π q → s x = s q → x = q)
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (hP : P.Monic)
    (hq : P.eval₂ (MvPolynomial.eval (π q)) (s q) = 0)
    (hreal : ∀ y z, P.eval₂ (MvPolynomial.eval y) z = 0 →
      ∃ x, π x = y ∧ s x = z)
    {N : Set X} (hN : IsOpen N) (hqN : q ∈ N) :
    π '' N ∈ 𝓝 (π q) := by
  classical
  let B : Set ℂ := s '' ({x : X | π x = π q} ∩ Nᶜ)
  have hB : B.Finite := (hfin.inter_of_left Nᶜ).image s
  have hqB : s q ∉ B := by
    rintro ⟨x, ⟨hx, hxN⟩, he⟩
    have hxe := hsep x hx he
    exact hxN (hxe ▸ hqN)
  obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.mp (hB.isClosed.isOpen_compl.mem_nhds hqB)
  let F := s ⁻¹' Metric.closedBall (s q) (ε / 2) ∩ Nᶜ
  have hF : IsClosed F := (Metric.isClosed_closedBall.preimage hs).inter hN.isClosed_compl
  have hπF : IsClosed (π '' F) := hπ.isClosedMap F hF
  have haF : π q ∉ π '' F := by
    rintro ⟨x, ⟨hx, hxN⟩, hxa⟩
    have hxB : s x ∈ B := ⟨x, ⟨hxa, hxN⟩, rfl⟩
    have hxball : s x ∈ Metric.ball (s q) ε := by
      change dist (s x) (s q) < ε
      change dist (s x) (s q) ≤ ε / 2 at hx
      exact lt_of_le_of_lt hx (by linarith)
    exact hεB hxball hxB
  have h₁ : ∀ᶠ y in 𝓝 (π q), y ∉ π '' F := hπF.isOpen_compl.mem_nhds haF
  have h₂ := polynomial_eventually_exists_near_root P hP (π q) (s q) hq (ε / 2) (by positivity)
  filter_upwards [h₁, h₂] with y hy hroot
  obtain ⟨z, hz, hzb⟩ := hroot
  obtain ⟨x, hxy, hxz⟩ := hreal y z hz
  refine ⟨x, ?_, hxy⟩
  by_contra hxN
  apply hy
  refine ⟨x, ⟨?_, hxN⟩, hxy⟩
  change dist (s x) (s q) ≤ ε / 2
  rw [hxz]
  exact hzb.le

end Release061

end OAI
