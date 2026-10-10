import Mathlib
import OAI.Analysis.SymmetricDomains.ScalarEquicontinuousHolomorphy
import OAI.Analysis.SymmetricDomains.PrimeZeroLocusMaximum

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

theorem zeroLocus_maximum_local {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    {W : Set (MvPolynomial.zeroLocus ℂ I)} (hW : IsOpen W)
    (h : ℕ → MvPolynomial.zeroLocus ℂ I → ℂ)
    (hh : ∀ i x, x ∈ W → ScalarAnalyticAt (h i) x)
    (hb : ∀ i x, x ∈ W → ‖h i x‖ ≤ 1)
    (f : MvPolynomial.zeroLocus ℂ I → ℂ) (hfc : ContinuousOn f W)
    (ht : ∀ x ∈ W, Tendsto (fun i => h i x) atTop (𝓝 (f x)))
    {q : MvPolynomial.zeroLocus ℂ I} (hq : q ∈ W) (hfq : f q = 1) :
    ∀ᶠ x in 𝓝 q, f x = 1 := by
  have : Finite I.minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).to_subtype
  let T : I.minimalPrimes → Set (MvPolynomial.zeroLocus ℂ I) :=
    fun J => {x | x.val ∈ MvPolynomial.zeroLocus ℂ J.val}
  have hT : ⋃ J, T J = univ := by
    apply eq_univ_of_forall
    intro x
    have hx := (zeroLocus_eq_union_minimalPrimes I).subset x.property
    rcases mem_iUnion.mp hx with ⟨J,hJ⟩
    exact mem_iUnion.mpr ⟨J,hJ⟩
  have he : 𝓝 q = ⨆ J, 𝓝[T J] q := by
    rw [← nhdsWithin_iUnion, hT, nhdsWithin_univ]
  rw [he, Filter.eventually_iSup]
  intro J
  by_cases hqJ : q ∈ T J
  · let : J.val.IsPrime := J.property.isPrime
    have hJI : MvPolynomial.zeroLocus ℂ J.val ⊆ MvPolynomial.zeroLocus ℂ I :=
      MvPolynomial.zeroLocus_anti_mono J.property.le
    let s : MvPolynomial.zeroLocus ℂ J.val → MvPolynomial.zeroLocus ℂ I :=
      fun x => ⟨x.val, hJI x.property⟩
    have hs : Continuous s := continuous_subtype_val.subtype_mk _
    have hem := prime_zeroLocus_maximum_local J.val (hW.preimage hs)
      (fun i x => h i (s x))
      (fun i x hx => (hh i (s x) hx).restrict hJI)
      (fun i x hx => hb i (s x) hx) (fun x => f (s x))
      (hfc.comp hs.continuousOn (fun _ hx => hx))
      (fun x hx => ht (s x) hx) (q := ⟨q.val,hqJ⟩) hq hfq
    rw [← eventually_nhds_subtype_iff (T J) ⟨q,hqJ⟩ (fun x => f x = 1)]
    let g : T J → MvPolynomial.zeroLocus ℂ J.val := fun x => ⟨x.val.val,x.property⟩
    have hg : Continuous g := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (hg.continuousAt (x := (⟨q,hqJ⟩ : T J))).eventually hem
  · have heq : 𝓝[T J] q = ⊥ := by
      rw [← notMem_closure_iff_nhdsWithin_eq_bot]
      have hclosed : IsClosed (T J) := (zeroLocus_closed J.val).preimage continuous_subtype_val
      simpa only [hclosed.closure_eq] using hqJ
    simp [heq]

theorem scalar_maximum_local_of_holomorphy {n : ℕ}
    {V U : Set (Affine n)} (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (h : ℕ → U → ℂ) (hh : ∀ i q, ScalarAnalyticAt (h i) q)
    (hb : ∀ i q, ‖h i q‖ ≤ 1) (f : U → ℂ) (hfc : Continuous f)
    (ht : ∀ x, Tendsto (fun i => h i x) atTop (𝓝 (f x)))
    {q : U} (hfq : f q = 1) : ∀ᶠ x in 𝓝 q, f x = 1 := by
  classical
  let I := MvPolynomial.vanishingIdeal ℂ V
  have hUI : U ⊆ MvPolynomial.zeroLocus ℂ I := by
    simpa only [I, hV.zeroLocus_vanishingIdeal] using hUV
  have hUo : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U) := by
    rw [show MvPolynomial.zeroLocus ℂ I = V from hV.zeroLocus_vanishingIdeal]
    exact hU
  let H : ℕ → MvPolynomial.zeroLocus ℂ I → ℂ :=
    fun i x => if hx : x.val ∈ U then h i ⟨x.val,hx⟩ else 0
  let F : MvPolynomial.zeroLocus ℂ I → ℂ :=
    fun x => if hx : x.val ∈ U then f ⟨x.val,hx⟩ else 0
  have hH : ∀ i (x : U), H i (Set.inclusion hUI x) = h i x := by
    intro i x
    simp only [H, Set.inclusion, x.property, dite_true]
  have hF : ∀ x : U, F (Set.inclusion hUI x) = f x := by
    intro x
    simp only [F, Set.inclusion, x.property, dite_true]
  have hHg : ∀ i x, x.val ∈ U → ScalarAnalyticAt (H i) x := by
    intro i x hx
    exact scalarAnalyticAt_of_open_extension hUI hUo (hH i) (hh i ⟨x.val,hx⟩)
  have hHb : ∀ i x, x.val ∈ U → ‖H i x‖ ≤ 1 := by
    intro i x hx
    simpa only [← hH i ⟨x.val,hx⟩] using hb i ⟨x.val,hx⟩
  have hFc : ContinuousOn F ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U) := by
    intro x hx
    have hcat : ContinuousAt F (Set.inclusion hUI ⟨x.val,hx⟩) := by
      rw [ContinuousAt, ← (Topology.IsOpenEmbedding.inclusion hUI hUo).map_nhds_eq]
      change Tendsto (F ∘ Set.inclusion hUI) (𝓝 (⟨x.val,hx⟩ : U)) (𝓝 (F x))
      have hFx : F x = f ⟨x.val,hx⟩ := hF ⟨x.val,hx⟩
      simpa only [Function.comp_def, hF, hFx] using
        (hfc.continuousAt (x := (⟨x.val,hx⟩ : U))).tendsto
    exact hcat.continuousWithinAt
  have hHt : ∀ x, x.val ∈ U → Tendsto (fun i => H i x) atTop (𝓝 (F x)) := by
    intro x hx
    simpa only [← hH _ ⟨x.val,hx⟩, ← hF ⟨x.val,hx⟩] using ht ⟨x.val,hx⟩
  have he := zeroLocus_maximum_local I hUo H hHg hHb F hFc hHt
    (q := Set.inclusion hUI q) q.property (by simpa only [hF] using hfq)
  have he' := (Topology.IsEmbedding.inclusion hUI).continuous.continuousAt.eventually he
  simpa only [hF] using he'

theorem scalar_maximum_of_holomorphy {n : ℕ}
    {V U : Set (Affine n)} (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U)) (hconn : IsPreconnected U)
    (h : ℕ → U → ℂ) (hh : ∀ i q, ScalarAnalyticAt (h i) q)
    (hb : ∀ i q, ‖h i q‖ ≤ 1) (f : U → ℂ) (hfc : Continuous f)
    (ht : ∀ x, Tendsto (fun i => h i x) atTop (𝓝 (f x)))
    {q : U} (hfq : f q = 1) : ∀ x, f x = 1 := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  exact eq_one_of_local_maximum_propagation f hfc q hfq
    (fun _ hx => scalar_maximum_local_of_holomorphy hV hUV hU h hh hb f hfc ht hx)

theorem scalar_singular_montel {n : ℕ}
    {V U : Set (Affine n)} (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (h : ℕ → U → ℂ) (hh : ∀ i q, ScalarAnalyticAt (h i) q)
    (hb : ∀ i q, ‖h i q‖ ≤ 1) :
    ∃ f : U → ℂ, Continuous f ∧ (∀ x, ‖f x‖ ≤ 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformly (fun i => h (φ i)) f atTop := by
  let : LocallyCompactSpace U := locallyCompact_of_relative_open hV hUV hU
  exact locally_uniform_subsequence_of_equicontinuous h
    (scalar_equicontinuous_of_holomorphy hV hUV hU h hh hb) hb

theorem integral_minpoly_constant_ne_zero
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    {x : S} (hx : IsIntegral R x) (hx0 : x ≠ 0) : (minpoly R x).coeff 0 ≠ 0 := by
  intro he
  have hdiv : X ∣ minpoly R x := X_dvd_iff.mpr he
  have hassoc : Associated (minpoly R x) X :=
    associated_of_dvd_dvd ((irreducible_X).dvd_symm (minpoly.irreducible hx) hdiv) hdiv
  have heq : minpoly R x = X := eq_of_monic_of_associated (minpoly.monic hx) monic_X hassoc
  have ha := minpoly.aeval R x
  rw [heq, aeval_X] at ha
  exact hx0 ha

theorem dense_character_nonzero {d : ℕ}
    {S X : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra (MvPolynomial (Fin d) ℂ) S]
    [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) S]
    [Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) S]
    [TopologicalSpace X]
    (e : X → (S →ₐ[ℂ] ℂ)) (π : X → (Fin d → ℂ)) (hπo : IsOpenMap π)
    (hbase : ∀ x r, e x (algebraMap (MvPolynomial (Fin d) ℂ) S r) = MvPolynomial.eval (π x) r)
    (t : S) (ht : t ≠ 0) : Dense {x | e x t ≠ 0} := by
  let R := MvPolynomial (Fin d) ℂ
  have htint : IsIntegral R t := Algebra.IsIntegral.isIntegral t
  have hP : (minpoly R t).coeff 0 ≠ 0 := integral_minpoly_constant_ne_zero htint ht
  apply ((dense_polynomial_nonzero ((minpoly R t).coeff 0) hP).preimage hπo).mono
  intro x hx hxt
  have hroot : (minpoly R t).eval₂ (MvPolynomial.eval (π x)) (e x t) = 0 := by
    rw [← algHom_aeval_of_base (e x) _ (hbase x), minpoly.aeval, map_zero]
  rw [hxt, Polynomial.eval₂_at_zero] at hroot
  exact hx hroot

theorem prime_zeroLocus_dense_polynomial_nonzero {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (Q : MvPolynomial (Fin n) ℂ) (hQI : Q ∉ I) :
    Dense {x : MvPolynomial.zeroLocus ℂ I | MvPolynomial.eval x.val Q ≠ 0} := by
  obtain ⟨d, _, g, hg, hgi⟩ := exists_integral_inj_algHom_of_quotient I Ideal.IsPrime.ne_top'
  choose P hP using fun j : Fin d => Ideal.Quotient.mkₐ_surjective ℂ I (g (MvPolynomial.X j))
  have ho := normalization_isOpenMap I g hg hgi P hP
  let R := MvPolynomial (Fin d) ℂ
  let S := MvPolynomial (Fin n) ℂ ⧸ I
  let normalizationAlgebra : Algebra R S := g.toRingHom.toAlgebra
  let : SMul R S := normalizationAlgebra.toSMul
  let : IsScalarTower ℂ R S := IsScalarTower.of_algHom g
  let : Algebra.IsIntegral R S := ⟨hgi⟩
  have ht : (Ideal.Quotient.mkₐ ℂ I) Q ≠ 0 := by
    intro he
    exact hQI (Ideal.Quotient.eq_zero_iff_mem.mp he)
  have hd := dense_character_nonzero (S := S) (affineCharacterEquiv I) _ ho
    (fun z r => DFunLike.congr_fun (affineCharacter_normalization I g P hP z) r)
    ((Ideal.Quotient.mkₐ ℂ I) Q) ht
  convert! hd using 1

theorem finite_sheet_isolating_neighborhood
    {X Y K : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [Finite K]
    (s : K → Y → X) {a : Y} (hs : ∀ i, ContinuousAt (s i) a)
    (hi : Function.Injective (fun i => s i a)) (i : K) :
    ∃ O : Set X, IsOpen O ∧ s i a ∈ O ∧ ∃ B : Set Y, IsOpen B ∧ a ∈ B ∧
      ∀ y ∈ B, ∀ j, s j y ∈ O ↔ j = i := by
  classical
  let A : Set X := Set.range (fun j => s j a)
  obtain ⟨U,hU,hUdisj⟩ := (Set.finite_range (fun j => s j a)).t2_separation
  have ha : s i a ∈ A := mem_range_self i
  let O := U (s i a)
  have hO : IsOpen O := (hU _).2
  have hsO : ∀ᶠ y in 𝓝 a, s i y ∈ O := (hs i).preimage_mem_nhds (hO.mem_nhds ((hU _).1))
  have hsnot : ∀ j, ∀ᶠ y in 𝓝 a, j ≠ i → s j y ∉ O := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ hj => False.elim (hj hji))
    · have haj : s j a ∈ A := mem_range_self j
      have hDis : Disjoint (U (s j a)) O := hUdisj haj ha (fun he => hji (hi he))
      filter_upwards [(hs j).preimage_mem_nhds (((hU _).2).mem_nhds ((hU _).1))] with y hy _
      exact Set.disjoint_left.mp hDis hy
  have hE : ∀ᶠ y in 𝓝 a, ∀ j, s j y ∈ O ↔ j = i := by
    filter_upwards [hsO, Filter.eventually_all.mpr hsnot] with y hy hnot
    intro j
    constructor
    · intro hj
      by_contra hji
      exact hnot j hji hj
    · rintro rfl
      exact hy
  obtain ⟨B,hBE,hBo,haB⟩ := mem_nhds_iff.mp hE
  exact ⟨O,hO,(hU _).1,B,hBo,haB,hBE⟩

theorem holomorphicOnSubset_of_analyticOnNhd {n m : ℕ} {S : Set (Affine n)}
    {F : Affine n → Affine m} (hF : AnalyticOnNhd ℂ F S) :
    HolomorphicOnSubset S (fun x => F x.val) := by
  intro q
  obtain ⟨r,hr,hFr⟩ := (hF q q.property).exists_ball_analyticOnNhd
  exact ⟨Metric.ball q.val r,Metric.isOpen_ball,Metric.mem_ball_self hr,F,hFr,fun _ _ => rfl⟩

noncomputable def biholomorphOfAmbientInverse {n m : ℕ}
    (S : Set (Affine n)) (D : Set (Affine m))
    (F : Affine n → Affine m) (G : Affine m → Affine n)
    (hF : AnalyticOnNhd ℂ F S) (hG : AnalyticOnNhd ℂ G D)
    (hFD : MapsTo F S D) (hGS : MapsTo G D S)
    (hGF : ∀ x ∈ S, G (F x) = x) (hFG : ∀ y ∈ D, F (G y) = y) :
    Biholomorph S D where
  toHomeomorph := {
    toEquiv := {
      toFun := fun x => ⟨F x.val,hFD x.property⟩
      invFun := fun y => ⟨G y.val,hGS y.property⟩
      left_inv := fun x => Subtype.ext (hGF x x.property)
      right_inv := fun y => Subtype.ext (hFG y y.property) }
    continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp hF.continuousOn).subtype_mk _
    continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp hG.continuousOn).subtype_mk _ }
  holomorphic_toFun := holomorphicOnSubset_of_analyticOnNhd hF
  holomorphic_invFun := holomorphicOnSubset_of_analyticOnNhd hG

end Release061

end OAI
