import OAI.AlgebraicGeometry.SurfaceCones.KummerSymmetry
import OAI.AlgebraicGeometry.SurfaceCones.KummerProjChart

namespace OAI

/-! Identification of smooth coefficient algebras with homogeneous Proj charts. -/
noncomputable section
namespace SourceSymmetry
open ExplicitCone Polynomial

lemma coefficientChart_normal (t : SectionIndex) (ht : Good t) :
    IsIntegrallyClosed (coefficientChart t) := by
  let := sectionChart_normal
  exact IsIntegrallyClosed.of_equiv (goodChartEquiv t ht).toRingEquiv

lemma coefficientChart_smooth (t : SectionIndex) (ht : Good t) :
    Algebra.Smooth ℂ (coefficientChart t) := by
  let := sectionChart_smooth
  exact Algebra.Smooth.of_equiv (goodChartEquiv t ht)

def coefficientCartierChart (t : SectionIndex) : Subalgebra ℂ (RatFunc L) :=
  PolynomialFieldChart.chart (coefficientChart t) (sectionCoefficient t)
    (coefficient_ne_zero t)

lemma generator_eq_ratio_mul_at (t i : SectionIndex) :
    generator i = RatFunc.C (sectionCoefficient i / sectionCoefficient t) * generator t := by
  unfold generator
  rw [map_div₀]
  have h : RatFunc.C (sectionCoefficient t) ≠ (0 : RatFunc L) := by
    simpa only [map_zero] using RatFunc.C_injective.ne (coefficient_ne_zero t)
  field_simp

lemma generator_mem_coefficientCartierChart (t i : SectionIndex) :
    generator i ∈ coefficientCartierChart t := by
  rw [generator_eq_ratio_mul_at t i]
  exact (coefficientCartierChart t).mul_mem
    (PolynomialFieldChart.constant_mem _ _ _
      ⟨_, ratioChart_generator sectionCoefficient t i⟩)
    (PolynomialFieldChart.variable_mem _ _ _)

lemma algebra_le_coefficientCartierChart (t : SectionIndex) :
    ExplicitCone.algebra ≤ coefficientCartierChart t := by
  apply Algebra.adjoin_le
  rintro _ ⟨i,rfl⟩
  exact generator_mem_coefficientCartierChart t i

lemma normalizedCone_le_coefficientCartierChart (t : SectionIndex) (ht : Good t) :
    normalizedCone ≤ coefficientCartierChart t := by
  let := coefficientChart_normal t ht
  exact PolynomialFieldChart.integralClosure_le _ _ _ ExplicitCone.algebra
    (algebra_le_coefficientCartierChart t)

lemma integral_polynomial_mem_coefficientCartierChart (t : SectionIndex) (ht : Good t)
    (p : L[X]) (hp : IsIntegral polynomialAlgebra p) :
    algebraMap L[X] (RatFunc L) p ∈ coefficientCartierChart t := by
  apply normalizedCone_le_coefficientCartierChart t ht
  change IsIntegral ExplicitCone.algebra (algebraMap L[X] (RatFunc L) p)
  exact hp.map_of_comp_eq polynomialEquiv.toRingHom (algebraMap L[X] (RatFunc L))
    (by ext p; rfl)

lemma normalized_coefficient_mem_coefficientChart (t : SectionIndex) (ht : Good t)
    (n : ℕ) (a : L) (ha : a ∈ pieces n) :
    a / sectionCoefficient t ^ n ∈ coefficientChart t := by
  have h := PolynomialFieldChart.scaled_coefficient_mem (coefficientChart t)
    (sectionCoefficient t) (coefficient_ne_zero t) (monomial n a)
    (integral_polynomial_mem_coefficientCartierChart t ht _ ha) n
  simpa using h

abbrev projChart (t : SectionIndex) := SectionCompletion.homogeneousChart pieces
  (sectionCoefficient t) (sectionCoefficient_mem_piece t)

def projChartEquiv (t : SectionIndex) (ht : Good t) :
    projChart t ≃ₐ[ℂ] coefficientChart t :=
  SectionCompletion.homogeneousChartAlgEquivOfAdjoin pieces (sectionCoefficient t)
    (sectionCoefficient_mem_piece t) (coefficient_ne_zero t) sectionCoefficient
    sectionCoefficient_mem_piece (normalized_coefficient_mem_coefficientChart t ht)

lemma projChart_smooth (t : SectionIndex) (ht : Good t) :
    Algebra.Smooth ℂ (projChart t) := by
  let := coefficientChart_smooth t ht
  exact Algebra.Smooth.of_equiv (projChartEquiv t ht).symm

open AlgebraicGeometry CategoryTheory
abbrev projSection (t : SectionIndex) := SectionCompletion.linearSection pieces
  (sectionCoefficient t) (sectionCoefficient_mem_piece t)

def projOpenIso (t : SectionIndex) (ht : Good t) :
    (Proj.basicOpen (SectionCompletion.homogeneous pieces) (projSection t)).toScheme ≅
      Spec (CommRingCat.of (coefficientChart t)) :=
  (Proj.basicOpenIsoSpec (SectionCompletion.homogeneous pieces) (projSection t)
    (SectionCompletion.linearSection_homogeneous pieces _ _) (by norm_num : 0 < (1 : ℕ))) ≪≫
    (Scheme.Spec.mapIso ((projChartEquiv t ht).symm.toRingEquiv.toCommRingCatIso).op)

end SourceSymmetry


/-! The twelve smooth section charts cover the normalized Proj. Seventh-power identities account for the remaining six sections. -/
namespace SourceSymmetry
open ExplicitCone Polynomial AlgebraicGeometry CategoryTheory

lemma integral_eq_scalar {k B : Type*} [Field k] [IsAlgClosed k]
    [CommRing B] [IsDomain B] [Algebra k B] {x : B} (hx : IsIntegral k x) :
    ∃ c : k, algebraMap k B c = x := by
  let S := Algebra.adjoin k ({x} : Set B)
  have : Module.Finite k S := Algebra.finite_adjoin_simple_of_isIntegral hx
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := S)).2
    ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  exact ⟨c, congrArg Subtype.val hc⟩

lemma integral_image_scalars
    {k B N Q : Type*} [Field k] [CommRing B] [CommRing N] [CommRing Q] [Nontrivial Q]
    [Algebra k B] [Algebra k N] [Algebra B N] [IsScalarTower k B N] [Algebra k Q]
    (f : N →ₐ[k] Q)
    (hf : ∀ b : B, f (algebraMap B N b) ∈ (⊥ : Subalgebra k Q))
    {x : N} (hx : IsIntegral B x) : IsIntegral k (f x) := by
  let g : B →ₐ[k] Q := f.comp (IsScalarTower.toAlgHom k B N)
  let g' : B →ₐ[k] (⊥ : Subalgebra k Q) := g.codRestrict ⊥ hf
  let φ : B →ₐ[k] k := (Algebra.botEquiv k Q).toAlgHom.comp g'
  apply IsIntegral.map_of_comp_eq φ.toRingHom f.toRingHom _ hx
  apply RingHom.ext
  intro b
  change algebraMap k Q ((Algebra.botEquiv k Q) (g' b)) = g b
  calc
    algebraMap k Q ((Algebra.botEquiv k Q) (g' b)) = (g' b).val := by
      exact congrArg Subtype.val ((Algebra.botEquiv k Q).symm_apply_apply (g' b))
    _ = g b := rfl

lemma adjoin_image_scalars {k B Q : Type*} [CommSemiring k] [CommSemiring B]
    [CommSemiring Q] [Algebra k B] [Algebra k Q] (s : Set B)
    (g : Algebra.adjoin k s →ₐ[k] Q)
    (hg : ∀ x (hx : x ∈ s), g ⟨x, Algebra.subset_adjoin hx⟩ ∈ (⊥ : Subalgebra k Q))
    (b : Algebra.adjoin k s) : g b ∈ (⊥ : Subalgebra k Q) := by
  have hh : ∀ x (hx : x ∈ Algebra.adjoin k s),
      g ⟨x,hx⟩ ∈ (⊥ : Subalgebra k Q) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hg x hx
    | algebraMap a =>
      change g (algebraMap k (Algebra.adjoin k s) a) ∈ _
      rw [g.commutes]
      exact (⊥ : Subalgebra k Q).algebraMap_mem a
    | add a b ha hb h₁ h₂ =>
      change g (⟨a,ha⟩ + ⟨b,hb⟩) ∈ _
      rw [map_add]
      exact (⊥ : Subalgebra k Q).add_mem h₁ h₂
    | mul a b ha hb h₁ h₂ =>
      change g (⟨a,ha⟩ * ⟨b,hb⟩) ∈ _
      rw [map_mul]
      exact (⊥ : Subalgebra k Q).mul_mem h₁ h₂
  exact hh b.val b.property

/-- Integral homogeneous extensions acquire no nonvertex point over the common vanishing of the generators. -/
lemma homogeneous_mem_of_integral_adjoin {k B A : Type*}
    [Field k] [IsAlgClosed k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    (s : Set B) (f : Algebra.adjoin k s →ₐ[k] A)
    (hint : f.toRingHom.IsIntegral) (P : HomogeneousIdeal 𝒜) [P.toIdeal.IsPrime]
    (hgen : ∀ a (ha : a ∈ s), f ⟨a, Algebra.subset_adjoin ha⟩ ∈ P)
    {n : ℕ} (hn : 0 < n) {b : A} (hb : b ∈ 𝒜 n) : b ∈ P := by
  let : Algebra (Algebra.adjoin k s) A := f.toAlgebra
  let : IsScalarTower k (Algebra.adjoin k s) A :=
    IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  have hscalar : ∀ a : Algebra.adjoin k s,
      (Ideal.Quotient.mkₐ k P.toIdeal) (f a) ∈ (⊥ : Subalgebra k (A ⧸ P.toIdeal)) := by
    apply adjoin_image_scalars s ((Ideal.Quotient.mkₐ k P.toIdeal).comp f)
    intro a ha
    change (Ideal.Quotient.mkₐ k P.toIdeal) (f ⟨a, _⟩) ∈ _
    have hz : (Ideal.Quotient.mkₐ k P.toIdeal) (f ⟨a, _⟩) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hgen a ha)
    rw [hz]
    exact zero_mem _
  have hi' : IsIntegral k ((Ideal.Quotient.mkₐ k P.toIdeal) b) :=
    integral_image_scalars (B := Algebra.adjoin k s) (N := A)
      (Ideal.Quotient.mkₐ k P.toIdeal) hscalar (hint b)
  obtain ⟨c,hc⟩ := integral_eq_scalar hi'
  have hd : b - algebraMap k A c ∈ P := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr hc.symm
  have hd' := P.isHomogeneous n hd
  have hcdeg : algebraMap k A c ∈ 𝒜 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (𝒜 0).smul_mem c SetLike.GradedOne.one_mem
  change (DirectSum.decompose 𝒜 (b - algebraMap k A c) n : A) ∈ P.toIdeal at hd'
  rw [DirectSum.decompose_sub] at hd'
  change (DirectSum.decompose 𝒜 b n : A) -
    (DirectSum.decompose 𝒜 (algebraMap k A c) n : A) ∈ P.toIdeal at hd'
  change b ∈ P.toIdeal
  simpa only [DirectSum.decompose_of_mem_same 𝒜 hb,
    DirectSum.decompose_of_mem_ne 𝒜 hcdeg (Nat.ne_of_gt hn).symm,
    ZeroMemClass.coe_zero, sub_zero] using hd'

abbrev S := SectionCompletion.polynomials pieces
abbrev grading := SectionCompletion.homogeneous pieces

def normalizationInclusion : polynomialAlgebra →ₐ[ℂ] S :=
  Subalgebra.inclusion fun p hp => by
    change p ∈ SectionCompletion.polynomials (GradedNormalization.piece polynomialAlgebra)
    rw [GradedNormalization.polynomial_piece_eq polynomialAlgebra polynomialAlgebra_scale]
    exact isIntegral_algebraMap (x := (⟨p,hp⟩ : polynomialAlgebra))

lemma normalization_generator (t : SectionIndex) :
    normalizationInclusion
      ⟨polynomialGenerator t, Algebra.subset_adjoin (Set.mem_range_self t)⟩ = projSection t := by
  apply Subtype.ext
  exact polynomialGenerator_eq_monomial t

lemma normalizationInclusion_integral :
    RingHom.IsIntegral (R := polynomialAlgebra) (A := S) normalizationInclusion.toRingHom := by
  intro b
  have hp := b.property
  change b.val ∈ SectionCompletion.polynomials (GradedNormalization.piece polynomialAlgebra) at hp
  rw [GradedNormalization.polynomial_piece_eq polynomialAlgebra polynomialAlgebra_scale] at hp
  change IsIntegral polynomialAlgebra (b : L[X]) at hp
  apply RingHom.IsIntegralElem.of_map
    (R := polynomialAlgebra) (S := S) (T := L[X])
    (f := normalizationInclusion.toRingHom) (g := S.val.toRingHom)
    Subtype.val_injective
  change IsIntegral polynomialAlgebra (b : L[X])
  exact hp

lemma homogeneous_integral_mem (P : HomogeneousIdeal grading) [P.toIdeal.IsPrime]
    (hgen : ∀ t, projSection t ∈ P) {n : ℕ} (hn : 0 < n)
    {b : S} (hb : b ∈ grading n) : b ∈ P := by
  apply homogeneous_mem_of_integral_adjoin grading (Set.range polynomialGenerator)
    normalizationInclusion normalizationInclusion_integral P ?_ hn hb
  rintro _ ⟨t,rfl⟩
  rw [normalization_generator]
  exact hgen t

lemma exists_section_nonvanishing (x : projectiveSurface) :
    ∃ t, projSection t ∉ x.asHomogeneousIdeal := by
  let := x.isPrime
  by_contra h
  push Not at h
  apply x.not_irrelevant_le
  change (HomogeneousIdeal.irrelevant grading).toIdeal ≤ x.asHomogeneousIdeal.toIdeal
  apply (HomogeneousIdeal.toIdeal_irrelevant_le grading).mpr
  intro n hn b hb
  exact homogeneous_integral_mem x.asHomogeneousIdeal h hn hb

lemma section_linear_pow_add {i j k : SectionIndex}
    (h : sectionCoefficient i ^ 7 = sectionCoefficient j ^ 7 + sectionCoefficient k ^ 7) :
    projSection i ^ 7 = projSection j ^ 7 + projSection k ^ 7 := by
  apply Subtype.ext
  change monomial 1 (sectionCoefficient i) ^ 7 =
    monomial 1 (sectionCoefficient j) ^ 7 + monomial 1 (sectionCoefficient k) ^ 7
  simp only [monomial_pow, h, map_add]

lemma section_linear_pow_sub {i j k : SectionIndex}
    (h : sectionCoefficient i ^ 7 = sectionCoefficient j ^ 7 - sectionCoefficient k ^ 7) :
    projSection i ^ 7 = projSection j ^ 7 - projSection k ^ 7 := by
  apply Subtype.ext
  change monomial 1 (sectionCoefficient i) ^ 7 =
    monomial 1 (sectionCoefficient j) ^ 7 - monomial 1 (sectionCoefficient k) ^ 7
  simp only [monomial_pow, h, map_sub]

lemma section_mem_of_good_mem (P : Ideal S) [P.IsPrime]
    (h : ∀ t, Good t → projSection t ∈ P) (t : SectionIndex) : projSection t ∈ P := by
  have ha {i j k : SectionIndex}
      (e : sectionCoefficient i ^ 7 = sectionCoefficient j ^ 7 + sectionCoefficient k ^ 7)
      (hj : Good j) (hk : Good k) : projSection i ∈ P := by
    apply (Ideal.IsPrime.mem_of_pow_mem (inferInstance : P.IsPrime) (n := 7))
    rw [section_linear_pow_add e]
    exact P.add_mem (P.pow_mem_of_mem (h j hj) 7 (by decide)) (P.pow_mem_of_mem (h k hk) 7 (by decide))
  have hs {i j k : SectionIndex}
      (e : sectionCoefficient i ^ 7 = sectionCoefficient j ^ 7 - sectionCoefficient k ^ 7)
      (hj : Good j) (hk : Good k) : projSection i ∈ P := by
    apply (Ideal.IsPrime.mem_of_pow_mem (inferInstance : P.IsPrime) (n := 7))
    rw [section_linear_pow_sub e]
    exact P.sub_mem (P.pow_mem_of_mem (h j hj) 7 (by decide)) (P.pow_mem_of_mem (h k hk) 7 (by decide))
  rcases t with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact h _ (by unfold Good; decide)
    | exact ha section_pow_10 (by unfold Good; decide) (by unfold Good; decide)
    | exact hs section_pow_40 (by unfold Good; decide) (by unfold Good; decide)
    | exact ha section_pow_21 (by unfold Good; decide) (by unfold Good; decide)
    | exact hs section_pow_31 (by unfold Good; decide) (by unfold Good; decide)
    | exact hs section_pow_52 (by unfold Good; decide) (by unfold Good; decide)
    | exact hs section_pow_02 (by unfold Good; decide) (by unfold Good; decide)

abbrev GoodIndex := {t : SectionIndex // Good t}

def smoothOpen (t : GoodIndex) : projectiveSurface.Opens :=
  Proj.basicOpen grading (projSection t.val)

lemma smoothOpen_cover : iSup smoothOpen = ⊤ := by
  apply top_unique
  intro x _
  let := x.isPrime
  obtain ⟨t,ht⟩ := exists_section_nonvanishing x
  have he : ∃ t : GoodIndex, projSection t.val ∉ x.asHomogeneousIdeal := by
    by_contra h
    push Not at h
    exact ht (section_mem_of_good_mem x.asHomogeneousIdeal.toIdeal
      (fun t ht => h ⟨t,ht⟩) t)
  obtain ⟨t,ht⟩ := he
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t,ht⟩

end SourceSymmetry

end

end OAI
