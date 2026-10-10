import OAI.AlgebraicGeometry.SurfaceCones.KummerProjChart

namespace OAI


noncomputable section
private lemma finiteType_of_sup_ranges
    {R S U B : Type*} [CommRing R] [CommRing S] [CommRing U] [CommRing B]
    [Algebra R S] [Algebra R U] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    [Algebra.FiniteType R U] (g : U →ₐ[R] B)
    (heq : (IsScalarTower.toAlgHom R S B).range ⊔ g.range = ⊤) :
    Algebra.FiniteType S B := by
  classical
  obtain ⟨s,hs⟩ := Algebra.FiniteType.out (R := R) (A := U)
  refine ⟨⟨s.image g, ?_⟩⟩
  let C := Algebra.adjoin S (↑(s.image g) : Set B)
  have hf : (IsScalarTower.toAlgHom R S B).range ≤ C.restrictScalars R := by
    rintro _ ⟨f,rfl⟩
    exact C.algebraMap_mem f
  have hg : g.range ≤ C.restrictScalars R := by
    rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin]
    apply Algebra.adjoin_le
    rintro _ ⟨a,ha,rfl⟩
    change g a ∈ Algebra.adjoin S (↑(s.image g) : Set B)
    apply Algebra.subset_adjoin
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have he := sup_le hf hg
  rw [heq] at he
  exact top_unique fun b _ => he (Set.mem_univ b)

namespace CompletedCartierChart
variable {k L : Type} [Field k] [Field L] [Algebra k L]
variable (T : ℕ → Submodule k L) [SetLike.GradedMonoid T]
variable (A : Subalgebra k L) (c : L)
variable (h : ∀ n a, a ∈ T n → a / c ^ n ∈ A)

instance sourceAlgebra : Algebra (SectionCompletion.series T) (chart T A c h) :=
  (sourceHom T A c h).toAlgebra

instance sourceTower : IsScalarTower k (SectionCompletion.series T) (chart T A c h) :=
  IsScalarTower.of_algHom (sourceHom T A c h)

instance finiteType [Algebra.FiniteType k A] :
    Algebra.FiniteType (SectionCompletion.series T) (chart T A c h) :=
  finiteType_of_sup_ranges (constantHom T A c h) (generators_sup_top T A c h)

lemma noetherian [Algebra.FiniteType k A]
    [IsNoetherianRing (SectionCompletion.series T)] :
    IsNoetherianRing (chart T A c h) :=
by
  let := finiteType T A c h
  exact Algebra.FiniteType.isNoetherianRing (SectionCompletion.series T) (chart T A c h)

end CompletedCartierChart


namespace RegularCartierLocal
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Lifting a minimal generating set through a surjection with principal
kernel adds at most one generator.  No regularity hypothesis is hidden
in this elementary embedding-dimension estimate. -/
theorem spanFinrank_le_map_add_one (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hI : I.FG) (x : R) (hxI : x ∈ I)
    (hker : RingHom.ker f = Ideal.span {x}) :
    I.spanFinrank ≤ (I.map f).spanFinrank + 1 := by
  classical
  obtain ⟨g, hgrev⟩ := hf.hasRightInverse
  have hg : ∀ b, f (g b) = b := hgrev
  let s := (I.map f).generators
  have hIf : (I.map f).FG := hI.map f
  have hs : s.Finite := Submodule.FG.finite_generators hIf
  let t := insert x (g '' s)
  have ht : t.Finite := (hs.image g).insert x
  have hkerI : RingHom.ker f ≤ I := by
    rw [hker]
    exact (Ideal.span_singleton_le_iff_mem I).mpr hxI
  have hkerJ : RingHom.ker f ≤ Ideal.span t := by
    rw [hker]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert x _))
  have hx0 : f x = 0 := by
    exact RingHom.mem_ker.mp (hker ▸ Ideal.subset_span (Set.mem_singleton x))
  have hmap : (Ideal.span t).map f = I.map f := by
    rw [Ideal.map_span]
    have him : f '' t = insert 0 s := by
      simp only [t, Set.image_insert_eq, hx0, Set.image_image, hg, Set.image_id']
    rw [him]
    change Submodule.span S (insert 0 s) = _
    rw [Submodule.span_insert_zero]
    exact (I.map f).span_generators
  have hspan : Ideal.span t = I := by
    have h := (Ideal.map_eq_iff_sup_ker_eq_of_surjective f hf).mp hmap
    simpa only [sup_of_le_left hkerI, sup_of_le_left hkerJ] using h
  calc
    I.spanFinrank = (Ideal.span t).spanFinrank := congrArg Submodule.spanFinrank hspan.symm
    _ ≤ t.ncard := Submodule.spanFinrank_span_le_ncard_of_finite ht
    _ ≤ (g '' s).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ s.ncard + 1 := Nat.add_le_add_right (Set.ncard_image_le hs) 1
    _ = (I.map f).spanFinrank + 1 := by exact congrArg (· + 1) (Submodule.FG.generators_ncard hIf)

/-- A regular Cartier quotient of a Noetherian local ring lifts regularity
to the ambient ring. -/
theorem isRegularLocalRing_of_quotient [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular R x)
    [IsRegularLocalRing (R ⧸ Ideal.span {x})] : IsRegularLocalRing R := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h := spanFinrank_le_map_add_one (Ideal.Quotient.mk (Ideal.span {x}))
    Ideal.Quotient.mk_surjective (maximalIdeal R) (IsNoetherian.noetherian _) x hx
    Ideal.mk_ker
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
  calc
    ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
        (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by exact_mod_cast h
    _ = ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal]
    _ = ringKrullDim R := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hx

end RegularCartierLocal


namespace RegularCartierLocalization
variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- Every point of a regular effective principal divisor in a Noetherian
integral scheme is a regular point of the ambient scheme. -/
theorem regular_at_prime (x : R) (hx : x ≠ 0)
    [IsRegularRing (R ⧸ Ideal.span {x})]
    (p : Ideal R) [p.IsPrime] (hxp : x ∈ p) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let S := Localization.AtPrime p
  let I : Ideal R := Ideal.span {x}
  let J : Ideal S := I.map (algebraMap R S)
  have hJ : J = Ideal.span {algebraMap R S x} := by
    simp only [J, I, Ideal.map_span, Set.image_singleton]
  have hm : algebraMap R S x ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff S p x).mpr hxp
  have hle : J ≤ IsLocalRing.maximalIdeal S := by
    rw [hJ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hm
  let : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hle)
  let : IsLocalRing (S ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsRegularRing (S ⧸ J) :=
    RegularLocalization.regular (Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl)
  have hq : IsRegularLocalRing (S ⧸ J) :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing (S ⧸ J)
  rw [hJ] at hq
  let := hq
  apply RegularCartierLocal.isRegularLocalRing_of_quotient (algebraMap R S x) hm
  exact IsSMulRegular.of_ne_zero (by simpa only [map_zero] using
    (FaithfulSMul.algebraMap_injective R S).ne hx)

end RegularCartierLocalization


namespace ExplicitCone

/-- The Cartier chart generated by the degreewise completed cone and the
constants of its Proj basic open, inside the coefficient power-series ring. -/
abbrev completedAffineChart := CompletedCartierChart.chart pieces sectionChart
  (sectionCoefficient (0,0)) normalized_coefficient_mem_sectionChart

instance completedAffineCommRing : CommRing completedAffineChart := completedAffineChart.toCommRing
instance completedAffineRing : Ring completedAffineChart := completedAffineCommRing.toRing
instance completedAffineSemiring : Semiring completedAffineChart := completedAffineRing.toSemiring

abbrev completedAffineSource : completedRing →ₐ[ℂ] completedAffineChart :=
  CompletedCartierChart.sourceHom pieces sectionChart
    (sectionCoefficient (0,0)) normalized_coefficient_mem_sectionChart

abbrev completedAffineParameter : completedAffineChart :=
  CompletedCartierChart.parameter pieces sectionChart
    (sectionCoefficient (0,0)) normalized_coefficient_mem_sectionChart
      (sectionCoefficient_mem_piece (0,0)) sectionCoefficient_base_ne_zero

theorem completedAffineSource_injective : Function.Injective completedAffineSource := by
  intro a b hab
  apply SectionChartSeries.hom_injective pieces sectionChart (sectionCoefficient (0,0))
    normalized_coefficient_mem_sectionChart sectionCoefficient_base_ne_zero
  exact congrArg Subtype.val hab

theorem completedAffineParameter_ne_zero : completedAffineParameter ≠ 0 :=
  CompletedCartierChart.parameter_ne_zero pieces sectionChart
    (sectionCoefficient (0,0)) normalized_coefficient_mem_sectionChart
      (sectionCoefficient_mem_piece (0,0)) sectionCoefficient_base_ne_zero

instance completedAffine_finiteType : Algebra.FiniteType completedRing completedAffineChart :=
  CompletedCartierChart.finiteType pieces sectionChart
    (sectionCoefficient (0,0)) normalized_coefficient_mem_sectionChart

instance completedAffine_noetherian : IsNoetherianRing completedAffineChart := by
  let := actualCompletion_noetherian
  exact CompletedCartierChart.noetherian pieces sectionChart
    (sectionCoefficient (0,0)) normalized_coefficient_mem_sectionChart

/-- The exceptional divisor on the completed affine chart is isomorphic
to the smooth chart of the projective section ring. -/
def completedAffineExceptionalEquiv :
    (completedAffineChart ⧸ Ideal.span {completedAffineParameter}) ≃ₐ[ℂ] sectionChart :=
  CompletedCartierChart.exceptionalEquiv pieces sectionChart
    (sectionCoefficient (0,0)) normalized_coefficient_mem_sectionChart zero_piece
      (sectionCoefficient_mem_piece (0,0)) sectionCoefficient_base_ne_zero

instance completedAffineExceptional_regular :
    IsRegularRing (completedAffineChart ⧸ Ideal.span {completedAffineParameter}) := by
  let := sectionChart_regular
  exact IsRegularRing.of_ringEquiv completedAffineExceptionalEquiv.symm.toRingEquiv

/-- In particular every prime lying on its exceptional divisor is a genuine
regular local ring of the algebraic completed-cone chart. -/
theorem completedAffine_regular_at_exceptional (p : Ideal completedAffineChart) [p.IsPrime]
    (hp : completedAffineParameter ∈ p) : IsRegularLocalRing (Localization.AtPrime p) :=
  RegularCartierLocalization.regular_at_prime completedAffineParameter
    completedAffineParameter_ne_zero p hp

end ExplicitCone


namespace ExplicitCone

/-- The actual completed cone embeds in the formal Cartier chart over the
literal `z₀z₁z₄` section open. This does NOT assert that the formal chart
is the uncompleted affine blowup base change. -/
def completedChartMap : completedRing →ₐ[ℂ] PowerSeries sectionChart :=
  SectionChartSeries.hom pieces sectionChart (sectionCoefficient (0,0))
    normalized_coefficient_mem_sectionChart

theorem completedChartMap_injective : Function.Injective completedChartMap :=
  SectionChartSeries.hom_injective pieces sectionChart (sectionCoefficient (0,0))
    normalized_coefficient_mem_sectionChart sectionCoefficient_base_ne_zero

lemma completedChartMap_coeff (f : completedRing) (n : ℕ) :
    ((PowerSeries.coeff n (completedChartMap f) : sectionChart) : L) =
      PowerSeries.coeff n f.val / sectionCoefficient (0,0) ^ n :=
  SectionChartSeries.coeff_hom _ _ _ _ _ _

/-- The original degree-one section, as an element of the degreewise
completion used in `MainClaim`. -/
def completedSection (i : Fin 6 × Fin 3) : completedRing :=
  ⟨PowerSeries.monomial 1 (sectionCoefficient i), by
    intro n
    by_cases hn : n = 1
    · subst n; simpa using sectionCoefficient_mem_piece i
    · simp [PowerSeries.coeff_monomial, hn]⟩

lemma completedChartMap_section (i : Fin 6 × Fin 3) :
    completedChartMap (completedSection i) =
      PowerSeries.C (⟨sectionRatio i, ratio_mem_sectionChart i⟩ : sectionChart) *
        PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  apply Subtype.ext
  rw [completedChartMap_coeff]
  simp only [completedSection, PowerSeries.coeff_monomial,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  by_cases hn : n = 1
  · subst n
    simp [sectionRatio]
  · simp [hn]

lemma completedChartMap_baseSection :
    completedChartMap (completedSection (0,0)) = PowerSeries.X := by
  rw [completedChartMap_section]
  have h : (⟨sectionRatio (0,0), ratio_mem_sectionChart (0,0)⟩ : sectionChart) = 1 := by
    apply Subtype.ext
    exact div_self sectionCoefficient_base_ne_zero
  rw [h, map_one, one_mul]

end ExplicitCone


namespace FractionChartComparison
variable {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra R B]

noncomputable def fieldMap (hf : Function.Injective (algebraMap R B)) :
    FractionRing R →ₐ[R] FractionRing B :=
  IsFractionRing.liftAlgHom (g := Algebra.ofId R (FractionRing B)) (by
    intro x y he
    apply hf
    apply IsFractionRing.injective B (FractionRing B)
    change algebraMap R (FractionRing B) x = algebraMap R (FractionRing B) y at he
    simpa only [IsScalarTower.algebraMap_apply R B (FractionRing B)] using he)

@[simp] lemma fieldMap_algebraMap (hf : Function.Injective (algebraMap R B)) (r : R) :
    fieldMap hf (algebraMap R (FractionRing R) r) = algebraMap R (FractionRing B) r :=
  (fieldMap hf).commutes r

/-- The literal fraction algebra of an ordinary blowup chart. -/
def chart {ι : Type*} (s : ι → R) (t : R) : Subalgebra R (FractionRing R) :=
  Algebra.adjoin R (Set.range fun i =>
    algebraMap R (FractionRing R) (s i) / algebraMap R (FractionRing R) t)

lemma fieldMap_ratio {ι : Type*} (s : ι → R) (t : R) (b : ι → B)
    (hf : Function.Injective (algebraMap R B)) (ht : t ≠ 0)
    (hb : ∀ i, b i * algebraMap R B t = algebraMap R B (s i)) (i : ι) :
    fieldMap hf (algebraMap R (FractionRing R) (s i) /
      algebraMap R (FractionRing R) t) = algebraMap B (FractionRing B) (b i) := by
  rw [map_div₀, fieldMap_algebraMap, fieldMap_algebraMap]
  have ht' : algebraMap R (FractionRing B) t ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).ne
      (by simpa only [map_zero] using hf.ne ht) |>.trans_eq (map_zero _)
  apply (div_eq_iff ht').mpr
  rw [IsScalarTower.algebraMap_apply R B (FractionRing B),
    IsScalarTower.algebraMap_apply R B (FractionRing B), ← map_mul, hb]

lemma map_chart {ι : Type*} (s : ι → R) (t : R) (b : ι → B)
    (hf : Function.Injective (algebraMap R B)) (ht : t ≠ 0)
    (hb : ∀ i, b i * algebraMap R B t = algebraMap R B (s i))
    (hgen : Algebra.adjoin R (Set.range b) = ⊤) :
    (chart s t).map (fieldMap hf) = (IsScalarTower.toAlgHom R B (FractionRing B)).range := by
  rw [chart, AlgHom.map_adjoin]
  have he : fieldMap hf '' Set.range (fun i =>
      algebraMap R (FractionRing R) (s i) / algebraMap R (FractionRing R) t) =
      (IsScalarTower.toAlgHom R B (FractionRing B)) '' Set.range b := by
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext i
    exact fieldMap_ratio s t b hf ht hb i
  rw [he, ← AlgHom.map_adjoin, hgen, Algebra.map_top]

/-- A domain generated by actual section ratios is the actual fraction
chart, not merely a ring agreeing with it modulo the exceptional equation. -/
noncomputable def chartEquiv {ι : Type*} (s : ι → R) (t : R) (b : ι → B)
    (hf : Function.Injective (algebraMap R B)) (ht : t ≠ 0)
    (hb : ∀ i, b i * algebraMap R B t = algebraMap R B (s i))
    (hgen : Algebra.adjoin R (Set.range b) = ⊤) : chart s t ≃ₐ[R] B :=
  ((chart s t).equivMapOfInjective (fieldMap hf) (fieldMap hf).injective).trans
    ((Subalgebra.equivOfEq _ _ (map_chart s t b hf ht hb hgen)).trans
      (AlgEquiv.ofInjective (IsScalarTower.toAlgHom R B (FractionRing B))
        (IsFractionRing.injective B (FractionRing B))).symm)

end FractionChartComparison

namespace AlgebraGenerators
lemma adjoin_of_sup_ranges
    {k R A B : Type*} [CommRing k] [CommRing R] [CommRing A] [CommRing B]
    [Algebra k R] [Algebra k A] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    (g : A →ₐ[k] B) (heq : (IsScalarTower.toAlgHom k R B).range ⊔ g.range = ⊤)
    {ι : Type*} (v : ι → A) (hgen : Algebra.adjoin k (Set.range v) = ⊤) :
    Algebra.adjoin R (Set.range (g ∘ v)) = ⊤ := by
  let C := Algebra.adjoin R (Set.range (g ∘ v))
  have hf : (IsScalarTower.toAlgHom k R B).range ≤ C.restrictScalars k := by
    rintro _ ⟨f,rfl⟩
    exact C.algebraMap_mem f
  have hg : g.range ≤ C.restrictScalars k := by
    rw [← Algebra.map_top, ← hgen, AlgHom.map_adjoin]
    apply Algebra.adjoin_le
    rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
    change g (v i) ∈ Algebra.adjoin R (Set.range (g ∘ v))
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  have he := sup_le hf hg
  rw [heq] at he
  exact top_unique fun b _ => he (Set.mem_univ b)
end AlgebraGenerators

namespace CompletedCartierChart
variable {k L : Type} [Field k] [Field L] [Algebra k L]
variable (T : ℕ → Submodule k L) [SetLike.GradedMonoid T]
variable (A : Subalgebra k L) (c : L)
variable (h : ∀ n a, a ∈ T n → a / c ^ n ∈ A)

lemma adjoin_of_constants {ι : Type*} (v : ι → A)
    (hv : Algebra.adjoin k (Set.range v) = ⊤) :
    Algebra.adjoin (SectionCompletion.series T)
      (Set.range (constantHom T A c h ∘ v)) = ⊤ :=
  AlgebraGenerators.adjoin_of_sup_ranges (constantHom T A c h)
    (generators_sup_top T A c h) v hv

end CompletedCartierChart


namespace ExplicitCone

abbrev completedAffineConstant : sectionChart →ₐ[ℂ] completedAffineChart :=
  CompletedCartierChart.constantHom pieces sectionChart
    (sectionCoefficient (0,0)) normalized_coefficient_mem_sectionChart

abbrev completedAffineRatio (i : Fin 6 × Fin 3) : completedAffineChart :=
  completedAffineConstant ⟨sectionRatio i, ratio_mem_sectionChart i⟩

lemma completedAffine_section (i : Fin 6 × Fin 3) :
    completedAffineSource (completedSection i) =
      completedAffineRatio i * completedAffineParameter := by
  apply Subtype.ext
  exact completedChartMap_section i

lemma completedAffine_baseSection :
    completedAffineSource (completedSection (0,0)) = completedAffineParameter := by
  apply Subtype.ext
  exact completedChartMap_baseSection

lemma completedSection_base_ne_zero : completedSection (0,0) ≠ 0 := by
  intro he
  have hh := completedAffine_baseSection
  rw [he, map_zero] at hh
  exact completedAffineParameter_ne_zero hh.symm

lemma sectionRatio_generates :
    Algebra.adjoin ℂ (Set.range fun i =>
      (⟨sectionRatio i, ratio_mem_sectionChart i⟩ : sectionChart)) = ⊤ := by
  apply (Subalgebra.map_injective (f := sectionChart.val) Subtype.val_injective)
  rw [AlgHom.map_adjoin, Algebra.map_top]
  have he : sectionChart.val '' Set.range (fun i =>
      (⟨sectionRatio i, ratio_mem_sectionChart i⟩ : sectionChart)) = Set.range sectionRatio := by
    rw [← Set.range_comp]
    rfl
  rw [he]
  exact sectionChart.range_val.symm

lemma completedAffineRatio_generates :
    Algebra.adjoin completedRing (Set.range completedAffineRatio) = ⊤ :=
  CompletedCartierChart.adjoin_of_constants pieces sectionChart
    (sectionCoefficient (0,0)) normalized_coefficient_mem_sectionChart
    (fun i => ⟨sectionRatio i, ratio_mem_sectionChart i⟩) sectionRatio_generates

/-- The ordinary fraction chart for the original eighteen completed sections.
This is the actual affine algebra R[s_i/s_00], not a formal tensor product. -/
abbrev completedFractionChart := FractionChartComparison.chart completedSection
  (completedSection (0,0))

/-- The algebraic power-series realization coincides with the literal
fraction chart of the blowup of the eighteen-section ideal. -/
def completedFractionChartEquiv : completedFractionChart ≃ₐ[completedRing]
    completedAffineChart :=
  FractionChartComparison.chartEquiv completedSection (completedSection (0,0))
    completedAffineRatio completedAffineSource_injective completedSection_base_ne_zero
    (fun i => by
      change completedAffineRatio i * completedAffineSource (completedSection (0,0)) =
        completedAffineSource (completedSection i)
      rw [completedAffine_baseSection, completedAffine_section])
    completedAffineRatio_generates

end ExplicitCone


namespace ReesProj
open Polynomial AlgebraicGeometry
open scoped DirectSum
variable {R : Type} [CommRing R] (I : Ideal R)

/-- Degree-n polynomials inside the coefficient section algebra. -/
def homogeneous (n : ℕ) : Submodule R (reesAlgebra I) where
  carrier := {p | ∀ m, m ≠ n → (p : R[X]).coeff m = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq m hm
    change (p.val + q.val).coeff m = 0
    simp [hp m hm, hq m hm]
  smul_mem' := by
    intro a p hp m hm
    change (a • p.val).coeff m = 0
    simp [hp m hm]

lemma homogeneous_eq_monomial {n : ℕ} {p : reesAlgebra I}
    (hp : p ∈ homogeneous I n) :
    p.val = monomial n (p.val.coeff n) := by
  ext m
  by_cases h : m = n
  · subst m; simp
  · simp only [coeff_monomial, ite_eq_right (Ne.symm h)]
    exact hp m h

instance homogeneousGradedMonoid : SetLike.GradedMonoid (homogeneous I) where
  one_mem := by intro m hm; simp [coeff_one, hm]
  mul_mem := by
    intro i j p q hp hq m hm
    change (p.val * q.val).coeff m = 0
    rw [homogeneous_eq_monomial I hp, homogeneous_eq_monomial I hq,
      monomial_mul_monomial, coeff_monomial, ite_eq_right (Ne.symm hm)]

def homogeneousPart (p : reesAlgebra I) (n : ℕ) : homogeneous I n :=
  ⟨⟨monomial n (p.val.coeff n), reesAlgebra.monomial_mem.mpr (p.property n)⟩,
    by intro m hm; simp [coeff_monomial, Ne.symm hm]⟩

lemma homogeneousPart_coe (p : reesAlgebra I) (n : ℕ) :
    ((homogeneousPart I p n).val : R[X]) = monomial n (p.val.coeff n) := rfl

/-- Finite support is the actual polynomial support, not an assumption of a
formal infinite homogeneous decomposition. -/
noncomputable def decomposePolynomial (p : reesAlgebra I) :
    ⨁ n, homogeneous I n :=
  DFinsupp.mk p.val.support (fun n => homogeneousPart I p n.val)

lemma decomposePolynomial_apply (p : reesAlgebra I) (n : ℕ) :
    decomposePolynomial I p n = homogeneousPart I p n := by
  classical
  unfold decomposePolynomial
  rw [DFinsupp.mk_apply]
  split_ifs with h
  · rfl
  · apply Subtype.ext
    apply Subtype.ext
    change 0 = monomial n (p.val.coeff n)
    rw [notMem_support_iff.mp h, map_zero]

lemma coeff_recompose (x : ⨁ n, homogeneous I n) (n : ℕ) :
    ((DirectSum.coeAddMonoidHom (homogeneous I) x).val).coeff n =
      ((x n).val.val).coeff n := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i p =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : n = i
    · subst n; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ h]
      exact p.property n h
  | add x y hx hy =>
    simp only [map_add, AddMemClass.coe_add, coeff_add]
    exact congrArg₂ (· + ·) hx hy

noncomputable instance polynomialGradedRing : GradedAlgebra (homogeneous I) where
  decompose' := decomposePolynomial I
  left_inv := by
    intro p
    apply Subtype.ext
    ext n
    rw [coeff_recompose, decomposePolynomial_apply]
    simp [homogeneousPart_coe]
  right_inv := by
    intro x
    apply DFinsupp.ext
    intro n
    rw [decomposePolynomial_apply]
    apply Subtype.ext
    apply Subtype.ext
    change monomial n _ = _
    rw [coeff_recompose]
    exact (homogeneous_eq_monomial I (x n).property).symm

/-- The projective scheme of the section-coefficient algebra. -/
noncomputable def proj : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Proj (homogeneous I)


instance degreeZeroTower : IsScalarTower R (homogeneous I 0) (reesAlgebra I) where
  smul_assoc a b c := by
    change (a • b.val) * c = a • (b.val * c)
    exact smul_mul_assoc a b.val c

instance finiteType_over_degreeZero [Algebra.FiniteType R (reesAlgebra I)] :
    Algebra.FiniteType (homogeneous I 0) (reesAlgebra I) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R (homogeneous I 0) (reesAlgebra I)

instance projProper [Nontrivial R] [Algebra.FiniteType R (reesAlgebra I)] :
    IsProper (Proj.toSpecZero (homogeneous I)) := inferInstance

/-- The degree-zero part of the actual Rees algebra is the original ring. -/
def zeroEquiv : R ≃ₐ[R] homogeneous I 0 :=
  AlgEquiv.ofBijective (Algebra.ofId R (homogeneous I 0)) ⟨by
    intro a b hab
    have he := congrArg (fun p : homogeneous I 0 => (p.val.val).coeff 0) hab
    simpa using he, by
    intro a
    refine ⟨a.val.val.coeff 0, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change Polynomial.C (a.val.val.coeff 0) = a.val.val
    rw [homogeneous_eq_monomial I a.property, monomial_zero_left]
    simp⟩

end ReesProj

end


noncomputable section
namespace FractionChartComparison
variable {R : Type*} [CommRing R] [IsDomain R]
variable {ι : Type*} (s : ι → R) (t : R)

lemma ratio_mem_of_mem_span (a : R) (ha : a ∈ Ideal.span (Set.range s)) :
    algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) t ∈ chart s t := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  | zero => simp
  | add a b ha hb h₁ h₂ =>
    simpa only [map_add, add_div] using (chart s t).add_mem h₁ h₂
  | smul r a ha h =>
    change algebraMap R (FractionRing R) (r * a) / algebraMap R (FractionRing R) t ∈ _
    rw [map_mul, mul_div_assoc]
    exact (chart s t).mul_mem ((chart s t).algebraMap_mem r) h

lemma scaled_mem_of_mem_power (n : ℕ) (a : R)
    (ha : a ∈ Ideal.span (Set.range s) ^ n) :
    algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) t ^ n ∈ chart s t := by
  induction n generalizing a with
  | zero => simp [(chart s t).algebraMap_mem a]
  | succ n hn =>
    rw [pow_succ'] at ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro a ha b hb
      change algebraMap R (FractionRing R) (a * b) /
        algebraMap R (FractionRing R) t ^ (n + 1) ∈ _
      rw [map_mul, pow_succ', ← div_mul_div_comm]
      exact (chart s t).mul_mem (ratio_mem_of_mem_span s t a ha) (hn b hb)
    · intro a b ha hb
      simpa only [map_add, add_div] using (chart s t).add_mem ha hb

end FractionChartComparison


namespace ReesProj
open Polynomial
variable {R K : Type} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (I : Ideal R)

/-- The actual degree-one Rees element associated to t ∈ I. -/
def linearSection (t : R) (ht : t ∈ I) : reesAlgebra I :=
  ⟨monomial 1 t, reesAlgebra.monomial_mem.mpr (by simpa using ht)⟩

lemma linearSection_homogeneous (t : R) (ht : t ∈ I) :
    linearSection I t ht ∈ homogeneous I 1 := by
  intro n hn
  simp [linearSection, coeff_monomial, Ne.symm hn]

abbrev homogeneousChart (t : R) (ht : t ∈ I) :=
  HomogeneousLocalization.Away (homogeneous I) (linearSection I t ht)

def evaluateOne : reesAlgebra I →+* K :=
  (Polynomial.eval₂RingHom (algebraMap R (K)) 1).comp (reesAlgebra I).val.toRingHom

omit [IsFractionRing R K] in
lemma evaluateOne_linearSection (t : R) (ht : t ∈ I) :
    evaluateOne (K := K) I (linearSection I t ht) = algebraMap R (K) t := by
  simp [evaluateOne, linearSection]

variable (t : R) (ht : t ∈ I) (hn : t ≠ 0)

lemma mapped_ne_zero (hn : t ≠ 0) : algebraMap R (K) t ≠ 0 :=
  (by simpa only [map_zero] using (IsFractionRing.injective R (K)).ne hn)

def homogeneousChartMap : homogeneousChart I t ht →+* K :=
  (Localization.awayLift (evaluateOne (K := K) I) (linearSection I t ht)
    (isUnit_iff_exists_inv.mpr ⟨(algebraMap R (K) t)⁻¹,
      by rw [evaluateOne_linearSection]; exact mul_inv_cancel₀ (mapped_ne_zero (K := K) t hn)⟩)).comp
    (algebraMap (homogeneousChart I t ht) (Localization.Away (linearSection I t ht)))

lemma homogeneousChartMap_mk (n : ℕ) (a : reesAlgebra I)
    (ha : a ∈ homogeneous I (n • 1)) :
    homogeneousChartMap (K := K) I t ht hn
      (HomogeneousLocalization.Away.mk (homogeneous I)
        (linearSection_homogeneous I t ht) n a ha) =
      algebraMap R (K) (a.val.coeff n) / algebraMap R (K) t ^ n := by
  simp only [homogeneousChartMap, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk _ _ _ _ (by
    rw [evaluateOne_linearSection]
    exact mul_inv_cancel₀ (mapped_ne_zero (K := K) t hn))]
  have he := homogeneous_eq_monomial I (by simpa using ha : a ∈ homogeneous I n)
  change a.val.eval₂ (algebraMap R (K)) 1 *
    ((algebraMap R (K) t)⁻¹) ^ n = _
  conv_lhs => rw [he]
  simp only [eval₂_monomial, one_pow, mul_one, inv_pow, div_eq_mul_inv]

lemma homogeneousChartMap_injective :
    Function.Injective (homogeneousChartMap (K := K) I t ht hn) := by
  have hk : ∀ x, homogeneousChartMap (K := K) I t ht hn x = 0 → x = 0 := by
    intro x hx
    obtain ⟨n,a,ha,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (homogeneous I) (linearSection_homogeneous I t ht) x
    rw [homogeneousChartMap_mk] at hx
    have hz' : algebraMap R (K) (a.val.coeff n) = 0 :=
      (div_eq_zero_iff).mp hx |>.resolve_right (pow_ne_zero n (mapped_ne_zero (K := K) t hn))
    have hz : a.val.coeff n = 0 := (IsFractionRing.injective R (K))
      (by simpa only [map_zero] using hz')
    have az : a = 0 := by
      apply Subtype.ext
      rw [homogeneous_eq_monomial I (by simpa using ha : a ∈ homogeneous I n), hz, map_zero]
      rfl
    subst a
    apply HomogeneousLocalization.val_injective _
    simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero]
    exact Localization.mk_zero _
  intro x y h
  apply sub_eq_zero.mp
  apply hk
  rw [map_sub, h, sub_self]

lemma scaledCoefficient_mem_range (n : ℕ) (a : R) (ha : a ∈ I ^ n) :
    algebraMap R (K) a / algebraMap R (K) t ^ n ∈
      RingHom.range (R := homogeneousChart I t ht) (homogeneousChartMap (K := K) I t ht hn) := by
  let p : reesAlgebra I := ⟨monomial n a, reesAlgebra.monomial_mem.mpr ha⟩
  have hp : p ∈ homogeneous I (n • 1) := by
    intro m hm
    simp only [smul_eq_mul, mul_one] at hm
    simp [p, coeff_monomial, Ne.symm hm]
  refine ⟨HomogeneousLocalization.Away.mk (homogeneous I)
    (linearSection_homogeneous I t ht) n p hp, ?_⟩
  rw [homogeneousChartMap_mk]
  simp [p]

instance homogeneousChartScalarAlgebra : Algebra R (homogeneousChart I t ht) :=
  ((algebraMap (homogeneous I 0) (homogeneousChart I t ht)).comp
    (algebraMap R (homogeneous I 0))).toAlgebra

lemma homogeneousChartMap_scalar (a : R) :
    homogeneousChartMap (K := K) I t ht hn ((@algebraMap R (homogeneousChart I t ht) _ _ (homogeneousChartScalarAlgebra I t ht)) a) =
      algebraMap R (K) a := by
  have ha : algebraMap R (reesAlgebra I) a ∈ homogeneous I (0 • 1) := by
    intro m hm
    change (C a).coeff m = 0
    simp only [smul_eq_mul, zero_mul] at hm
    simp [coeff_C, hm]
  have hs : (@algebraMap R (homogeneousChart I t ht) _ _ (homogeneousChartScalarAlgebra I t ht)) a =
    HomogeneousLocalization.Away.mk (homogeneous I)
      (linearSection_homogeneous I t ht) 0 (algebraMap R (reesAlgebra I) a) ha := by
    apply HomogeneousLocalization.val_injective _
    rfl
  rw [hs, homogeneousChartMap_mk]
  change algebraMap R (K) ((C a).coeff 0) /
    algebraMap R (K) t ^ 0 = _
  simp

end ReesProj


namespace ReesProj
variable {R K : Type} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
variable {ι : Type*} (s : ι → R) (t : R)

def fractionChart : Subalgebra R K :=
  Algebra.adjoin R (Set.range fun i => algebraMap R K (s i) / algebraMap R K t)

omit [IsFractionRing R K] in
lemma ratio_mem_of_mem_span (a : R) (ha : a ∈ Ideal.span (Set.range s)) :
    algebraMap R K a / algebraMap R K t ∈ fractionChart (K := K) s t := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  | zero => simp
  | add a b ha hb h₁ h₂ =>
    simpa only [map_add, add_div] using (fractionChart (K := K) s t).add_mem h₁ h₂
  | smul r a ha h =>
    change algebraMap R K (r * a) / algebraMap R K t ∈ _
    rw [map_mul, mul_div_assoc]
    exact (fractionChart (K := K) s t).mul_mem ((fractionChart (K := K) s t).algebraMap_mem r) h

omit [IsFractionRing R K] in
lemma scaled_mem_of_mem_power (n : ℕ) (a : R)
    (ha : a ∈ Ideal.span (Set.range s) ^ n) :
    algebraMap R K a / algebraMap R K t ^ n ∈ fractionChart (K := K) s t := by
  induction n generalizing a with
  | zero => simp [(fractionChart (K := K) s t).algebraMap_mem a]
  | succ n hn =>
    rw [pow_succ'] at ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro a ha b hb
      change algebraMap R K (a * b) / algebraMap R K t ^ (n + 1) ∈ _
      rw [map_mul, pow_succ', ← div_mul_div_comm]
      exact (fractionChart (K := K) s t).mul_mem (ratio_mem_of_mem_span s t a ha) (hn b hb)
    · intro a b ha hb
      simpa only [map_add, add_div] using (fractionChart (K := K) s t).add_mem ha hb

variable (ht : t ∈ Ideal.span (Set.range s)) (hn : t ≠ 0)

abbrev generatedChart := homogeneousChart (Ideal.span (Set.range s)) t ht

def generatedChartHom : generatedChart s t ht →ₐ[R] K :=
  { homogeneousChartMap (Ideal.span (Set.range s)) t ht hn with
    commutes' := homogeneousChartMap_scalar (Ideal.span (Set.range s)) t ht hn }

lemma generatedChartHom_range : (generatedChartHom (K := K) s t ht hn).range =
    fractionChart (K := K) s t := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    obtain ⟨n,a,ha,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (homogeneous (Ideal.span (Set.range s)))
      (linearSection_homogeneous (Ideal.span (Set.range s)) t ht) x
    change homogeneousChartMap (K := K) (Ideal.span (Set.range s)) t ht hn _ ∈ _
    rw [homogeneousChartMap_mk]
    exact scaled_mem_of_mem_power s t n _ (a.property n)
  · apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    obtain ⟨x,hx⟩ := scaledCoefficient_mem_range (K := K) (Ideal.span (Set.range s)) t ht hn
      1 (s i) (by simpa using Ideal.subset_span (Set.mem_range_self i))
    refine ⟨x, ?_⟩
    change homogeneousChartMap (K := K) (Ideal.span (Set.range s)) t ht hn x = _
    simpa only [pow_one] using hx

/-- A literal Rees-Proj affine chart is the usual algebra of section fractions. -/
def generatedChartEquiv : generatedChart s t ht ≃ₐ[R] fractionChart (K := K) s t :=
  (AlgEquiv.ofInjective (generatedChartHom s t ht hn)
    (homogeneousChartMap_injective (K := K) (Ideal.span (Set.range s)) t ht hn)).trans
      (Subalgebra.equivOfEq _ _ (generatedChartHom_range s t ht hn))

open AlgebraicGeometry CategoryTheory

def basicOpenIsoFractionChart :
    (Proj.basicOpen (homogeneous (Ideal.span (Set.range s)))
      (linearSection (Ideal.span (Set.range s)) t ht)).toScheme ≅
      Spec (.of (fractionChart (K := K) s t)) :=
  (Proj.basicOpenIsoSpec (homogeneous (Ideal.span (Set.range s)))
    (linearSection (Ideal.span (Set.range s)) t ht)
    (linearSection_homogeneous (Ideal.span (Set.range s)) t ht) (by decide : 0 < (1 : ℕ))).trans
      (Scheme.Spec.mapIso (generatedChartEquiv (K := K) s t ht hn).symm.toRingEquiv.toCommRingCatIso.op)

end ReesProj

end

end OAI
