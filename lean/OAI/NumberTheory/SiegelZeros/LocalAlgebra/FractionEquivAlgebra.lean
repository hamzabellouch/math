import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Intersection.TorusEvalOne

namespace OAI

namespace SiegelZeros

section

section GeometryExtra1
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry

namespace WeightedTorusJets.Geometry

theorem ringKrullDim_away_eq_of_finiteType
    {K R : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    [Algebra.FiniteType K R] (r : R) (hr : r ≠ 0) :
    ringKrullDim (Localization.Away r) = ringKrullDim R := by
  let S := Localization.Away r
  have : IsDomain S := Localization.Away.isDomain hr
  have : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).mpr
      (IsLocalization.injective S
        (powers_le_nonZeroDivisors_of_noZeroDivisors hr))
  have : Algebra.IsAlgebraic R S := IsLocalization.isAlgebraic S (Submonoid.powers r)
  have : Algebra.FiniteType K S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K R) (inferInstance : Algebra.FiniteType R S)
  obtain ⟨n, hn, htn⟩ := WeightedTorusJets.finiteType_dimension_trdeg (K := K) (A := R)
  obtain ⟨m, hm, htm⟩ := WeightedTorusJets.finiteType_dimension_trdeg (K := K) (A := S)
  have hz : Algebra.trdeg R S = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have ht := lift_trdeg_add_eq K R S
  have he : n = m := by simpa [htn, htm, hz] using ht
  rw [hm, hn, he]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

universe u

theorem openImmersion_affine_topologicalKrullDim_eq
    {K : Type u} [Field K] {R : CommRingCat.{u}} [IsDomain R] [Algebra K R]
    [Algebra.FiniteType K R] {X : Scheme.{u}} [Nonempty X]
    (j : X ⟶ Spec R) [IsOpenImmersion j] :
    topologicalKrullDim X = ringKrullDim R := by
  apply le_antisymm
  · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R]
    exact j.isOpenEmbedding.isInducing.topologicalKrullDim_le
  · let x : X := Classical.choice inferInstance
    obtain ⟨_, ⟨r, rfl⟩, hrx, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (show j x ∈ Set.range j from ⟨x, rfl⟩) j.isOpenEmbedding.isOpen_range
    have hr : r ≠ 0 := by
      intro hr
      exact hrx (hr.symm ▸ Ideal.zero_mem _)
    let l : Spec (.of (Localization.Away r)) ⟶ Spec R :=
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
    have hl : Set.range l ⊆ Set.range j := by
      change Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) ⊆ _
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hsub
    let k := IsOpenImmersion.lift j l hl
    have hlow : topologicalKrullDim (PrimeSpectrum (Localization.Away r)) ≤
        topologicalKrullDim X := k.isOpenEmbedding.isInducing.topologicalKrullDim_le
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      ringKrullDim_away_eq_of_finiteType (K := K) r hr] at hlow
    exact hlow

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

universe u

local instance locallyClosedAlgebra_top_nonempty (Z : Scheme) [Nonempty Z] :
    Nonempty (⊤ : Z.Opens) := ⟨⟨Classical.choice inferInstance, Set.mem_univ _⟩⟩

theorem exists_prime_fractionField_algEquiv_of_immersion
    {K : Type u} [Field K] {R : CommRingCat.{u}} [Algebra K R]
    [Algebra.FiniteType K R] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec R) [QuasiCompact f] [IsImmersion f] :
    let b := f ≫ Spec.map (CommRingCat.ofHom (algebraMap K R))
    let : Algebra K X.functionField := schemeBaseStalkAlgebra b (genericPoint X)
    ∃ (P : Ideal R) (hP : P.IsPrime),
      letI := hP
      ∃ E : FractionRing (R ⧸ P) ≃ₐ[K] X.functionField,
        topologicalKrullDim X = ringKrullDim (R ⧸ P) ∧
        ∀ r : R, E (algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P r)) =
          X.germToFunctionField ⊤ (((Scheme.ΓSpecIso R).inv ≫ f.appTop) r) := by
  let b := f ≫ Spec.map (CommRingCat.ofHom (algebraMap K R))
  let : Algebra K X.functionField := schemeBaseStalkAlgebra b (genericPoint X)
  obtain ⟨P, e, he⟩ := IsClosedImmersion.Spec_iff.mp
    (inferInstance : IsClosedImmersion f.imageι)
  have : IsIntegral (Spec (.of (R ⧸ P))) := IsIntegral.of_isIso e.hom
  have : IsDomain (R ⧸ P) := (affine_isIntegral_iff (.of (R ⧸ P))).mp inferInstance
  have hP : P.IsPrime := (Ideal.Quotient.isDomain_iff_prime P).mp inferInstance
  let j : X ⟶ Spec (.of (R ⧸ P)) := f.toImage ≫ e.hom
  have hj : j ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) = f := by
    dsimp only [j]
    rw [Category.assoc, ← he, f.toImage_imageι]
  let g := Spec.map (CommRingCat.ofHom (algebraMap K (R ⧸ P)))
  have hg : g = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R)) := Spec.map_comp _ _
  have hbase : j ≫ g = b := by rw [hg, ← Category.assoc, hj]
  let : Algebra K (Spec (.of (R ⧸ P))).functionField :=
    schemeBaseStalkAlgebra g (genericPoint (Spec (.of (R ⧸ P))))
  have : IsFractionRing (R ⧸ P) (Spec (.of (R ⧸ P))).functionField :=
    functionField_isFractionRing_of_affine (.of (R ⧸ P))
  let E : FractionRing (R ⧸ P) ≃+* X.functionField :=
    (FractionRing.algEquiv (R ⧸ P) (Spec (.of (R ⧸ P))).functionField).toRingEquiv.trans
      (openImmersionFunctionFieldEquiv j)
  have hscalar (c : K) : E (algebraMap K (FractionRing (R ⧸ P)) c) =
      algebraMap K X.functionField c := by
    change E (algebraMap K (FractionRing (R ⧸ P)) c) =
      schemeBaseToStalk b (genericPoint X) c
    let : Algebra K X.functionField := schemeBaseStalkAlgebra (j ≫ g) (genericPoint X)
    have h := ((affineFractionFieldAlgEquiv K (R ⧸ P)).trans
      (openImmersionFunctionFieldAlgEquiv j g)).commutes c
    change E (algebraMap K (FractionRing (R ⧸ P)) c) =
      schemeBaseToStalk (j ≫ g) (genericPoint X) c at h
    simpa only [hbase] using h
  refine ⟨P, hP, { E with commutes' := hscalar },
    Geometry.openImmersion_affine_topologicalKrullDim_eq (K := K) j, ?_⟩
  intro r
  change openImmersionFunctionFieldEquiv j
    ((FractionRing.algEquiv (R ⧸ P) (Spec (.of (R ⧸ P))).functionField)
      (algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P r))) = _
  rw [AlgEquiv.commutes]
  change dominantFunctionFieldHom j ((Spec (.of (R ⧸ P))).germToFunctionField ⊤
    ((Scheme.ΓSpecIso (.of (R ⧸ P))).inv (Ideal.Quotient.mk P r))) = _
  have hn := congrArg (fun h : Γ(Spec (.of (R ⧸ P)), ⊤) ⟶ X.functionField ↦
    h ((Scheme.ΓSpecIso (.of (R ⧸ P))).inv (Ideal.Quotient.mk P r)))
    (germToFunctionField_dominantFunctionFieldHom j)
  refine hn.trans ?_
  apply congrArg (X.germToFunctionField ⊤)
  have hm : CommRingCat.ofHom (Ideal.Quotient.mk P) ≫
      (Scheme.ΓSpecIso (.of (R ⧸ P))).inv ≫ j.appTop =
      (Scheme.ΓSpecIso R).inv ≫ f.appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop, hj]
    rfl
  exact congrArg (fun h : R ⟶ Γ(X, ⊤) ↦ h r) hm

end WeightedTorusJets

namespace WeightedTorusJets

variable {K A F : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field F] [Algebra K F]

noncomputable abbrev fractionEquivAlgebra (E : FractionRing A ≃ₐ[K] F) : Algebra A F :=
  (E.toRingHom.comp (algebraMap A (FractionRing A))).toAlgebra

theorem fractionEquiv_isFractionRing_and_scalarTower (E : FractionRing A ≃ₐ[K] F) :
    let : Algebra A F := fractionEquivAlgebra E
    IsFractionRing A F ∧ IsScalarTower K A F := by
  let : Algebra A F := fractionEquivAlgebra E
  let Eₐ : FractionRing A ≃ₐ[A] F := { E.toRingEquiv with commutes' := fun _ ↦ rfl }
  exact ⟨IsFractionRing.of_algEquiv Eₐ,
    IsScalarTower.of_algHom (E.toAlgHom.comp (IsScalarTower.toAlgHom K A (FractionRing A)))⟩

end WeightedTorusJets

namespace WeightedTorusJets

universe u

theorem quasiCompact_immersion_of_finiteType_affine
    {K : Type u} [Field K] {R : CommRingCat.{u}} [Algebra K R]
    [Algebra.FiniteType K R] {X : Scheme.{u}} (f : X ⟶ Spec R) [IsImmersion f] :
    QuasiCompact f := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have : TopologicalSpace.NoetherianSpace X := f.isEmbedding.isInducing.noetherianSpace
  infer_instance

end WeightedTorusJets

end GeometryExtra1

section GeometryExtra2
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry

namespace WeightedTorusJets.Geometry

universe u

local instance locallyClosedLogForm_top_nonempty (X : Scheme) [Nonempty X] :
    Nonempty (⊤ : X.Opens) := WeightedTorusJets.locallyClosedAlgebra_top_nonempty X

theorem logarithmicForm_ne_zero_on_locallyClosed_torus_subvariety
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X]
    (j : X ⟶ Spec (.of (AddMonoidAlgebra K (Fin 4 →₀ ℤ))))
    [IsImmersion j]
    (hdim : 0 < topologicalKrullDim X)
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c) :
    let b := j ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (AddMonoidAlgebra K (Fin 4 →₀ ℤ))))
    let : Algebra K X.functionField := WeightedTorusJets.schemeBaseStalkAlgebra b (genericPoint X)
    logarithmicForm c (fun i ↦ X.germToFunctionField ⊤
      (((Scheme.ΓSpecIso (.of (AddMonoidAlgebra K (Fin 4 →₀ ℤ)))).inv ≫ j.appTop)
        (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) ≠ 0 := by
  let b := j ≫ Spec.map (CommRingCat.ofHom
    (algebraMap K (AddMonoidAlgebra K (Fin 4 →₀ ℤ))))
  let : Algebra K X.functionField := WeightedTorusJets.schemeBaseStalkAlgebra b (genericPoint X)
  have := WeightedTorusJets.laurent_finiteType (K := K) (ι := Fin 4)
  have := WeightedTorusJets.quasiCompact_immersion_of_finiteType_affine (K := K) j
  obtain ⟨P, hP, E, hE, hx⟩ :=
    WeightedTorusJets.exists_prime_fractionField_algEquiv_of_immersion (K := K) j
  have hn := logarithmicForm_ne_zero_on_torus_subvariety P (hE ▸ hdim) c hc
  refine fun h ↦ hn ?_
  have hm := WeightedTorusJets.logarithmic_relation_map_algHom E.symm.toAlgHom c _
    (by simpa only [logarithmicForm, div_eq_mul_inv] using h)
  simpa only [AlgEquiv.coe_toAlgHom, ← hx, AlgEquiv.symm_apply_apply,
    logarithmicForm, div_eq_mul_inv] using hm

theorem logarithmicHyperplane_normal_rank_on_locallyClosed_torus_subvariety
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X]
    (j : X ⟶ Spec (.of (AddMonoidAlgebra K (Fin 4 →₀ ℤ))))
    [IsImmersion j]
    (hdim : 0 < topologicalKrullDim X)
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c) :
    let b := j ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (AddMonoidAlgebra K (Fin 4 →₀ ℤ))))
    let : Algebra K X.functionField := WeightedTorusJets.schemeBaseStalkAlgebra b (genericPoint X)
    let x := fun i ↦ X.germToFunctionField ⊤
      (((Scheme.ΓSpecIso (.of (AddMonoidAlgebra K (Fin 4 →₀ ℤ)))).inv ≫ j.appTop)
        (AddMonoidAlgebra.single (Finsupp.single i 1) 1))
    let T := LinearMap.range (logarithmicTangentMap (k := K) x)
    Module.finrank X.functionField (LinearMap.range
      (T.mkQ.domRestrict (LinearMap.ker (logarithmicLinearForm (F := X.functionField) c)))) =
        4 - ((topologicalKrullDim X).unbotD 0).toNat := by
  let b := j ≫ Spec.map (CommRingCat.ofHom
    (algebraMap K (AddMonoidAlgebra K (Fin 4 →₀ ℤ))))
  let : Algebra K X.functionField := WeightedTorusJets.schemeBaseStalkAlgebra b (genericPoint X)
  have := WeightedTorusJets.laurent_finiteType (K := K) (ι := Fin 4)
  have := WeightedTorusJets.quasiCompact_immersion_of_finiteType_affine (K := K) j
  obtain ⟨P, hP, E, hE, hx⟩ :=
    WeightedTorusJets.exists_prime_fractionField_algEquiv_of_immersion (K := K) j
  let A := AddMonoidAlgebra K (Fin 4 →₀ ℤ) ⧸ P
  let : Algebra A X.functionField := WeightedTorusJets.fractionEquivAlgebra E
  obtain ⟨hfrac, htower⟩ := WeightedTorusJets.fractionEquiv_isFractionRing_and_scalarTower E
  let x := fun i ↦ X.germToFunctionField ⊤
    (((Scheme.ΓSpecIso (.of (AddMonoidAlgebra K (Fin 4 →₀ ℤ)))).inv ≫ j.appTop)
      (AddMonoidAlgebra.single (Finsupp.single i 1) 1))
  have hi : Function.Injective (logarithmicTangentMap (k := K) x) := by
    let y : Fin 4 → FractionRing A := fun i ↦ algebraMap A (FractionRing A)
      (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))
    have hy := logarithmicTangentMap_injective_laurent_quotient P
    suffices Function.Injective (logarithmicTangentMap (k := K) (fun i ↦ E (y i))) by
      simpa only [y, A, hx, x] using this
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro D hD
    let D' : Derivation K (FractionRing A) (FractionRing A) :=
      Derivation.mk' (E.symm.toLinearMap.comp (D.toLinearMap.comp E.toLinearMap))
        (by intro a b; simp [map_mul, D.leibniz])
    have hD'_apply (z : FractionRing A) : D' z = E.symm (D (E z)) := rfl
    have hz : logarithmicTangentMap (k := K) y D' = 0 := by
      ext i
      apply E.injective
      simpa [logarithmicTangentMap, hD'_apply] using congrFun hD i
    have hz' : D' = 0 := hy (hz.trans (map_zero _).symm)
    ext y
    apply E.symm.injective
    simpa [hD'_apply] using Derivation.congr_fun hz' (E.symm y)
  have hn := (logarithmicForm_ne_zero_iff_tangent_not_le c x).mp
    (logarithmicForm_ne_zero_on_locallyClosed_torus_subvariety j hdim c hc)
  have hr := finrank_normal_image_of_not_le (logarithmicLinearForm c)
    (LinearMap.range (logarithmicTangentMap (k := K) x)) hn
  rw [LinearMap.finrank_range_of_inj hi] at hr
  have hdim' : topologicalKrullDim X =
      (Module.finrank X.functionField (Derivation K X.functionField X.functionField) : WithBot ℕ∞) :=
    hE.trans (ringKrullDim_eq_finrank_derivation (K := K) (A := A) (F := X.functionField))
  simpa [hdim', x] using hr

end WeightedTorusJets.Geometry

end GeometryExtra2

section GeometryExtra3
open scoped TensorProduct

namespace WeightedTorusJets.Geometry

theorem torusIdentity_tangent_coordinates {K : Type*} [Field K] :
    let P := MvPolynomial (Fin 4) K
    let S := Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P))
    let : Algebra S K := (torusEvalOne (K := K)).toAlgebra
    ∃ e : Module.Dual K (K ⊗[S] Ω[S⁄K]) ≃ₗ[K] (Fin 4 → K),
      (∀ (φ : Module.Dual K (K ⊗[S] Ω[S⁄K])) (i : Fin 4),
        e φ i = φ (1 ⊗ₜ[S] KaehlerDifferential.D K S
          (algebraMap P S (MvPolynomial.X i)))) ∧
      ∀ c : Fin 4 → K,
        let D := localizeDerivation (T := S)
          (Submonoid.powers (∏ i : Fin 4, (MvPolynomial.X i : P))) (invariantDerivation c)
        e (((Algebra.linearMap S K).comp D.liftKaehlerDifferential).liftBaseChange K) = c := by
  let P := MvPolynomial (Fin 4) K
  let S := Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P))
  let : Algebra S K := (torusEvalOne (K := K)).toAlgebra
  let : Algebra.FormallyEtale P S :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (∏ i : Fin 4, (MvPolynomial.X i : P)))
  have hx : ∀ i : Fin 4, IsUnit (algebraMap P S (MvPolynomial.X i)) := fun i =>
    IsLocalization.Away.isUnit_of_dvd _
      (Finset.dvd_prod_of_mem (fun j : Fin 4 => (MvPolynomial.X j : P))
        (Finset.mem_univ i))
  have heval (i : Fin 4) :
      algebraMap S K (algebraMap P S (MvPolynomial.X i)) = 1 := by
    change torusEvalOne (algebraMap P S (MvPolynomial.X i)) = 1
    simp [P, S]
  refine ⟨logarithmicAmbientEquiv hx, ?_, ?_⟩
  · intro φ i
    rw [logarithmicAmbientEquiv_apply, heval, inv_one, one_mul]
  · intro c
    ext i
    rw [logarithmicAmbientEquiv_apply, heval, inv_one, one_mul]
    simp only [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
      Derivation.liftKaehlerDifferential_comp_D, Algebra.linearMap_apply, one_smul,
      localize_invariantDerivation_X, map_mul]
    change torusEvalOne (algebraMap K S (c i)) *
      torusEvalOne (algebraMap P S (MvPolynomial.X i)) = c i
    rw [torusEvalOne_algebraMap, MvPolynomial.eval_X, mul_one]
    rw [IsScalarTower.algebraMap_apply K P S]
    change torusEvalOne (algebraMap P S (MvPolynomial.C (c i))) = c i
    simp [P, S]

end WeightedTorusJets.Geometry

end GeometryExtra3

section GeometryExtra4
namespace WeightedTorusJets.Geometry

noncomputable def torusEvalPoint {K : Type*} [Field K] (y : Fin 4 → Kˣ) :
    Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom
    (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))
    (f := MvPolynomial.aeval (fun i ↦ (y i : K)))
    (by simpa using (Units.isUnit (∏ i : Fin 4, y i)))

@[simp]
theorem torusEvalPoint_algebraMap {K : Type*} [Field K] (y : Fin 4 → Kˣ)
    (f : MvPolynomial (Fin 4) K) :
    torusEvalPoint y (algebraMap (MvPolynomial (Fin 4) K) _ f) =
      MvPolynomial.aeval (fun i ↦ (y i : K)) f := by
  simp [torusEvalPoint]

theorem torus_point_normal_equiv_rank {K : Type*} [Field K] [CharZero K]
    (y : Fin 4 → Kˣ) (c : Fin 4 → K) (hc : LinearIndependent ℚ c) :
    let q := RingHom.ker (torusEvalPoint y).toRingHom
    let : q.IsPrime := RingHom.ker_isPrime _
    let A := Localization.AtPrime q
    let κ := IsLocalRing.ResidueField A
    let m := IsLocalRing.maximalIdeal A
    let T := LinearMap.range (logarithmicTangentMap (k := K)
      (fun i : Fin 4 ↦ algebraMap (MvPolynomial (Fin 4) K) κ (MvPolynomial.X i)))
    ∃ e : ((Fin 4 → κ) ⧸ T) ≃ₗ[κ] Module.Dual κ m.Cotangent,
      (∀ (D : Derivation K A A) (v : Fin 4 → K),
        (∀ i, D (algebraMap (MvPolynomial (Fin 4) K) A (MvPolynomial.X i)) =
          algebraMap K A (v i) *
            algebraMap (MvPolynomial (Fin 4) K) A (MvPolynomial.X i)) →
        ∀ f : m, e (T.mkQ (algebraMap K κ ∘ v)) (m.toCotangent f) =
          Ideal.Quotient.mk m (D f)) ∧
      Module.finrank κ (LinearMap.range
        ((e.toLinearMap.comp T.mkQ).domRestrict
          (LinearMap.ker (dotProductEquiv κ (Fin 4) (algebraMap K κ ∘ c))))) = 3 := by
  let q := RingHom.ker (torusEvalPoint y).toRingHom
  let : q.IsPrime := RingHom.ker_isPrime _
  let A := Localization.AtPrime q
  let p := q.comap (algebraMap (MvPolynomial (Fin 4) K) _)
  have : IsLocalization.AtPrime A p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))) A q
  have hp : p = RingHom.ker (MvPolynomial.aeval (fun i ↦ (y i : K))).toRingHom := by
    ext f
    simp only [p, q, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, torusEvalPoint_algebraMap]
  let κ := IsLocalRing.ResidueField A
  let m := IsLocalRing.maximalIdeal A
  let T := LinearMap.range (logarithmicTangentMap (k := K)
    (fun i : Fin 4 ↦ algebraMap (MvPolynomial (Fin 4) K) κ (MvPolynomial.X i)))
  have hcoords (i : Fin 4) :
      IsUnit (algebraMap (MvPolynomial (Fin 4) K) A (MvPolynomial.X i)) ∧
        algebraMap (MvPolynomial (Fin 4) K) κ (MvPolynomial.X i) = algebraMap K κ (y i) := by
    constructor
    · apply (IsLocalization.AtPrime.isUnit_to_map_iff A p _).mpr
      change MvPolynomial.X i ∉ p
      rw [hp]
      simp
    · have hm : MvPolynomial.X i - MvPolynomial.C (y i : K) ∈ p := by
        rw [hp]
        simp
      have hz : algebraMap (MvPolynomial (Fin 4) K) (IsLocalRing.ResidueField A)
          (MvPolynomial.X i - MvPolynomial.C (y i : K)) = 0 := by
        apply (IsLocalRing.residue_eq_zero_iff _).mpr
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p _).mpr hm
      simpa only [map_sub, MvPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
        sub_eq_zero] using hz
  have hx := fun i ↦ (hcoords i).1
  have : Algebra.FormallyEtale (MvPolynomial (Fin 4) K) A :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  have : Algebra.EssFiniteType (MvPolynomial (Fin 4) K) A :=
    Algebra.EssFiniteType.of_isLocalization A p.primeCompl
  have : Algebra.EssFiniteType K A := Algebra.EssFiniteType.comp K (MvPolynomial (Fin 4) K) A
  let e : ((Fin 4 → κ) ⧸ T) ≃ₗ[κ] Module.Dual κ m.Cotangent :=
    coordinateNormalEquivCotangentDual m hx
  refine ⟨e, ?_, ?_⟩
  · intro D v hv f
    exact coordinateNormal_invariant_pairing m hx D (fun i ↦ algebraMap K A (v i)) hv f
  · have hT : T = ⊥ := by
      rw [LinearMap.range_eq_bot]
      ext D i
      change (algebraMap (MvPolynomial (Fin 4) K) κ (MvPolynomial.X i))⁻¹ *
        D (algebraMap (MvPolynomial (Fin 4) K) κ (MvPolynomial.X i)) = 0
      rw [(hcoords i).2, D.map_algebraMap, mul_zero]
    have hq : Function.Injective T.mkQ := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ, hT]
    have hi : Function.Injective ((e.toLinearMap.comp T.mkQ).domRestrict
        (LinearMap.ker (dotProductEquiv κ (Fin 4) (algebraMap K κ ∘ c)))) :=
      e.injective.comp (hq.comp (LinearMap.ker
        (dotProductEquiv κ (Fin 4) (algebraMap K κ ∘ c))).injective_subtype)
    rw [LinearMap.finrank_range_of_inj hi]
    have hω : dotProductEquiv κ (Fin 4) (algebraMap K κ ∘ c) ≠ 0 := by
      apply (dotProductEquiv κ (Fin 4)).map_ne_zero_iff.mpr
      intro h
      have hz := congrFun h 0
      exact hc.ne_zero 0 ((map_eq_zero (algebraMap K κ)).mp hz)
    have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hω
    have h4 : Module.finrank κ (Fin 4 → κ) = 4 := by simp
    omega

end WeightedTorusJets.Geometry

end GeometryExtra4

section GeometryExtra5
namespace WeightedTorusJets.Geometry

theorem exists_torusEvalPoint_of_quotient_dimension_zero {K : Type*}
    [Field K] [IsAlgClosed K]
    (q : Ideal (Localization.Away
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) [q.IsPrime]
    (hdim : ringKrullDim (_ ⧸ q) = 0) :
    ∃ y : Fin 4 → Kˣ, q = RingHom.ker (torusEvalPoint y).toRingHom := by
  let P := MvPolynomial (Fin 4) K
  let S := Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P))
  have : Ring.KrullDimLE 0 (S ⧸ q) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  let : Field (S ⧸ q) := (Ring.KrullDimLE.isField_of_isDomain (R := S ⧸ q)).toField
  have : Algebra.FiniteType K S := Algebra.FiniteType.trans (S := P) inferInstance inferInstance
  have : Module.Finite K (S ⧸ q) := finite_of_finite_type_of_isJacobsonRing K (S ⧸ q)
  let e : (S ⧸ q) →ₐ[K] K :=
    (AlgEquiv.ofBijective (Algebra.ofId K (S ⧸ q))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm.toAlgHom
  let φ : S →ₐ[K] K := e.comp (Ideal.Quotient.mkₐ K q)
  have hx (i : Fin 4) : IsUnit (algebraMap P S (MvPolynomial.X i)) :=
    IsLocalization.Away.isUnit_of_dvd _
      (Finset.dvd_prod_of_mem (fun j : Fin 4 => (MvPolynomial.X j : P))
        (Finset.mem_univ i))
  let y : Fin 4 → Kˣ := fun i => ((hx i).map φ.toRingHom).unit
  have hφ : φ = torusEvalPoint y := by
    apply IsLocalization.algHom_ext
      (Submonoid.powers (∏ i : Fin 4, (MvPolynomial.X i : P)))
    ext i
    change φ (algebraMap P S (MvPolynomial.X i)) =
      torusEvalPoint y (algebraMap P S (MvPolynomial.X i))
    rw [torusEvalPoint_algebraMap, MvPolynomial.aeval_X]
    exact ((hx i).map φ.toRingHom).unit_spec.symm
  refine ⟨y, ?_⟩
  rw [← hφ]
  ext s
  change s ∈ q ↔ e (Ideal.Quotient.mk q s) = 0
  rw [map_eq_zero, Ideal.Quotient.eq_zero_iff_mem]

end WeightedTorusJets.Geometry

end GeometryExtra5

end

end SiegelZeros

end OAI
