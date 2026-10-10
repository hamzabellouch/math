import Mathlib

namespace OAI

section
noncomputable section
                                              

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open KaehlerDifferential

section CoordinateBasis
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

theorem formallyUnramified_polynomial_of_basis
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyUnramified (MvPolynomial ι R) S := by
  have hz : KaehlerDifferential.map R (MvPolynomial ι R) S S = 0 := by
    apply b.ext
    intro i
    rw [hb, KaehlerDifferential.map_D]
    change D (MvPolynomial ι R) S
      (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) = 0
    exact Derivation.map_algebraMap _ _
  constructor
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) S x
  obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) S y
  rw [hz]
  rfl

theorem formallySmooth_polynomial_of_basis [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallySmooth (MvPolynomial ι R) S := by
  classical
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  let : Algebra R B := Algebra.compHom B (algebraMap R (MvPolynomial ι R))
  let : IsScalarTower R (MvPolynomial ι R) B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective R S I hI (f.restrictScalars R)
  let : Algebra S B := g.toRingHom.toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let correction (i : ι) : I := ⟨algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) -
      g (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)), by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, sub_eq_zero]
    change _ = (Ideal.Quotient.mkₐ R I) (g _)
    rw [← AlgHom.comp_apply, hg]
    exact (f.commutes _).symm⟩
  let d : Derivation R S I := (b.constr S correction).compDer (D R S)
  let g' : S →ₐ[R] B := liftOfDerivationToSquareZero I hI d
  have hcoords (i : ι) : g' (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) =
      algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) := by
    change ((b.constr S correction) (D R S (algebraMap _ _ (MvPolynomial.X i))) : B) +
      g (algebraMap _ _ (MvPolynomial.X i)) = _
    rw [← hb, b.constr_basis]
    exact sub_add_cancel _ _
  have hcomm : g'.comp (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) =
      IsScalarTower.toAlgHom R (MvPolynomial ι R) B := by
    apply MvPolynomial.algHom_ext
    exact hcoords
  let lift : S →ₐ[MvPolynomial ι R] B :=
    { g'.toRingHom with commutes' := fun p => AlgHom.congr_fun hcomm p }
  refine ⟨lift, ?_⟩
  ext s
  change Ideal.Quotient.mk I (g' s) = f s
  rw [liftOfDerivationToSquareZero_mk_apply]
  exact AlgHom.congr_fun hg s

theorem formallyEtale_polynomial_of_basis [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyEtale (MvPolynomial ι R) S := by
  let := formallySmooth_polynomial_of_basis b hb
  let := formallyUnramified_polynomial_of_basis b hb
  constructor <;> infer_instance

end CoordinateBasis

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem presentation_coordinate_formallyEtale {σ : Type*} [Finite σ] [Finite ι]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    (MvPolynomial.aeval (R := R) (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)).toRingHom.FormallyEtale := by
  let φ := MvPolynomial.aeval (R := R) (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)
  let : Algebra (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let := P.isStandardSmooth
  change Algebra.FormallyEtale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S
  apply formallyEtale_polynomial_of_basis P.basisKaehler
  intro i
  rw [P.basisKaehler_apply]
  change D R S (P.val i) = D R S (φ (MvPolynomial.X i))
  simp only [φ, MvPolynomial.aeval_X]

theorem exists_formallyEtale_coordinates (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ (κ : Type) (_ : Finite κ) (x : κ → S), Nat.card κ = n ∧
      (MvPolynomial.aeval (R := R) x).toRingHom.FormallyEtale := by
  classical
  obtain ⟨κ, σ, hσ, hκ, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := n) (R := R) (S := S)
  let : Fintype κ := Fintype.ofFinite κ
  let : Fintype σ := Fintype.ofFinite σ
  refine ⟨((Set.range P.map)ᶜ : Set κ), inferInstance, (fun i => P.val i), ?_,
    presentation_coordinate_formallyEtale P⟩
  rw [← hP]
  simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
    Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]

end

noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem presentation_coordinate_etale {ι σ : Type*} [Finite σ] [Finite ι]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    (MvPolynomial.aeval (R := R)
      (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)).toRingHom.Etale := by
  let φ := MvPolynomial.aeval (R := R)
    (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)
  have hφ := presentation_coordinate_formallyEtale P
  let : Algebra (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FinitePresentation R S := P.finitePresentation_of_isFinite
  let : Algebra.FinitePresentation (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ S
  let : Algebra.FormallyEtale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := hφ
  change Algebra.Etale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S
  constructor <;> infer_instance

theorem exists_etale_coordinates (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ (κ : Type) (_ : Finite κ) (x : κ → S), Nat.card κ = n ∧
      (MvPolynomial.aeval (R := R) x).toRingHom.Etale := by
  classical
  obtain ⟨κ, σ, hσ, hκ, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := n) (R := R) (S := S)
  let : Fintype κ := Fintype.ofFinite κ
  let : Fintype σ := Fintype.ofFinite σ
  refine ⟨((Set.range P.map)ᶜ : Set κ), inferInstance, (fun i => P.val i), ?_,
    presentation_coordinate_etale P⟩
  rw [← hP]
  simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
    Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]

end

noncomputable section
open KaehlerDifferential
universe u v w
variable {R : Type u} {S : Type v} {ι : Type w}
  [CommRing R] [CommRing S] [Algebra R S]

lemma differentials_span_of_generators (v : ι → S)
    (hv : Function.Surjective (MvPolynomial.aeval (R := R) v)) :
    Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤ := by
  apply top_unique
  rw [← span_range_derivation R S, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  obtain ⟨q, rfl⟩ := hv s
  induction q using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.aeval_C, Derivation.map_algebraMap]
      exact Submodule.zero_mem _
  | add f g hf hg =>
      simp only [map_add]
      exact Submodule.add_mem _ hf hg
  | mul_X f i hf =>
      simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
        (Submodule.smul_mem _ _ hf)

theorem exists_local_differential_basis [Algebra.Smooth R S]
    (v : ι → S)
    (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤)
    (p : Ideal S) [p.IsPrime] :
    ∃ g : S, g ∉ p ∧ ∃ (κ : Type w) (_ : Finite κ) (a : κ → ι)
      (b : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R]),
      ∀ i, b i = D R (Localization.Away g) (algebraMap S (Localization.Away g) (v (a i))) := by
  let w : ι → Ω[Localization.AtPrime p⁄R] :=
    fun i => map R R S (Localization.AtPrime p) (D R S (v i))
  have hw : Submodule.span (Localization.AtPrime p) (Set.range w) = ⊤ := by
    have hh := span_eq_top_of_isLocalizedModule (Localization.AtPrime p) p.primeCompl
      (map R R S (Localization.AtPrime p)) hv
    simpa only [← Set.range_comp, Function.comp_def, w] using hh
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat w hw
  let e : (κ →₀ S) →ₗ[S] Ω[S⁄R] :=
    Finsupp.linearCombination S fun i : κ => D R S (v (a i))
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[Localization.AtPrime p⁄R] := map R R S (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p]
      Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have he : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e (l₁ (Finsupp.single i 1))
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb, w]
  have heₚ : Function.Bijective eₚ := he ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] := map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ : (κ →₀ Localization.Away g) →ₗ[Localization.Away g]
      Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  refine ⟨g, hg, κ, inferInstance, a, .ofRepr (LinearEquiv.ofBijective eₜ h).symm, ?_⟩
  intro i
  change eₜ (Finsupp.single i 1) = _
  trans IsLocalizedModule.map (Submonoid.powers g) l₁ₜ l₂ₜ e (l₁ₜ (Finsupp.single i 1))
  · simp [eₜ, -IsLocalizedModule.map_apply, l₁ₜ]
  · simp [l₂ₜ, e]

theorem exists_local_generator_basis [Algebra.Smooth R S]
    (v : ι → S) (hv : Function.Surjective (MvPolynomial.aeval (R := R) v))
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S), g ∉ p ∧ ∃ (κ : Type w) (_ : Finite κ) (a : κ → ι)
      (b : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R]),
      ∀ i, b i = D R (Localization.Away g) (algebraMap S (Localization.Away g) (v (a i))) :=
  exists_local_differential_basis v (differentials_span_of_generators v hv) p

theorem coordinate_map_etale [Algebra.Smooth R S] [Finite ι]
    (v : ι → S) (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (v i)) :
    (MvPolynomial.aeval (R := R) v).toRingHom.Etale := by
  let φ := MvPolynomial.aeval (R := R) v
  let : Algebra (MvPolynomial ι R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ι R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FinitePresentation (MvPolynomial ι R) S :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ S
  let : Algebra.FormallyEtale (MvPolynomial ι R) S :=
    formallyEtale_polynomial_of_basis b (by
      intro i
      change b i = D R S (φ (MvPolynomial.X i))
      simpa only [φ, MvPolynomial.aeval_X] using hb i)
  change Algebra.Etale (MvPolynomial ι R) S
  constructor <;> infer_instance

theorem exists_local_etale_from_spanning (n : ℕ)
    [IsDomain S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (v : ι → S)
    (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤)
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S), g ∉ p ∧ ∃ (κ : Type w) (_ : Finite κ) (a : κ → ι),
      Nat.card κ = n ∧
      (MvPolynomial.aeval (R := R)
        (fun i => algebraMap S (Localization.Away g) (v (a i)))).toRingHom.Etale := by
  let : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  obtain ⟨g, hg, κ, hκ, a, b, hb⟩ := exists_local_differential_basis v hv p
  let : Finite κ := hκ
  let : Fintype κ := Fintype.ofFinite κ
  have hg0 : g ≠ 0 := fun h => hg (h ▸ Ideal.zero_mem p)
  let : IsDomain (Localization.Away g) := Localization.Away.isDomain hg0
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 S (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away g
  let : Algebra.IsStandardSmoothOfRelativeDimension n R (Localization.Away g) := by
    simpa using (Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := S)
      (T := Localization.Away g) (n := n) (m := 0))
  let : Algebra.IsStandardSmooth R (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  refine ⟨g, hg, κ, hκ, a, ?_, coordinate_map_etale _ b hb⟩
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := Localization.Away g) n
  rw [rank_eq_card_basis b] at hr
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hr

end

noncomputable section
open KaehlerDifferential TensorProduct
variable {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
 [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

lemma differentials_span_of_formallyEtale [Algebra.FormallyEtale S T]
    (v : ι → S) (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤) :
    Submodule.span T (Set.range (fun i => D R T (algebraMap S T (v i)))) = ⊤ := by
  let M := Submodule.span T (Set.range (fun i => D R T (algebraMap S T (v i))))
  have hmem (s : Ω[S⁄R]) : map R R S T s ∈ M := by
    have hh : Submodule.span S (Set.range (fun i => D R S (v i))) ≤
        (M.restrictScalars S).comap (map R R S T) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change map R R S T (D R S (v i)) ∈ M
      rw [map_D]
      exact Submodule.subset_span (Set.mem_range_self i)
    rw [hv] at hh
    exact hh (Submodule.mem_top)
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨z, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale R S T).surjective x
  induction z using TensorProduct.inductionOn with
  | tmul t s =>
      rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
      exact M.smul_mem t (hmem s)
  | add x y hx hy =>
      rw [map_add]
      exact M.add_mem hx hy

end
end MaximalSeshadri.AlgebraicJets


end
end

end OAI
