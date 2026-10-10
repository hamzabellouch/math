import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.GenericSmoothness

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory

theorem integral_of_integral_open_cover {X : Scheme} (C : X.OpenCover)
    [∀ i, IsIntegral (C.X i)] (i₀ : C.I₀)
    (hoverlap : ∀ i, (Set.range (C.f i₀) ∩ Set.range (C.f i)).Nonempty) :
    IsIntegral X := by
  let : IsReduced X := IsReduced.of_openCover X C
  have hd : Dense (Set.range (C.f i₀)) := by
    apply dense_iff_inter_open.mpr
    intro V hV hVne
    obtain ⟨x, hx⟩ := hVne
    obtain ⟨i, y, hy⟩ := C.exists_eq x
    have hVpre : ((C.f i) ⁻¹' V).Nonempty := ⟨y, by
      change C.f i y ∈ V
      rw [hy]
      exact hx⟩
    have hOpre : ((C.f i) ⁻¹' Set.range (C.f i₀)).Nonempty := by
      obtain ⟨z, hz₀, hz⟩ := hoverlap i
      obtain ⟨w, rfl⟩ := hz
      exact ⟨w, hz₀⟩
    obtain ⟨w, hwV, hwO⟩ := nonempty_preirreducible_inter
      (hV.preimage (C.f i).continuous)
      ((C.f i₀).isOpenEmbedding.isOpen_range.preimage (C.f i).continuous) hVpre hOpre
    exact ⟨C.f i w, hwV, hwO⟩
  have hi : IsIrreducible (Set.range (C.f i₀)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := C.X i₀)).image (C.f i₀)
        (C.f i₀).continuous.continuousOn
  let : IrreducibleSpace X := (irreducibleSpace_def X).mpr (by
    change IsIrreducible (Set.univ : Set X)
    rw [← hd.closure_eq]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem integral_subscheme_of_affine_quotients {α : Type} (X : Scheme.{0})
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    (I : X.IdealSheafData) [∀ j, IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j))]
    (j₀ : α) (hoverlap : ∀ j, ∃ x : I.subscheme,
      I.subschemeι x ∈ (U j₀).1 ∧ I.subschemeι x ∈ (U j).1) :
    IsIntegral I.subscheme := by
  have hD (j : α) : IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j)) := inferInstance
  have hOpen (j : α) : IsOpenImmersion (I.subschemeCover.f (U j)) :=
    I.subschemeCover.map_prop (U j)
  let : ∀ j, IsOpenImmersion (I.subschemeCover.f (U j)) := hOpen
  let C : I.subscheme.OpenCover := .mkOfCovers α
    (fun j => Spec (CommRingCat.of (Γ(X, (U j).1) ⧸ I.ideal (U j))))
    (fun j => I.subschemeCover.f (U j)) (by
      intro x
      obtain ⟨j, hj⟩ := hcover (I.subschemeι x)
      have hh : x ∈ (I.subschemeCover.f (U j)).opensRange := by
        rw [I.opensRange_subschemeCover_map]
        exact hj
      obtain ⟨y, hy⟩ := hh
      exact ⟨j, y, hy⟩) (by intro j; exact hOpen j)
  let : ∀ j, IsIntegral (C.X j) := fun j => by
    change IsIntegral (Spec (CommRingCat.of (Γ(X, (U j).1) ⧸ I.ideal (U j))))
    exact (affine_isIntegral_iff _).mpr (hD j)
  apply integral_of_integral_open_cover C j₀
  intro j
  let : IsOpenImmersion (I.subschemeCover.f (U j)) := hOpen j
  let : IsOpenImmersion (I.subschemeCover.f (U j₀)) := hOpen j₀
  obtain ⟨x, hx₀, hx⟩ := hoverlap j
  refine ⟨x, ?_, ?_⟩
  · change x ∈ (I.subschemeCover.f (U j₀)).opensRange
    rw [I.opensRange_subschemeCover_map]
    exact hx₀
  · change x ∈ (I.subschemeCover.f (U j)).opensRange
    rw [I.opensRange_subschemeCover_map]
    exact hx

end

noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory

theorem subscheme_meets_affine {X : Scheme.{0}} (I : X.IdealSheafData)
    (U : X.affineOpens) [Nontrivial (Γ(X, U.1) ⧸ I.ideal U)] :
    ∃ x : I.subscheme, I.subschemeι x ∈ U.1 := by
  let : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
  obtain ⟨y⟩ := (inferInstance : Nonempty
    (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U))))
  refine ⟨I.subschemeCover.f U y, ?_⟩
  have hx : I.subschemeCover.f U y ∈ (I.subschemeCover.f U).opensRange := ⟨y, rfl⟩
  rw [I.opensRange_subschemeCover_map] at hx
  exact hx

theorem integral_subscheme_of_affine_overlap_quotients {α : Type} (X : Scheme.{0})
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    (I : X.IdealSheafData) [∀ j, IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j))]
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1) :
    IsIntegral I.subscheme := by
  apply integral_subscheme_of_affine_quotients X U hcover I j₀
  intro j
  obtain ⟨x, hx⟩ := subscheme_meets_affine I (U (overlap j))
  exact ⟨x, hleft j hx, hright j hx⟩

end

noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem smooth_integral_linear_family
    {K α : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable α] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, IsDomain Γ(X, (U j).1)]
    [∀ j, Algebra K Γ(X, (U j).1)] [∀ j, Algebra.FiniteType K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g)
    (σ : α → Type) [∀ j, Algebra (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    (v : ∀ j, Fin n → Γ(X, (U j).1)) (i₁ i₂ : α → Fin n) (a b : ∀ j, σ j)
    (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, v j (i₁ j) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (a j)))
    (hvb : ∀ j, v j (i₂ j) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (b j)))
    (e : α → (Option (Fin n) ≃ Option (Fin n)))
    (I : (Option (Fin n) → K) → X.IdealSheafData)
    (hI : ∀ t j, (I t).ideal (U j) = Ideal.span
      {algebraMap K Γ(X, (U j).1) (t (e j none)) -
        ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k})
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (I t).subscheme ∧ Smooth ((I t).subschemeι ≫ g) := by
  obtain ⟨T, _, hqT, f, hf, hh⟩ := simultaneous_reindexed_smooth_integral_hyperplanes
    (fun j => Γ(X, (U j).1)) σ v i₁ i₂ a b hab hva hvb e
    (q.coeffs : Set K) q.coeffs.countable_toSet
  let t : Option (Fin n) → K := fun o => f (hyperplaneVariable o)
  have hqv : MvPolynomial.aeval t q ≠ 0 := by
    have ht : t = (fun o => o.elim (f Polynomial.X)
        (fun i => f (C (MvPolynomial.X i)))) := by
      funext o
      cases o <;> rfl
    rw [ht]
    exact hyperplane_parameter_polynomial_ne_zero T q hq hqT f hf
  have hD (j : α) : IsDomain (Γ(X, (U j).1) ⧸ (I t).ideal (U j)) := by
    rw [hI]
    exact (hh j).1
  have hS (j : α) : Algebra.Smooth K (Γ(X, (U j).1) ⧸ (I t).ideal (U j)) := by
    rw [hI]
    exact (hh j).2
  let : ∀ j, IsDomain (Γ(X, (U j).1) ⧸ (I t).ideal (U j)) := hD
  let : ∀ j, Algebra.Smooth K (Γ(X, (U j).1) ⧸ (I t).ideal (U j)) := hS
  exact ⟨t, hqv,
    integral_subscheme_of_affine_overlap_quotients X U hcover (I t) j₀ overlap hleft hright,
    MaximalSeshadri.SchemeBertini.smooth_subscheme_of_affine_quotients
      X g U hcover hOver (I t)⟩

end

noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

lemma vanishingIdeal_compl_eq_span {X : Scheme} (D : X.Opens)
    (U : X.affineOpens) (f : Γ(X, U.1))
    (hD : U.2.fromSpec ⁻¹ᵁ D = PrimeSpectrum.basicOpen f)
    [IsDomain (Γ(X, U.1) ⧸ Ideal.span {f})] :
    (Scheme.IdealSheafData.vanishingIdeal D.compl).ideal U = Ideal.span {f} := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal
    (U.2.fromSpec ⁻¹' (D.compl : Set X) : Set (PrimeSpectrum Γ(X, U.1))) = Ideal.span {f}
  have hset : (U.2.fromSpec ⁻¹' (D.compl : Set X) : Set (PrimeSpectrum Γ(X, U.1))) =
      PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set Γ(X, U.1))) := by
    rw [PrimeSpectrum.zeroLocus_span]
    have h := congrArg (fun V : (Spec (CommRingCat.of Γ(X, U.1))).Opens =>
      (V : Set (Spec (CommRingCat.of Γ(X, U.1))))) hD
    change U.2.fromSpec ⁻¹' (D : Set X) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Γ(X, U.1))) at h
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl] at h
    have hc := congrArg (fun s : Set (PrimeSpectrum Γ(X, U.1)) => sᶜ) h
    change (U.2.fromSpec ⁻¹' (D : Set X) : Set (PrimeSpectrum Γ(X, U.1)))ᶜ = _
    exact hc.trans (compl_compl _)
  rw [hset, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact ((Ideal.Quotient.isDomain_iff_prime _).mp inferInstance).isRadical.radical

theorem smooth_integral_zero_family
    {K α : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable α] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, IsDomain Γ(X, (U j).1)]
    [∀ j, Algebra K Γ(X, (U j).1)] [∀ j, Algebra.FiniteType K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g)
    (σ : α → Type) [∀ j, Algebra (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    (v : ∀ j, Fin n → Γ(X, (U j).1)) (i₁ i₂ : α → Fin n) (a b : ∀ j, σ j)
    (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, v j (i₁ j) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (a j)))
    (hvb : ∀ j, v j (i₂ j) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (b j)))
    (e : α → (Option (Fin n) ≃ Option (Fin n)))
    (D : (Option (Fin n) → K) → X.Opens)
    (hD : ∀ t j, (U j).2.fromSpec ⁻¹ᵁ D t = PrimeSpectrum.basicOpen
      (algebraMap K Γ(X, (U j).1) (t (e j none)) -
        ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k))
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal (D t).compl).subscheme ∧
      Smooth ((Scheme.IdealSheafData.vanishingIdeal (D t).compl).subschemeι ≫ g) := by
  obtain ⟨T, _, hqT, f, hf, hh⟩ := simultaneous_reindexed_smooth_integral_hyperplanes
    (fun j => Γ(X, (U j).1)) σ v i₁ i₂ a b hab hva hvb e
    (q.coeffs : Set K) q.coeffs.countable_toSet
  let t : Option (Fin n) → K := fun o => f (hyperplaneVariable o)
  have hqv : MvPolynomial.aeval t q ≠ 0 := by
    have ht : t = (fun o => o.elim (f Polynomial.X)
        (fun i => f (C (MvPolynomial.X i)))) := by
      funext o
      cases o <;> rfl
    rw [ht]
    exact hyperplane_parameter_polynomial_ne_zero T q hq hqT f hf
  let I := Scheme.IdealSheafData.vanishingIdeal (D t).compl
  have hI (j : α) : I.ideal (U j) = Ideal.span
      {algebraMap K Γ(X, (U j).1) (t (e j none)) -
        ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k} := by
    let := (hh j).1
    exact vanishingIdeal_compl_eq_span (D t) (U j) _ (hD t j)
  have hDom (j : α) : IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j)) := by
    rw [hI]
    exact (hh j).1
  have hS (j : α) : Algebra.Smooth K (Γ(X, (U j).1) ⧸ I.ideal (U j)) := by
    rw [hI]
    exact (hh j).2
  let : ∀ j, IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j)) := hDom
  let : ∀ j, Algebra.Smooth K (Γ(X, (U j).1) ⧸ I.ideal (U j)) := hS
  exact ⟨t, hqv,
    integral_subscheme_of_affine_overlap_quotients X U hcover I j₀ overlap hleft hright,
    MaximalSeshadri.SchemeBertini.smooth_subscheme_of_affine_quotients
      X g U hcover hOver I⟩

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
