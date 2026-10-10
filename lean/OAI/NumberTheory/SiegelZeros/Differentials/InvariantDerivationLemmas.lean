import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalFractionAlgebra

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section


namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem maximal_mvPolynomial_height {σ : Type*} [Fintype σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsMaximal] : p.height = Fintype.card σ := by
  let e := (MvPolynomial.renameEquiv K (Fintype.equivFin σ)).toRingEquiv
  have := maximal_polynomial_height (Fintype.card σ) (p.map e)
  rwa [e.height_map] at this

end WeightedTorusJets.Geometry











namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R] (I p : Ideal R) [p.IsPrime]

theorem regular_local_maximal_height [IsRegularLocalRing R] :
    (IsLocalRing.maximalIdeal R).height =
      (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) : ℕ∞) := by
  apply WithBot.coe_injective
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm

variable {K : Type*} [Field K]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K R : Type*} [Field K] [Infinite K] [CommRing R] [Algebra K R]

theorem exists_mem_submodule_notMem_ideals (V : Submodule K R)
    {ι : Type*} [Finite ι] (p : ι → Ideal R)
    (hp : ∀ i, ¬ Ideal.span (V : Set R) ≤ p i) :
    ∃ x ∈ V, ∀ i, x ∉ p i := by
  let q (i : ι) : Submodule K V :=
    ((p i).restrictScalars K).comap V.subtype
  have hq (i : ι) : q i ≠ ⊤ := by
    intro hi
    apply hp i
    rw [Ideal.span_le]
    intro x hx
    have : (⟨x, hx⟩ : V) ∈ q i := hi ▸ Submodule.mem_top
    exact this
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top q hq
  exact ⟨x, x.property, hx⟩

theorem exists_finset_mem_submodule_height [IsNoetherianRing R]
    (V : Submodule K R) (r : ℕ) (hr : r ≤ (Ideal.span (V : Set R)).height) :
    ∃ s : Finset R, (∀ x ∈ s, x ∈ V) ∧ s.card ≤ r ∧
      r ≤ (Ideal.span (s : Set R)).height := by
  classical
  induction r with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨s, hsV, hsc, hsh⟩ := ih ((WithTop.coe_le_coe.mpr r.le_succ).trans hr)
    let J : Ideal R := Ideal.span (s : Set R)
    let S := {p : Ideal R | p ∈ J.minimalPrimes ∧ p.height = r}
    have hS : S.Finite := J.finite_minimalPrimes_of_isNoetherianRing.subset (fun _ h => h.1)
    have : Finite S := hS.to_subtype
    have hp (p : S) : ¬ Ideal.span (V : Set R) ≤ p.1 := by
      intro hVp
      have h := hr.trans (Ideal.height_mono hVp)
      rw [p.2.2] at h
      exact (Nat.not_succ_le_self r) (by exact_mod_cast h)
    obtain ⟨x, hxV, hxp⟩ := exists_mem_submodule_notMem_ideals V (fun p : S => p.1) hp
    have hspan : Ideal.span ((insert x s : Finset R) : Set R) = J ⊔ Ideal.span {x} := by
      rw [Finset.coe_insert, Ideal.span_insert]
      exact sup_comm _ _
    refine ⟨insert x s, ?_, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hsc 1), ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxV
      · exact hsV y hy
    · rw [hspan, Ideal.height_eq_inf_minimalPrimes]
      refine le_iInf₂ fun p hp => ?_
      have : p.IsPrime := hp.isPrime
      have hJp : J ≤ p := le_sup_left.trans hp.le
      have hle : (r : ℕ∞) ≤ p.height := hsh.trans (Ideal.height_mono hJp)
      by_cases htop : p.height = ⊤
      · exact htop ▸ le_top
      have : p.FiniteHeight := ⟨Or.inr htop⟩
      have hne : (r : ℕ∞) ≠ p.height := by
        intro heq
        have hpS : p ∈ S := ⟨Ideal.mem_minimalPrimes_of_height_le hJp (heq.symm.trans_le hsh),
          heq.symm⟩
        exact hxp ⟨p, hpS⟩ (hp.le <| Ideal.mem_sup_right <| Ideal.mem_span_singleton_self x)
      exact Order.add_one_le_of_lt (lt_of_le_of_ne hle hne)

theorem exists_parameters_in_submodule [IsNoetherianRing R] [IsLocalRing R]
    (V : Submodule K R) (h : ℕ)
    (hV : (Ideal.span (V : Set R)).radical = IsLocalRing.maximalIdeal R)
    (hdim : (IsLocalRing.maximalIdeal R).height = h) :
    ∃ s : Finset R, (∀ x ∈ s, x ∈ V) ∧ s.card = h ∧
      (Ideal.span (s : Set R)).radical = IsLocalRing.maximalIdeal R := by
  have hheight : (Ideal.span (V : Set R)).height = h := by
    rw [Ideal.height_eq_inf_minimalPrimes,
      ← (Ideal.span (V : Set R)).radical_minimalPrimes, hV,
      ← Ideal.height_eq_inf_minimalPrimes, hdim]
  obtain ⟨s, hsV, hsc, hsh⟩ := exists_finset_mem_submodule_height V h hheight.ge
  have hsm : Ideal.span (s : Set R) ≤ IsLocalRing.maximalIdeal R := by
    refine (Ideal.span_le.mpr fun x hx => ?_)
    rw [← hV]
    exact Ideal.le_radical (Ideal.subset_span (hsV x hx))
  have hsproper : Ideal.span (s : Set R) ≠ ⊤ := by
    intro ht
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (ht ▸ hsm))
  have hcard : s.card = h := le_antisymm hsc (by
    exact_mod_cast hsh.trans (Ideal.height_span_le_card_of_span_ne_top hsproper))
  refine ⟨s, hsV, hcard, le_antisymm ?_ ?_⟩
  · exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr hsm
  · rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun p hp => ?_
    have : p.IsPrime := hp.isPrime
    have hpheight : (IsLocalRing.maximalIdeal R).height ≤ p.height := by
      rw [hdim]
      exact hsh.trans (Ideal.height_mono hp.le)
    exact (Ideal.eq_of_le_of_height_le p
      (IsLocalRing.le_maximalIdeal hp.isPrime.ne_top) hpheight).ge

theorem exists_polynomial_parameters [IsNoetherianRing R] [IsLocalRing R]
    {σ : Type*} (φ : MvPolynomial σ K →ₐ[K] R) (S : Set (MvPolynomial σ K))
    (d h : ℕ) (hS : ∀ f ∈ S, f.totalDegree ≤ d)
    (hI : (Ideal.span (φ '' S)).radical = IsLocalRing.maximalIdeal R)
    (hdim : (IsLocalRing.maximalIdeal R).height = h) :
    ∃ g : Fin h → MvPolynomial σ K,
      (∀ i, g i ∈ Submodule.span K S) ∧ (∀ i, (g i).totalDegree ≤ d) ∧
      Ideal.span (Set.range (φ ∘ g)) ≤ Ideal.span (φ '' S) ∧
      (Ideal.span (Set.range (φ ∘ g))).radical = IsLocalRing.maximalIdeal R := by
  let U : Submodule K (MvPolynomial σ K) := Submodule.span K S
  let V : Submodule K R := U.map φ.toLinearMap
  have hV : (Ideal.span (V : Set R)).radical = IsLocalRing.maximalIdeal R := by
    change (Ideal.span ((Submodule.span K S).map φ.toLinearMap : Set R)).radical = _
    rw [Submodule.map_span]
    change Ideal.radical (Submodule.span R (Submodule.span K (φ '' S) : Set R)) = _
    rw [Submodule.span_span_of_tower]
    exact hI
  obtain ⟨s, hsV, hsc, hsrad⟩ := exists_parameters_in_submodule V h hV hdim
  have hlift (x : s) : ∃ f ∈ U, φ f = (x : R) := Submodule.mem_map.mp (hsV x x.property)
  choose f hfU hf using hlift
  let e : s ≃ Fin h := Finset.equivFinOfCardEq hsc
  let g (i : Fin h) := f (e.symm i)
  have hg (i : Fin h) : g i ∈ U := hfU (e.symm i)
  have hgr : Set.range (φ ∘ g) = (s : Set R) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      simpa only [Function.comp_apply, g, hf, Finset.mem_coe] using (e.symm i).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      simpa only [Function.comp_apply, g, e.symm_apply_apply] using hf ⟨x, hx⟩
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro i
    apply (MvPolynomial.mem_restrictTotalDegree σ d (g i)).mp
    exact (Submodule.span_le.mpr fun f hf =>
      (MvPolynomial.mem_restrictTotalDegree σ d f).mpr (hS f hf)) (hg i)
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.span_subset_span K R _
      (Submodule.apply_mem_span_image_of_mem_span φ.toLinearMap (hg i))
  · rw [hgr]
    exact hsrad

end WeightedTorusJets.Geometry


namespace WeightedTorusJets.Geometry

theorem polynomial_parameters_at_generic_point {K σ A : Type*}
    [Field K] [Infinite K] [Finite σ] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] [IsLocalization.AtPrime A p]
    (S : Set (MvPolynomial σ K)) (hp : p ∈ (Ideal.span S).minimalPrimes)
    (d : ℕ) (hS : ∀ f ∈ S, f.totalDegree ≤ d) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)) →
        MvPolynomial σ K,
      (∀ i, g i ∈ Submodule.span K S) ∧ (∀ i, (g i).totalDegree ≤ d) ∧
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i))) ≤
        (Ideal.span S).map (algebraMap (MvPolynomial σ K) A) ∧
      (Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i)))).radical =
        IsLocalRing.maximalIdeal A := by
  have : IsRegularLocalRing A := IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A).toRingEquiv
  let φ : MvPolynomial σ K →ₐ[K] A := IsScalarTower.toAlgHom K (MvPolynomial σ K) A
  have hrad : (Ideal.span (φ '' S)).radical = IsLocalRing.maximalIdeal A := by
    change (Ideal.span ((algebraMap (MvPolynomial σ K) A) '' S)).radical = _
    rw [← Ideal.map_span,
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A p (Ideal.span S) hp,
      IsLocalization.AtPrime.map_eq_maximalIdeal]
  obtain ⟨g, hg, hdeg, hle, hrad⟩ := exists_polynomial_parameters φ S d _ hS hrad
    (regular_local_maximal_height (R := A))
  refine ⟨g, hg, hdeg, ?_, hrad⟩
  rw [Ideal.map_span]
  exact hle



theorem polynomial_parameters_at_localized_generic_point {K σ A : Type*}
    [Field K] [Infinite K] [Finite σ] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A]
    (M : Submonoid (MvPolynomial σ K)) [Algebra (Localization M) A]
    [IsScalarTower (MvPolynomial σ K) (Localization M) A]
    (p : Ideal (Localization M)) [p.IsPrime] [IsLocalization.AtPrime A p]
    (S : Set (MvPolynomial σ K))
    (hp : p ∈ ((Ideal.span S).map (algebraMap (MvPolynomial σ K) (Localization M))).minimalPrimes)
    (d : ℕ) (hS : ∀ f ∈ S, f.totalDegree ≤ d) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)) →
        MvPolynomial σ K,
      (∀ i, g i ∈ Submodule.span K S) ∧ (∀ i, (g i).totalDegree ≤ d) ∧
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i))) ≤
        (Ideal.span S).map (algebraMap (MvPolynomial σ K) A) ∧
      (Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i)))).radical =
        IsLocalRing.maximalIdeal A := by
  have : IsLocalization.AtPrime A (p.comap (algebraMap (MvPolynomial σ K) (Localization M))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M A p
  rw [IsLocalization.minimalPrimes_map M (Localization M) (Ideal.span S)] at hp
  exact polynomial_parameters_at_generic_point
    (p.comap (algebraMap (MvPolynomial σ K) (Localization M))) S hp d hS



theorem quotient_length_antitone {R : Type*} [CommRing R]
    {I J : Ideal R} (hIJ : I ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ I) := by
  exact Module.length_le_of_surjective (Ideal.Quotient.factorₐ R hIJ).toLinearMap
    (Ideal.Quotient.factor_surjective hIJ)

theorem local_quotient_artinian_of_radical {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (J : Ideal R)
    (hJ : J.radical = IsLocalRing.maximalIdeal R) : IsArtinianRing (R ⧸ J) := by
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  rw [← J.radical_minimalPrimes, hJ, Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

theorem local_quotient_length_ne_top_of_radical {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (J : Ideal R)
    (hJ : J.radical = IsLocalRing.maximalIdeal R) :
    Module.length R (R ⧸ J) ≠ ⊤ := by
  have := local_quotient_artinian_of_radical J hJ
  have : IsArtinian R (R ⧸ J) :=
    isArtinian_of_surjective_algebraMap (R := R ⧸ J) Ideal.Quotient.mk_surjective
  exact Module.length_ne_top



theorem polynomial_parameters_with_finite_length {K σ A : Type*}
    [Field K] [Infinite K] [Finite σ] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A]
    (M : Submonoid (MvPolynomial σ K)) [Algebra (Localization M) A]
    [IsScalarTower (MvPolynomial σ K) (Localization M) A]
    (p : Ideal (Localization M)) [p.IsPrime] [IsLocalization.AtPrime A p]
    (S : Set (MvPolynomial σ K))
    (hp : p ∈ ((Ideal.span S).map (algebraMap (MvPolynomial σ K) (Localization M))).minimalPrimes)
    (d : ℕ) (hS : ∀ f ∈ S, f.totalDegree ≤ d) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)) →
        MvPolynomial σ K,
      (∀ i, g i ∈ Submodule.span K S) ∧ (∀ i, (g i).totalDegree ≤ d) ∧
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i))) ≤
        (Ideal.span S).map (algebraMap (MvPolynomial σ K) A) ∧
      (Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i)))).radical =
        IsLocalRing.maximalIdeal A ∧
      Module.length A (A ⧸ (Ideal.span S).map (algebraMap (MvPolynomial σ K) A)) ≤
        Module.length A (A ⧸ Ideal.span
          (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i)))) ∧
      Module.length A (A ⧸ Ideal.span
        (Set.range (fun i => algebraMap (MvPolynomial σ K) A (g i)))) ≠ ⊤ := by
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  obtain ⟨g, hg, hd, hle, hrad⟩ :=
    polynomial_parameters_at_localized_generic_point (A := A) M p S hp d hS
  exact ⟨g, hg, hd, hle, hrad, quotient_length_antitone hle,
    local_quotient_length_ne_top_of_radical _ hrad⟩

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

noncomputable def invariantDerivation (c : ι → R) :
    Derivation R (MvPolynomial ι R) (MvPolynomial ι R) :=
  ∑ i, c i • ((MvPolynomial.X i : MvPolynomial ι R) • MvPolynomial.pderiv i)

theorem invariantDerivation_monomial (c : ι → R) (m : ι →₀ ℕ) (r : R) :
    invariantDerivation c (MvPolynomial.monomial m r) =
      (∑ i, c i * (m i : R)) • MvPolynomial.monomial m r := by
  simp only [invariantDerivation, sum_apply, Derivation.smul_apply, smul_eq_mul,
    MvPolynomial.X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul R, smul_smul,
    Finset.sum_smul]

theorem coeff_invariantDerivation (c : ι → R) (f : MvPolynomial ι R) (m : ι →₀ ℕ) :
    (invariantDerivation c f).coeff m = (∑ i, c i * (m i : R)) * f.coeff m := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial n r =>
      simp only [invariantDerivation_monomial, MvPolynomial.coeff_smul, smul_eq_mul,
        MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst n
        rfl
      · simp
  | add f g hf hg =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg, mul_add]

noncomputable def invariantJet (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (f : MvPolynomial ι R) : MvPolynomial ι R :=
  (invariantDerivation (c 0))^[a 0]
    ((invariantDerivation (c 1))^[a 1]
      ((invariantDerivation (c 2))^[a 2] f))

theorem coeff_iterate_invariantDerivation (c : ι → R) (f : MvPolynomial ι R)
    (m : ι →₀ ℕ) (k : ℕ) :
    ((invariantDerivation c)^[k] f).coeff m =
      (∑ i, c i * (m i : R)) ^ k * f.coeff m := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [Function.iterate_succ_apply', coeff_invariantDerivation, hk, pow_succ']
    exact (mul_assoc _ _ _).symm

theorem coeff_invariantJet (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (f : MvPolynomial ι R) (m : ι →₀ ℕ) :
    (invariantJet c a f).coeff m =
      ((∑ i, c 0 i * (m i : R)) ^ a 0 *
        (∑ i, c 1 i * (m i : R)) ^ a 1 *
        (∑ i, c 2 i * (m i : R)) ^ a 2) * f.coeff m := by
  simp only [invariantJet, coeff_iterate_invariantDerivation, mul_assoc]

theorem support_invariantJet_subset (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (f : MvPolynomial ι R) : (invariantJet c a f).support ⊆ f.support := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_invariantJet] at hm
  exact MvPolynomial.mem_support_iff.mpr (fun h ↦ hm (by rw [h, mul_zero]))

theorem totalDegree_invariantJet_le (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (f : MvPolynomial ι R) : (invariantJet c a f).totalDegree ≤ f.totalDegree :=
  MvPolynomial.totalDegree_le_of_support_subset (support_invariantJet_subset c a f)

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
