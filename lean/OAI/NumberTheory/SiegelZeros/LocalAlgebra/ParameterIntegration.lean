import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic
import OAI.NumberTheory.SiegelZeros.Structure.ComponentHeight
import OAI.NumberTheory.SiegelZeros.Structure.FinsuppCandidates
import OAI.NumberTheory.SiegelZeros.Structure.GenericCombination

namespace OAI

namespace SiegelZeros

section

namespace W20

variable {K R J : Type*} [Field K] [Infinite K] [CommRing R]
  [Algebra K R] [IsNoetherianRing R]

theorem exists_constant_span_finset_of_height
    (g : J → R) (r : ℕ) (hr : r ≤ (Ideal.span (Set.range g)).height) :
    ∃ s : Finset R,
      (∀ x ∈ s, x ∈ Submodule.span K (Set.range g)) ∧
      s.card ≤ r ∧ r ≤ (Ideal.span (s : Set R)).height := by
  classical
  induction r with
  | zero =>
    refine ⟨∅, ?_, by simp, ?_⟩
    · simp
    · exact bot_le
  | succ r ih =>
    obtain ⟨s, hs, hcard, hheight⟩ :=
      ih ((WithTop.coe_le_coe.mpr r.le_succ).trans hr)
    let A : Ideal R := Ideal.span (s : Set R)
    let S : Set (Ideal R) := {P | P ∈ A.minimalPrimes ∧ P.height = r}
    have hS : S.Finite := Set.Finite.subset A.finite_minimalPrimes_of_isNoetherianRing
      (fun _ h => h.1)
    let : Fintype S := hS.fintype
    obtain ⟨x, hxspan, hxavoid⟩ := exists_span_element_avoiding_ideals
      (K := K) g (fun p : S => p.1) (by
        intro p hp
        have hle := hr.trans (Ideal.height_mono hp)
        rw [p.2.2, ← not_lt] at hle
        norm_cast at hle
        exact hle r.lt_succ_self)
    have havoid : ∀ p ∈ S, x ∉ p := fun p hp => hxavoid ⟨p, hp⟩
    have hnext : (r + 1 : ℕ∞) ≤ (A ⊔ Ideal.span {x}).height := by
      rw [Ideal.height_eq_inf_minimalPrimes]
      refine le_iInf₂ (fun p hp => ?_)
      have := hp.1.1
      by_cases h : p.height = ⊤
      · rw [h]
        exact le_top
      have : p.FiniteHeight := ⟨Or.inr h⟩
      have hmono := Ideal.height_mono (le_sup_left.trans hp.1.2)
      suffices h : (r : ℕ∞) ≠ p.height by
        have hle := hheight.trans hmono
        exact Order.add_one_le_of_lt (lt_of_le_of_ne hle h)
      intro heq
      apply havoid p
      · have heighth : A.height = p.height := by
          apply le_antisymm
          · exact hmono
          · rwa [← heq]
        refine ⟨Ideal.mem_minimalPrimes_of_height_le
          (le_sup_left.trans hp.1.2) heighth.ge, heq.symm⟩
      · exact hp.1.2 <| Ideal.mem_sup_right <| Ideal.subset_span <| Set.mem_singleton x
    refine ⟨insert x s, ?_, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxspan
      · exact hs y hy
    · exact (Finset.card_insert_le x s).trans (Nat.add_le_add_right hcard 1)
    · simpa only [Finset.coe_insert, Ideal.span_insert, sup_comm, Nat.cast_add,
        Nat.cast_one] using hnext

theorem exists_constant_span_parameter_finset [IsLocalRing R]
    (g : J → R) (r : ℕ)
    (hgen : (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal R)
    (hdim : (IsLocalRing.maximalIdeal R).height = r) :
    ∃ s : Finset R,
      (∀ x ∈ s, x ∈ Submodule.span K (Set.range g)) ∧
      s.card ≤ r ∧
      (Ideal.span (s : Set R)).radical = IsLocalRing.maximalIdeal R := by
  have heighth : (Ideal.span (Set.range g)).height =
      (IsLocalRing.maximalIdeal R).height := by
    apply le_antisymm
    · apply Ideal.height_mono
      intro x hx
      rw [← hgen]
      exact Ideal.le_radical hx
    · rw [Ideal.height_eq_inf_minimalPrimes (Ideal.span (Set.range g))]
      refine le_iInf₂ (fun P hP => ?_)
      let : P.IsPrime := hP.1.1
      have hmle : IsLocalRing.maximalIdeal R ≤ P := by
        rw [← hgen]
        exact (hP.1.1).radical_le_iff.mpr hP.1.2
      exact Ideal.height_mono hmle
  obtain ⟨s, hs, hcard, hheight⟩ :=
    exists_constant_span_finset_of_height (K := K) g r (by rw [heighth, hdim])
  have hspan : Submodule.span K (Set.range g) ≤
      (IsLocalRing.maximalIdeal R).restrictScalars K := by
    apply Submodule.span_le.mpr
    intro x hx
    change x ∈ IsLocalRing.maximalIdeal R
    rw [← hgen]
    exact Ideal.le_radical (Ideal.subset_span hx)
  have hle : Ideal.span (s : Set R) ≤ IsLocalRing.maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro x hx
    exact hspan (hs x hx)
  have hmin : IsLocalRing.maximalIdeal R ∈ (Ideal.span (s : Set R)).minimalPrimes :=
    Ideal.mem_minimalPrimes_of_height_le hle (by rwa [hdim])
  refine ⟨s, hs, hcard, le_antisymm ?_ ?_⟩
  · exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr hle
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro P hP
    exact hmin.2 ⟨hP.2, hP.1⟩ (IsLocalRing.le_maximalIdeal hP.2.ne_top)

theorem exists_constant_coefficients_parameter_finset [IsLocalRing R]
    (g : J → R) (r : ℕ)
    (hgen : (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal R)
    (hdim : (IsLocalRing.maximalIdeal R).height = r) :
    ∃ (s : Finset R) (c : s → J →₀ K),
      (∀ x : s, Finsupp.linearCombination K g (c x) = (x : R)) ∧
      s.card ≤ r ∧
      (Ideal.span (s : Set R)).radical = IsLocalRing.maximalIdeal R := by
  obtain ⟨s, hs, hcard, hrad⟩ :=
    exists_constant_span_parameter_finset (K := K) g r hgen hdim
  have hex : ∀ x : s, ∃ c : J →₀ K,
      Finsupp.linearCombination K g c = (x : R) := by
    intro x
    have hx := hs x x.2
    rw [← Finsupp.range_linearCombination] at hx
    exact hx
  choose c hc using hex
  exact ⟨s, c, hc, hcard, hrad⟩

end W20

end

section

namespace W20

variable {K σ J S : Type*} [Field K] [Infinite K]
  [CommRing S] [Algebra K S] [IsNoetherianRing S] [IsLocalRing S]

theorem exists_degree_bounded_polynomial_parameters
    (φ : MvPolynomial σ K →ₐ[K] S) (f : J → MvPolynomial σ K)
    (r d : ℕ)
    (hgen : ((Ideal.span (Set.range f)).map φ.toRingHom).radical =
      IsLocalRing.maximalIdeal S)
    (hdim : (IsLocalRing.maximalIdeal S).height = r)
    (hdegree : ∀ j, (f j).totalDegree ≤ d) :
    ∃ t : Finset (MvPolynomial σ K),
      t.card ≤ r ∧
      (∀ p ∈ t, p.totalDegree ≤ d) ∧
      Ideal.span (t : Set (MvPolynomial σ K)) ≤ Ideal.span (Set.range f) ∧
      ((Ideal.span (t : Set (MvPolynomial σ K))).map φ.toRingHom).radical =
        IsLocalRing.maximalIdeal S ∧
      ((Ideal.span (t : Set (MvPolynomial σ K))).map φ.toRingHom).IsPrimary := by
  classical
  have hgen' : (Ideal.span (Set.range (φ ∘ f))).radical =
      IsLocalRing.maximalIdeal S := by
    simpa only [Ideal.map_span, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      ← Set.range_comp] using hgen
  obtain ⟨s, c, hc, hcard, hrad⟩ :=
    exists_constant_coefficients_parameter_finset (K := K) (φ ∘ f) r hgen' hdim
  let chosen : s → MvPolynomial σ K := fun x => Finsupp.linearCombination K f (c x)
  let t : Finset (MvPolynomial σ K) := Finset.univ.image chosen
  have hφ : ∀ x : s, φ (chosen x) = (x : S) := by
    intro x
    exact (Finsupp.apply_linearCombination K φ.toLinearMap f (c x)).trans (hc x)
  have himage : φ '' (t : Set (MvPolynomial σ K)) = (s : Set S) := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
      rw [hφ]
      exact x.2
    · intro hz
      refine ⟨chosen ⟨z, hz⟩, ?_, hφ ⟨z, hz⟩⟩
      exact Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩
  have htcard : t.card ≤ r := by
    calc
      t.card ≤ (Finset.univ : Finset s).card := Finset.card_image_le
      _ = s.card := by simp
      _ ≤ r := hcard
  have htdegree : ∀ p ∈ t, p.totalDegree ≤ d := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact WeightedTorusJets.W22.linearCombination_totalDegree_le f (c x) hdegree
  have htle : Ideal.span (t : Set (MvPolynomial σ K)) ≤ Ideal.span (Set.range f) := by
    apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact WeightedTorusJets.W22.linearCombination_mem_ideal f (c x) _
      (fun j => Ideal.subset_span (Set.mem_range_self j))
  have htrad : ((Ideal.span (t : Set (MvPolynomial σ K))).map φ.toRingHom).radical =
      IsLocalRing.maximalIdeal S := by
    have hset : φ.toRingHom '' (t : Set (MvPolynomial σ K)) = (s : Set S) := himage
    have hmap : (Ideal.span (t : Set (MvPolynomial σ K))).map φ.toRingHom =
        Ideal.span (s : Set S) :=
      (Ideal.map_span φ.toRingHom (t : Set (MvPolynomial σ K))).trans
        (congrArg Ideal.span hset)
    exact (congrArg Ideal.radical hmap).trans hrad
  refine ⟨t, htcard, htdegree, htle, htrad, ?_⟩
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [htrad]
  infer_instance

end W20

namespace W20

variable {K σ J : Type*} [Field K] [Infinite K] [Finite σ]

omit [Infinite K] [Finite σ] in
theorem localized_maximalIdeal_height
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).height = P.height := by
  rw [← IsLocalization.height_under P.primeCompl
    (IsLocalRing.maximalIdeal (Localization.AtPrime P))]
  rw [Localization.AtPrime.under_maximalIdeal]

theorem exists_localized_polynomial_parameters
    (f : J → MvPolynomial σ K) (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (r d : ℕ)
    (hgen : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hdim : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).height = r)
    (hdegree : ∀ j, (f j).totalDegree ≤ d) :
    ∃ t : Finset (MvPolynomial σ K),
      t.card ≤ r ∧
      (∀ p ∈ t, p.totalDegree ≤ d) ∧
      Ideal.span (t : Set (MvPolynomial σ K)) ≤ Ideal.span (Set.range f) ∧
      ((Ideal.span (t : Set (MvPolynomial σ K))).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))).radical =
          IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
      ((Ideal.span (t : Set (MvPolynomial σ K))).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))).IsPrimary ∧
      P ∈ (Ideal.span (t : Set (MvPolynomial σ K))).minimalPrimes ∧
      P.height ≤ t.card := by
  let φ : MvPolynomial σ K →ₐ[K] Localization.AtPrime P :=
    IsScalarTower.toAlgHom K (MvPolynomial σ K) (Localization.AtPrime P)
  obtain ⟨t, hcard, hdeg, hle, hrad, hprimary⟩ :=
    exists_degree_bounded_polynomial_parameters φ f r d hgen hdim hdegree
  refine ⟨t, hcard, hdeg, hle, hrad, hprimary, ?_, ?_⟩
  · exact WeightedTorusJets.W22.mem_minimalPrimes_of_localized_radical _ P hrad
  · exact WeightedTorusJets.W22.height_le_card_of_localized_radical_span t P hrad

theorem exists_exact_localized_polynomial_parameters
    (f : J → MvPolynomial σ K) (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (r d : ℕ)
    (hgen : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hheight : P.height = r)
    (hdegree : ∀ j, (f j).totalDegree ≤ d) :
    ∃ t : Finset (MvPolynomial σ K),
      t.card = r ∧
      (∀ p ∈ t, p.totalDegree ≤ d) ∧
      Ideal.span (t : Set (MvPolynomial σ K)) ≤ Ideal.span (Set.range f) ∧
      ((Ideal.span (t : Set (MvPolynomial σ K))).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))).radical =
          IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
      ((Ideal.span (t : Set (MvPolynomial σ K))).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))).IsPrimary ∧
      P ∈ (Ideal.span (t : Set (MvPolynomial σ K))).minimalPrimes := by
  obtain ⟨t, hcard, hdeg, hle, hrad, hprimary, hminimal, hbound⟩ :=
    exists_localized_polynomial_parameters f P r d hgen
      ((localized_maximalIdeal_height P).trans hheight) hdegree
  have hcard' : r ≤ t.card := by
    rw [hheight] at hbound
    exact_mod_cast hbound
  exact ⟨t, Nat.le_antisymm hcard hcard', hdeg, hle, hrad, hprimary, hminimal⟩

end W20

end

end SiegelZeros

end OAI
