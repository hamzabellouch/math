import OAI.AlgebraicGeometry.CartierSections.EtaleDerivatives
import OAI.AlgebraicGeometry.CartierSections.WeightIdeals
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.Tactic.LinearCombination

namespace OAI

/-!
# Isolated jets on regular charts

Euler operators and transverse derivatives isolate a least boundary monomial.
Faithful flatness descends the resulting congruence from formal power series
to the regular coordinate chart.
-/

open scoped BigOperators

namespace CartierSections

/-- A unit coefficient modulo a proper extended colon ideal descends along a
faithfully flat local algebra map. -/
theorem isolated_unit_descends
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.FaithfullyFlat R S]
    (I : Ideal R) (a g : R)
    (ha : algebraMap R S a ∉ I.map (algebraMap R S))
    (u q : S) (hu : IsUnit u) (hq : q ∈ I.map (algebraMap R S))
    (heq : algebraMap R S g = u * algebraMap R S a + q) :
    ∃ v r : R, IsUnit v ∧ r ∈ I ∧ g = v * a + r := by
  let J : Ideal R := Ideal.span {a} ⊔ I
  have hgS : algebraMap R S g ∈ J.map (algebraMap R S) := by
    rw [heq]
    apply Ideal.add_mem
    · apply Ideal.mul_mem_left
      apply Ideal.mem_map_of_mem
      exact (show Ideal.span {a} ≤ J from le_sup_left) (Ideal.subset_span rfl)
    · exact Ideal.map_mono (show I ≤ J from le_sup_right) hq
  have hg : g ∈ J := by
    rw [← J.comap_map_eq_self_of_faithfullyFlat (B := S)]
    exact hgS
  obtain ⟨b, hb, r, hr, hbr⟩ := Submodule.mem_sup.mp hg
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hb
  have hgR : g = v * a + r := by rw [hv]; exact hbr.symm
  have hvunit : IsUnit v := by
    apply (isUnit_map_iff (algebraMap R S) v).mp
    have hu' : IsUnit (algebraMap R S v + (u - algebraMap R S v)) := by
      simpa using hu
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu' with hvS | hdiff
    · exact hvS
    · exfalso
      apply ha
      apply (I.map (algebraMap R S)).unit_mul_mem_iff_mem hdiff |>.mp
      have hmul : (u - algebraMap R S v) * algebraMap R S a =
          algebraMap R S r - q := by
        have h := congrArg (algebraMap R S) hgR
        simp only [map_add, map_mul] at h
        rw [heq] at h
        linear_combination h
      rw [hmul]
      exact Ideal.sub_mem _ (Ideal.mem_map_of_mem _ hr) hq
  exact ⟨v, r, hvunit, hr, hgR⟩

end CartierSections

namespace CartierSections
/-- In the actual maximal-ideal completion, both the locality and faithful
flatness needed for descent follow from Noetherian locality. -/
theorem isolated_unit_descends_from_completion
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (a g : R)
    (ha : algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) a ∉
      I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))
    (u q : AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (hu : IsUnit u)
    (hq : q ∈ I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))
    (heq : algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) g =
      u * algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) a + q) :
    ∃ v r : R, IsUnit v ∧ r ∈ I ∧ g = v * a + r := by
  let : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact isolated_unit_descends I a g ha u q hu hq heq
end CartierSections

namespace CartierSections
section RegularOperators
variable {k A ι : Type*} [Field k] [CommRing A]
  [Algebra k A] [Algebra (MvPolynomial ι k) A]
  [IsScalarTower k (MvPolynomial ι k) A]
  [Algebra.FormallyEtale (MvPolynomial ι k) A]

noncomputable def chartEulerStep (i : ι) (l : ℕ) (f : A) : A :=
  algebraMap (MvPolynomial ι k) A (MvPolynomial.X i) *
    etalePartial (k := k) (T := A) i f - (l : k) • f

noncomputable def chartIterEuler : List (ι × ℕ) → A → A
  | [] => id
  | (i,l) :: L => fun f => chartEulerStep (k := k) i l (chartIterEuler L f)

noncomputable def chartIterPartial : List ι → A → A
  | [] => id
  | i :: L => fun f => etalePartial (k := k) (T := A) i (chartIterPartial L f)

variable (θ : A →ₐ[k] MvPowerSeries ι k)
  (hz : ∀ i, θ (algebraMap (MvPolynomial ι k) A (MvPolynomial.X i)) = MvPowerSeries.X i)

include hz

@[simp] theorem chartIterEuler_series (L : List (ι × ℕ)) (f : A) :
    θ (chartIterEuler (k := k) L f) = iterEuler L (θ f) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [chartIterEuler, chartEulerStep, map_sub, map_mul, map_smul,
      etalePartial_series_natural θ hz, hz, ih, iterEuler, eulerStep]

@[simp] theorem chartIterPartial_series (L : List ι) (f : A) :
    θ (chartIterPartial (k := k) L f) = iterPartial L (θ f) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [chartIterPartial, iterPartial, etalePartial_series_natural θ hz, ih]

omit [Algebra.FormallyEtale (MvPolynomial ι k) A] in
@[simp] theorem chart_polynomial_series (p : MvPolynomial ι k) :
    θ (algebraMap (MvPolynomial ι k) A p) = (p : MvPowerSeries ι k) := by
  have h : θ.comp (IsScalarTower.toAlgHom k (MvPolynomial ι k) A) =
      MvPolynomial.coeToMvPowerSeries.algHom k := by
    apply MvPolynomial.algHom_ext
    simpa using hz
  exact AlgHom.congr_fun h p

variable [Fintype ι]

/-- The monomial ideal of boundary exponents above a given weight in the local chart. -/
noncomputable def chartBoundaryWeightIdeal (B : Finset ι) (w : ι → ℝ) (L : ℝ) : Ideal A :=
  Ideal.span ((fun d => algebraMap (MvPolynomial ι k) A (MvPolynomial.monomial d 1)) ''
    {d | (∀ i ∉ B, d i = 0) ∧ L < realWeight w d})

omit [Algebra.FormallyEtale (MvPolynomial ι k) A] in
@[simp] theorem chartBoundaryWeightIdeal_map (B : Finset ι) (w : ι → ℝ) (L : ℝ) :
    (chartBoundaryWeightIdeal (k := k) (A := A) B w L).map θ.toRingHom =
      boundaryWeightIdeal B w L := by
  rw [chartBoundaryWeightIdeal, Ideal.map_span, Set.image_image]
  unfold boundaryWeightIdeal
  congr 1
  apply Set.image_congr
  intro d hd
  change θ (algebraMap (MvPolynomial ι k) A (MvPolynomial.monomial d 1)) = _
  rw [chart_polynomial_series θ hz]
  simp

/-- Isolation of an initial boundary monomial by regular differential operators.
The power series calculation descends to the chart by faithful flatness. -/
theorem regular_chart_isolated_jet [CharZero k]
    [Algebra A (MvPowerSeries ι k)] [IsScalarTower k A (MvPowerSeries ι k)]
    [Module.FaithfullyFlat A (MvPowerSeries ι k)]
    [IsLocalHom (algebraMap A (MvPowerSeries ι k))]
    (hθ : θ.toRingHom = algebraMap A (MvPowerSeries ι k))
    (f : A) (hf : θ f ≠ 0) (s : Finset ℕ) (p : ℕ → MvPolynomial ι k) (N : ℕ)
    (hdeg : ∀ j ∈ s, (p j).totalDegree ≤ N) (hnonzero : ∃ j ∈ s, p j ≠ 0)
    (hrelation : ∑ j ∈ s, (p j : MvPowerSeries ι k) * (θ f)^j = 0)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (B : Finset ι)
    (hB : ∀ i ∈ B, 0 < w i) (hwzero : ∀ i ∉ B, w i = 0) :
    ∃ (γ α β : ι →₀ ℕ) (u q : A),
      IsInitialExponent w (θ f) γ ∧ exponentDegree γ ≤ N ∧
      α + β = γ ∧ (∀ i ∉ B, α i = 0) ∧ (∀ i ∈ B, β i = 0) ∧
      realWeight w α = realWeight w γ ∧
      (eulerFactors B N α).length + β.toMultiset.toList.length ≤ (B.card + 1) * (N+1) ∧
      IsUnit u ∧
      chartIterPartial (k := k) β.toMultiset.toList (chartIterEuler (k := k) (eulerFactors B N α) f) =
        u * algebraMap (MvPolynomial ι k) A (MvPolynomial.monomial α 1) + q ∧
      q ∈ chartBoundaryWeightIdeal (k := k) B w (realWeight w γ) := by
  classical
  obtain ⟨γ, α, β, u, q, hγ, hγdeg, hab, hα, hβ, hwα, horder, hu, heq, hq⟩ :=
    algebraic_series_isolated_jet hf s p N hdeg hnonzero hrelation w hw B hB hwzero
  let I : Ideal A := chartBoundaryWeightIdeal (k := k) B w (realWeight w γ)
  let a : A := algebraMap (MvPolynomial ι k) A (MvPolynomial.monomial α 1)
  let g : A := chartIterPartial (k := k) β.toMultiset.toList (chartIterEuler (k := k) (eulerFactors B N α) f)
  have hI : I.map (algebraMap A (MvPowerSeries ι k)) = boundaryWeightIdeal B w (realWeight w γ) := by
    rw [← hθ]
    exact chartBoundaryWeightIdeal_map θ hz B w _
  have ha : algebraMap A (MvPowerSeries ι k) a = MvPowerSeries.monomial α 1 := by
    rw [← hθ]
    simpa [a] using chart_polynomial_series θ hz (MvPolynomial.monomial α 1)
  have haneq : algebraMap A (MvPowerSeries ι k) a ∉ I.map (algebraMap A (MvPowerSeries ι k)) := by
    rw [hI, ha, ← hwα]
    exact initial_monomial_not_mem_boundaryWeightIdeal B w hw α
  obtain ⟨v, r, hv, hr, hgr⟩ := isolated_unit_descends I a g haneq u q hu
    (by rwa [hI]) (by
      rw [ha, ← hθ]
      change θ (chartIterPartial (k := k) _ (chartIterEuler (k := k) _ f)) = _
      rw [chartIterPartial_series θ hz, chartIterEuler_series θ hz, heq, mul_comm])
  exact ⟨γ, α, β, v, r, hγ, hγdeg, hab, hα, hβ, hwα, horder, hv, hgr, hr⟩
end RegularOperators
end CartierSections

end OAI
