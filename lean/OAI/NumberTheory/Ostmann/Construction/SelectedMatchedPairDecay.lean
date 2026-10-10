import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchedSizeDecay
import OAI.NumberTheory.Ostmann.Construction.ConstituentCoreFrequencySupport
import OAI.NumberTheory.Ostmann.Construction.SelectedNonanchorWitness
import OAI.NumberTheory.Ostmann.Construction.ScheduledRootIndex

namespace OAI

/-! # Code-changing diagonal pairs with the actual varying-cutoff histories -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_selected_matched_pair_decay {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Ar Kr : ℕ)
    (s C S H z α βw γs βa γw c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα : 0 < α) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (size : I → ℕ) (Smax : ℕ)
      (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M))
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) (n + 1)))
      (_hχ : ∀ i, χ (copyScheduleOrigin (n + 1) (e i).val) = χ (copyScheduleOrigin (n + 1) i.val))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n + 1, ∀ r ∈ ranges j, r.atoms.length ≤ Ar)
      (_hcount : ∀ j ≤ n + 1, (ranges j).length ≤ Kr)
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hX : 0 < X) (_hXlo : 1 < X * lo)
      (_hu : ∀ j ≤ n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let K := CopyScheduleH ρ (n + 1) ⊕ CopyScheduleY ρ (n + 1)
    let FP := WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀ (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, ρ (bulk i) = .word)
      (_he : e ∈ cellPreservingMatchings (selectedBulkLabel ρ (n + 1) m bulk hbulk) \
        selectedAnchorMatchingSet ρ (n + 1) m bulk hbulk)
      (small large : Fin (n + 1) → (Σ a, Fin (size a)))
      (_hsmall : ∀ j, ρ (small j) = .anchor j) (_hlarge : ∀ j, ρ (large j) = .anchor j)
      (_hp : ∀ j < n + 1, ρ (pivot j) = .pivot j)
      (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
      (Q₀ : (Σ i, Fin (size i)) → Finset ℕ) (_hQP : ∀ i, Q₀ i ⊆ P)
      (_hQmass : ∀ i, 0 < ∑ q ∈ Q₀ i, (q : ℝ)⁻¹)
      (_hχsmall : ∀ j q, q ∈ Q₀ (small j) → χ (small j) q ^ 2 ≠ 1)
      (_hχword : ∀ i q, q ∈ Q₀ (bulk i) → χ (bulk i) q ^ 2 ≠ 1)
      (ℓs ℓw : ℝ) (_hℓs : 0 < ℓs) (_hℓw : 0 < ℓw) (Bs Bw Aw Ew Aa Ea : ℕ)
      (_hAw : 0 < Aw) (_hAa : 0 < Aa)
      (_hsmallrange : ∀ j q, q ∈ Q₀ (small j) → ℓs ≤ (q : ℝ) ∧ q ≤ Bs)
      (_hwordrange : ∀ i p, p ∈ Q₀ (bulk i) →
        (ℓw ≤ (p : ℝ) ∧ p ≤ Bw) ∧ (2 * Aw ≤ p ∧ p ≤ Ew))
      (_hlargerange : ∀ j p, p ∈ Q₀ (large j) → 2 * Aa ≤ p ∧ p ≤ Ea)
      (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R) (N : ℕ) (_hN : (N : ℝ) ≤ R)
      (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
      (Z : ℝ) (_hZ : 0 < Z) (loH : CopyScheduleH ρ (n + 1) → ℝ) (_hloH : ∀ h, 0 ≤ loH h)
      (_hcell : ∀ h p, p ∈ Q₀ (copyScheduleOrigin (n + 1) h.val) → loH h ≤ (p : ℝ))
      (_hscale : Z ≤ ∏ h, loH h)
      (cutoff : ℕ → ℕ) (_hcutoff : Monotone cutoff)
      (_hVfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * (1 + M)))
      (_hs₀ : SchwartzMap.seminorm ℝ 0 0 FP.profile ≤ S)
      (_hs₁ : SchwartzMap.seminorm ℝ 0 1 FP.profile ≤ S)
      (_hwidth : ∀ i, FP.upper i - FP.lower i ≤ Real.exp (C * (1 + M)))
      (_hEw : ((Nat.log 2 Ew + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hEa : ((Nat.log 2 Ea + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hQinv : ∀ i, (∑ q ∈ Q₀ i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
      (_hshorts : Real.exp (c * Real.exp (α * L)) ≤ ℓs)
      (_hshortw : Real.exp (c * Real.exp (α * L)) ≤ ℓw)
      (_hlongw : Real.exp (Real.exp (βw * L)) ≤ (Aw : ℝ))
      (_hlonga : Real.exp (Real.exp (βa * L)) ≤ (Aa : ℝ))
      (_hBs : (Bs : ℝ) ≤ Real.exp (Real.exp (γs * L)))
      (_hBw : (Bw : ℝ) ≤ Real.exp (Real.exp (γw * L)))
      (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α * L)) ≤ (p : ℝ))
      (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
      (_hprimefreq : ∀ p ∈ P, cutoff (n + 1) < p)
      (d d' : ScheduledFrequencyIndex cutoff (n + 1)),
    let Q : K → Finset ℕ := Sum.elim
      (fun h => Q₀ (copyScheduleOrigin (n + 1) h.val))
      (fun y => Q₀ (copyScheduleOrigin (n + 1) y.val))
    let core := fun x : K → P => constituentCharacterCore role size χ κ pivot (n + 1) P hprime
      childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      (scheduledFrequencyHistory cutoff (n + 1)) (fun y => x (.inr y)) N
    ‖∑ x : K → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) *
      (core x ((fun h => x (.inl h)), d) * conj (core x ((fun h => x (.inl (e h))), d')))‖ ≤
      (∏ h : CopyScheduleH ρ (n + 1), (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ *
        Real.exp (-(c / 32) * Real.exp (α * L)) := by
  filter_upwards [eventual_constituent_matched_pair_from_sizes role (n + 1) Ar Kr
      s C S H z α βw γs c hs hC hS hH hz hα hαw hsw hc,
    eventual_constituent_matched_pair_from_sizes role (n + 1) Ar Kr
      s C S H z α βa γw c hs hC hS hH hz hα hαa hwa hc] with L hdecw hdeca
  intro size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ e hχ childBound pivotBound ranges
    hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu ρ K FP m bulk hbulk he small large hsmall hlarge
    hp P hP hprime Q₀ hQP hQmass hχsmall hχword ℓs ℓw hℓs hℓw Bs Bw Aw Ew Aa Ea hAw hAa
    hsmallrange hwordrange hlargerange V R hV hR N hN hlowerP hupperP Z hZ loH hloH hcell hscale
    cutoff hcutoff hVfreq hs₀ hs₁ hwidth hEw hEa hQinv hshorts hshortw hlongw hlonga hBs hBw
    hmin hratio hprimefreq d d' Q core
  let t := scheduledFrequencyHistory cutoff (n + 1) d
  let t' := scheduledFrequencyHistory cutoff (n + 1) d'
  have hnonneg : 0 ≤ (∏ h : CopyScheduleH ρ (n + 1),
      (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ * Real.exp (-(c / 32) * Real.exp (α * L)) :=
    mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (inv_nonneg.mpr hZ.le))
      (Real.exp_nonneg _)
  by_cases hzero : ∀ (x : K → P) (l : CopyScheduleH ρ (n + 1) → P), core x (l, d) = 0
  · simp only [hzero, zero_mul, mul_zero, Finset.sum_const_zero, norm_zero]
    exact hnonneg
  by_cases hzero' : ∀ (x : K → P) (l : CopyScheduleH ρ (n + 1) → P), core x (l, d') = 0
  · simp only [hzero', map_zero, mul_zero, Finset.sum_const_zero, norm_zero]
    exact hnonneg
  push Not at hzero hzero'
  obtain ⟨x, l, hxl⟩ := hzero
  obtain ⟨x', l', hxl'⟩ := hzero'
  obtain ⟨ht, hn⟩ := constituentCharacterCore_nonzero_frequencies role size χ κ pivot (n + 1)
    P hprime childBound pivotBound ranges ψ X lo hi hX hXlo
    (scheduledFrequencyHistory cutoff (n + 1)) (fun y => x (.inr y)) N l d hxl
  obtain ⟨ht', hn'⟩ := constituentCharacterCore_nonzero_frequencies role size χ κ pivot (n + 1)
    P hprime childBound pivotBound ranges ψ X lo hi hX hXlo
    (scheduledFrequencyHistory cutoff (n + 1)) (fun y => x' (.inr y)) N l' d' hxl'
  have hfv := scheduledFrequencyHistory_all_bound cutoff hcutoff (n + 1) d
  have hfv' := scheduledFrequencyHistory_all_bound cutoff hcutoff (n + 1) d'
  obtain ⟨hfreq, hrealFreq⟩ := finite_frequency_range_data P hP R (cutoff (n + 1))
    hprimefreq hupperP (n + 1) t hn hfv
  obtain ⟨hfreq', hrealFreq'⟩ := finite_frequency_range_data P hP R (cutoff (n + 1))
    hprimefreq hupperP (n + 1) t' hn' hfv'
  obtain ⟨a, b, hab, hself, hreverse, hnonprincipal, hcases⟩ :=
    selected_nonanchor_prime_ranges ρ pivot n m bulk hbulk e he small large hsmall hlarge hp χ Q₀
      hχsmall hχword ℓs ℓw Bs Bw Aw Ew Aa Ea hsmallrange hwordrange hlargerange
  have hQP' : ∀ i, Q i ⊆ P := by intro i; cases i <;> exact hQP _
  have hQmass' : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹ := by intro i; cases i <;> exact hQmass _
  have hQinv' : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)) := by
    intro i; cases i <;> exact hQinv _
  rcases hcases with hcase | hcase
  · exact hdecw size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ e hχ childBound pivotBound ranges
      hrange hcount ψ hreal X lo hi hlo hhi hu a b hab t t' ht ht' hself hreverse P hP hprime Q
      hQP' hQmass' hnonprincipal Aw Ew hAw hfreq hfreq'
      (fun p hp => (hcase.2 p hp).1) (fun p hp => (hcase.2 p hp).2) ℓs hℓs
      (fun q hq => (hcase.1 q hq).1) Bs (fun q => (hcase.1 q.val q.property).2)
      V R hV hR N hN hlowerP hupperP hrealFreq hrealFreq' Z hZ loH hloH hcell hscale
      (cutoff (n + 1)) hVfreq hfv hfv' hs₀ hs₁ hwidth hEw hQinv' hshorts hlongw hBs hmin hratio
  · exact hdeca size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ e hχ childBound pivotBound ranges
      hrange hcount ψ hreal X lo hi hlo hhi hu a b hab t t' ht ht' hself hreverse P hP hprime Q
      hQP' hQmass' hnonprincipal Aa Ea hAa hfreq hfreq'
      (fun p hp => (hcase.2 p hp).1) (fun p hp => (hcase.2 p hp).2) ℓw hℓw
      (fun q hq => (hcase.1 q hq).1) Bw (fun q => (hcase.1 q.val q.property).2)
      V R hV hR N hN hlowerP hupperP hrealFreq hrealFreq' Z hZ loH hloH hcell hscale
      (cutoff (n + 1)) hVfreq hfv hfv' hs₀ hs₁ hwidth hEa hQinv' hshortw hlonga hBw hmin hratio

end Ostmann

end OAI
