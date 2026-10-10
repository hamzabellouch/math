import OAI.NumberTheory.Ostmann.Construction.ConstituentSupportedPairDecay
import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchedCostData
import OAI.NumberTheory.Ostmann.Construction.FinalPairPeriodScale

namespace OAI

/-! # The matched original-prior comparison with its actual finite costs -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_constituent_supported_pair_from_sizes {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Aw Kr : ℕ) (s C S H z α₀ β γ c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα₀ : 0 < α₀) (hαβ : α₀ < β) (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (size : I → ℕ) (Smax : ℕ)
      (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M))
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
      (_hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n, ∀ r ∈ ranges j, r.atoms.length ≤ Aw)
      (_hcount : ∀ j ≤ n, (ranges j).length ≤ Kr)
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hu : ∀ j ≤ n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let K := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n
    let ρ := (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
    let G := constituentMatchedGraph role size pivot n e
    let FP := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀
    (a b : K) (_hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (_ht : NonzeroInternalFrequencies n t)
    (_ht' : NonzeroInternalFrequencies n t')
    (_hself : G a a = 0 ∧ G b b = 0) (_hreverse : G b a = 0)
    (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
    (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (_hnonprincipal : ∀ q ∈ Q a, (scheduledRetainedCharacters ρ χ n) a q ^ G a b ≠ 1)
    (A E : ℕ) (_hA : 0 < A)
    (_hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (_hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (_hlow : ∀ p ∈ Q b, 2 * A ≤ p) (_hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (_hlower : 0 < lower) (_hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (_hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R) (N : ℕ) (_hN : (N : ℝ) ≤ R)
    (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (_hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (_hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (Z : ℝ) (_hZ : 0 < Z) (_hproduct : ConstituentHProductLower role size n childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) Z)
    (Vfreq : ℕ)
    (_hVfreq : (Vfreq : ℝ) ≤ Real.exp (C * (1 + M)))
    (_hfv : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ Vfreq)
    (_hfv' : ∀ s ∈ allFrequencyList n t', s.natAbs ≤ Vfreq)
    (_hs₀ : SchwartzMap.seminorm ℝ 0 0 (FP).profile ≤ S)
    (_hs₁ : SchwartzMap.seminorm ℝ 0 1 (FP).profile ≤ S)
    (_hwidth : ∀ i, (FP).upper i - (FP).lower i ≤ Real.exp (C * (1 + M)))
    (_hE : ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
    (_hQinv : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
    (_hshort : Real.exp (c * Real.exp (α₀ * L)) ≤ lower)
    (_hlong : Real.exp (Real.exp (β * L)) ≤ (A : ℝ))
    (_hBqscale : (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)))
    (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α₀ * L)) ≤ (p : ℝ))
    (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M))),
    let leaf := scheduleFourierLeaf role ψ X lo hi
    let core := fun x : K → P => constituentCharacterCore role size χ κ pivot n P hprime
      childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) N
    ‖∑ x : K → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) *
      (core x ((fun h => x (.inl h)), t) * conj (core x ((fun h => x (.inl (e h))), t')))‖ ≤
      (∏ h : CopyScheduleH ρ n, (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ *
        Real.exp (-(c / 32) * Real.exp (α₀ * L)) := by
  let a₀ := constituentFinalCountRate (Fintype.card I) n s
  let b₀ := (((2 * 3 ^ n * Fintype.card I + Aw : ℕ) : ℝ) * s + 4)
  let d₀ : ℝ := (Kr * (2 ^ (n + 1) - 1) + 1 : ℕ)
  have ha₀ : 0 ≤ a₀ := constituentFinalCountRate_nonneg _ _ _ hs
  have hb₀ : 0 ≤ b₀ := by dsimp [b₀]; positivity
  have hd₀ : 0 ≤ d₀ := by dsimp [d₀]; positivity
  filter_upwards [eventual_constituent_supported_pair_decay n a₀ b₀ d₀ C S H z α₀ β γ c
      ha₀ hb₀ hd₀ hC hS hH hz hα₀ hαβ hγβ hc,
    eventual_final_pair_period_scale n b₀ C z β hb₀ hC hz (hα₀.trans hαβ)]
    with L hdec hperiod
  intro size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ e hχ childBound pivotBound ranges
    hrange hcount ψ hreal X lo hi hlo hhi hu K ρ G FP
    a b hab t t' ht ht' hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    V R hV hR N hN hlowerP hupperP hfreq hfreq' Z hZ hproduct
    Vfreq hVfreq hfv hfv' hs₀ hs₁ hwidth hE hQinv hshort hlong hBqscale hmin hratio leaf core
  let W := insertedConstituentWord role size n
  let W' := fun v => List.map (insertedConstituentPerm role size n e) (W v)
  let B := 2 * 3 ^ n * Fintype.card I * Smax + Aw * Smax + 4
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBlinear : (B : ℝ) ≤ b₀ * (1 + M) :=
    constituent_word_budget_linear n Aw Smax s M hSm hm
  obtain ⟨hw, hw', hD, hD', hU, hU'⟩ :=
    constituent_pair_word_bounds role size n e childBound pivotBound ranges
      Smax Aw hSmax hsize hrange
  have hcounts := constituent_matched_linear_counts role size n e Smax s M
    hSmax hsize hs hm hSm
  have hranges := expandedRootRanges_pair_linear_count role n Kr W W' ranges hcount
    (originalProductRange ((retainedHWord (CopyScheduleH ρ n) (CopyScheduleY ρ n)).map some) n Z 0) M hm
  have hMA := hperiod M B Vfreq A t t' hm hmL hBlinear hVfreq hfv hfv' hlong
  have hword := constituent_retained_word_bound role size n Smax Aw hsize
  exact hdec I role size χ κ pivot hκ e hχ childBound pivotBound ranges ψ hreal X lo hi hlo hhi hu
    a b hab t t' ht ht' B hB hw hw' hD hD' hU hU' hself hreverse P hP hprime Q hQP hQmass
    hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq V R hV hR
    N hN hlowerP hupperP hfreq hfreq' hword Z hZ hproduct
    M hm hmL Vfreq hBlinear hranges.1 hranges.2 hVfreq hfv hfv' hs₀ hs₁ hwidth hE hQinv
    hshort hlong hBqscale hmin hratio hcounts.1 hcounts.2

end Ostmann

end OAI
