import OAI.NumberTheory.Ostmann.Construction.ScheduledMatchedPairDecay
import OAI.NumberTheory.Ostmann.Construction.ScheduledAnchorSymmetry
import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchingPairSum

namespace OAI

/-! # The actual code-changing diagonal after summing external pivots -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_scheduled_nonanchor_diagonal {I : Type u} [Fintype I]
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
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n + 1, ∀ r ∈ ranges j, r.atoms.length ≤ Ar)
      (_hcount : ∀ j ≤ n + 1, (ranges j).length ≤ Kr)
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hX : 0 < X) (_hXlo : 1 < X * lo)
      (_hu : ∀ j ≤ n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let FP := WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀ (m : ℕ) (word : Fin m ≃ {i : Σ a, Fin (size a) // ρ i = .word})
      (_hχ : ∀ e ∈ cellPreservingMatchings (scheduledBulkLabel ρ (n + 1)) \
        scheduledAnchorMatchingSet ρ (n + 1) m word,
        ∀ i, χ (copyScheduleOrigin (n + 1) (e i).val) = χ (copyScheduleOrigin (n + 1) i.val))
      (small large : Fin (n + 1) → (Σ a, Fin (size a)))
      (_hsmall : ∀ j, ρ (small j) = .anchor j) (_hlarge : ∀ j, ρ (large j) = .anchor j)
      (_hp : ∀ j < n + 1, ρ (pivot j) = .pivot j)
      (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
      (Q₀ : (Σ i, Fin (size i)) → Finset ℕ) (_hQP : ∀ i, Q₀ i ⊆ P)
      (_hQmass : ∀ i, 0 < ∑ q ∈ Q₀ i, (q : ℝ)⁻¹)
      (_hχsmall : ∀ j q, q ∈ Q₀ (small j) → χ (small j) q ^ 2 ≠ 1)
      (_hχword : ∀ v, ρ v = .word → ∀ q ∈ Q₀ v, χ v q ^ 2 ≠ 1)
      (ℓs ℓw : ℝ) (_hℓs : 0 < ℓs) (_hℓw : 0 < ℓw) (Bs Bw Aw Ew Aa Ea : ℕ)
      (_hAw : 0 < Aw) (_hAa : 0 < Aa)
      (_hsmallrange : ∀ j q, q ∈ Q₀ (small j) → ℓs ≤ (q : ℝ) ∧ q ≤ Bs)
      (_hwordrange : ∀ v, ρ v = .word → ∀ p ∈ Q₀ v,
        (ℓw ≤ (p : ℝ) ∧ p ≤ Bw) ∧ (2 * Aw ≤ p ∧ p ≤ Ew))
      (_hlargerange : ∀ j p, p ∈ Q₀ (large j) → 2 * Aa ≤ p ∧ p ≤ Ea)
      (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R) (a b : ℕ) (_ha : 0 < a) (_hb : (b : ℝ) ≤ R) (gap : ℝ)
      (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
      (loH : CopyScheduleH ρ (n + 1) → ℝ) (_hloH : ∀ h, 0 < loH h)
      (_hcell : ∀ h p, p ∈ Q₀ (copyScheduleOrigin (n + 1) h.val) → loH h ≤ (p : ℝ))
      (_hgap : Real.exp gap * (b : ℝ) ≤ ∏ h, loH h)
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
      (_hprimefreq : ∀ p ∈ P, cutoff (n + 1) < p),
    let Sbad := cellPreservingMatchings (scheduledBulkLabel ρ (n + 1)) \
      scheduledAnchorMatchingSet ρ (n + 1) m word
    (∑ N ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot (n + 1) P hprime Q₀ childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) (scheduledFrequencyHistory cutoff (n + 1)) Sbad N).re) ≤
      Real.exp (-gap) * ((Sbad.card : ℝ) *
        (Fintype.card (ScheduledFrequencyIndex cutoff (n + 1)) : ℝ) ^ 2 *
        (∏ h : CopyScheduleH ρ (n + 1),
          (∑ p ∈ Q₀ (copyScheduleOrigin (n + 1) h.val), (p : ℝ)⁻¹)⁻¹)) *
        Real.exp (-(c / 32) * Real.exp (α * L)) := by
  filter_upwards [eventual_scheduled_matched_pair_decay role n Ar Kr
    s C S H z α βw γs βa γw c hs hC hS hH hz hα hαw hsw hαa hwa hc] with L hdec
  intro size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ childBound pivotBound ranges
    hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu ρ FP m word hχ small large hsmall hlarge
    hp P hP hprime Q₀ hQP hQmass hχsmall hχword ℓs ℓw hℓs hℓw Bs Bw Aw Ew Aa Ea hAw hAa
    hsmallrange hwordrange hlargerange V R hV hR a b ha hb gap hlowerP hupperP loH hloH hcell hgap
    cutoff hcutoff hVfreq hs₀ hs₁ hwidth hEw hEa hQinv hshorts hshortw hlongw hlonga hBs hBw
    hmin hratio hprimefreq Sbad
  apply constituentMatchingFamily_interval_pair_bound role size χ κ pivot (n + 1) P hprime Q₀
    childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
    (scheduledFrequencyHistory cutoff (n + 1)) Sbad a b ha gap
    (Real.exp (-(c / 32) * Real.exp (α * L))) (Real.exp_nonneg _) loH hloH hgap
  intro N hN e he d d' _
  have hinv := scheduled_nonanchor_symm ρ (n + 1) m word e he
  have hNr : (N : ℝ) ≤ R := (Nat.cast_le.mpr (Finset.mem_Icc.mp hN).2).trans hb
  have hh := hdec size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ e.symm (hχ _ hinv)
    childBound pivotBound ranges hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu
    m word hinv small large hsmall hlarge hp P hP hprime Q₀ hQP hQmass hχsmall hχword
    ℓs ℓw hℓs hℓw Bs Bw Aw Ew Aa Ea hAw hAa hsmallrange hwordrange hlargerange
    V R hV hR N hNr hlowerP hupperP (∏ h, loH h) (Finset.prod_pos fun h _ => hloH h) loH
    (fun h => (hloH h).le) hcell le_rfl cutoff hcutoff hVfreq hs₀ hs₁ hwidth hEw hEa hQinv
    hshorts hshortw hlongw hlonga hBs hBw hmin hratio hprimefreq d d'
  simpa only [constituentOriginalMatchedPair, Equiv.symm_symm, Sum.elim_inl, Sum.elim_inr,
    finite_univ_canonical] using hh

end Ostmann

end OAI
