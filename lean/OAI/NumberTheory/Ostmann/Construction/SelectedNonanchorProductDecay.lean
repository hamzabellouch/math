import OAI.NumberTheory.Ostmann.Construction.SelectedNonanchorProductDiagonal
import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchingError

namespace OAI

/-! # Every code-changing diagonal cost is absorbed by the actual character error -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_selected_nonanchor_product_decay {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Ar Kr : ℕ)
    (s C S H z α βw γs βa γw c T : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα : 0 < α) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hc : 0 < c) (hT : 0 ≤ T) :
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
    ∀ (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, ρ (bulk i) = .word)
      (_hχ : ∀ e ∈ cellPreservingMatchings (selectedBulkLabel ρ (n + 1) m bulk hbulk) \
        selectedAnchorMatchingSet ρ (n + 1) m bulk hbulk,
        ∀ i, χ (copyScheduleOrigin (n + 1) (e i).val) = χ (copyScheduleOrigin (n + 1) i.val))
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
      (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R) (a b : ℕ) (_ha : 0 < a) (_hb : (b : ℝ) ≤ R) (gap : ℝ)
      (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
      (productLower : ℝ) (_hproductLower : 0 < productLower)
      (_hgap : Real.exp gap * (b : ℝ) ≤ productLower)
      (_hproduct : ConstituentHProductLower role size (n + 1) childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) productLower)
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
    let Sbad := cellPreservingMatchings (selectedBulkLabel ρ (n + 1) m bulk hbulk) \
      selectedAnchorMatchingSet ρ (n + 1) m bulk hbulk
    (∑ N ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot (n + 1) P hprime Q₀ childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) (scheduledFrequencyHistory cutoff (n + 1)) Sbad N).re) ≤
      Real.exp (-gap) * Real.exp (-T * M) := by
  filter_upwards [eventual_selected_nonanchor_product_diagonal role n Ar Kr
      s C S H z α βw γs βa γw c hs hC hS hH hz hα hαw hsw hαa hwa hc,
    eventual_constituent_matching_error role (n + 1) s C H T z α (c / 32)
      hs hC hH hT hz hα (by positivity)] with L hdiag herr
  intro size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ childBound pivotBound ranges
    hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu ρ FP m bulk hbulk hχ small large hsmall hlarge
    hp P hP hprime Q₀ hQP hQmass hχsmall hχword ℓs ℓw hℓs hℓw Bs Bw Aw Ew Aa Ea hAw hAa
    hsmallrange hwordrange hlargerange V R hV hR a b ha hb gap hlowerP hupperP productLower hproductLower hgap hproduct
    cutoff hcutoff hVfreq hs₀ hs₁ hwidth hEw hEa hQinv hshorts hshortw hlongw hlonga hBs hBw
    hmin hratio hprimefreq Sbad
  have hd := hdiag size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ childBound pivotBound ranges
    hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu m bulk hbulk hχ small large hsmall hlarge
    hp P hP hprime Q₀ hQP hQmass hχsmall hχword ℓs ℓw hℓs hℓw Bs Bw Aw Ew Aa Ea hAw hAa
    hsmallrange hwordrange hlargerange V R hV hR a b ha hb gap hlowerP hupperP productLower hproductLower hgap hproduct
    cutoff hcutoff hVfreq hs₀ hs₁ hwidth hEw hEa hQinv hshorts hshortw hlongw hlonga hBs hBw
    hmin hratio hprimefreq
  have he := herr size Smax hsize M hm hmL hSm cutoff hcutoff hVfreq Sbad Q₀ hQinv
  apply hd.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)

end Ostmann

end OAI
