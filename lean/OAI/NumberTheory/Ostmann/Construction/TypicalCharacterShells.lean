import OAI.NumberTheory.Ostmann.Construction.TypicalCharacterEndpoints
import OAI.NumberTheory.Ostmann.Construction.TargetPrimeWords

namespace OAI

/-! # A fixed finite test family covers precisely the needed character shells -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

abbrev CharacterShellTestIndex (k : ℕ) := Fin (5 * k + 1) ⊕ ((Fin k × Bool) ⊕ Bool)

noncomputable def characterShellTests (k : ℕ) (P Ubulk T₀ : Finset ℕ)
    (Ulate T c : ℝ) (u : Fin k × Bool → ℝ) : CharacterShellTestIndex k → Finset ℕ
  | .inl j => if c ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ ∧
      (∀ p ∈ loglogShell P (Ulate + j), Real.log (p : ℝ) ≤ T / 4)
      then loglogShell P (Ulate + j) else Ubulk
  | .inr (.inl j) => loglogShell P (u j)
  | .inr (.inr false) => Ubulk
  | .inr (.inr true) => T₀

/-- Ineligible grid shells are represented by the bulk test. Thus the index
set is fixed before L, without asking for mass in empty or unusable shells. -/
theorem eventual_typical_character_shells
    (hsize : PublishedSummandSizeBound) {C : ℝ} (hM : MertensLowerBound C)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (k : ℕ) (α β D δ c : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∃ L₀ t₀ : ℝ, ∀ L T : ℝ, L₀ ≤ L → t₀ ≤ T →
      Real.log T ≤ β * L + D → ∀ X : ℕ, (X : ℝ) = Real.exp T →
      ∀ (P Ubulk T₀ : Finset ℕ) (Ulate : ℝ) (u : Fin k × Bool → ℝ)
        (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (center : ∀ p : ℕ, ZMod p) (ζ : ℂ),
      ‖ζ‖ = 1 → (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, Real.exp (α * L) ≤ Real.log (p : ℝ)) →
      Ubulk ⊆ P → T₀ ⊆ P →
      c ≤ ∑ p ∈ Ubulk, (p : ℝ)⁻¹ → c ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
      (∀ j, c ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
      (∀ p ∈ Ubulk, Real.log (p : ℝ) ≤ T / 4) →
      (∀ p ∈ T₀, Real.log (p : ℝ) ≤ T / 4) →
      (∀ j p, p ∈ loglogShell P (u j) → Real.log (p : ℝ) ≤ T / 4) →
      (∀ p ∈ P, δ ≤ residueTestMean (tailSupport A N p)
        (realTranslatedCharacterTest χ center ζ p)) →
      ∃ G ⊆ summandTail A (summandTailCutoff T) X,
        a * Real.exp (T / 2) / T ^ 3 ≤ (G.card : ℝ) ∧
        ∀ x ∈ G,
          (δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P Ubulk p : ℂ) *
            χ p ((x : ZMod p) - center p)‖) ∧
          (δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P T₀ p : ℂ) *
            χ p ((x : ZMod p) - center p)‖) ∧
          (∀ j, (δ / 2) * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
            ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * χ p ((x : ZMod p) - center p)).re) ∧
          (∀ j : ℕ, j ≤ 5 * k →
            c ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ →
            (∀ p ∈ loglogShell P (Ulate + j), Real.log (p : ℝ) ≤ T / 4) →
            (δ / 2) * (∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) ≤
              ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ *
                (ζ * χ p ((x : ZMod p) - center p)).re) := by
  obtain ⟨a, ha, L₀, t₀, ht⟩ := eventual_typical_character_tests hsize hM hA hB h N hN
    (Finset.univ : Finset (CharacterShellTestIndex k)) α β D δ c hα hδ hc
  refine ⟨a, ha, L₀, t₀, ?_⟩
  intro L T hL hT hlog X hX P Ubulk T₀ Ulate u χ center ζ hζ hP hmin hUP hTP
    hUmass hTmass humass hUcut hTcut hucut href
  let R := characterShellTests k P Ubulk T₀ Ulate T c u
  have hdata : ∀ j, R j ⊆ P ∧ c ≤ ∑ p ∈ R j, (p : ℝ)⁻¹ ∧
      ∀ p ∈ R j, Real.log (p : ℝ) ≤ T / 4 := by
    rintro (j | (j | b))
    · dsimp only [R, characterShellTests]
      split_ifs with hj
      · exact ⟨Finset.filter_subset _ _, hj.1, hj.2⟩
      · exact ⟨hUP, hUmass, hUcut⟩
    · exact ⟨Finset.filter_subset _ _, humass j, hucut j⟩
    · cases b
      · exact ⟨hUP, hUmass, hUcut⟩
      · exact ⟨hTP, hTmass, hTcut⟩
  obtain ⟨G, hG, hcard, hgood⟩ := ht L T hL hT hlog X hX P R χ center ζ hζ
    (fun j _ => (hdata j).1) (by
      intro j _ p hp
      have hpp := hP p ((hdata j).1 hp)
      refine ⟨hpp, ?_, hmin p ((hdata j).1 hp)⟩
      calc
        (p : ℝ) = Real.exp (Real.log (p : ℝ)) :=
          (Real.exp_log (by exact_mod_cast hpp.pos)).symm
        _ ≤ Real.exp (T / 4) := Real.exp_le_exp.mpr ((hdata j).2.2 p hp))
    (fun j _ => (hdata j).2.1) (fun j _ p hp => href p ((hdata j).1 hp))
  refine ⟨G, hG, hcard, ?_⟩
  intro x hx
  refine ⟨(hgood x hx (.inr (.inr false)) (Finset.mem_univ _)).2,
    (hgood x hx (.inr (.inr true)) (Finset.mem_univ _)).2,
    fun j => (hgood x hx (.inr (.inl j)) (Finset.mem_univ _)).1, ?_⟩
  intro j hj hmass hcut
  have hh := (hgood x hx (.inl ⟨j, Nat.lt_succ_of_le hj⟩) (Finset.mem_univ _)).1
  simpa only [R, characterShellTests, ite_eq_left (And.intro hmass hcut)] using hh

end Ostmann

end OAI
