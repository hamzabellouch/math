import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelationsParts

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap

noncomputable def dualCorrelationZeroCorrection (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₂ : ℕ → ℕ → ℝ) : ℂ :=
  complementaryPair S a (fun q => dualCorrelationZeroTerm W M Δ K q X₂)

noncomputable def dualCorrelationLargeCorrection (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₂ : ℕ → ℕ → ℝ) : ℂ :=
  complementaryPair S a (fun q => dualCorrelationLargeTerm W M Δ K q X₂)

noncomputable def dualCorrelationFourierCorrection (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₁ X₂ L : ℕ → ℕ → ℝ) : ℂ :=
  complementaryPair S a (fun q => dualCorrelationFourierTerm W M Δ K q X₁ X₂ L)

theorem dualCorrelationLeadingPair_eq (W : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) (M : ℝ) (hM : 0 < M) (Δ K N : ℕ) (hΔ : Odd Δ)
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : S ⊆ oddSquarefreeUpTo N) :
    complementaryPair S a (fun q => dualCorrelationLeadingTerm W M Δ K q) =
      dualLeadingCorrelation M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ S a := by
  let I : ℂ := ∫ x : ℝ in Ioi 0, W (x^2)
  have heq : complementaryPair S a (fun q => dualCorrelationLeadingTerm W M Δ K q) =
      complementaryPair S a (fun q => (I/2) * ∑ b ∈ oddSquarefreeUpTo K,
        (Real.sqrt (M/b) : ℂ) * ((Nat.totient q : ℂ)/(q : ℂ)) *
          leadingDivisorCoefficient Δ q * (jacobiSym (b : ℤ) q : ℂ)) := by
    apply complementaryPair_congr
    intro n hn t ht hcop
    obtain ⟨hnp, hnb, hno, hns⟩ := mem_oddSquarefreeUpTo.mp (hS hn)
    obtain ⟨htp, htb, hto, hts⟩ := mem_oddSquarefreeUpTo.mp (hS ht)
    let : NeZero (n*t) := ⟨(Nat.mul_pos hnp htp).ne'⟩
    exact dualCorrelationLeadingTerm_eq W hc hs M hM Δ K (n*t) hΔ (hno.mul hto)
      (Nat.squarefree_mul_iff.mpr ⟨hcop,hns,hts⟩)
  rw [heq, complementaryPair_mul, complementaryPair_sum]
  unfold dualLeadingCorrelation
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  simp only [complementaryPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> ring

theorem dualCorrelationMain_eq_leading (W : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) (M : ℝ) (hM : 0 < M) (Δ K N : ℕ) (hΔ : Odd Δ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₁ X₂ L : ℕ → ℕ → ℝ) (hS : S ⊆ oddSquarefreeUpTo N) :
    dualCorrelationMain W M Δ K S a X₁ X₂ L =
      dualLeadingCorrelation M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ S a +
        dualCorrelationZeroCorrection W M Δ K S a X₂ +
        dualCorrelationLargeCorrection W M Δ K S a X₂ +
        dualCorrelationFourierCorrection W M Δ K S a X₁ X₂ L := by
  unfold dualCorrelationMain dualCorrelationZeroCorrection
    dualCorrelationLargeCorrection dualCorrelationFourierCorrection
  simp_rw [dualCorrelationMainTerm_parts]
  rw [complementaryPair_add, complementaryPair_add, complementaryPair_add,
    dualCorrelationLeadingPair_eq W hc hs M hM Δ K N hΔ S a hS]

end Ostmann.QuadraticSieve

end OAI
