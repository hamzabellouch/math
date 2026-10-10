import OAI.InformationTheory.QuantumCircuit.ProductDistribution

namespace OAI

/-! Probability bounds for retained reflection outcomes. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

lemma heavy_low_outcome (hspec : PublishedProductSpectralResolution)
    {N : ℕ} (hN : 1 ≤ N) (M : Count N) (ψ : State N) (hψ : ‖ψ‖ = 1)
    {r : ℝ} (hr : 0 < r) (hmean : meanCount M ψ ≤ r / 2) :
    ∃ F : Finset (Fin N), F ⊆ M.support ∧ (F.card : ℝ) < r ∧
      1 / (2 * ((N + 1 : ℝ)^(⌈r⌉₊ + 1))) ≤ outcomeMass M ψ F := by
  classical
  let s := M.support.powerset.filter (fun F => (F.card : ℝ) < r)
  let t := M.support.powerset.filter (fun F => r ≤ (F.card : ℝ))
  let mass := outcomeMass M ψ
  have hhigh : r * (∑ F ∈ t, mass F) ≤ meanCount M ψ := by
    dsimp [t, meanCount]
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro F _
    split_ifs with hF
    · exact mul_le_mul_of_nonneg_right hF (outcomeMass_nonneg M ψ F)
    · simpa using mul_nonneg (Nat.cast_nonneg F.card) (outcomeMass_nonneg M ψ F)
  have htotal : (∑ F ∈ s, mass F) + (∑ F ∈ t, mass F) = 1 := by
    dsimp [s, t]
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    calc
      _ = ∑ F ∈ M.support.powerset, mass F := by
        apply Finset.sum_congr rfl
        intro F _
        by_cases hF : r ≤ (F.card : ℝ) <;> simp [hF, not_lt.mpr, lt_of_not_ge]
      _ = 1 := by rw [outcomeMass_total hspec M ψ, hψ]; norm_num
  have hlower : (1 : ℝ)/2 ≤ ∑ F ∈ s, mass F := by nlinarith
  have hs : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hlower
    norm_num at hlower
  obtain ⟨F, hF, hmax⟩ := s.exists_max_image mass hs
  have hsum : ∑ G ∈ s, mass G ≤ (s.card : ℝ) * mass F := by
    calc
      _ ≤ ∑ _G ∈ s, mass F := Finset.sum_le_sum (fun G hG => hmax G hG)
      _ = _ := by simp
  have hcard : (s.card : ℝ) ≤ (N + 1 : ℝ)^(⌈r⌉₊+1) := by
    exact_mod_cast low_patterns_card M.support (r := r) hN
  have hmF := outcomeMass_nonneg M ψ F
  have hbound : (1 : ℝ)/2 ≤ (N + 1 : ℝ)^(⌈r⌉₊+1) * mass F :=
    hlower.trans (hsum.trans (mul_le_mul_of_nonneg_right hcard hmF))
  refine ⟨F, Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1,
    (Finset.mem_filter.mp hF).2, ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 2 * (N + 1 : ℝ)^(⌈r⌉₊+1))).mpr
  nlinarith

end QAC

end

end OAI
