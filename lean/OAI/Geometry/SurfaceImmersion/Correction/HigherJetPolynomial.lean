import OAI.Geometry.SurfaceImmersion.Geometry.HigherJetMonomial

namespace OAI

/-! Finite sums of higher-jet monomials retain one scale-loss exponent
for every output derivative order, as required in the small-increment step. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {A J E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup J] [NormedSpace ℝ J] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scale loss in a finite higher-jet polynomial is bounded by the
largest sum of its additional derivative orders. -/
theorem compact_higher_jet_polynomial {ι τ : Type*} {U : Set A} {V K : Set J}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (c : τ → J → E) (hc : ∀ j, ContDiffOn ℝ ∞ (c j) V)
    (b : Finset τ) (a : τ → Finset ι) (vs : τ → ι → List A) (P m : ℕ)
    (hP : ∀ j ∈ b, (∑ i ∈ a j, (vs j i).length) ≤ P) :
    ∃ D : τ → ℝ, (∀ j, 1 ≤ D j) ∧
      ∀ (Q : A → J) (f : τ → ι → A → ℝ) (s B : ℝ) (C : τ → ι → ℝ),
      0 < s → s ≤ 1 → 1 ≤ B → (∀ j ∈ b, ∀ i ∈ a j, 0 ≤ C j i) →
      (∀ j ∈ b, ∀ i ∈ a j, ∀ v ∈ vs j i, ‖v‖ ≤ 1) →
      ContDiffOn ℝ ∞ Q U → Set.MapsTo Q U K → WeightedBound U s m B Q →
      (∀ j ∈ b, ∀ i ∈ a j, ContDiffOn ℝ ∞ (f j i) U) →
      (∀ j ∈ b, ∀ i ∈ a j,
        WeightedBound U s (m + (vs j i).length) (C j i) (f j i)) →
      WeightedBound U s m
        ((∑ j ∈ b, 2 ^ m * ((2 ^ m) ^ (a j).card * ∏ i ∈ a j, C j i) *
          ((m.factorial : ℝ) * D j * B ^ m)) / s ^ P)
        (fun x => ∑ j ∈ b, (∏ i ∈ a j, iteratedDirectional (vs j i) (f j i) x) • c j (Q x)) := by
  choose D hD hd using fun j =>
    compact_higher_jet_monomial hU hV hK hKV (hc j) (a j) (vs j) m
  refine ⟨D, hD, ?_⟩
  intro Q f s B C hs hs1 hB hC hv hQ hQK hbQ hf hbf
  apply WeightedBound.finset_sum_losses hU.uniqueDiffOn hs hs1 b
    (fun j => 2 ^ m * ((2 ^ m) ^ (a j).card * ∏ i ∈ a j, C j i) *
      ((m.factorial : ℝ) * D j * B ^ m))
    (fun j => ∑ i ∈ a j, (vs j i).length)
  · intro j hj
    have hprod : 0 ≤ ∏ i ∈ a j, C j i := Finset.prod_nonneg (hC j hj)
    have hDj : 0 ≤ D j := zero_le_one.trans (hD j)
    positivity
  · exact hP
  · intro j hj
    exact (contDiffOn_prod (fun i hi => contDiffOn_iteratedDirectional hU (hf j hj i hi)
      (vs j i))).smul (hc j |>.comp hQ (fun x hx => hKV (hQK hx)))
  · intro j hj
    exact hd j Q (f j) s B (C j) hs hB (hC j hj) (hv j hj) hQ hQK hbQ (hf j hj) (hbf j hj)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
