import OAI.Geometry.SurfaceImmersion.Geometry.DirectionalJetBounds

namespace OAI

/-! Weighted bounds for a smooth low-jet coefficient times a finite product
of higher-jet components, the monomials of paper 094-01, equation (polynomial-jet-monomial). -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {A J E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup J] [NormedSpace ℝ J] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compact control of the low jets, together with finite weighted control
of the second jets, gives a fixed scale loss for each higher-jet monomial. -/
theorem compact_higher_jet_monomial {ι : Type*} {U : Set A} {V K : Set J}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {c : J → E} (hc : ContDiffOn ℝ ∞ c V) (a : Finset ι) (vs : ι → List A) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (Q : A → J) (f : ι → A → ℝ) (s B : ℝ) (C : ι → ℝ),
      0 < s → 1 ≤ B → (∀ i ∈ a, 0 ≤ C i) →
      (∀ i ∈ a, ∀ v ∈ vs i, ‖v‖ ≤ 1) →
      ContDiffOn ℝ ∞ Q U → Set.MapsTo Q U K → WeightedBound U s m B Q →
      (∀ i ∈ a, ContDiffOn ℝ ∞ (f i) U) →
      (∀ i ∈ a, WeightedBound U s (m + (vs i).length) (C i) (f i)) →
      WeightedBound U s m
        ((2 ^ m * ((2 ^ m) ^ a.card * ∏ i ∈ a, C i) *
          ((m.factorial : ℝ) * D * B ^ m)) / s ^ (∑ i ∈ a, (vs i).length))
        (fun x => (∏ i ∈ a, iteratedDirectional (vs i) (f i) x) • c (Q x)) := by
  obtain ⟨D, hD, hd⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn hV.uniqueDiffOn hK hKV hc m
  refine ⟨D, hD, ?_⟩
  intro Q f s B C hs hB hC hv hQ hQK hbQ hf hbf
  have hp := weighted_higher_jet_monomial hU hs a C vs f m hC hv hf hbf
  have hcs := hc.comp hQ (fun x hx => hKV (hQK hx))
  have hcb := hd Q s B hs hB hQ hQK hbQ
  have hps : ContDiffOn ℝ ∞ (fun x => ∏ i ∈ a, iteratedDirectional (vs i) (f i) x) U :=
    contDiffOn_prod (fun i hi => contDiffOn_iteratedDirectional hU (hf i hi) (vs i))
  have hCn : 0 ≤ (2 ^ m) ^ a.card * ∏ i ∈ a, C i :=
    mul_nonneg (by positivity) (Finset.prod_nonneg hC)
  have hDn : 0 ≤ (m.factorial : ℝ) * D * B ^ m := by positivity
  have h := hp.smul_real hU.uniqueDiffOn hs.le
    (div_nonneg hCn (pow_nonneg hs.le _)) hDn hps hcs hcb
  convert h using 1 <;> (first | rfl | ring)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
