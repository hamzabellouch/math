import OAI.MeasureTheory.Falconer.Graphs.ActualDirectGraph

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem source_angular_direct {lam sig kap eps : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (T : ℝ) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : AngularStateData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 →
      d.a₀ ≤ d.a → d.a ≤ d.v → d.v ≤ d.t₀ → d.t₀ ≤ d.N →
      (d.t₀:ℝ) ≤ (d.v:ℝ)+sig*d.N → d.a+100*d.q < d.v → d.i+1 ≤ d.J →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig ≤ d.a →
      ∃ e : PolicyDescriptor,
        DirectPolicyWitness d.profile d.N d.q d.a₀ d.t₀ d.a d.v d.sig e ∧
        let p := descriptorAnchor e
        d.energy k h Ψ ≠ ⊤ ∧ (∀ row, d.childEnergy k h p Ψ row ≠ ⊤) ∧
        (∀ l, ∑ b ∈ d.retainedList p, k l b ≤ K) ∧
        (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
          (-2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(lam+sig)+eps) *
            d.childMaximum k h p Ψ + ((2:ℝ)^d.N)^(-T) := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,h₂⟩ := AngularStateData.uniform_direct_graph hlam hsig heps T K
    (sourceSmoothingLevels sig kap) (sourceSmoothingLevels_pos hsig hkap) hΨ hpos hs
  refine ⟨max N₁ N₂,?_⟩
  intro d hdLam hdSig hdq hdJ hN hQ ha₀ hav hvt htN ht hw hi hX hY B δ hprof k hk h hh hhb hdir
  have hNpos : 0 < d.N := hN₁.trans_le ((le_max_left _ _).trans hN)
  have hq : 0 < d.q := by rw [hdq]; exact sourcePolicyBlock_pos hNpos hkap
  have hslack := h₁ d.N ((le_max_left _ _).trans hN)
  rw [← hdq,← hdSig] at hslack
  have hsig' : 0 < d.sig := hdSig ▸ hsig
  have ht' : (d.t₀:ℝ) ≤ (d.v:ℝ)+d.sig*d.N := by simpa only [hdSig] using ht
  obtain ⟨e,he⟩ := actual_direct_policy_witness d.profile hsig'.le hq hslack.1
    hslack.2.2 hslack.2.1 ht' hw hdir
  refine ⟨e,he,?_⟩
  exact h₂ d hdLam hdSig hdJ ((le_max_right _ _).trans hN) hQ hq (hvt.trans htN)
    (by omega) hX hY B δ hprof k hk h hh hhb e he

end PlanarFalconer

end OAI
