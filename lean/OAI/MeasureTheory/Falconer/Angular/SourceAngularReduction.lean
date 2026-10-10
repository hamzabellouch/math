import OAI.MeasureTheory.Falconer.Angular.SourceAngularDirect
import OAI.MeasureTheory.Falconer.Angular.AngularStateNearFar

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem source_angular_reduction {lam sig kap eps : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (T : ℝ) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : AngularStateData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N →
      d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
      d.a₀ ≤ d.a → d.a ≤ d.v → d.v ≤ d.t₀ → d.t₀ ≤ d.N →
      (d.t₀:ℝ) ≤ (d.v:ℝ)+sig*d.N → d.a+100*d.q < d.v → d.i+1 ≤ d.J →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      d.energy k h Ψ ≠ ⊤ ∧ ∃ p : ℕ, d.a < p ∧ p < d.v ∧
        (∀ row, d.childEnergy k h p Ψ row ≠ ⊤) ∧
        (∀ l, ∑ b ∈ d.retainedList p, k l b ≤ K) ∧
        ((∃ e : PolicyDescriptor, p = descriptorAnchor e ∧
          DirectPolicyWitness d.profile d.N d.q d.a₀ d.t₀ d.a d.v d.sig e ∧
          (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
            (-2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(lam+sig)+eps) *
              d.childMaximum k h p Ψ + ((2:ℝ)^d.N)^(-T)) ∨
        (p = d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig ∧
          p+5 < d.v ∧
          (∀ b ∈ Finset.Icc (d.a+9) (p+5), d.a < b ∧ b < d.v ∧ d.farDistanceMaximum b ≠ ⊤) ∧
          (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
            (-2*(d.profile p-d.profile d.a)+12*lam+eps)*d.childMaximum k h p Ψ +
              d.farSum p + ((2:ℝ)^d.N)^(-T))) := by
  obtain ⟨N₁,h₁⟩ := source_angular_direct hlam hsig hkap hgap heps T K hΨ hpos hs
  obtain ⟨N₂,h₂⟩ := AngularStateData.uniform_state_near_far hlam hsig heps T K
    (sourceSmoothingLevels sig kap) (sourceSmoothingLevels_pos hsig hkap) hΨ hpos hs
  refine ⟨max N₁ N₂,?_⟩
  intro d hdLam hdSig hdq hdJ hN hQ hcarry ha₀ hav hvt htN ht hw hi hX hY B δ hprof k hk h hh hhb
  let p := d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig
  by_cases hp : d.a < p
  · have hq : 0 < d.q := by
      rw [hdq]
      exact sourcePolicyBlock_pos (by omega : 0 < d.N) hkap
    have hn := h₂ d hdLam hdSig hdJ ((le_max_right _ _).trans hN) hQ hcarry hq ha₀ hvt htN
      hX hY B δ hprof k hk h hh hhb hp
    exact ⟨hn.2.1,p,hp,by omega,hn.2.2.1,hn.2.2.2.1,
      Or.inr ⟨rfl,hn.1,hn.2.2.2.2.1,hn.2.2.2.2.2⟩⟩
  · obtain ⟨e,he,hg⟩ := h₁ d hdLam hdSig hdq hdJ ((le_max_left _ _).trans hN) hQ ha₀ hav hvt
      htN ht hw hi hX hY B δ hprof k hk h hh hhb (by omega)
    exact ⟨hg.1,descriptorAnchor e,he.anchor_gt,he.anchor_lt,hg.2.1,hg.2.2.1,
      Or.inl ⟨e,rfl,he,hg.2.2.2⟩⟩

end PlanarFalconer

end OAI
