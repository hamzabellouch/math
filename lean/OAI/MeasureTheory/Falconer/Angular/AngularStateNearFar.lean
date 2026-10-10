import OAI.MeasureTheory.Falconer.Angular.AngularStateContributions

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace AngularStateData

theorem uniform_state_near_far {lam sig eps : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (heps : 0 < eps) (T : ℝ) (K J : ℕ) (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : AngularStateData,
      d.lam = lam → d.sig = sig → d.J = J → N₀ ≤ d.N →
      d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 → 0 < d.q →
      d.a₀ ≤ d.a → d.v ≤ d.t₀ → d.t₀ ≤ d.N →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      let p := d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig
      d.a < p →
      p+5 < d.v ∧ d.energy k h Ψ ≠ ⊤ ∧
      (∀ row, d.childEnergy k h p Ψ row ≠ ⊤) ∧
      (∀ l, ∑ b ∈ d.retainedList p, k l b ≤ K) ∧
      (∀ b ∈ Finset.Icc (d.a+9) (p+5), d.a < b ∧ b < d.v ∧ d.farDistanceMaximum b ≠ ⊤) ∧
      (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
        (-2*(d.profile p-d.profile d.a)+12*lam+eps)*d.childMaximum k h p Ψ +
          d.farSum p + ((2:ℝ)^d.N)^(-T) := by
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  obtain ⟨N₁,h₁⟩ := uniform_actual_far_source_equation24 (T := T) hΨ hpos hs hW
    (fun x => (le_abs_self _).trans (hWb x)) hsig K hJ hlam
  obtain ⟨N₂,h₂⟩ := uniform_state_near K heps
  obtain ⟨N₃,h₃⟩ := uniform_source_far_buffer hsig
  refine ⟨max N₁ (max N₂ N₃),?_⟩
  intro d hdLam hdSig hdJ hN hQ hcarry hq ha₀ hvt htN hX hY B δ hprof k hk h hh hhb p hp
  subst lam
  subst sig
  subst J
  let := hprof.probability
  let : ∀ _l : Fin 2, IsFiniteMeasure d.ρ := fun _ => inferInstance
  have hap : d.a ≤ p := hp.le
  have hpv : p ≤ d.v := Nat.sub_le _ _
  have hpN : p ≤ d.N := hpv.trans (hvt.trans htN)
  have heq : d.a+(p-d.a) = p := Nat.add_sub_of_le hap
  have heqR : (d.a:ℝ)+((p-d.a:ℕ):ℝ) = (p:ℝ) := by exact_mod_cast heq
  have hbuf := h₃ d.N (by omega) ((d.retainedList d.a).sup descriptorLength) d.v d.a hp
  have hp5 : p+5 < d.v := by
    have hh : d.a+(p-d.a)+5 < d.v := hbuf.2.1
    omega
  have hn := h₂ d (by omega) hQ hX hY B δ hprof k hk h hh hhb p hap hpN hΨ hpos hs
  have hcard (_l : Fin 2) : (d.retainedList d.a).card ≤ (d.N+1)^3+1 :=
    (remainingPolicyDescriptors_card d.profile hq).trans (Nat.le_succ _)
  have hfar := h₁ d.N (by omega) (fun _ : Fin 2 => d.Q) (fun _ => hQ) (fun _ => d.ρ)
    (fun _ => hcarry) d.mass d.q d.a₀ d.t₀ d.a d.v hq ha₀ hvt (hvt.trans htN)
    (fun _ => d.retainedList d.a) k (fun _ => Finset.Subset.refl _) hcard hk
    ((d.retainedList d.a).sup descriptorLength) (d.retained_length_le_N hq htN d.a)
    (fun _ _ hb => Finset.le_sup hb) hp B δ (fun _ => hprof) (fun _ => d.i) h hh hhb
    d.X d.Y hX hY
  have hf : ‖d.farContribution k h p Ψ‖ ≤ d.farSum p+((2:ℝ)^d.N)^(-T) := by
    dsimp only at hfar
    dsimp only [p] at heq heqR
    simp only [heq,heqR] at hfar
    exact hfar
  have htotal : (d.energy k h Ψ).toReal ≤ ‖d.nearContribution k h p Ψ‖+‖d.farContribution k h p Ψ‖ := by
    calc
      _ = ‖((d.energy k h Ψ).toReal : ℂ)‖ := by
        simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
      _ = ‖d.nearContribution k h p Ψ+d.farContribution k h p Ψ‖ := by rw [hn.2.2.1]
      _ ≤ _ := norm_add_le _ _
  refine ⟨hp5,hn.1,hn.2.1,fun l => d.child_budget hap (k l) (hk l),?_,?_⟩
  · intro b hb
    have hb' := Finset.mem_Icc.mp hb
    exact ⟨by omega,by omega,d.farDistanceMaximum_finite b⟩
  · exact htotal.trans (by linarith [hn.2.2.2,hf])

end AngularStateData

end PlanarFalconer

end OAI
