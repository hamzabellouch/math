import OAI.MeasureTheory.Falconer.Recursion.ActualRecursiveProfile

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem source_parameter_recursion_hierarchy {delta lam sig kap : ℝ}
    (hdelta : delta < 1) (hlam : 0 < lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hblock : 10^6*kap < (delta/10))
    (hgap : sig < kap/1000)
    (hloss : 10^7*(lam+sig)/kap < (delta/10)/100) :
    0 ≤ lam ∧ 0 < kap ∧ kap ≤ 1 ∧ 0 < sig ∧ sig < kap/1000 ∧ 4000*(lam+sig) < 1 := by
  have hkap1 : kap ≤ 1 := by linarith
  have he := (div_lt_iff₀ hkap).mp hloss
  have hd : (delta/10)/100 < 1 := by linarith
  have hp := mul_lt_mul_of_pos_right hd hkap
  refine ⟨hlam.le,hkap,hkap1,hsig,hgap,?_⟩
  nlinarith

theorem source_profile_equation25 {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1) (heta : 0 < eta) (K₀ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ d : AngularStateData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
      d.a₀ = d.a → d.t₀ = d.N → d.v = d.N → d.i = 0 →
      d.a+100*d.q < d.N → d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ e ∈ d.retainedList d.a, k l e ≤ K₀) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      d.energy k h Ψ ≠ ⊤ ∧ (d.energy k h Ψ).toReal ≤
        ((2:ℝ)^d.N)^(2*d.profile d.a-potential d.profile d.a d.N (10*d.q)
          +500*kap+10^6*(lam+sig)/kap+eta) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_actual_recursive_profile hlam hsig hkap hkap1 hgap hloss heta K₀
    hΨ hpos hs hone
  refine ⟨N₀,hN₀,?_⟩
  intro d hdlam hdsig hdq hdJ hN hQ hcarry ha₀ ht₀ hv hi hw hX hY B δ hprof k hk h hh hhb
  let e : RecursiveEnvironment := ⟨d.Q,d.ρ,d.mass,d.N,d.q,d.J,d.lam,d.sig⟩
  have hvalid : d.branchState.Valid e.N e.sig := by
    change d.a₀ ≤ d.a ∧ d.a ≤ d.v ∧ d.v ≤ d.t₀ ∧ d.t₀ ≤ d.N ∧ (d.t₀:ℝ) ≤ d.v+d.sig*d.N
    rw [ha₀,ht₀,hv,hdsig]
    exact ⟨le_rfl,by omega,le_rfl,le_rfl,le_add_of_nonneg_right (mul_nonneg hsig.le (Nat.cast_nonneg _))⟩
  have hwide : d.branchState.start+10*e.q ≤ d.branchState.finish := by
    change d.a+10*d.q ≤ d.v
    rw [hv]
    omega
  have hmem : e.energies K₀ Ψ d.branchState (d.energy k h Ψ).toReal :=
    ⟨d.X,d.Y,hX,hY,k,hk,h,hh,hhb,rfl⟩
  have hb := h₀ e hdlam hdsig hdq hdJ hN hQ hcarry B δ hprof d.branchState hvalid hi hwide _ hmem
  let := hprof.probability
  refine ⟨d.cellEnergy_finite (by rw [hQ]; norm_num) _ k K₀ hk h hh hhb d.a hΨ hpos hs _,?_⟩
  change (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^(2*d.profile d.a-
    potential d.profile d.a d.v (10*d.q)+500*kap+10^6*(lam+sig)/kap+eta) at hb
  simpa only [hv] using hb

end PlanarFalconer

end OAI
