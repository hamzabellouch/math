import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationExpectedDeficit
import OAI.Analysis.CoulombRadii.Packets.PhysicalInteriorTransfer

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_finite_propagation {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z)
    {ψ : Wavefunction (N+1)} {g : Gradient (N+1)} (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    {g₀ : 𝓢(Position,ℝ)} (hgs : ∀ x,1<‖x‖ → g₀ x=0) (hm : (∫ x,g₀ x^2)=1)
    {c ε B C r₀ s M : ℝ} (hc : 0<c) (hε : 0<ε) (hB : 0<B) (hBC : B ≤ C)
    (hr : 0<r₀) (hr1 : r₀ ≤ 1) (hs : 0<s) (hM : 0 ≤ M)
    (hq : c*s^packetExponent ≤ 1/4) (hcubic : (Z:ℝ)*r₀^3=ε^3)
    (hnum : (N+1:ℝ) ≤ 3*(Z:ℝ)) (hBe : B ≤ ε^3/10) (heC : 32*ε^3 ≤ C)
    (hR : tfReaction (2*ε^3) ≤ (3/40:ℝ)*ε^3) (hbar : 4*Real.pi*kTF*Real.sqrt B ≤ 19/2)
    (k : PropagationConstants B C) :
    let := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let rs := fun j : Fin J => r₀*2^j.val
    let μ := fun j o => conditionalPacketDensity P Prod.fst (tailObservation rs j) g₀ c r₀ s (tailObservation rs j o)
    ∀ {G₀ : Set (Fin J → UnorderedArray (N+1))},MeasurableSet G₀ →
      P.real (tailObservation rs 0 ⁻¹' G₀ᶜ) ≤ 343*r₀^35 →
      (∀ a∈G₀,∀ x,r₀ ≤ ‖x‖ → ‖x‖ ≤ 2*r₀ →
        potentialOf (conditionalPacketDensity P Prod.fst (tailObservation rs 0) g₀ c r₀ s a) x ≤ (1/10:ℝ)*(Z:ℝ)/r₀) →
    ∀ (G : Fin J → Set (ObservationSample (N+1) J)),
      (∀ j,MeasurableSet (G j)) →
      (∀ j,∀ o∈G j,∀ x,rs j ≤ ‖x‖ → ‖x‖ ≤ 4*k.L*(rs j) →
        let F := (Z:ℝ)*coulombKernel x-potentialOf (μ j.val o) x
        F ≤ C/‖x‖^4 ∧ ∀ h∈Icc (B/2) C,
          (Coulomb.tfScalarDensity h ≤ ‖x‖^6*μ j.val o x → h-k.ξ ≤ ‖x‖^4*F) ∧
          (‖x‖^6*μ j.val o x ≤ Coulomb.tfScalarDensity h → ‖x‖^4*F ≤ h+k.ξ)) →
      (∀ j,(∫ o in (G j)ᶜ,∫ x in {x : Position | rs j ≤ ‖x‖ ∧ ‖x‖<2*(rs j)},μ j.val o x ∂volume ∂P) ≤ M*(rs j)^9) →
    (∫ x,rawCount (Metric.ball (0:Position) ((r₀*2^J)/2)) x ∂rawLaw ψ) ≤
      (Z:ℝ)-(tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*(r₀*2^J)^3)+
        (1029*ε^3+M)*(r₀*2^J)^9 := by
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let rs := fun j : Fin J => r₀*2^j.val
  let μ := fun j o => conditionalPacketDensity P Prod.fst (tailObservation rs j) g₀ c r₀ s (tailObservation rs j o)
  let H := fun j o x => -potentialOf (μ j o) x
  intro G₀ hG₀ hp₀ hlow G hG hgood hcost
  have hcompact : HasCompactSupport (g₀ : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun x hx => hgs x
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx))
  have hZr : 0<(Z:ℝ) := by exact_mod_cast (zero_lt_one.trans_le hZ)
  have q (j : ℕ) : NuclearRandomDatum (Z:ℝ) (μ j) (H j) :=
    posterior_nuclear_datum P Prod.fst (tailObservation rs j) (measurable_tailObservation rs j)
      g₀.continuous hcompact hm hc hr hs Z
  let bad₀ := fun o => tailObservation rs 0 o∉G₀
  have hb₀ : MeasurableSet {o | bad₀ o} := hG₀.compl.preimage (measurable_tailObservation rs 0)
  have gates := initial_scaled_gates (B:=B) hZr hr hcubic hR
  have init := (q 0).initial_hypotheses (bad:=bad₀) hB hZr.le hr
    (by positivity : 0 ≤ (Z:ℝ)/(80*r₀^3)) k.L_large.le
    (by rw [mul_assoc,hcubic]; linarith only [hBe]) hBC
    (by rw [mul_assoc,hcubic]; exact heC) gates.1 gates.2 hbar (by
      intro o ho x hx hx'
      have hh := hlow (tailObservation rs 0 o) (by simpa only [bad₀,not_not] using ho) x hx hx'
      change potentialOf (μ 0 o) x ≤ _ at hh
      change -(1/10:ℝ)*(Z:ℝ)/r₀ ≤ -potentialOf (μ 0 o) x
      simpa only [neg_mul,neg_div] using neg_le_neg hh)
  let d₀ := initialPropagationDatum (P:=P) hr hb₀ (q 0).H_measurable (q 0).mu_measurable
    (q 0).H_bounds (q 0).mu_bounds (Eventually.of_forall init)
  have hnε : (N+1:ℝ)*r₀^3 ≤ 3*ε^3 := by
    rw [←hcubic,←mul_assoc]
    exact mul_le_mul_of_nonneg_right hnum (pow_nonneg hr.le 3)
  have he₀ : (∫ o,(∫ x,d₀.error o x) ∂P) ≤ 1029*ε^3*r₀^9 :=
    (q 0).initial_error_bound hb₀ (fun o => (conditionalPacketDensity_mass P Prod.fst
      (tailObservation rs 0) g₀.continuous hm hc hr hs _).le) hr hr1 hε.le (by simpa using hnε) hp₀
  let bad := fun j o => ∃ hj : j<J,o∉G ⟨j,hj⟩
  obtain ⟨d,hd'⟩ := propagation_finite_iteration k hB hBC hr hbar J μ H
    (fun j => tailObservation rs j) bad d₀ (by positivity : 0 ≤ 1029*ε^3) hM he₀
    (fun j _ => measurable_tailObservation rs (j+1)) (fun j hj => by
      have he : {o | bad j o}=(G ⟨j,hj⟩)ᶜ := by ext o; simp [bad,hj]
      rw [he]; exact (hG _).compl)
    (fun j _ => q j) (by
      intro j hj o ho x hx hx'
      have hh := (hgood ⟨j,hj⟩ o (by simpa [bad,hj] using ho) x hx hx').1
      simpa only [H,sub_eq_add_neg] using hh) (by
      intro j hj o ho x hx hx' h hh
      have hgood' := (hgood ⟨j,hj⟩ o (by simpa [bad,hj] using ho) x hx hx').2 h hh
      simpa only [H,sub_eq_add_neg] using hgood')
    (fun j _ => posteriorPacketDensity_tower (rawLaw ψ) g₀.continuous hcompact hc hr hs rs (Nat.le_succ j)) (by
      intro j hj
      have he : {o | bad j o}=(G ⟨j,hj⟩)ᶜ := by ext o; simp [bad,hj]
      rw [he]; exact hcost ⟨j,hj⟩)
  have hrJ : 0<r₀*2^J := by positivity
  have hrle : r₀ ≤ r₀*2^J := le_mul_of_one_le_right hr.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have htrans := physical_interior_packet_transfer hd hn rs J g₀.continuous hm hgs hc hr hs hrle hq
  exact htrans.trans ((d.expected_charge_deficit (q J) hrJ hB.le (hB.le.trans hBC)).trans
    (add_le_add le_rfl hd'))
end NeutralAtom
end

end

end OAI
