import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationConstants
import OAI.Analysis.CoulombRadii.Propagation.PropagationPosteriorMass
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorRegularBounds

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure NuclearRandomDatum {Ω : Type*} [MeasurableSpace Ω] (Z : ℝ)
    (μ H : Ω → Position → ℝ) : Prop where
  mu_measurable : Measurable (Function.uncurry μ)
  H_measurable : Measurable (Function.uncurry H)
  mu_bounds : ∀ D : ℝ,∃ M : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤M
  H_bounds : ∀ D : ℝ,∃ M : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤M
  continuous_H : ∀ o,Continuous (H o)
  nonpositive_H : ∀ o x,H o x≤0
  nonnegative_mu : ∀ o x,0≤μ o x
  integrable_mu : ∀ o,Integrable (μ o)
  nuclear : ∀ o,WeakNuclearSubsolution (fun x => Z*coulombKernel x+H o x) Z univ
    (fun x => 4*Real.pi*μ o x)

lemma posterior_nuclear_datum {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → A) (ho : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r s : ℝ} (hc : 0<c) (hr : 0<r) (hs : 0<s) (Z : ℝ) :
    let μ := fun o => conditionalPacketDensity P raw obs g c r s (obs o)
    NuclearRandomDatum Z μ (fun o x => -potentialOf (μ o) x) := by
  let μ := fun o => conditionalPacketDensity P raw obs g c r s (obs o)
  refine ⟨(measurable_conditionalPacketDensity_joint P raw obs hg hgs hc hr hs).comp (ho.prodMap measurable_id),
    ((measurable_conditionalPacketPotential_joint P raw obs hg hgs hm hc hr hs).comp (ho.prodMap measurable_id)).neg,
    ?_,?_,fun o => (conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr hs (obs o)).neg,
    fun o x => neg_nonpos.mpr (potentialOf_nonneg (conditionalPacketDensity_nonneg P raw obs g hc hr hs (obs o)) x),
    fun o => conditionalPacketDensity_nonneg P raw obs g hc hr hs (obs o),
    fun o => mixturePacketDensity_integrable hg hm hc hr hs _,fun o => ?_⟩
  · intro D
    obtain ⟨C,hC⟩ := conditionalPacketDensity_uniform_bounds P raw obs hg hgs hc hr hs D
    exact ⟨C,fun o => hC (obs o)⟩
  · intro D
    obtain ⟨C,hC⟩ := conditionalPacketOffset_uniform_bounds P raw obs hg hgs hm hc hr hs D
    exact ⟨C,fun o => hC (obs o)⟩
  · exact conditionalPacketField_nuclear P raw obs hg hgs hm hc hr hs (obs o) Z

section Assembly
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B C r Z : ℝ}
variable {μ H : Ω → Position → ℝ} {bad : Ω → Prop}

lemma PropagationDatum.step_hypotheses (k : PropagationConstants B C)
    (d : PropagationDatum P B C r Z k.L μ) (q : NuclearRandomDatum Z μ H)
    (hB : 0<B) (hBC : B≤C) (hr : 0<r) (hbar : 4*Real.pi*kTF*Real.sqrt B≤19/2)
    (hcap : ∀ o,¬bad o → ∀ x,r≤‖x‖ → ‖x‖≤4*k.L*r → Z*coulombKernel x+H o x≤C/‖x‖^4)
    (hinv : ∀ o,¬bad o → ∀ x,r≤‖x‖ → ‖x‖≤4*k.L*r → ∀ h∈Icc (B/2) C,
      (Coulomb.tfScalarDensity h≤‖x‖^6*μ o x → h-k.ξ≤‖x‖^4*(Z*coulombKernel x+H o x)) ∧
      (‖x‖^6*μ o x≤Coulomb.tfScalarDensity h → ‖x‖^4*(Z*coulombKernel x+H o x)≤h+k.ξ)) :
    ∀ᵐ o ∂P,PropagationStepHypotheses (bad o) B C r (2*r) Z k.L k.l1 k.l2 k.e k.ξ (B/2) C
      (d.offset o) (H o) (μ o) (d.error o) := by
  filter_upwards [d.invariant] with o hi
  refine ⟨hB,hr,rfl,k.L_large,k.l2_pos.le,k.l2_le_l1,k.l1_le_gamma,hBC,k.upper_overlap,
    k.e_pos,k.xi_pos.le,k.xi_lt_l2,k.gain_gap,k.height_lower,le_rfl,
    hi.continuous_offset,q.continuous_H o,q.nonnegative_mu o,hi.nonnegative_error,
    q.mu_measurable.of_uncurry_left,d.error_measurable.of_uncurry_left,?_,?_,
    hi.weak,q.nuclear o,hbar,hi.caps,?_,?_⟩
  · intro D; obtain ⟨M,hM⟩ := q.mu_bounds D; exact ⟨M,hM o⟩
  · intro D; obtain ⟨M,hM⟩ := d.error_bounds D; exact ⟨M,hM o⟩
  · intro hb x hx hx'; apply hcap o hb x hx; nlinarith only [hx']
  · intro hb x hx hx' h hh
    exact (hinv o hb x hx (by nlinarith only [hx']) h hh).symm

lemma NuclearRandomDatum.initial_hypotheses (q : NuclearRandomDatum Z μ H)
    {a L : ℝ} (hB : 0<B) (hZ : 0≤Z) (hr : 0<r) (ha : 0≤a) (hL : 2≤L)
    (hBZ : B≤(1/10:ℝ)*Z*r^3) (hBC : B≤C) (hZC : 32*Z*r^3≤C)
    (hquad : 4*a*r^2≤(1/20:ℝ)*Z/r) (hreac : tfReaction (2*Z/r)≤6*a)
    (hbar : 4*Real.pi*kTF*Real.sqrt B≤19/2)
    (hlo : ∀ o,¬bad o → ∀ x,r≤‖x‖ → ‖x‖≤2*r → -(1/10:ℝ)*Z/r≤H o x) :
    ∀ o,InitialPropagationData (bad o) B C Z r a L (H o) (μ o) := by
  intro o
  refine ⟨hB,hZ,hr,ha,hL,hBZ,hBC,hZC,hquad,hreac,hbar,q.continuous_H o,
    q.nonpositive_H o,hlo o,q.mu_measurable.of_uncurry_left,q.nonnegative_mu o,?_,q.nuclear o⟩
  intro D
  obtain ⟨M,hM⟩ := q.mu_bounds D
  exact ⟨M,hM o⟩
end Assembly
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Iteration
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable {P : Measure Ω} [IsProbabilityMeasure P] {B C r Z : ℝ}

theorem propagation_finite_iteration (k : PropagationConstants B C)
    (hB : 0<B) (hBC : B≤C) (hr : 0<r) (hbar : 4*Real.pi*kTF*Real.sqrt B≤19/2)
    (J : ℕ) (μ H : ℕ → Ω → Position → ℝ) (obs : ℕ → Ω → A) (bad : ℕ → Ω → Prop)
    (d₀ : PropagationDatum P B C r Z k.L (μ 0))
    {M₀ M : ℝ} (hM₀ : 0≤M₀) (hM : 0≤M)
    (hinit : (∫ o,(∫ x,d₀.error o x) ∂P)≤M₀*r^9)
    (ho : ∀ j<J,Measurable (obs (j+1)))
    (hb : ∀ j<J,MeasurableSet {o | bad j o})
    (hq : ∀ j<J,NuclearRandomDatum Z (μ j) (H j))
    (hcap : ∀ j<J,∀ o,¬bad j o → ∀ x,r*2^j≤‖x‖ → ‖x‖≤4*k.L*(r*2^j) →
      Z*coulombKernel x+H j o x≤C/‖x‖^4)
    (hinv : ∀ j<J,∀ o,¬bad j o → ∀ x,r*2^j≤‖x‖ → ‖x‖≤4*k.L*(r*2^j) → ∀ h∈Icc (B/2) C,
      (Coulomb.tfScalarDensity h≤‖x‖^6*μ j o x → h-k.ξ≤‖x‖^4*(Z*coulombKernel x+H j o x)) ∧
      (‖x‖^6*μ j o x≤Coulomb.tfScalarDensity h → ‖x‖^4*(Z*coulombKernel x+H j o x)≤h+k.ξ))
    (htower : ∀ j<J,∀ᵐ o ∂P,posteriorAverage P (obs (j+1)) (μ j) (obs (j+1) o)=μ (j+1) o)
    (hcost : ∀ j<J,(∫ o in {o | bad j o},∫ x in {x : Position | r*2^j≤‖x‖ ∧ ‖x‖<2*(r*2^j)},
      μ j o x ∂volume ∂P)≤M*(r*2^j)^9) :
    ∃ d : PropagationDatum P B C (r*2^J) Z k.L (μ J),
      (∫ o,(∫ x,d.error o x) ∂P)≤(M₀+M)*(r*2^J)^9 := by
  have HI : ∀ j≤J,∃ d : PropagationDatum P B C (r*2^j) Z k.L (μ j),
      (∫ o,(∫ x,d.error o x) ∂P)≤(M₀+M)*(r*2^j)^9 := by
    intro j
    induction j with
    | zero =>
      intro hj
      have he : r*(2:ℝ)^(0:ℕ)=r := by simp
      rw [he]
      exact ⟨d₀,hinit.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM) (by positivity))⟩
    | succ j ih =>
      intro hj
      have hjJ : j<J := Nat.lt_of_succ_le hj
      obtain ⟨d,hd⟩ := ih (Nat.le_of_lt hjJ)
      have hrj : 0<r*2^j := by positivity
      have hs := d.step_hypotheses k (hq j hjJ) hB hBC hrj hbar (hcap j hjJ) (hinv j hjJ)
      let d' := d.posteriorStep (obs (j+1)) (ho j hjJ) (by positivity : 0<2*(r*2^j))
        (hb j hjJ) (hq j hjJ).H_measurable (hq j hjJ).mu_measurable
        (hq j hjJ).H_bounds (hq j hjJ).mu_bounds hs (htower j hjJ)
      have htotal := d.posteriorStep_total (obs (j+1)) (ho j hjJ) (by positivity : 0<2*(r*2^j))
        (hb j hjJ) (hq j hjJ).H_measurable (hq j hjJ).mu_measurable
        (hq j hjJ).H_bounds (hq j hjJ).mu_bounds hs (htower j hjJ)
      have he : r*2^(j+1)=2*(r*2^j) := by rw [pow_succ]; ring
      rw [he]
      refine ⟨d',?_⟩
      change (∫ o,(∫ x,d'.error o x) ∂P)=_ at htotal
      rw [htotal]
      calc
        _≤(M₀+M)*(r*2^j)^9+M*(r*2^j)^9 := add_le_add hd (hcost j hjJ)
        _≤(M₀+M)*(2*(r*2^j))^9 := by
          rw [mul_pow]
          nlinarith [pow_nonneg hrj.le 9]
  exact HI J le_rfl
end Iteration
end NeutralAtom
end

end

end OAI
