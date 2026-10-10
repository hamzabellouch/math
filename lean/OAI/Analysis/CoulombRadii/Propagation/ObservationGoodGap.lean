import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationNegativeMean

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace Coulomb

lemma tf_reaction_response_good_gap {v θ A M e e₀ δ Qlo Qhi L U : ℝ}
    (hθ : 0≤θ) (hθ1 : θ≤1) (hM : 0≤M) (hMass : |M-1|≤δ)
    (hL : 0≤L) (hU : 0≤U) (he : e≤e₀)
    (hlo : Qlo≤tfScalarDensity (v+θ*(A+max (-v) 0))*M+e)
    (hhi : tfScalarDensity (v-θ*(A+max (-v) 0))*M-e≤Qhi)
    : (tfScalarDensity (L+θ*A)*(1+δ)+e₀<Qlo → L<v) ∧
      (Qhi<tfScalarDensity (U-θ*A)*(1-δ)-e₀ → v<U) := by
  have hm := abs_le.mp hMass
  constructor
  · intro hlmargin
    by_contra hnot
    have hvL : v≤L := le_of_not_gt hnot
    have hv := shifted_negative_feedback_mono (A:=A) hθ hθ1 hvL
    dsimp only at hv
    rw [max_eq_right (by linarith : -L≤0),add_zero] at hv
    have H1 := mul_le_mul_of_nonneg_right (tfScalarDensity_mono hv) hM
    have H2 := mul_le_mul_of_nonneg_left (show M≤1+δ by linarith) (tfScalarDensity_nonneg (L+θ*A))
    linarith
  · intro humargin
    by_contra hnot
    have hUv : U≤v := le_of_not_gt hnot
    have hv : 0≤v := hU.trans hUv
    rw [max_eq_right (by linarith : -v≤0),add_zero] at hhi
    have H1 := mul_le_mul_of_nonneg_right (tfScalarDensity_mono (show U-θ*A≤v-θ*A by linarith)) hM
    have H2 := mul_le_mul_of_nonneg_left (show 1-δ≤M by linarith) (tfScalarDensity_nonneg (U-θ*A))
    linarith
end Coulomb
namespace NeutralAtom

theorem arrayEvent_fresh_good_gap (g : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z,g z^2)=1) :
    ∃ C D E F K : ℝ, 0<C ∧ 0<D ∧ 0<E ∧ 0<F ∧ 0<K ∧
    ∀ {c r₀ s : ℝ}, 0<c → 0<r₀ → 0<s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ {H : Type*} [Fintype H] {n J : ℕ}
    (ℓ : H → ℝ), (∀ h, 0<ℓ h) → ∀ (h : H)
    {B : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet B →
    ∀ (ψ : Wavefunction n) (u : Coulomb.H1Vector n),
    (∀ f : Coulomb.Configuration n → ℝ, Coulomb.potentialForm f u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ B))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*f (flattenConfiguration n x))) →
    ∀ (S : Coulomb.Nuclei J) (T : Coulomb.RecordedEnsemble n), T.Conserves u →
    ∀ {a b t M Qlo Qhi q L U : ℝ} (ha : 0<a) (hb : 0<b), 18*b≤a →
    ∀ (ht : t∈Set.Icc (5*a) (6*a)) (y : Position) (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 2*packetWidth c r₀ s y≤a →
    (∀ z∈B, Qlo≤∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y) →
    (∀ z∈B, (∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y)≤Qhi) →
    (∀ z∈B, rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) →
    0≤L → 0≤U → C*(2*packetWidth c r₀ s y/a)≤1 →
    let w := packetWidth c r₀ s y
    let θ := C*(2*w/a)
    let δ := E*(c*(1+packetExponent)*s^packetExponent)
    let e := Real.sqrt ((D/w^5)*q)+(F/w^4*(2*b)+K/w^4*(Real.sqrt 3*ℓ h))*M
    ∀ p spin, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice spin x)≠0 →
      Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn spin x≤q →
      (Coulomb.tfScalarDensity (L+θ*(a^4)⁻¹)*(1+δ)+e<Qlo →
        L<Coulomb.patchTFScreenedField S ((T.vector p).coreSlice spin x).normalized ha hb ht.2 y hn y) ∧
      (Qhi<Coulomb.tfScalarDensity (U-θ*(a^4)⁻¹)*(1-δ)-e →
        Coulomb.patchTFScreenedField S ((T.vector p).coreSlice spin x).normalized ha hb ht.2 y hn y<U) := by
  obtain ⟨C,D,E,F,K,hC,hD,hE,hF,hK,Hresponse⟩ := arrayEvent_fresh_patch_response g hg hm
  refine ⟨C,D,E,F,K,hC,hD,hE,hF,hK,?_⟩
  intro c r₀ s hc hr hs hscale H inst n J ℓ hℓ h B hB ψ u hlaw S T hT a b t M Qlo Qhi q L U ha hb hsmall ht y hn hcs hw hlo hhi hcount hL hU hθ
  dsimp only
  intro p spin
  have HR := Hresponse hc hr hs hscale ℓ hℓ h hB ψ u hlaw S T hT ha hb hsmall ht y hn hcs hw hlo hhi hcount p spin
  filter_upwards [HR] with x hx
  intro hmass hgap
  obtain ⟨hl,hu,hmass'⟩ := hx hmass
  have hpw := packetWidth_pos hc hr hs y
  have he : Real.sqrt ((D/(packetWidth c r₀ s y)^5)*
      Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn spin x)≤
      Real.sqrt ((D/(packetWidth c r₀ s y)^5)*q) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hgap (div_nonneg hD.le (pow_nonneg hpw.le _)))
  exact Coulomb.tf_reaction_response_good_gap (by positivity) hθ
    (integral_nonneg (fun z => packetKernel_nonneg g hc hr hs z y)) hmass' hL hU
    (add_le_add he le_rfl) hu hl
end NeutralAtom
end

end

end OAI
