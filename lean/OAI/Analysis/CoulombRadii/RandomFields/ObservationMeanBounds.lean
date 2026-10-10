import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.PatchFieldMeans
import OAI.Analysis.CoulombRadii.Propagation.ObservationGoodGap

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem arrayEvent_fresh_field_means (g : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hm : (∫ z,g z^2)=1) :
    ∃ C D E F K N B₀ : ℝ, 0<C ∧ 0<D ∧ 0<E ∧ 0<F ∧ 0<K ∧ 0<N ∧ 0<B₀ ∧
    ∀ {c r₀ s : ℝ}, 0<c → 0<r₀ → 0<s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ {H : Type*} [Fintype H] {n J : ℕ}
    (ℓ : H → ℝ), (∀ h, 0<ℓ h) → ∀ (h : H)
    {B : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet B →
    ∀ (ψ : Wavefunction n) (u : Coulomb.H1Vector n),
    (∀ f : Coulomb.Configuration n → ℝ, Coulomb.potentialForm f u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ B))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*f (flattenConfiguration n x))) →
    ∀ (S : Coulomb.Nuclei J) (T : Coulomb.RecordedEnsemble n), T.Conserves u → T.totalMass=1 →
    ∀ {a b t M Qlo Qhi q L U : ℝ} (ha : 0<a) (hb : 0<b), 18*b≤a →
    ∀ (ht : t∈Set.Icc (5*a) (6*a)) (y : Position) (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 2*packetWidth c r₀ s y≤a →
    (∀ z∈B, Qlo≤∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y) →
    (∀ z∈B, (∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y)≤Qhi) →
    (∀ z∈B, rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) →
    0≤L → 0≤U → 0<q → C*(2*packetWidth c r₀ s y/a)≤1 →
    let w := packetWidth c r₀ s y
    let θ := C*(2*w/a)
    let δ := E*(c*(1+packetExponent)*s^packetExponent)
    let e := Real.sqrt ((D/w^5)*q)+(F/w^4*(2*b)+K/w^4*(Real.sqrt 3*ℓ h))*M
    let G := ∑ p,Coulomb.sliceExpectation (T.vector p) (Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn)
    let V := ∑ p,Coulomb.sliceExpectation (T.vector p) (fun spin x =>
      Coulomb.patchTFScreenedField S ((T.vector p).coreSlice spin x).normalized ha hb ht.2 y hn y)
    (∀ {P : ℝ}, 0<P → N*(2*w/a)≤1/2 →
      P≤Qlo-(B₀/w^4)*(Real.sqrt 3*ℓ h+2*b)*M →
      Coulomb.tfScalarDensity (L+θ*(a^4)⁻¹)*(1+δ)+e<Qlo →
      L-(L/q+2*(B₀/w^3)/P)*G-2*(N*(2*w/a))*(a^4)⁻¹≤V) ∧
    (Qhi<Coulomb.tfScalarDensity (U-θ*(a^4)⁻¹)*(1-δ)-e →
      V≤U+((Coulomb.tfInteriorConstant Coulomb.thomasFermiKineticConstant/a^4)/q)*G) := by
  obtain ⟨C,D,E,F,K,hC,hD,hE,hF,hK,Hgood⟩ := arrayEvent_fresh_good_gap g hg hm
  obtain ⟨N,hN,Hneg⟩ := exists_arrayEvent_fresh_negative_mean
  obtain ⟨B₀,hB₀,Hkernel⟩ := master_kernel_estimates g hg hm
  refine ⟨C,D,E,F,K,N,B₀,hC,hD,hE,hF,hK,hN,hB₀,?_⟩
  intro c r₀ s hc hr hs hscale H inst n J ℓ hℓ h B hB ψ u hlaw S T hT hTM a b t M Qlo Qhi q L U ha hb hsmall ht y hn hcs hw hlo hhi hcount hL hU hq hθ
  dsimp only
  have HG := Hgood (q:=q) hc hr hs hscale ℓ hℓ h hB ψ u hlaw S T hT ha hb hsmall ht y hn hcs hw hlo hhi hcount hL hU hθ
  constructor
  · intro P hP hNw hPm hmargin
    have hpw := packetWidth_pos hc hr hs y
    obtain ⟨hsp,hamp,hLip,_,_⟩ := Hkernel hc hr hs hscale y
    have hχm : Measurable (fun z => packetKernel g c r₀ s z y) :=
      ((continuous_packetKernel g.continuous hc hr hs).comp (continuous_id.prodMk continuous_const)).measurable
    obtain ⟨hi,hnmean⟩ := Hneg ℓ hℓ h hB ψ u hlaw S T hT ha hb hsmall ht y hn hcs
      (show 0≤2*packetWidth c r₀ s y by positivity) hw
      (show 2*packetWidth c r₀ s y+2*b<t-7*b by linarith [ht.1]) hNw
      (show 0≤B₀/(packetWidth c r₀ s y)^4 by positivity)
      (show 0≤B₀/(packetWidth c r₀ s y)^3 by positivity) hP hPm
      (fun z => packetKernel g c r₀ s z y) hχm
      (fun z => ⟨packetKernel_nonneg g hc hr hs z y,(le_abs_self _).trans (hamp z)⟩)
      (fun z hz => by simpa only [norm_sub_rev] using hsp z hz) hLip hlo hcount
    have Hmean := Coulomb.patch_field_mean_lower S T ha hb hsmall ht y hn hcs hq hL hi (fun p spin => ?_)
    · rw [hTM,mul_one] at Hmean hnmean
      linarith
    · filter_upwards [HG p spin] with x hx
      exact fun hm hg => ((hx hm hg).1 hmargin).le
  · intro hmargin
    have Hmean := Coulomb.patch_field_mean_upper S T ha hb hsmall ht y hn hcs hq hU (fun p spin => ?_)
    · simpa only [hTM,mul_one] using Hmean
    · filter_upwards [HG p spin] with x hx
      exact fun hm hg => ((hx hm hg).2 hmargin).le
end NeutralAtom
end

end

end OAI
