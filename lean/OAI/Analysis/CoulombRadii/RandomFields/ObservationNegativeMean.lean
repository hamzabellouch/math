import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PatchPacketResponse
import OAI.Analysis.CoulombRadii.RandomFields.ObservationHigh
import OAI.Analysis.CoulombRadii.FieldAnalysis.PatchNegativeMean

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

theorem exists_arrayEvent_fresh_negative_mean :
    ∃ C : ℝ, 0<C ∧ ∀ {J n : ℕ} {H : Type*} [Fintype H]
    (ℓ : H → ℝ), (∀ h, 0<ℓ h) → ∀ (h : H)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet E →
    ∀ (ψ : Wavefunction n) (u : Coulomb.H1Vector n),
    (∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x))) →
    ∀ (S : Coulomb.Nuclei J) (T : Coulomb.RecordedEnsemble n), T.Conserves u →
    ∀ {a b t r L M Q K P : ℝ} (ha : 0<a) (hb : 0<b), 18*b≤a →
    ∀ (ht : t∈Set.Icc (5*a) (6*a)) (y : Position) (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 0≤r → r≤a → r+2*b<t-7*b →
    C*(r/a)≤1/2 → 0≤L → 0≤K → 0<P → P≤Q-L*(Real.sqrt 3*ℓ h+2*b)*M →
    ∀ (χ : Position → ℝ), Measurable χ → (∀ z, 0≤χ z ∧ χ z≤K) →
    (∀ v, χ v≠0 → ‖v-y‖≤r) → (∀ v w, |χ v-χ w|≤L*‖v-w‖) →
    (∀ z∈E, Q≤∑ i, χ (observationArrayPositions h z i)) →
    (∀ z∈E, rawCount (Metric.closedBall y (r+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) →
    (∀ p s, Integrable (fun x => Coulomb.mass ((T.vector p).coreSlice s x)*
      max (-Coulomb.patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0)) ∧
    (∑ p, Coulomb.sliceExpectation (T.vector p) (fun s x =>
      max (-Coulomb.patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) 0))≤
      (2*K/P)*(∑ p, Coulomb.sliceExpectation (T.vector p)
        (Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn))+
      (2*(C*(r/a))*(a^4)⁻¹)*T.totalMass := by
  obtain ⟨C,hC,Hbound⟩ := Coulomb.exists_patch_negative_mean_bound
  refine ⟨C,hC,?_⟩
  intro J n H inst ℓ hℓ h E hE ψ u hbayes S T hT a b t r L M Q K P ha hb hsmall ht y hn hcs hr hra hret hθ hL hK hP hmargin χ hχm hχ hs hLip hhigh hcount
  have Hfine := arrayEvent_fresh_fine_lower ℓ hℓ h hE ψ u hbayes T hT χ hχm y hb hL hret hcs
    (fun z => by rw [abs_of_nonneg (hχ z).1]; exact (hχ z).2) hs hLip hhigh hcount
  apply Hbound S T ha hb hsmall ht y hn hcs hr hra hθ χ K P hK hP hχm hχ hs
  intro p s
  filter_upwards [Hfine p s] with x hx
  exact fun hm => hmargin.trans (hx hm)

theorem arrayEvent_fresh_statistic_upper {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)} (hE : MeasurableSet E)
    (ψ : Wavefunction n) (u : Coulomb.H1Vector n)
    (hbayes : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x)))
    (T : Coulomb.RecordedEnsemble n) (hT : T.Conserves u)
    (χ : Position → ℝ) (hχm : Measurable χ) {A : Set Position}
    (hχ : ∀ z∈A, χ z=0) (hcs : T.CoreSupported A)
    (y : Position) {r L M Q : ℝ} (hL : 0≤L)
    (hs : ∀ v, χ v≠0 → ‖v-y‖≤r) (hLip : ∀ v w, |χ v-χ w|≤L*‖v-w‖)
    (hlow : ∀ z∈E, (∑ i, χ (observationArrayPositions h z i))≤Q)
    (hcount : ∀ z∈E, rawCount (Metric.closedBall y (r+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) :
    ∀ p s, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice s x)≠0 →
      Coulomb.arrayStatistic χ x≤Q+L*(Real.sqrt 3*ℓ h)*M := by
  have Hlow := arrayEvent_fresh_statistic_lower ℓ hℓ h hE ψ u hbayes T hT
    (fun z => -χ z) hχm.neg
    (fun z hz => by rw [hχ z hz,neg_zero]) hcs y hL
    (fun v hv => hs v (fun hh => hv (by rw [hh,neg_zero])))
    (fun v w => by simpa only [neg_sub_neg,abs_sub_comm] using hLip v w)
    (Q:=-Q) (fun z hz => by simpa only [Finset.sum_neg_distrib,neg_le_neg_iff] using hlow z hz) hcount
  intro p s
  filter_upwards [Hlow p s] with x hx
  intro hm
  have HH := hx hm
  simp only [Coulomb.arrayStatistic,Finset.sum_neg_distrib] at HH ⊢
  linarith

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace NeutralAtom

theorem arrayEvent_fresh_patch_response (g : 𝓢(Position,ℝ))
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
    ∀ {a b t M Qlo Qhi : ℝ} (ha : 0<a) (hb : 0<b), 18*b≤a →
    ∀ (ht : t∈Set.Icc (5*a) (6*a)) (y : Position) (hn : ∀ j, 20*a≤‖S.position j-y‖),
    T.CoreSupported {z | t≤‖z-y‖} → 2*packetWidth c r₀ s y≤a →
    (∀ z∈B, Qlo≤∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y) →
    (∀ z∈B, (∑ i, packetKernel g c r₀ s (observationArrayPositions h z i) y)≤Qhi) →
    (∀ z∈B, rawCount (Metric.closedBall y
        (2*packetWidth c r₀ s y+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) →
    ∀ p spin, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice spin x)≠0 →
    let w := packetWidth c r₀ s y
    let χ := fun z => packetKernel g c r₀ s z y
    let v := Coulomb.patchTFScreenedField S ((T.vector p).coreSlice spin x).normalized ha hb ht.2 y hn y
    let d := C*(2*w/a)*((a^4)⁻¹+max (-v) 0)
    let e := Real.sqrt ((D/w^5)*Coulomb.patchSliceTFGap S (T.vector p) ha hb ht.2 y hn spin x)+
      (F/w^4*(2*b)+K/w^4*(Real.sqrt 3*ℓ h))*M
    Coulomb.tfScalarDensity (v-d)*(∫ z,χ z)-e≤Qhi ∧
    Qlo≤Coulomb.tfScalarDensity (v+d)*(∫ z,χ z)+e ∧
    |(∫ z,χ z)-1|≤E*(c*(1+packetExponent)*s^packetExponent) := by
  obtain ⟨C,D,E,F,hC,hD,hE,hF,Hresponse⟩ := Coulomb.master_kernel_patch_array_response g hg hm
  obtain ⟨K,hK,Hkernel⟩ := master_kernel_estimates g hg hm
  refine ⟨C,D,E,F,K,hC,hD,hE,hF,hK,?_⟩
  intro c r₀ s hc hr hs hq H inst n J ℓ hℓ h B hB ψ u hbayes S T hT a b t M Qlo Qhi ha hb hsmall ht y hn hcs hw hhigh hlow hcount
  let w := packetWidth c r₀ s y
  let χ := fun z => packetKernel g c r₀ s z y
  have hpw : 0<w := packetWidth_pos hc hr hs y
  obtain ⟨hsp,_,hLip,_,_⟩ := Hkernel hc hr hs hq y
  have hχm : Measurable χ := (((continuous_packetKernel g.continuous hc hr hs).comp
    (continuous_id.prodMk (continuous_const (y := y)))).measurable)
  have hχs (z) (hz : χ z≠0) : ‖z-y‖≤2*w := by
    simpa only [norm_sub_rev] using hsp z hz
  have hχ (z) (hz : t≤‖z-y‖) : χ z=0 := by
    by_contra hh
    have HH := hχs z hh
    dsimp only [w] at HH
    linarith [ht.1]
  have hd : 0≤Real.sqrt 3*ℓ h := mul_nonneg (Real.sqrt_nonneg _) (hℓ h).le
  have hrawcount (z) (hz : z∈B) {R : ℝ} (hR : R≤2*w+2*b+2*(Real.sqrt 3*ℓ h)) :
      rawCount (Metric.closedBall y R) (observationArrayPositions h z)≤M := by
    have HH := Coulomb.localCount_mono (Metric.closedBall_subset_closedBall (x:=y) hR)
      (flattenConfiguration n (observationArrayPositions h z))
    simp only [Coulomb.localCount,position_flattenConfiguration] at HH
    exact HH.trans (hcount z hz)
  have Hhigh := arrayEvent_fresh_statistic_lower ℓ hℓ h hB ψ u hbayes T hT χ hχm hχ hcs y
    (show 0≤K/w^4 by positivity) hχs hLip hhigh (fun z hz => hrawcount z hz (by linarith))
  have Hlow := arrayEvent_fresh_statistic_upper ℓ hℓ h hB ψ u hbayes T hT χ hχm hχ hcs y
    (show 0≤K/w^4 by positivity) hχs hLip hlow (fun z hz => hrawcount z hz (by linarith))
  have Hcount := arrayEvent_fresh_count_upper ℓ hℓ h hB ψ u hbayes T hT hcs y
    (R:=2*w+2*b) (fun z hz => by change t≤‖z-y‖ at hz; dsimp only [w]; linarith [ht.1])
    (fun z hz => hrawcount z hz (by linarith))
  intro p spin
  have Hcore : ∀ᵐ x, Coulomb.SpatiallySupported ((T.vector p).coreSlice spin x).normalized
      {z | t≤‖z-y‖} := ((hcs p).coreSlice spin).mono (fun _ hx => hx.normalized)
  filter_upwards [Hhigh p spin,Hlow p spin,Hcount p spin,Hcore] with x hhi hlo hco hcore
  intro hmass
  have Hhi := hhi hmass
  have Hlo := hlo hmass
  have Hco := hco hmass
  have Hresponse := Hresponse hc hr hs hq S (T.vector p) ha hb hsmall ht y hn hw spin x hcore
  have HE := mul_le_mul_of_nonneg_left Hco (show 0≤F/w^4*(2*b) by positivity)
  dsimp only at Hresponse ⊢
  dsimp only [Coulomb.arrayStatistic,χ,w] at Hhi Hlo HE
  refine ⟨?_,?_,Hresponse.2.2⟩ <;> linarith [Hresponse.1,Hresponse.2.1]
end NeutralAtom

end

end OAI
