import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds

namespace OAI

section

/-! # The uniform source estimate for a dominated geometric cold family -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem geometric_family_source (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b L t R z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (ht : 0 < t) (htmax : t ≤ 1/32) (hz : 0 ≤ z)
    (A : ℝ) (N : ℕ) (x : Velocity) (hx : ∀ k, |x k| ≤ 1)
    {G : ℝ × JetPrototype.Phase → ℝ} {c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ}
    (hGm : Measurable G) (hcm : ∀ i, Measurable (c i))
    (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R) (hc : ∀ i u, 0 ≤ c i u ∧ c i u ≤ R)
    (hSum : ∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, c i u ≤ G u)
    (hzero : ∀ i, ¬i.annulus < N → c i = 0)
    (hhot : ∀ w, G (t,(JetPeriodicDatum.spatialMap x,w))-
      ∑' i, c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤ z)
    (hU : ∀ i w, VelocityWeight.H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,w))
    (he : JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A ≤ 1) :
    ∀ᵐ v : Velocity, remainderForcing q b L G c (t,(JetPeriodicDatum.spatialMap x,v))-
        L*(G (t,(JetPeriodicDatum.spatialMap x,v))-
          ∑' i, c i (t,(JetPeriodicDatum.spatialMap x,v))) ≤
      (2*JetMainGain.coefficient K α γ q/(JetGeometry.jetScale s₀ η N+t))*z+
        2*HotApplication.realBound q*z^2+
        (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
          ((JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A)/t) := by
  let e := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A
  have htail (w) : (∑' i, escaped s₀ η t N x
      (fun j => c j (t,(JetPeriodicDatum.spatialMap x,w))) i) ≤ e :=
    normalized_escaped_bound hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le hd₀ hd₀max ht htmax hsmall A q N
      (fun j => c j (t,(JetPeriodicDatum.spatialMap x,w))) x w hx
      (fun i => (hc i _).1)
      (summable_of_sum_le (fun i => (hc i _).1) (fun s => hSum s _)) (fun i _ => hU i w)
  have he0 : 0 ≤ e := mul_nonneg
    (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α (JetEscapedEnvelope.exponent A))
    (Real.rpow_nonneg ht.le A)
  exact uniform_hot_source hcarleman hs₀ hsmax hη hηmax hK hα hγ hd₀ hd₀max hq₁ hq₂ ht htmax hz he0 he
    N x (t,JetPeriodicDatum.spatialMap x) (GaussianLocal.measurable_state hGm)
    (fun i => GaussianLocal.measurable_state (hcm i))
    (fun u => hG (u.1.1,(u.1.2,u.2))) (fun i u => hc i (u.1.1,(u.1.2,u.2)))
    (fun s u => hSum s (u.1.1,(u.1.2,u.2)))
    (fun i hi w => congrFun (hzero i hi) (t,(JetPeriodicDatum.spatialMap x,w))) hhot htail hU b L

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform-in-time bounds for a periodic geometric cold family -/

noncomputable section

open Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem geometric_cold_sum_bound {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hTmax : T ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (N : ℕ)
    {c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ}
    (hcn : ∀ i u, 0 ≤ c i u) (hcs : ∀ u, Summable (fun i => c i u))
    (hzero : ∀ i, ¬i.annulus < N → c i = 0)
    (hU : ∀ t ∈ Ioc 0 T, ∀ i (x w : Velocity),
      VelocityWeight.H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,w))
    (hcperiodic : ∀ n i, pull (displacement n) (c i) = c (relabel n i)) :
    ∀ t ∈ Ioc 0 T, ∀ p : JetPrototype.Phase, (∑' i, c i (t,p)) ≤ coldNormBound s₀ η K α d₀ N := by
  intro t ht p
  obtain ⟨n,x,hx,he⟩ := exists_shift_in_cell p.1
  have hp : shift (displacement n) p = (JetPeriodicDatum.spatialMap x,p.2) := Prod.ext he rfl
  have hbound := cell_cold_sum_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    ht.1 (ht.2.trans hTmax) hsmall N x hx
    (fun i v => c i (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun i v => hcn i (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun v => hcs (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun i hi v => congrFun (hzero i hi) (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun i v => hU t ht i x v) p.2
  have hshift := family_sum_pull (displacement n) (relabel n) (hcperiodic n) (t,p)
  rw [hp] at hshift
  rw [← hshift]
  exact hbound

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Essential-norm source control for reconstructed geometric cold families -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem geometric_hot_norm_source (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hL : 0 ≤ L) (hTmax : T ≤ 1/32)
    (A : ℝ) (N : ℕ)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hzero : ∀ i, ¬i.annulus < N → c i = 0)
    (hU : ∀ t ∈ Ioc 0 T, ∀ i (x w : Velocity),
      VelocityWeight.H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,w))
    (hperiodic : ∀ n, pull (displacement n) F = F)
    (hcperiodic : ∀ n i, pull (displacement n) (c i) = c (relabel n i))
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p))))
    (he : ∀ t ∈ Ioc 0 T,
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A ≤ 1) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → remainderForcing q b L F c u ≤
      scalarMajorant s₀ η K α γ d₀ q A N u.1
        (PhaseEssSup.size (fun p => F (u.1,p)-∑' i, c i (u.1,p)))+
        L*PhaseEssSup.size (fun p => F (u.1,p)-∑' i, c i (u.1,p)) := by
  classical
  let G := HotCanonical.familyReplacement F c
  let z (t : ℝ) := PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p))
  let w (t : ℝ) := scalarMajorant s₀ η K α γ d₀ q A N t (z t)
  let k (u : ℝ × JetPrototype.Phase) := remainderForcing q b L G c u-L*(G u-∑' i, c i u)
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hSum {i} u).trans (hF u).2
  have hcs (u) : Summable (fun i => c i u) := summable_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hcF (u) : (∑' i, c i u) ≤ F u := Real.tsum_le_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hg := HotCanonical.family_properties hFm hcm (fun u => (hF u).2) hcn hcs hcF hnorm
  have hGp (n) : pull (displacement n) G = G :=
    familyReplacement_pull (displacement n) (relabel n) (hperiodic n) (hcperiodic n)
  have hkp (n) : pull (displacement n) k = k := by
    have hr : pull (displacement n) (remainderForcing q b L G c) = remainderForcing q b L G c :=
      remainderForcing_pull q b L (displacement n) (relabel n) (hGp n) (hcperiodic n)
    funext u
    have hsum := family_sum_pull (displacement n) (relabel n) (hcperiodic n) u
    change remainderForcing q b L G c (u.1,shift (displacement n) u.2)-
      L*(G (u.1,shift (displacement n) u.2)-_) = remainderForcing q b L G c u-L*(G u-_)
    rw [show remainderForcing q b L G c (u.1,shift (displacement n) u.2) =
      remainderForcing q b L G c u from congrFun hr u,
      show G (u.1,shift (displacement n) u.2) = G u from congrFun (hGp n) u,hsum]
  have hkm : Measurable k := ((measurable_forcing hg.1 q b L).sub
    (Measurable.tsum (fun i => measurable_coldForcing hg.1 (hcm i) q b L))).sub
      ((hg.1.sub (Measurable.tsum hcm)).const_mul L)
  have hwm : Measurable w := by
    have hzm : Measurable z := hnorm
    unfold w scalarMajorant
    fun_prop
  have hbound : ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → k u ≤ w u.1 := by
    apply ae_bound_of_cell hkm hwm hkp
    intro t ht x hx
    exact geometric_family_source hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq₁ hq₂ ht.1 (ht.2.trans hTmax) (PhaseEssSup.size_nonneg _) A N x hx
      hg.1 hcm hg.2.1 hcb hg.2.2.1 hzero
      (fun v => hg.2.2.2.1 (t,(JetPeriodicDatum.spatialMap x,v))) (fun i v => hU t ht i x v) (he t ht)
  have hcongr := remainderForcing_congr hg.2.2.2.2 q b L c
  filter_upwards [hbound,hcongr,hg.2.2.2.2] with u hu hcu hgu hut
  change G u = F u at hgu
  change remainderForcing q b L G c u = remainderForcing q b L F c u at hcu
  have hh := hg.2.2.2.1 u
  have hbnd := hu hut
  change G u-∑' i, c i u ≤ z u.1 at hh
  change remainderForcing q b L G c u-L*(G u-∑' i, c i u) ≤ w u.1 at hbnd
  rw [hgu] at hh hbnd
  rw [hcu] at hbnd
  have hmul := mul_le_mul_of_nonneg_left hh hL
  change remainderForcing q b L F c u ≤ w u.1+L*z u.1
  linarith

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Net source control, with artificial damping cancelled -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem geometric_hot_net_source (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hTmax : T ≤ 1/32)
    (A : ℝ) (N : ℕ)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hzero : ∀ i, ¬i.annulus < N → c i = 0)
    (hU : ∀ t ∈ Ioc 0 T, ∀ i (x w : Velocity),
      VelocityWeight.H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,w))
    (hperiodic : ∀ n, pull (displacement n) F = F)
    (hcperiodic : ∀ n i, pull (displacement n) (c i) = c (relabel n i))
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p))))
    (he : ∀ t ∈ Ioc 0 T,
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A ≤ 1) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T →
      remainderForcing q b L F c u-L*(F u-∑' i, c i u) ≤
      scalarMajorant s₀ η K α γ d₀ q A N u.1
        (PhaseEssSup.size (fun p => F (u.1,p)-∑' i, c i (u.1,p))) := by
  classical
  let G := HotCanonical.familyReplacement F c
  let z (t : ℝ) := PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p))
  let w (t : ℝ) := scalarMajorant s₀ η K α γ d₀ q A N t (z t)
  let k (u : ℝ × JetPrototype.Phase) := remainderForcing q b L G c u-L*(G u-∑' i, c i u)
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hSum {i} u).trans (hF u).2
  have hcs (u) : Summable (fun i => c i u) := summable_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hcF (u) : (∑' i, c i u) ≤ F u := Real.tsum_le_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hg := HotCanonical.family_properties hFm hcm (fun u => (hF u).2) hcn hcs hcF hnorm
  have hGp (n) : pull (displacement n) G = G :=
    familyReplacement_pull (displacement n) (relabel n) (hperiodic n) (hcperiodic n)
  have hkp (n) : pull (displacement n) k = k := by
    have hr : pull (displacement n) (remainderForcing q b L G c) = remainderForcing q b L G c :=
      remainderForcing_pull q b L (displacement n) (relabel n) (hGp n) (hcperiodic n)
    funext u
    have hsum := family_sum_pull (displacement n) (relabel n) (hcperiodic n) u
    change remainderForcing q b L G c (u.1,shift (displacement n) u.2)-
      L*(G (u.1,shift (displacement n) u.2)-_) = remainderForcing q b L G c u-L*(G u-_)
    rw [show remainderForcing q b L G c (u.1,shift (displacement n) u.2) =
      remainderForcing q b L G c u from congrFun hr u,
      show G (u.1,shift (displacement n) u.2) = G u from congrFun (hGp n) u,hsum]
  have hkm : Measurable k := ((measurable_forcing hg.1 q b L).sub
    (Measurable.tsum (fun i => measurable_coldForcing hg.1 (hcm i) q b L))).sub
      ((hg.1.sub (Measurable.tsum hcm)).const_mul L)
  have hwm : Measurable w := by
    have hzm : Measurable z := hnorm
    unfold w scalarMajorant
    fun_prop
  have hbound : ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → k u ≤ w u.1 := by
    apply ae_bound_of_cell hkm hwm hkp
    intro t ht x hx
    exact geometric_family_source hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq₁ hq₂ ht.1 (ht.2.trans hTmax) (PhaseEssSup.size_nonneg _) A N x hx
      hg.1 hcm hg.2.1 hcb hg.2.2.1 hzero
      (fun v => hg.2.2.2.1 (t,(JetPeriodicDatum.spatialMap x,v))) (fun i v => hU t ht i x v) (he t ht)
  have hcongr := remainderForcing_congr hg.2.2.2.2 q b L c
  filter_upwards [hbound,hcongr,hg.2.2.2.2] with u hu hcu hgu hut
  change G u = F u at hgu
  change remainderForcing q b L G c u = remainderForcing q b L F c u at hcu
  have hbnd := hu hut
  change remainderForcing q b L G c u-L*(G u-∑' i, c i u) ≤ w u.1 at hbnd
  rw [hgu,hcu] at hbnd
  exact hbnd

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The source created between distinct cold colors -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def coldFamilySource (q b : ℝ) (c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ)
    (u : ℝ × JetPrototype.Phase) : ℝ :=
  remainderForcing q b 0 (fun z => ∑' i, c i z) c u

theorem geometric_cold_source (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hTmax : T ≤ 1/32)
    (A : ℝ) (N : ℕ)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hF : ∀ u, F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hzero : ∀ i, ¬i.annulus < N → c i = 0)
    (hU : ∀ t ∈ Ioc 0 T, ∀ i (x w : Velocity),
      VelocityWeight.H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,w))
    (hcperiodic : ∀ n i, pull (displacement n) (c i) = c (relabel n i))
    (he : ∀ t ∈ Ioc 0 T,
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A ≤ 1) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T →
      0 ≤ coldFamilySource q b c u ∧
        coldFamilySource q b c u ≤ scalarMajorant s₀ η K α γ d₀ q A N u.1 0 := by
  let C : ℝ × JetPrototype.Phase → ℝ := fun u => ∑' i, c i u
  have hcs (u) : Summable (fun i => c i u) :=
    summable_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hCF (u) : C u ≤ F u :=
    Real.tsum_le_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hCm : Measurable C := Measurable.tsum hcm
  have hCB (u) : 0 ≤ C u ∧ C u ≤ R :=
    ⟨tsum_nonneg (fun i => hcn i u),(hCF u).trans (hF u)⟩
  have hCS (s : Finset JetLattice.Label) (u) : ∑ i ∈ s, c i u ≤ C u :=
    (hcs u).sum_le_tsum s (fun i _ => hcn i u)
  have hcp (n) : pull (displacement n) C = C := by
    funext u
    exact family_sum_pull (displacement n) (relabel n) (hcperiodic n) u
  have hz (t : ℝ) : PhaseEssSup.size (fun p => C (t,p)-∑' i, c i (t,p)) = 0 := by
    simp only [C,sub_self,PhaseEssSup.size]
    change (eLpNorm (0 : JetPrototype.Phase → ℝ) ⊤ FlightMeasure.phaseVolume).toReal = 0
    rw [eLpNorm_zero,ENNReal.toReal_zero]
  have hnorm : Measurable (fun t => PhaseEssSup.size (fun p => C (t,p)-∑' i, c i (t,p))) := by
    simp_rw [hz]
    exact measurable_const
  have hb := geometric_hot_net_source (b := b) (L := 0) hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ hTmax A N hCm hcm hCB hcn hCS hzero hU hcp hcperiodic hnorm he
  have hci (i) (z) : 0 ≤ GaussianLocal.state (c i) z ∧
      GaussianLocal.state (c i) z ≤ R := by
    refine ⟨hcn i _,?_⟩
    exact ((hcs _).le_tsum i (fun j _ => hcn j _)).trans (hCB _).2
  have hlo (u : ℝ × JetPrototype.Phase) : 0 ≤ coldFamilySource q b c u := by
    have h := HotRepresentative.hot_net_source_lower (q := q) (b := b) 0
      (fun i => GaussianLocal.measurable_state (hcm i)) (GaussianLocal.measurable_state hCm)
      hci (fun z => hCB (z.1.1,(z.1.2,z.2)))
      (fun s z => hCS s (z.1.1,(z.1.2,z.2))) ((u.1,u.2.1),u.2.2)
    simp only [zero_mul,sub_zero] at h
    change -(HotRepresentative.frequency q b (GaussianLocal.state C)
      ((u.1,u.2.1),u.2.2)*(C u-∑' i, c i u)) ≤ coldFamilySource q b c u at h
    simpa only [C,sub_self,mul_zero,neg_zero] using h
  filter_upwards [hb] with u hu hut
  refine ⟨hlo u,?_⟩
  change remainderForcing q b 0 C c u ≤ _
  simpa only [hz,zero_mul,sub_zero] using hu hut

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
