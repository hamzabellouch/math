import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedColdShift
import OAI.MathematicalPhysics.Boltzmann.Branching.FamilyHotBounds
import OAI.MathematicalPhysics.Boltzmann.Branching.HotSeedCoreLower
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseDecompositionNorm
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedHotGain
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetSolutions
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Branching.ZeroProfileParameters
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialJointAnalytic
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicSourceBound
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricMesh
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreMomentBound
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreConvergence
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarriers
import OAI.MathematicalPhysics.Boltzmann.Jets.JetSupersolutions
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies
import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles

namespace OAI

section

/-! # Uniform hot-source control from the periodic cold decomposition -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem scale_antitone {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {i j : ℕ} (hij : i ≤ j) : jetScale s₀ η j ≤ jetScale s₀ η i := by
  unfold jetScale DatumBounds.scale
  apply mul_le_mul_of_nonneg_left _ hs₀
  apply Real.exp_le_exp.mpr
  have h : ((i+1 : ℕ) : ℝ) ≤ ((j+1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hij 1
  nlinarith

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem select_remainder {s₀ η t z e : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (htmax : t ≤ 1/32)
    (N : ℕ) (x : Velocity) (y : X) (F : X × Velocity → ℝ) (c : Label → X × Velocity → ℝ)
    (hcs : ∀ w, Summable (fun i => c i (y,w)))
    (hzero : ∀ i, ¬i.annulus < N → ∀ w, c i (y,w) = 0)
    (hhot : ∀ w, F (y,w)-(∑' i, c i (y,w)) ≤ z)
    (htail : ∀ w, (∑' i, escaped s₀ η t N x (fun j => c j (y,w)) i) ≤ e) :
    ∃ i : Label, i.annulus ≤ N ∧ ∀ w, F (y,w)-c i (y,w) ≤ z+e := by
  obtain ⟨i,hi,hcore,hout⟩ | hout := main_or_outside hs₀ hsmax hη hηmax htmax N x
  · refine ⟨i,hi.le,?_⟩
    intro w
    have he := sum_sub_main (hcs w) (fun j hj => hzero j hj w) i hcore hout
    have hh := hhot w
    have ht := htail w
    linarith
  · let i : Label := ⟨N,false,0⟩
    refine ⟨i,le_refl N,?_⟩
    intro w
    have hi : c i (y,w) = 0 := hzero i (lt_irrefl N) w
    have he := sum_all_escaped (fun j hj => hzero j hj w) hout
    have hh := hhot w
    have ht := htail w
    rw [hi]
    linarith

theorem uniform_hot_source (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q t R z e : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hz : 0 ≤ z) (he : 0 ≤ e) (he₁ : e ≤ 1)
    (N : ℕ) (x : Velocity) (y : X)
    {F : X × Velocity → ℝ} {c : Label → X × Velocity → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R)
    (hSum : ∀ u : Finset Label, ∀ p, ∑ i ∈ u, c i p ≤ F p)
    (hzero : ∀ i, ¬i.annulus < N → ∀ w, c i (y,w) = 0)
    (hhot : ∀ w, F (y,w)-(∑' i, c i (y,w)) ≤ z)
    (htail : ∀ w, (∑' i, escaped s₀ η t N x (fun j => c j (y,w)) i) ≤ e)
    (hcU : ∀ i w, VelocityWeight.H q w*c i (y,w) ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,w)) (b L : ℝ) :
    ∀ᵐ v : Velocity,
      HotRepresentative.source q b L F (y,v) -
        (∑' i, HotRepresentative.coldSource q b L F (c i) (y,v)) -
        L*(F (y,v)-(∑' i, c i (y,v))) ≤
      (2*JetMainGain.coefficient K α γ q/(jetScale s₀ η N+t))*z +
        2*HotApplication.realBound q*z^2 +
        (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*(e/t) := by
  have hcs (w) : Summable (fun i => c i (y,w)) :=
    summable_of_sum_le (fun i => (hc i (y,w)).1) (fun u => hSum u (y,w))
  obtain ⟨i,hi,hrem⟩ := select_remainder hs₀ hsmax hη hηmax htmax N x y F c hcs hzero hhot htail
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
  have hsn := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hss := JetEscapedTotal.scale_bound hs₀ hη i.annulus
  filter_upwards [HotRepresentative.jet_hot_source_le hcarleman hK hα hγ hs
    (hss.trans hsmax) hd₀ hd₀max ht htmax hq₁ hq₂ (add_nonneg hz he) η i.positive
    (JetSpatialBox.shifted x i.lattice) hFm hcm hc hF hSum i y (hcU i) hrem b L] with v hv
  exact hv.trans (HotScalarBound.remainder_majorant (JetMainGain.coefficient_nonneg hK α γ q)
    (HotApplication.realBound_pos q).le hz he he₁ hsn (scale_antitone hs₀.le hη.le hi)
    ht (htmax.trans (by norm_num)))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform source bound for the actual constructed periodic hot remainder -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem hot_source_bound (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b L T R t z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (ht : t ∈ Ioc 0 T) (htmax : t ≤ 1/32) (hz : 0 ≤ z)
    (A : ℝ) (N : ℕ) (x : Velocity) (hx : ∀ k, |x k| ≤ 1)
    {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight
      (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) u)
    (hhot : ∀ w, hotRemainder q b L T F (color s₀ η K α γ d₀ q N)
      (t,(JetPeriodicDatum.spatialMap x,w)) ≤ z)
    (he : JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A ≤ 1) :
    ∀ᵐ v : Velocity,
      hotForcing q b L T F (color s₀ η K α γ d₀ q N) (t,(JetPeriodicDatum.spatialMap x,v)) -
        L*hotRemainder q b L T F (color s₀ η K α γ d₀ q N) (t,(JetPeriodicDatum.spatialMap x,v)) ≤
      (2*JetMainGain.coefficient K α γ q/(JetGeometry.jetScale s₀ η N+t))*z +
        2*HotApplication.realBound q*z^2 +
        (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
          ((JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A)/t) := by
  let c (i : JetLattice.Label) := cold s₀ η K α γ d₀ q b L T N F i
  let e := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hp (i : JetLattice.Label) := coldLimit_solution hq₂ hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N i) hF (hi.1 i) hF₀ hFeq
  have hcm (i) : Measurable (c i) := (hp i).1
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R :=
    ⟨((hp i).2.1 u).1,((hp i).2.1 u).2.trans (hF u).2⟩
  have hsum (s : Finset JetLattice.Label) (u) : ∑ i ∈ s, c i u ≤ F u :=
    finite_sum_coldLimit_le hq₂ hb hL hT hR hloss s hFm
      (fun i _ => measurable_color s₀ η K α γ d₀ q N i) hF (fun i _ => hi.1 i) hF₀ (hi.2 s) hFeq u
  have hU (i : JetLattice.Label) (w : Velocity) :
      VelocityWeight.H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,w) := by
    have h := cold_envelope hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall hq₂ hb hL hT hR hTmax
      hloss N hh₀ hFm hF hF₀ hFeq i ht (JetPeriodicDatum.spatialMap x,w)
    exact h
  have htail (w) : (∑' i, escaped s₀ η t N x (fun j => c j (t,(JetPeriodicDatum.spatialMap x,w))) i) ≤ e :=
    normalized_escaped_bound hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le hd₀ hd₀max ht.1 htmax hsmall A q N
      (fun j => c j (t,(JetPeriodicDatum.spatialMap x,w))) x w hx
      (fun i => (hcb i _).1)
      (summable_of_sum_le (fun i => (hcb i _).1) (fun s => hsum s _)) (fun i _ => hU i w)
  have he0 : 0 ≤ e := mul_nonneg
    (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α (JetEscapedEnvelope.exponent A))
    (Real.rpow_nonneg ht.1.le A)
  have hzero (i : JetLattice.Label) (hi : ¬i.annulus < N) (w : Velocity) :
      GaussianLocal.state (c i) ((t,JetPeriodicDatum.spatialMap x),w) = 0 := by
    have hh := congrFun (cold_zero s₀ η K α γ d₀ q b L T N F i hi) (t,(JetPeriodicDatum.spatialMap x,w))
    exact hh
  exact uniform_hot_source hcarleman hs₀ hsmax hη hηmax hK hα hγ hd₀ hd₀max hq₁ hq₂ ht.1 htmax hz he0 he
    N x (t,JetPeriodicDatum.spatialMap x) (GaussianLocal.measurable_state hFm)
    (fun i => GaussianLocal.measurable_state (hcm i))
    (fun u => hF (u.1.1,(u.1.2,u.2))) (fun i u => hcb i (u.1.1,(u.1.2,u.2)))
    (fun s u => hsum s (u.1.1,(u.1.2,u.2))) hzero hhot htail hU b L

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform bounds for the free-core velocity averages -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermal_integral_one :
    (∫ w : Transverse × ℝ, JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume) = 1 := by
  rw [HotRectangleDensity.join_measurePreserving.integral_comp
    SheetMeasures.join.measurableEmbedding, JetThermalKernel.J_integral]

theorem masked_thermal_bound {χ : Transverse × ℝ → ℝ}
    (hχ : ∀ w, |χ w| ≤ 1) :
    |∫ w, χ w*JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume| ≤ 1 := by
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  dsimp only [Function.comp_def] at hJ
  rw [← Real.norm_eq_abs, ← thermal_integral_one]
  apply norm_integral_le_of_norm_le hJ
  filter_upwards [] with w
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hχ w) (JetThermalKernel.J_nonneg _)

theorem free_average_bound {K α γ s d t B : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 < t) (η : ℝ) (a : Bool) (x : JetPrototype.Space)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    |∫ v, JetFreeTransport.free η K α γ s d t a (x,v)*ψ v| ≤
      ((K*max 1 (α*γ)⁻¹)/t)*B := by
  rw [free_test_integral hK hα.le hγ.le hs hd ht.le η a x hψ,← Real.norm_eq_abs]
  let C := (K*max 1 (α*γ)⁻¹)/t
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hK (le_max_of_le_left zero_le_one)) ht.le
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  dsimp only [Function.comp_def] at hJ
  have hb (w) : weight η K α γ s d t a x w ≤ C*JetThermalKernel.J (SheetMeasures.join w) := by
    apply (weight_bound hK hα hγ hs ht.le η d a x w).trans
    apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
    exact div_le_div_of_nonneg_left
      (mul_nonneg hK (le_max_of_le_left zero_le_one)) ht (by linarith)
  calc
    _ ≤ ∫ w, (C*B)*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume := by
      apply norm_integral_le_of_norm_le (hJ.const_mul (C*B))
      filter_upwards [] with w
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (weight_nonneg hK hα.le hγ.le hs ht.le η d a x w)]
      exact (mul_le_mul (hb w) (hψB _) (abs_nonneg _) (mul_nonneg hC
        (JetThermalKernel.J_nonneg _))).trans_eq (by ring)
    _ = C*B := by rw [integral_const_mul,thermal_integral_one,mul_one]

theorem dilated_free_average_bound {r K α γ s d t B : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (η : ℝ) (a : Bool) (x : JetPrototype.Space)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    |∫ v, r*JetFreeTransport.free η K α γ s d (r*t) a (r • x,v)*ψ v| ≤
      ((K*max 1 (α*γ)⁻¹)/t)*B := by
  have hb := mul_le_mul_of_nonneg_left
    (free_average_bound hK hα hγ hs hd (mul_pos hr ht) η a (r • x) hψ hψB) hr.le
  simp_rw [mul_assoc r,integral_const_mul,abs_mul,abs_of_pos hr]
  convert hb using 1
  field_simp

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Uniform source bound after replacing the total representative -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem family_hot_source_bound (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b L T R t z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (ht : t ∈ Ioc 0 T) (htmax : t ≤ 1/32) (hz : 0 ≤ z)
    (A : ℝ) (N : ℕ) (x : Velocity) (hx : ∀ k, |x k| ≤ 1)
    {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight
      (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) u)
    {G : ℝ × JetPrototype.Phase → ℝ} (hGm : Measurable G)
    (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (hGsum : ∀ s : Finset JetLattice.Label, ∀ u,
      ∑ i ∈ s, cold s₀ η K α γ d₀ q b L T N F i u ≤ G u)
    (hhot : ∀ w, G (t,(JetPeriodicDatum.spatialMap x,w)) -
      ∑' i, cold s₀ η K α γ d₀ q b L T N F i (t,(JetPeriodicDatum.spatialMap x,w)) ≤ z)
    (he : JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A ≤ 1) :
    ∀ᵐ v : Velocity,
      remainderForcing q b L G (cold s₀ η K α γ d₀ q b L T N F)
        (t,(JetPeriodicDatum.spatialMap x,v)) -
        L*(G (t,(JetPeriodicDatum.spatialMap x,v)) -
          ∑' i, cold s₀ η K α γ d₀ q b L T N F i (t,(JetPeriodicDatum.spatialMap x,v))) ≤
      (2*JetMainGain.coefficient K α γ q/(JetGeometry.jetScale s₀ η N+t))*z +
        2*HotApplication.realBound q*z^2 +
        (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
          ((JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A)/t) := by
  let c (i : JetLattice.Label) := cold s₀ η K α γ d₀ q b L T N F i
  let e := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hp (i : JetLattice.Label) := coldLimit_solution hq₂ hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N i) hF (hi.1 i) hF₀ hFeq
  have hcm (i) : Measurable (c i) := (hp i).1
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R :=
    ⟨((hp i).2.1 u).1,((hp i).2.1 u).2.trans (hF u).2⟩
  have hsum (s : Finset JetLattice.Label) (u) : ∑ i ∈ s, c i u ≤ F u :=
    finite_sum_coldLimit_le hq₂ hb hL hT hR hloss s hFm
      (fun i _ => measurable_color s₀ η K α γ d₀ q N i) hF (fun i _ => hi.1 i) hF₀ (hi.2 s) hFeq u
  have hU (i : JetLattice.Label) (w : Velocity) :
      VelocityWeight.H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,w) := by
    have h := cold_envelope hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall hq₂ hb hL hT hR hTmax
      hloss N hh₀ hFm hF hF₀ hFeq i ht (JetPeriodicDatum.spatialMap x,w)
    exact h
  have htail (w) : (∑' i, escaped s₀ η t N x (fun j => c j (t,(JetPeriodicDatum.spatialMap x,w))) i) ≤ e :=
    normalized_escaped_bound hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le hd₀ hd₀max ht.1 htmax hsmall A q N
      (fun j => c j (t,(JetPeriodicDatum.spatialMap x,w))) x w hx
      (fun i => (hcb i _).1)
      (summable_of_sum_le (fun i => (hcb i _).1) (fun s => hsum s _)) (fun i _ => hU i w)
  have he0 : 0 ≤ e := mul_nonneg
    (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α (JetEscapedEnvelope.exponent A))
    (Real.rpow_nonneg ht.1.le A)
  have hzero (i : JetLattice.Label) (hi : ¬i.annulus < N) (w : Velocity) :
      GaussianLocal.state (c i) ((t,JetPeriodicDatum.spatialMap x),w) = 0 := by
    have hh := congrFun (cold_zero s₀ η K α γ d₀ q b L T N F i hi) (t,(JetPeriodicDatum.spatialMap x,w))
    exact hh
  exact uniform_hot_source hcarleman hs₀ hsmax hη hηmax hK hα hγ hd₀ hd₀max hq₁ hq₂ ht.1 htmax hz he0 he
    N x (t,JetPeriodicDatum.spatialMap x) (GaussianLocal.measurable_state hGm)
    (fun i => GaussianLocal.measurable_state (hcm i))
    (fun u => hG (u.1.1,(u.1.2,u.2))) (fun i u => hcb i (u.1.1,(u.1.2,u.2)))
    (fun s u => hGsum s (u.1.1,(u.1.2,u.2))) hzero hhot htail hU b L

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual periodic shooting data converge to the common cold datum in L¹ -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetPeriodicDatum

theorem measurable_pullback {f : JetPrototype.Phase → ℝ} (hf : Measurable f) :
    Measurable (pullback f) :=
  hf.comp (phaseMap_measurePreserving.measurable.comp TorusChart.phase_measurePreserving.measurable)

def truncated (s₀ η K α γ d₀ : ℝ) (N : ℕ) : Density :=
  pullback (JetTruncation.truncated s₀ η K α γ d₀ N)

theorem truncated_integrable {s₀ η K γ d₀ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) (N : ℕ) :
    Integrable (truncated s₀ η K α γ d₀ N) := by
  have hi := integrable_pullback (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α)
  apply hi.mono' (measurable_pullback (JetTruncation.truncated_measurable s₀ η K α γ d₀ N)).aestronglyMeasurable
  filter_upwards [] with p
  have h := JetTruncation.truncated_eq_or_zero hs₀ hsmax hη hηmax K α γ d₀ N
    (phaseMap (TorusChart.phaseRepresentative p))
  rcases h with h | h
  · change ‖JetTruncation.truncated _ _ _ _ _ _ _ _‖ ≤ _
    rw [h,Real.norm_of_nonneg (JetDatumMoments.datum_nonneg hs₀ hK hd₀.le η α γ _)]
    exact le_rfl
  · change ‖JetTruncation.truncated _ _ _ _ _ _ _ _‖ ≤ _
    rw [h,norm_zero]
    exact JetDatumMoments.datum_nonneg hs₀ hK hd₀.le η α γ _

theorem truncated_L1_tendsto {s₀ η K γ d₀ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) :
    Tendsto (fun N => ∫ p, ‖truncated s₀ η K α γ d₀ N p-datum s₀ η K α γ d₀ p‖)
      atTop (𝓝 0) :=
  JetConvergence.selection_L1_tendsto
    (fun N => (measurable_pullback (JetTruncation.truncated_measurable s₀ η K α γ d₀ N)).aestronglyMeasurable)
    (integrable_pullback (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α))
    (fun N p => JetTruncation.truncated_eq_or_zero hs₀ hsmax hη hηmax K α γ d₀ N (phaseMap (TorusChart.phaseRepresentative p)))
    (fun p => JetTruncation.eventually_truncated_eq hs₀ hsmax hη hηmax K α γ d₀ (phaseMap (TorusChart.phaseRepresentative p)))

end BoltzmannNonuniqueness.JetPeriodicDatum

namespace BoltzmannNonuniqueness.JetConvergence

theorem add_L1_tendsto {f g : ℕ → Density} {f₀ : Density}
    (hf : ∀ n, Integrable (f n)) (hg : ∀ n, Integrable (g n)) (hf₀ : Integrable f₀)
    (hflim : Tendsto (fun n => ∫ p, ‖f n p-f₀ p‖) atTop (𝓝 0))
    (hglim : Tendsto (fun n => ∫ p, ‖g n p‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p, ‖f n p+g n p-f₀ p‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun p => norm_nonneg _))
    (fun n => ?_) (by simpa only [zero_add] using hflim.add hglim)
  calc
    _ ≤ ∫ p, ‖f n p-f₀ p‖+‖g n p‖ := by
      apply integral_mono (((hf n).add (hg n)).sub hf₀).norm (((hf n).sub hf₀).norm.add (hg n).norm)
      intro p
      have h := norm_add_le (f n p-f₀ p) (g n p)
      change ‖f n p+g n p-f₀ p‖ ≤ _
      rw [show f n p+g n p-f₀ p = (f n p-f₀ p)+g n p by ring]
      exact h
    _ = _ := integral_add ((hf n).sub hf₀).norm (hg n).norm

end BoltzmannNonuniqueness.JetConvergence

namespace BoltzmannNonuniqueness.JetCopyDatum

def periodicInitial (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (ell : ℝ) : Density :=
  fun p => JetPeriodicDatum.pullback (initial s₀ η K α γ d₀ q N
    (fun z => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) z)) p * H q p.2

theorem periodicInitial_eq {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ) (ell : ℝ)
    (p : Phase) :
    periodicInitial s₀ η K α γ d₀ q N ell p =
      JetPeriodicDatum.truncated s₀ η K α γ d₀ N p+
        ell*HotSeedProfile.periodicDensity q (DatumBounds.scale s₀ η (N+1)) p := by
  have he := seed_on_cube hs₀ hsmax hη hηmax K α γ d₀ q N
    (TorusChart.representative_mem p.1) p.2
  change (seed s₀ η K α γ d₀ q N (JetPeriodicDatum.spatialMap (TorusChart.representative p.1),p.2)+
    ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1))
      (JetPeriodicDatum.spatialMap (TorusChart.representative p.1),p.2))*H q p.2 = _
  rw [he,add_mul,div_mul_cancel₀ _ (H_pos q p.2).ne']
  simp only [JetPeriodicDatum.truncated,JetPeriodicDatum.pullback,HotSeedProfile.periodicDensity,
    JetPeriodicDatum.phaseMap,TorusChart.phaseRepresentative]
  ring

theorem periodicInitial_L1_tendsto {s₀ η K γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq : 0 ≤ q) (hqmax : q < 2)
    (α : ℝ) {ell : ℕ → ℝ} (hell : ∀ n, ell n ∈ Set.Icc (0:ℝ) 2) :
    Tendsto (fun N => ∫ p, ‖periodicInitial s₀ η K α γ d₀ q N (ell N) p-
      JetPeriodicDatum.datum s₀ η K α γ d₀ p‖) atTop (𝓝 0) := by
  have hδ (n : ℕ) : 0 < DatumBounds.scale s₀ η (n+1) := DatumBounds.scale_pos hs₀ _
  have hδmax (n : ℕ) : DatumBounds.scale s₀ η (n+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hδlim : Tendsto (fun n => DatumBounds.scale s₀ η (n+1)) atTop (𝓝 0) :=
    (DatumBounds.scale_tendsto_zero s₀ hη).comp (tendsto_add_atTop_nat 1)
  simp_rw [periodicInitial_eq hs₀ hsmax hη hηmax]
  exact JetConvergence.add_L1_tendsto
    (JetPeriodicDatum.truncated_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α)
    (fun n => (HotSeedProfile.periodicDensity_integrable hq hqmax (hδ n) (hδmax n)).const_mul (ell n))
    (JetPeriodicDatum.integrable_pullback (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α))
    (JetPeriodicDatum.truncated_L1_tendsto hs₀ hsmax hη hηmax hK hγ hd₀ α)
    (HotSeedProfile.periodicDensity_L1_tendsto hq hqmax hδ hδmax hδlim hell)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform finite mesh windows for the original cold enlargements -/

noncomputable section

open Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem enlargement_dilated_shell {s₀ η r : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hr : 0 < r) (j : ℕ) (a : Bool) {y : Transverse}
    (hy : r • y ∈ enlargement η (jetScale s₀ η j) a) :
    y ∈ scaleShell η (GeometricMesh.point (GeometricMesh.phase (s₀/r) η) η
      (GeometricMesh.jetMeshIndex s₀ η r j)) := by
  have hb := enlargement_subset_annulus hη (DatumBounds.scale_pos hs₀ _) a hy
  rw [← GeometricMesh.jetScale_ratio_exact hs₀ hr hη j]
  change jetScale s₀ η j/r < ‖y‖ ∧ ‖y‖ < Real.exp η*(jetScale s₀ η j/r)
  have hn : ‖r • y‖ = r*‖y‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  change jetScale s₀ η j < ‖r • y‖ ∧ ‖r • y‖ < Real.exp η*jetScale s₀ η j at hb
  rw [hn] at hb
  constructor
  · exact (div_lt_iff₀ hr).mpr (by simpa only [mul_comm] using hb.1)
  · rw [← mul_div_assoc]
    exact (lt_div_iff₀ hr).mpr (by simpa only [mul_comm] using hb.2)

theorem enlargement_mesh_window {s₀ η r δ R : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hr : 0 < r) (hδ : 0 < δ) (j : ℕ) (a : Bool) {y : Transverse}
    (hy : r • y ∈ enlargement η (jetScale s₀ η j) a) (hlo : δ ≤ ‖y‖) (hhi : ‖y‖ ≤ R) :
    GeometricMesh.index (δ/Real.exp η) η ≤ GeometricMesh.jetMeshIndex s₀ η r j ∧
      GeometricMesh.jetMeshIndex s₀ η r j ≤ GeometricMesh.index R η :=
  GeometricMesh.shell_index_window (GeometricMesh.phase_bounds hη _).1
    (GeometricMesh.phase_bounds hη _).2 hη hδ
    (enlargement_dilated_shell hs₀ hη hr j a hy) hlo hhi

end BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.GeometricMesh

theorem window_eventually_below_top {s₀ η R : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∀ᶠ n in atTop, index R η < index (s₀/r n) η :=
  (index_tendsto_atTop hs₀ hη hr hrlim).eventually_gt_atTop _

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Separating the shell factor from the thermal stripe average -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem masked_thermal_integrable {χ : Transverse × ℝ → ℝ}
    (hχ : Measurable χ) (hb : ∀ w, |χ w| ≤ 1) :
    Integrable (fun w => χ w*JetThermalKernel.J (SheetMeasures.join w))
      ((volume : Measure Transverse).prod volume) := by
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  dsimp only [Function.comp_def] at hJ
  apply hJ.mono' (hχ.mul (JetThermalKernel.J_smooth.continuous.measurable.comp
    SheetMeasures.join.measurable)).aestronglyMeasurable
  filter_upwards [] with w
  change ‖χ w*JetThermalKernel.J (SheetMeasures.join w)‖ ≤
    JetThermalKernel.J (SheetMeasures.join w)
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb w) (JetThermalKernel.J_nonneg _)

theorem dilatedMask_eq (r η s d t : ℝ) (a : Bool) (x : JetPrototype.Space)
    (w : Transverse × ℝ) :
    dilatedMask r η s d t a x w =
      (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • (x.1-t • (d • w.1))) := by
  unfold dilatedMask
  congr 1
  module

end BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetGeometry

theorem maskError_average_eq (r η s d μ t : ℝ) (a : Bool) (x : JetPrototype.Space) :
    (∫ w, maskError r η (r*s) d μ t a (x.1,w)
      ∂(volume : Measure Transverse).prod volume) =
    (∫ w, JetCoreDensity.dilatedMask r η s d t a x w*JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume)-
    (scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1*
      (∫ w, (stripe (r*s) a).indicator (fun _ => (1:ℝ))
        (r • (x.1-t • (d • w.1)))*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume) := by
  have hb (A : Set Transverse) (w : Transverse × ℝ) :
      |A.indicator (fun _ => (1:ℝ)) (r • (x.1-t • (d • w.1)))| ≤ 1 := by
    by_cases h : r • (x.1-t • (d • w.1)) ∈ A <;> simp [h]
  have hm (A : Set Transverse) (hA : MeasurableSet A) :
      Measurable (fun w : Transverse × ℝ =>
        A.indicator (fun _ => (1:ℝ)) (r • (x.1-t • (d • w.1)))) :=
    (measurable_const.indicator hA).comp (by fun_prop)
  have hi := JetCoreDensity.masked_thermal_integrable
    (hm _ (JetMaskMeasure.measurableSet_mask η (r*s) a)) (hb _)
  have hs := JetCoreDensity.masked_thermal_integrable
    (hm _ (JetMaskMeasure.measurableSet_stripe (r*s) a)) (hb _)
  simp_rw [maskError,JetCoreDensity.dilatedMask_eq,sub_mul,mul_assoc]
  rw [integral_sub hi (hs.const_mul _),integral_const_mul]

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Essential-norm source estimate for the actual periodic hot remainder -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def scalarMajorant (s₀ η K α γ d₀ q A : ℝ) (N : ℕ) (t z : ℝ) : ℝ :=
  (2*JetMainGain.coefficient K α γ q/(JetGeometry.jetScale s₀ η N+t))*z +
    2*HotApplication.realBound q*z^2 +
    (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      ((JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A)/t)

theorem hot_source_norm_bound (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (A : ℝ) (N : ℕ)
    {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight
      (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) u)
    (hperiodic : ∀ n, pull (displacement n) F = F)
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p =>
      hotRemainder q b L T F (color s₀ η K α γ d₀ q N) (t,p))))
    (he : ∀ t ∈ Ioc 0 T,
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A ≤ 1) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T →
      hotForcing q b L T F (color s₀ η K α γ d₀ q N) u ≤
        scalarMajorant s₀ η K α γ d₀ q A N u.1
          (PhaseEssSup.size (fun p => hotRemainder q b L T F (color s₀ η K α γ d₀ q N) (u.1,p))) +
        L*PhaseEssSup.size (fun p => hotRemainder q b L T F (color s₀ η K α γ d₀ q N) (u.1,p)) := by
  let c := cold s₀ η K α γ d₀ q b L T N F
  let G := HotCanonical.familyReplacement F c
  let z (t : ℝ) := PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p))
  let w (t : ℝ) := scalarMajorant s₀ η K α γ d₀ q A N t (z t)
  let k (u : ℝ × JetPrototype.Phase) := remainderForcing q b L G c u-L*(G u-∑' i, c i u)
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc (i : JetLattice.Label) := coldLimit_solution hq₂ hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N i) hF (hi.1 i) hF₀ hFeq
  have hcm (i) : Measurable (c i) := (hc i).1
  have hcn (i) (u) : 0 ≤ c i u := ((hc i).2.1 u).1
  have hcs (u) := WeightedLocal.cold_family_summable hq₂ hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hi.1 hF₀ hi.2 hFeq u
  have hg := HotCanonical.family_properties hFm hcm (fun u => (hF u).2) hcn
    (fun u => (hcs u).1) (fun u => (hcs u).2) hnorm
  have hGp (n) : pull (displacement n) G = G := familyReplacement_shift n (hperiodic n)
  have hkp (n) : pull (displacement n) k = k := by
    have hr : pull (displacement n) (remainderForcing q b L G c) =
        remainderForcing q b L G c := remainderForcing_shift n (hperiodic n) (hGp n)
    funext u
    have hsum : (∑' i, c i (u.1,shift (displacement n) u.2)) = ∑' i, c i u :=
      coldSum_shift n (hperiodic n) u
    change remainderForcing q b L G c (u.1,shift (displacement n) u.2)-
      L*(G (u.1,shift (displacement n) u.2)-_) = remainderForcing q b L G c u-L*(G u-_)
    rw [show remainderForcing q b L G c (u.1,shift (displacement n) u.2) =
      remainderForcing q b L G c u from congrFun hr u,
      show G (u.1,shift (displacement n) u.2) = G u from congrFun (hGp n) u,
      hsum]
  have hkm : Measurable k := by
    exact ((measurable_forcing hg.1 q b L).sub
      (Measurable.tsum (fun i => measurable_coldForcing hg.1 (hcm i) q b L))).sub
        ((hg.1.sub (Measurable.tsum hcm)).const_mul L)
  have hwm : Measurable w := by
    have hzm : Measurable z := hnorm
    unfold w scalarMajorant
    fun_prop
  have hbound : ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → k u ≤ w u.1 := by
    apply ae_bound_of_cell hkm hwm hkp
    intro t ht x hx
    exact family_hot_source_bound hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq₁ hq₂ hb hL hT hR (hTmax.trans (by norm_num)) hloss ht (ht.2.trans hTmax)
      (PhaseEssSup.size_nonneg _) A N x hx hh₀ hFm hF hF₀ hFeq hg.1 hg.2.1 hg.2.2.1
      (fun v => hg.2.2.2.1 (t,(JetPeriodicDatum.spatialMap x,v))) (he t ht)
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

/-! # Spatial regularity of the two terms in thermal concentration -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

def limitingCoefficient (K α γ μ t σ : ℝ) (ψ : Velocity → ℝ)
    (x : JetPrototype.Space) : ℝ :=
  compressed K α γ μ t (AxialFlow.foot σ α γ μ t x.2)*
    ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t x.2))

theorem limitingCoefficient_measurable {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (K σ : ℝ) {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    Measurable (limitingCoefficient K α γ μ t σ ψ) := by
  have hp : Continuous (fun x : JetPrototype.Space => (t,x.2)) :=
    continuous_const.prodMk continuous_snd
  have hf := (AxialFlow.clamped_foot_continuous (σ := σ) hα hγ hμ).comp hp
  have hv := (AxialFlow.clamped_velocity_continuous (σ := σ) hα hγ hμ).comp hp
  dsimp only [Function.comp_def] at hf hv
  simp only [max_eq_right ht] at hf hv
  have hj : Measurable (fun x : JetPrototype.Space =>
      PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t x.2)) :=
    VelocityWeight.split.symm.measurable.comp (hv.measurable.prodMk measurable_const)
  exact ((continuous_compressed hα hγ hμ ht K).comp hf).measurable.mul (hψ.measurable.comp hj)

theorem limitingCoefficient_bound {K α γ μ t B : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ) (ht : 0 < t)
    {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (σ : ℝ) (x : JetPrototype.Space) :
    |limitingCoefficient K α γ μ t σ ψ x| ≤ ((K*max 1 (α*γ)⁻¹)/t)*B := by
  rw [limitingCoefficient,abs_mul,abs_of_nonneg (compressed_nonneg hK hα.le hγ.le hμ ht.le _)]
  apply mul_le_mul _ (hψB _) (abs_nonneg _) (by positivity)
  exact (compressed_bound hK hα hγ hμ ht.le _).trans
    (div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one)) ht (by linarith))

theorem free_average_measurable (r η K α γ s d t : ℝ) (a : Bool)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun x : JetPrototype.Space =>
      ∫ v, r*JetFreeTransport.free η K α γ s d (r*t) a (r • x,v)*ψ v) := by
  have hp : Measurable (fun p : JetPrototype.Space × Velocity => (r • p.1,p.2)) :=
    by fun_prop
  have hm : Measurable (fun p : JetPrototype.Space × Velocity =>
      r*JetFreeTransport.free η K α γ s d (r*t) a (r • p.1,p.2)*ψ p.2) :=
    (measurable_const.mul
    ((JetFreeTransport.measurable_free η K α γ s d (r*t) a).comp hp)).mul
      (hψ.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem mask_average_measurable (r η s d t : ℝ) (a : Bool) :
    Measurable (fun x : JetPrototype.Space => ∫ w,
      dilatedMask r η s d t a x w*JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume) := by
  have hp : Measurable (fun p : JetPrototype.Space × (Transverse × ℝ) =>
      r • p.1.1-(r*t) • (d • p.2.1)) := by fun_prop
  have hmask : Measurable (fun p : JetPrototype.Space × (Transverse × ℝ) =>
      (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • p.1.1-(r*t) • (d • p.2.1))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η (r*s) a)).comp hp
  have hm := hmask.mul
      ((JetThermalKernel.J_smooth.continuous.measurable.comp
        SheetMeasures.join.measurable).comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Local total-variation error of a surviving cold core -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetLocalFreeError

theorem integral_error_le {K α γ s d t E ε : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (hE : 0 ≤ E) (hε : 0 ≤ ε)
    (η : ℝ) (a : Bool) (y : Space) (μ : Measure Space) [IsFiniteMeasure μ]
    {c : JetPrototype.Phase → ℝ} (hcm : Measurable c)
    (hlower : ∀ᵐ p ∂μ.prod volume,
      Real.exp (-E)*JetFreeTransport.free η K α γ s d t a (shift y p) ≤ c p)
    (hupper : ∀ᵐ p ∂μ.prod volume,
      c p ≤ JetFreeTransport.free η K α γ s d t a (shift y p)+
        ε*barrier η K α γ s d t a (shift y p)) :
    Integrable (fun p => |c p-JetFreeTransport.free η K α γ s d t a (shift y p)|)
      (μ.prod volume) ∧
    (∫ p, |c p-JetFreeTransport.free η K α γ s d t a (shift y p)| ∂μ.prod volume) ≤
      (E+ε)*μ.real univ*(JetBarrierLocalMass.massConstant*(K/s)) := by
  let f : JetPrototype.Phase → ℝ := fun p => JetFreeTransport.free η K α γ s d t a (shift y p)
  let B : JetPrototype.Phase → ℝ := fun p => barrier η K α γ s d t a (shift y p)
  have hBi : Integrable B (μ.prod volume) :=
    JetBarrierLocalMass.local_integrable hK hα hγ hs hd ht htmax η a y μ
  have hfm : Measurable f := (JetFreeTransport.measurable_free η K α γ s d t a).comp
    (measurable_shift y)
  have hb : ∀ᵐ p ∂μ.prod volume, |c p-f p| ≤ (E+ε)*B p := by
    filter_upwards [hlower,hupper] with p hl hu
    have hfn : 0 ≤ f p := JetFreeTransport.free_nonneg hK hs.le hd.le η α γ t a _
    have hBn : 0 ≤ B p := barrier_nonneg hK hs.le hd.le η α γ t a _
    have hfb : f p ≤ B p := JetFreeTransport.free_le_barrier hK hd hα hγ hs ht
      (htmax.trans (by norm_num)) η a _
    have he := abs_sub_le_of_survival hfn (mul_nonneg hε hBn) hE hl hu
    exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hfb hE])
  have hci : Integrable (fun p => |c p-f p|) (μ.prod volume) := by
    apply (hBi.const_mul (E+ε)).mono' (hcm.sub hfm).aestronglyMeasurable.norm
    simpa only [Real.norm_eq_abs,Pi.sub_apply,abs_abs] using hb
  refine ⟨hci,?_⟩
  have he := integral_mono_ae hci (hBi.const_mul (E+ε)) hb
  rw [integral_const_mul] at he
  have hm := mul_le_mul_of_nonneg_left
    (JetBarrierLocalMass.local_integral_le hK hα hγ hs hd ht htmax η a y μ)
    (add_nonneg hE hε)
  exact he.trans (by simpa only [B,shift,mul_assoc] using hm)

end BoltzmannNonuniqueness.JetLocalFreeError

end

end

section

/-! # A finite cold-norm bound from one core and the escaped tail -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

def colorAmplitude (K α s d : ℝ) : ℝ :=
  2*JetGaussianEscape.constant α*(K/s)*(d^3)⁻¹*VelocityWeight.tiltConstant

theorem colorAmplitude_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (α : ℝ) : 0 ≤ colorAmplitude K α s d := by
  unfold colorAmplitude JetGaussianEscape.constant VelocityWeight.tiltConstant
  have := JetThermalKernel.bound_pos
  positivity

theorem color_le_amplitude {K α γ s d t q c : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η : ℝ) (a : Bool) (x : Space) (v : Velocity)
    (hc : VelocityWeight.H q v*c ≤ JetSupersolution.U η K α γ s d t a (x,v)) :
    c ≤ colorAmplitude K α s d := by
  have hh := hc.trans (JetEnvelopeBound.U_le_H hK hα hγ hs hd hdmax ht htmax hε η q a x v)
  change VelocityWeight.H q v*c ≤ colorAmplitude K α s d*VelocityWeight.H q v at hh
  nlinarith [VelocityWeight.H_pos q v]

theorem cold_sum_le_of_core_bound {s₀ η t B e : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (htmax : t ≤ 1/32) (N : ℕ) (x : Velocity) (f : JetLattice.Label → Velocity → ℝ)
    (hfs : ∀ v, Summable (fun i => f i v))
    (hzero : ∀ i, ¬i.annulus < N → ∀ v, f i v = 0)
    (htail : ∀ v, (∑' i, escaped s₀ η t N x (fun j => f j v) i) ≤ e)
    (hcore : ∀ i : JetLattice.Label, i.annulus ≤ N → ∀ v, f i v ≤ B) :
    ∀ v, (∑' i, f i v) ≤ B+e := by
  let c (i : JetLattice.Label) (p : Unit × Velocity) := f i p.2
  obtain ⟨i,hi,hh⟩ := select_remainder hs₀ hsmax hη hηmax htmax N x ()
    (fun p : Unit × Velocity => ∑' j, c j p) c hfs hzero (fun _ => sub_self _ |>.le) htail
  intro v
  have h := hh v
  have hc := hcore i hi v
  change (∑' j, f j v)-f i v ≤ 0+e at h
  linarith

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A finite uniform-in-time norm bound for the retained cold family -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

def finiteAmplitude (s₀ η K α d₀ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), colorAmplitude K α (JetGeometry.jetScale s₀ η j)
    (d₀*JetGeometry.jetScale s₀ η j^10)

theorem finiteAmplitude_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 < d₀) (η α : ℝ) (N : ℕ) : 0 ≤ finiteAmplitude s₀ η K α d₀ N := by
  apply Finset.sum_nonneg
  intro j _
  have hs : 0 < JetGeometry.jetScale s₀ η j := DatumBounds.scale_pos hs₀ _
  exact colorAmplitude_nonneg hK hs (by positivity) α

theorem amplitude_le_finite {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 < d₀) (η α : ℝ) {N j : ℕ} (hj : j ≤ N) :
    colorAmplitude K α (JetGeometry.jetScale s₀ η j) (d₀*JetGeometry.jetScale s₀ η j^10) ≤
      finiteAmplitude s₀ η K α d₀ N := by
  unfold finiteAmplitude
  apply Finset.single_le_sum (s := Finset.range (N+1)) (a := j)
    (f := fun i => colorAmplitude K α (JetGeometry.jetScale s₀ η i)
      (d₀*JetGeometry.jetScale s₀ η i^10))
  · intro i _
    have hs : 0 < JetGeometry.jetScale s₀ η i := DatumBounds.scale_pos hs₀ _
    exact colorAmplitude_nonneg hK hs (by positivity) α
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)

theorem cell_cold_sum_bound {s₀ η K α γ d₀ q t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ) (x : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (f : JetLattice.Label → Velocity → ℝ) (hfn : ∀ i v, 0 ≤ f i v)
    (hfs : ∀ v, Summable (fun i => f i v))
    (hzero : ∀ i, ¬i.annulus < N → ∀ v, f i v = 0)
    (hU : ∀ i v, VelocityWeight.H q v*f i v ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,v)) :
    ∀ v, (∑' i, f i v) ≤ finiteAmplitude s₀ η K α d₀ N+
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0) := by
  apply cold_sum_le_of_core_bound hs₀ hsmax hη hηmax htmax N x f hfs hzero
  · intro v
    have h := normalized_escaped_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      ht htmax hsmall 0 q N (fun i => f i v) x v hx (fun i => hfn i v) (hfs v)
      (fun i _ => hU i v)
    simpa only [Real.rpow_zero,mul_one] using h
  · intro i hi v
    have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
    have hss := JetEscapedTotal.scale_bound hs₀ hη i.annulus
    have hd : 0 < d₀*JetGeometry.jetScale s₀ η i.annulus^10 := by positivity
    have hdmax : d₀*JetGeometry.jetScale s₀ η i.annulus^10 ≤ 1/16 := by
      calc
        _ ≤ 1*(1/8:ℝ)^10 := mul_le_mul hd₀max
          (pow_le_pow_left₀ hs.le (hss.trans hsmax) 10) (pow_nonneg hs.le _) (by norm_num)
        _ ≤ 1/16 := by norm_num
    have he := JetEscapedEnvelope.epsilon_small hK hd₀.le hs hss hsmall
    exact (color_le_amplitude hK hα hγ hs hd hdmax ht (htmax.trans (by norm_num)) he η i.positive
      (JetSpatialBox.shifted x i.lattice) v (hU i v)).trans
        (amplitude_le_finite hs₀ hK hd₀ η α hi)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A fixed-truncation bound for the full periodic cold sum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def coldNormBound (s₀ η K α d₀ : ℝ) (N : ℕ) : ℝ :=
  finiteAmplitude s₀ η K α d₀ N+
    JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)

theorem coldNormBound_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 < d₀) (η α : ℝ) (N : ℕ) : 0 ≤ coldNormBound s₀ η K α d₀ N :=
  add_nonneg (finiteAmplitude_nonneg hs₀ hK hd₀ η α N)
    (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)

theorem cold_sum_bound {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight
      (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) u)
    (hperiodic : ∀ n, pull (displacement n) F = F) :
    ∀ t ∈ Ioc 0 T, ∀ p : JetPrototype.Phase,
      (∑' i, cold s₀ η K α γ d₀ q b L T N F i (t,p)) ≤ coldNormBound s₀ η K α d₀ N := by
  let c := cold s₀ η K α γ d₀ q b L T N F
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc (i : JetLattice.Label) := coldLimit_solution hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N i) hF (hi.1 i) hF₀ hFeq
  have hcs (u) := WeightedLocal.cold_family_summable hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hi.1 hF₀ hi.2 hFeq u
  intro t ht p
  obtain ⟨n,x,hx,he⟩ := exists_shift_in_cell p.1
  have hp : shift (displacement n) p = (JetPeriodicDatum.spatialMap x,p.2) := Prod.ext he rfl
  have hU (i : JetLattice.Label) (v : Velocity) :
      VelocityWeight.H q v*c i (t,(JetPeriodicDatum.spatialMap x,v)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,v) :=
    cold_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq hb hL hT hR
      (hTmax.trans (by norm_num)) hloss N hh₀ hFm hF hF₀ hFeq i ht (JetPeriodicDatum.spatialMap x,v)
  have hz (i : JetLattice.Label) (hi : ¬i.annulus < N) (v : Velocity) :
      c i (t,(JetPeriodicDatum.spatialMap x,v)) = 0 :=
    congrFun (cold_zero s₀ η K α γ d₀ q b L T N F i hi) _
  have hbound := cell_cold_sum_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    ht.1 (ht.2.trans hTmax) hsmall N x hx
    (fun i v => c i (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun i v => ((hc i).2.1 (t,(JetPeriodicDatum.spatialMap x,v))).1)
    (fun v => (hcs (t,(JetPeriodicDatum.spatialMap x,v))).1) hz hU p.2
  have hshift : (∑' i, c i (t,shift (displacement n) p)) = ∑' i, c i (t,p) :=
    coldSum_shift n (hperiodic n) (t,p)
  rw [hp] at hshift
  change (∑' i, c i (t,p)) ≤ _
  rw [← hshift]
  exact hbound

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A fixed velocity majorant away from the small spatial annuli -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cell_outer_bound {s₀ η K α γ d₀ q t Z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N J : ℕ) (x : Velocity) (hx : x ∈ TorusChart.cube)
    (hxout : ∀ j : ℕ, J ≤ j → transverse x ∉ AnnularEnvelope.shell s₀ η j)
    (F : Velocity → ℝ) (c : Label → Velocity → ℝ)
    (hcn : ∀ i v, 0 ≤ c i v) (hcs : ∀ v, Summable (fun i => c i v))
    (hzero : ∀ i, ¬i.annulus < N → ∀ v, c i v = 0)
    (hU : ∀ i v, H q v*c i v ≤ JetSupersolution.U η K α γ (jetScale s₀ η i.annulus)
      (d₀*jetScale s₀ η i.annulus^10) t i.positive (JetSpatialBox.shifted x i.lattice,v))
    (hhot : ∀ᵐ v, F v-∑' i, c i v ≤ Z) :
    ∀ᵐ v, F v ≤ Z+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J := by
  have hx1 (k) : |x k| ≤ 1 := by
    have h := hx k
    exact (abs_le.mpr ⟨h.1.le,h.2⟩).trans (by norm_num)
  have he (v) : (∑' i, escaped s₀ η t N x (fun j => c j v) i) ≤
      escapedConstant s₀ η K α d₀ := by
    simpa only [Real.rpow_zero,mul_one,escapedConstant] using
      normalized_escaped_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht htmax
        hsmall 0 q N (fun j => c j v) x v hx1 (fun i => hcn i v) (hcs v)
        (fun i _ => hU i v)
  rcases main_or_outside hs₀ hsmax hη hηmax htmax N x with ⟨i,_,hi,hout⟩ | hout
  · have hiJ : i.annulus ≤ J := by
      have hh := enlargement_central_shell hs₀ hsmax hη htmax hx hi
      have hn : ¬J ≤ i.annulus := fun h => hxout _ h hh
      omega
    have hs : 0 < jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
    have hsbound := (JetEscapedTotal.scale_bound hs₀ hη i.annulus).trans hsmax
    have hd : 0 < d₀*jetScale s₀ η i.annulus^10 := by positivity
    have hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/16 :=
      JetEnvelopeGain.thermal_width_le hd₀max hs.le hsbound
    have hε := JetEscapedEnvelope.epsilon_small hK hd₀.le hs
      (JetEscapedTotal.scale_bound hs₀ hη _) hsmall
    filter_upwards [hhot] with v hv
    have hc := (color_le_amplitude hK hα hγ hs hd hdmax ht (htmax.trans (by norm_num)) hε
      η i.positive (JetSpatialBox.shifted x i.lattice) v (hU i v)).trans
      (amplitude_le_finite hs₀ hK hd₀ η α hiJ)
    have hsum := sum_sub_main (hcs v) (fun j hj => hzero j hj v) i hi hout
    have htail := he v
    linarith
  · filter_upwards [hhot] with v hv
    have hsum := sum_all_escaped (fun j hj => hzero j hj v) hout
    have htail := he v
    have ha := finiteAmplitude_nonneg hs₀ hK hd₀ η α J
    rw [hsum] at hv
    linarith

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The geometric cold family for an a.e. mild total solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def rebuilt (s₀ η K α γ d₀ q b L T : ℝ) (N : ℕ)
    (F : ℝ × JetPrototype.Phase → ℝ) : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ :=
  rebuiltColdFamily q b L T F (color s₀ η K α γ d₀ q N)

theorem rebuilt_envelope {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hTmax : T ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (i : JetLattice.Label) {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    physical q (rebuilt s₀ η K α γ d₀ q b L T N F i) (t,p) ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
        (shift (displacement i.lattice) p) := by
  have hi := (initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀).1
  have hcb (j) (p) : 0 ≤ color s₀ η K α γ d₀ q N j p ∧ color s₀ η K α γ d₀ q N j p ≤ R :=
    ⟨(hi j p).1,(hi j p).2.trans (hF₀ p)⟩
  have hc (j) := clippedCold_solution hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N j) hF (hcb j)
  have hn := (normalizedFamily_bounds (F := F) (fun j u => ((hc j).2.1 u).1) i (t,p)).2
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
  have he := clippedCold_shifted_envelope hq hb hL hT hR hloss hK hα hγ hs
    (mul_pos hd₀ (pow_pos hs _)) hTmax
    (JetEscapedEnvelope.epsilon_small hK hd₀.le hs (JetEscapedTotal.scale_bound hs₀ hη _) hsmall)
    η i.positive (displacement i.lattice) hFm (measurable_color s₀ η K α γ d₀ q N i) hF
    (hcb i) (physical_color_le hs₀ hK hd₀.le η α γ q N i) ht p
  exact (mul_le_mul_of_nonneg_left hn (VelocityWeight.H_nonneg q p.2)).trans he

theorem rebuilt_zero (s₀ η K α γ d₀ q b L T : ℝ) (N : ℕ)
    {F : ℝ × JetPrototype.Phase → ℝ} (hF : ∀ u, 0 ≤ F u)
    (i : JetLattice.Label) (hi : ¬i.annulus < N) :
    rebuilt s₀ η K α γ d₀ q b L T N F i = 0 := by
  have hz : color s₀ η K α γ d₀ q N i = 0 := by
    funext p
    simp only [color,ite_eq_right hi,Pi.zero_apply]
  apply normalizedFamily_zero F
  change clippedColdLimit q b L T F (color s₀ η K α γ d₀ q N i) = 0
  rw [hz,clippedColdLimit_zero q b L T hF]

theorem rebuilt_shift {s₀ η K α γ d₀ q b L T : ℝ} {N : ℕ}
    {F : ℝ × JetPrototype.Phase → ℝ} (n : JetLattice.Lattice)
    (hF : pull (displacement n) F = F) (i : JetLattice.Label) :
    pull (displacement n) (rebuilt s₀ η K α γ d₀ q b L T N F i) =
      rebuilt s₀ η K α γ d₀ q b L T N F (relabel n i) := by
  unfold rebuilt
  rw [← rebuiltColdFamily_pull,hF]
  have hc : (fun j p => color s₀ η K α γ d₀ q N j (shift (displacement n) p)) =
      (fun j => color s₀ η K α γ d₀ q N (relabel n j)) := by
    funext j p
    exact color_shift s₀ η K α γ d₀ q N n j p
  rw [hc,rebuiltColdFamily_reindex]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Fixed outer-annulus velocity bounds for the actual rebuilt positive solutions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.JetGeometry BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_cell_outer_bound {s₀ η K α γ d₀ q b L T R Z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N J : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight
        (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) (t,p)))
    {t : ℝ} (ht : t ∈ Ioc 0 T)
    (hsize : PhaseEssSup.size (fun p => F (t,p)-∑' i,
      rebuilt s₀ η K α γ d₀ q b L T N F i (t,p)) ≤ Z) :
    ∀ᵐ x : Velocity, x ∈ TorusChart.cube →
      (∀ j : ℕ, J ≤ j → transverse x ∉ AnnularEnvelope.shell s₀ η j) →
      ∀ᵐ v : Velocity, F (t,(JetPeriodicDatum.spatialMap x,v)) ≤
        Z+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J := by
  let c := rebuilt s₀ η K α γ d₀ q b L T N F
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ R := ⟨(hi.1 i p).1,(hi.1 i p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hc₀ hi.2 hFeq
  have hcn (i) (u) : 0 ≤ c i u := (hp.2.1 i u).1
  have hh := family_hot_bounds hq hb hR hloss hFm hp.1 hF hcn hp.2.2.1
  have hae := PhaseEssSup.ae_abs_le_size
    (hh.1.comp (measurable_const.prodMk measurable_id))
    (fun p => show |F (t,p)-∑' i, c i (t,p)| ≤ R from by
      change |F (t,p)-∑' i, rebuiltColdFamily q b L T F (color s₀ η K α γ d₀ q N) i (t,p)| ≤ R
      rw [abs_of_nonneg (hh.2.1 (t,p)).1]
      exact (hh.2.1 (t,p)).2)
  have hz : ∀ᵐ p ∂FlightMeasure.phaseVolume, F (t,p)-∑' i, c i (t,p) ≤ Z := by
    filter_upwards [hae] with p hp'
    exact (le_abs_self _).trans (hp'.trans hsize)
  have hm := JetPeriodicDatum.phaseMap_measurePreserving.quasiMeasurePreserving.ae hz
  rw [Measure.volume_eq_prod] at hm
  have hs := Measure.ae_ae_of_ae_prod hm
  filter_upwards [hs] with x hxhot
  intro hx hxout
  apply cell_outer_bound hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le hd₀ hd₀max
    ht.1 (ht.2.trans hTmax) hsmall N J x hx hxout
    (fun v => F (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun i v => c i (t,(JetPeriodicDatum.spatialMap x,v)))
  · exact fun i v => hcn i _
  · exact fun v => (hp.2.2.2.1 (t,(JetPeriodicDatum.spatialMap x,v))).1
  · intro i hi v
    exact congrFun (rebuilt_zero s₀ η K α γ d₀ q b L T N (fun u => (hF u).1) i hi) _
  · intro i v
    exact rebuilt_envelope hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall hq hb hL hT hR
      (hTmax.trans (by norm_num)) hloss N hh₀ hFm hF hF₀ i ht (JetPeriodicDatum.spatialMap x,v)
  · exact hxhot

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The geometric hot-source estimate in polynomial comparison form -/

noncomputable section

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem scalarMajorant_eq_source (s₀ η K α γ d₀ q : ℝ) (N m : ℕ) {t : ℝ}
    (ht : 0 < t) (z : ℝ) :
    scalarMajorant s₀ η K α γ d₀ q (m+1 : ℕ) N t z =
      ZeroProfile.source (2*JetMainGain.coefficient K α γ q) (2*HotApplication.realBound q)
        ((2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
          JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ)))
        (JetGeometry.jetScale s₀ η N) m t z := by
  unfold scalarMajorant ZeroProfile.source
  rw [Real.rpow_natCast,pow_succ t m,add_comm (JetGeometry.jetScale s₀ η N) t]
  have he (E : ℝ) : E*(t^m*t)/t = E*t^m := by
    field_simp [ne_of_gt ht]
  rw [he]
  ring

theorem tail_small {E T t : ℝ} {m : ℕ} (hE : 0 ≤ E) (ht : 0 ≤ t) (htT : t ≤ T)
    (hT : E*T^(m+1) ≤ 1) : E*t^(m+1) ≤ 1 :=
  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htT (m+1)) hE).trans hT

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
