import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedGeometricBlock
import OAI.MathematicalPhysics.Boltzmann.Branching.EndpointHistoryMass
import OAI.MathematicalPhysics.Boltzmann.Branching.MainPositiveRemainderBound
import OAI.MathematicalPhysics.Boltzmann.Branching.OccupationSliceIntegral
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseSliceLocalization
import OAI.MathematicalPhysics.Boltzmann.Branching.SmallFirstGain
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedOriginDeletion

namespace OAI

section

/-! # Axial spatial escape forces the actual positive fifth gain to vanish -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positive_five_axial_escape_tendsto {K α γ q a T V s₀ η d₀ : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (N : ℕ → ℕ) (z : ℕ → Published.KineticPhase)
    (ht : ∀ n, (z n).1.1 ∈ Icc a T) (hv : ∀ n, ‖(z n).2‖ ≤ V)
    (hx : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ k : Lattice,
      R ≤ |axial ((z n).1.2-(r n)⁻¹ • latticeVector k)|)
    {f : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hf : ∀ n y, y.1.1 ∈ Icc a T → f n y ≤ B) :
    Tendsto (fun n => iterate a (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n))
      (f n) 5 (z n)) atTop (𝓝 0) := by
  refine five_tendsto_of_small_first_mass
    (C := ENNReal.ofReal ((2*JetCoreSheet.growthConstant K α γ q)/a))
    (fun n => positiveMainKernel (r n) s₀ η K α γ d₀ q (N n)) ENNReal.ofReal_ne_top hB ?_ hf z ht ?_
  · intro n y hy
    apply (positiveMainKernel_bound (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
      (N n) y (ha.trans_le hy.1)).trans
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (JetCoreSheet.growthConstant_nonneg hK α γ q)) ha hy.1)
  · intro ε hε
    filter_upwards [selected_axial_escape_small hK hα hγ hq₁ hq₂ ha.le hs₀ hsmax
      hη hηmax hd₀ hdmax r hr N z ht hv hx (half_pos hε)] with n hn
    intro s hs
    have h := hn s hs
    change ((selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n) (flight (z n) s))+
      (selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n) (flight (z n) s))) univ ≤ _
    rw [Measure.add_apply]
    apply (add_le_add h h).trans_eq
    rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
    congr 1
    ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A positive bounded seed on a prescribed full-measure set of times -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

theorem exists_nonzero_phaseSlice {F : ℝ × Phase → ℝ} (hF : Measurable F)
    (a b : ℝ)
    (hne : (positiveDensityMeasure volume F).restrict (Prod.fst ⁻¹' Ioc a b) ≠ 0)
    {G : Set ℝ} (hG : ∀ᵐ t ∂volume, t ∈ G) :
    ∃ t ∈ Ioc a b, t ∈ G ∧ phaseSlice F t ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  apply Measure.measure_univ_eq_zero.mp
  have H := occupation_slice_lintegral hF a b (f := fun _ => 1) measurable_const
  simp only [lintegral_one] at H
  rw [H]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hG] with t ht htg
  rw [h t ht htg]
  simp

theorem exists_positive_seed_slice {F : ℝ × Phase → ℝ} (hF : Measurable F)
    (a b : ℝ)
    (hne : (positiveDensityMeasure volume F).restrict (Prod.fst ⁻¹' Ioc a b) ≠ 0)
    {G : Set ℝ} (hG : ∀ᵐ t ∂volume, t ∈ G) :
    ∃ t ∈ Ioc a b, t ∈ G ∧ ∃ n : ℕ, 0 < phaseSlice F t (seedPortion n) := by
  obtain ⟨t,ht,htG,htn⟩ := exists_nonzero_phaseSlice hF a b hne hG
  have hac : phaseSlice F t ≪ volume := by
    unfold phaseSlice positiveDensityMeasure
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨n,hn⟩ := exists_positive_seedPortion (phaseSlice F t) hac htn
  exact ⟨t,ht,htG,n,hn⟩

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Scalar exponential control of the actual positive Volterra inequality -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem iterate_unit_factorial_bound {T C B : ℝ} (hT : T ≤ 1) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (K : Kernel KineticPhase Velocity)
    (hK : ∀ z, z.1.1 ∈ Icc 0 T → K z univ ≤ ENNReal.ofReal C)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ∈ Icc 0 T → f z ≤ ENNReal.ofReal B)
    (n : ℕ) (z : KineticPhase) (hz : z.1.1 ∈ Icc 0 T) :
    iterate 0 K f n z ≤ ENNReal.ofReal (B*(C^n/(n.factorial:ℝ))) := by
  apply (iterate_factorial_bound hC hB K hK hf n z hz).trans
  apply ENNReal.ofReal_le_ofReal
  have ht : z.1.1^n ≤ 1 := pow_le_one₀ hz.1 (hz.2.trans hT)
  have hh := mul_le_mul_of_nonneg_left ht (mul_nonneg hB (pow_nonneg hC n))
  calc
    _ ≤ (B*C^n*1)/(n.factorial:ℝ) := div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)
    _ = _ := by ring

theorem sum_iterate_const_le_exp {T C c : ℝ} (hT : T ≤ 1) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (K : Kernel KineticPhase Velocity)
    (hK : ∀ z, z.1.1 ∈ Icc 0 T → K z univ ≤ ENNReal.ofReal C)
    (n : ℕ) (z : KineticPhase) (hz : z.1.1 ∈ Icc 0 T) :
    (∑ j ∈ Finset.range n, iterate 0 K (fun _ => ENNReal.ofReal c) j z) ≤
      ENNReal.ofReal (c*Real.exp C) := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal (c*(C^j/(j.factorial:ℝ))) :=
      Finset.sum_le_sum (fun j _ => iterate_unit_factorial_bound hT hC hc K hK
        (fun _ _ => le_rfl) j z hz)
    _ = ENNReal.ofReal (c*∑ j ∈ Finset.range n, C^j/(j.factorial:ℝ)) := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
      intro j _
      positivity
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hC n) hc)

end BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

open PositiveIteration

theorem positiveMain_exponential_bound (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q T C B c : ℝ) (N : ℕ)
    (hT : T ≤ 1) (hC : 0 ≤ C) (hB : 0 ≤ B) (hc : 0 ≤ c)
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f)
    (hfB : ∀ z, z.1.1 ∈ Icc 0 T → f z ≤ ENNReal.ofReal B)
    (hmass : ∀ z, z.1.1 ∈ Icc 0 T →
      positiveMainKernel r s₀ η K α γ d₀ q N z univ ≤ ENNReal.ofReal C)
    (h : ∀ t ∈ Icc 0 T, ∀ᵐ p : Velocity × Velocity, f ((t,p.1),p.2) ≤
      ENNReal.ofReal c+step 0 (positiveMainKernel r s₀ η K α γ d₀ q N) f ((t,p.1),p.2))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ p : Velocity × Velocity, f ((t,p.1),p.2) ≤ ENNReal.ofReal (c*Real.exp C) := by
  let J := positiveMainKernel r s₀ η K α γ d₀ q N
  have hall : ∀ᵐ p : Velocity × Velocity, ∀ n : ℕ,
      f ((t,p.1),p.2) ≤ ENNReal.ofReal (c*Real.exp C)+ENNReal.ofReal (B*(C^n/(n.factorial:ℝ))) := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [positiveMain_residual_on_slab hcarleman r s₀ η K α γ d₀ q 0 T N hf
      (ENNReal.ofReal c) h n ht] with p hp
    exact hp.trans (add_le_add (sum_iterate_const_le_exp hT hC hc J hmass n _ ht)
      (iterate_unit_factorial_bound hT hC hB J hmass hfB n _ ht))
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (c*Real.exp C)+
      ENNReal.ofReal (B*(C^n/(n.factorial:ℝ)))) atTop (𝓝 (ENNReal.ofReal (c*Real.exp C))) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((FloorSemiring.tendsto_pow_div_factorial_atTop C).const_mul B)
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero,add_zero] using tendsto_const_nhds.add hh
  filter_upwards [hall] with p hp
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds htend hp

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Positive finite endpoint histories transfer positive seed mass to the hot trace -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace BoltzmannNonuniqueness

theorem positive_endpoint_of_pointwise
    (K : Kernel (ℝ × WeakTime.Phase) WeakTime.Phase)
    (μ ν : Measure WeakTime.Phase) (s : ℝ) {A B : Set WeakTime.Phase}
    (hA : MeasurableSet A) (hmass : 0 < μ B)
    (hdom : K ∘ₘ WeakTime.phaseSeed s μ ≤ ν)
    (hpoint : ∀ p ∈ B, 0 < K (s,p) A) : 0 < ν A := by
  have hf : Measurable (fun p : WeakTime.Phase => K (s,p) A) :=
    (K.measurable_coe hA).comp (by fun_prop)
  have hp : 0 < ∫⁻ p, K (s,p) A ∂μ := (lintegral_pos_iff_support hf).mpr
    (hmass.trans_le (measure_mono (fun p hp => ne_of_gt (hpoint p hp))))
  have hh := hdom A
  rw [Measure.bind_apply hA K.aemeasurable,WeakTime.phaseSeed,
    lintegral_map (K.measurable_coe hA) (show Measurable (fun p : WeakTime.Phase => (s,p)) by fun_prop)] at hh
  exact hp.trans_le hh

theorem single_endpoint_history_le
    (K : Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase))
    (L : Kernel (ℝ × WeakTime.Phase) WeakTime.Phase)
    (μ : Measure (ℝ × WeakTime.Phase)) (ν : Measure WeakTime.Phase) (N : ℕ)
    (hdom : L ∘ₘ (∑ j ∈ Finset.range (N+1), (K^j) ∘ₘ μ) ≤ ν) :
    (L ∘ₖ (K^N)) ∘ₘ μ ≤ ν := by
  have hterm : (K^N) ∘ₘ μ ≤ ∑ j ∈ Finset.range (N+1), (K^j) ∘ₘ μ :=
    Finset.single_le_sum (f := fun j : ℕ => (K^j) ∘ₘ μ) (fun j _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_self N))
  rw [← Measure.comp_assoc]
  exact (KernelHistoryOrder.measure_comp_mono le_rfl hterm).trans hdom

open EuclideanFlight in
 theorem covered_hot_positive_history
    {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ} (hf : ∀ z, 0 ≤ f z)
    {β : WeakTime.Phase → ℝ} (hβ₁ : ∀ p, β p ≤ 1)
    (a U R s t : ℝ) {A B : Set WeakTime.Phase} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hβ : ∀ p ∈ B, β p = 1)
    (hcover : ∀ p ∈ tsupport β, hotCharacteristicEquiv (s,p) ∈
      JetCopyDatum.AttainedCapSequence.coldCylinderSet a U R)
    (K : Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase)) (C : ℝ) (N : ℕ)
    (hmass : 0 < hotPhaseSlice f s B)
    (hdom : WeakTime.phaseEndpointKernel C t ∘ₘ
      (∑ j ∈ Finset.range (N+1), (K^j) ∘ₘ WeakTime.phaseSeed s
        (WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a U R f)) s)) ≤
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a U R f)) t)
    (hpoint : ∀ p ∈ B, 0 < (WeakTime.phaseEndpointKernel C t ∘ₖ (K^N)) (s,p) A) :
    0 < hotPhaseSlice f t A := by
  have heq := cylinder_phaseSlice_eq_on (f := f) hB hβ hcover
  have hm : 0 < WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a U R f)) s B :=
    heq.symm ▸ hmass
  exact (positive_endpoint_of_pointwise _ _ _ s hA hm
    (single_endpoint_history_le K _ _ _ N hdom) hpoint).trans_le
      (cylinder_phaseSlice_le hf hβ₁ a U R t A)

end BoltzmannNonuniqueness

end

end

end OAI
