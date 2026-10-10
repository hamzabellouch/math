import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierSpatialNetBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierQuantitativeStepBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierActualInitialization_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem actual_initial_barrier (Z : ℕ) (hZ : 1 ≤ Z)
    {lam r₀ s c₁ ε k B : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hr1 : r₀ ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hrs : r₀ ≤ s) (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 0 ≤ k) (hB : 0 < B)
    (hrel : (Z:ℝ)*r₀^3 = ε^3)
    (heps : initialDensityConstant*ε^(6/5:ℝ) < 1/20)
    (hquad : 4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20)
    (hBsmall : B ≤ ε^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {N : ℕ} (hN : PriceMinimizes (energy Z) lam N) (K j : ℕ) {δ G : ℝ} (hδ : 0 < δ)
    (hbudget : 3*(Z:ℝ)*lam+observationFisherConstant*r₀^(-2.02:ℝ)*
      (Real.log (Real.exp 1/r₀^40))^5+δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hinterp : (48*Real.pi*G*c₁⁻¹^3)*r₀^(1-3*masterExponent) ≤ 1/20)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hG : ∀ z, (g z)^2 ≤ G) (hgn : ∫ z, (g z)^2 = 1)
    (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    N ≤ 3*Z ∧ ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∃ a p : OriginalDatum N K (fun k => dyadicObservationWidth r₀ k) j → TFSpace → ℝ,
        IsNuclearBarrier
          ((physicalObservationLaw (graphRawLaw F) K).map
            (originalDatum (fun k => dyadicObservationWidth r₀ k) j))
          (jointMasterPosterior (graphRawLaw F) (fun k => dyadicObservationWidth r₀ k) j c₁ r₀ s g)
          (Z:ℝ) k B (max B (32*ε^3)) r₀ 2 (5184*r₀^32) a p := by
  have hZr : 0 < (Z:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hZ)
  have hsmall := initial_density_small_of_nuclear_relation hZr hr hε hrel heps
  obtain ⟨hcount,F,hn,hF,A,hA,hgood,hbad⟩ := actual_initial_good_event Z hZ hlam hr hr1 hs hs1 hrs hc hc1
    hN K j hδ hbudget hsmall hinterp hg hcg hG hgn hrad hgs
  let := graphRawLaw_probability F hn
  let ell : Fin K → ℝ := fun l => dyadicObservationWidth r₀ l
  let μ := jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g
  let P := (physicalObservationLaw (graphRawLaw F) K).map (originalDatum ell j)
  have hP : IsProbabilityMeasure P := inferInstance
  let := hP
  let A' : Set (OriginalDatum N K ell j) := A
  have hAm : MeasurableSet A' := hA
  have hbad' : P.real A'ᶜ ≤ 1728*r₀^37 := by
    change ((physicalObservationLaw (graphRawLaw F) K).map (originalDatum ell j)).real A'ᶜ ≤ _
    rw [map_measureReal_apply (originalDatum_measurable ell j) hAm.compl]
    exact hbad
  obtain ⟨M,hM,hMb⟩ := jointMasterPosterior_global_bound (graphRawLaw F) ell j hc hr hs hrs hg.continuous hcg
  have hμm : Measurable (Function.uncurry μ) := jointMasterPosterior_measurable (graphRawLaw F) ell j hc hr hs hg.continuous
  have hμn : ∀ z y, 0 ≤ μ z y := jointMasterPosterior_nonneg (graphRawLaw F) ell j c₁ r₀ s g
  have hμb : ∀ z y, μ z y ≤ M := fun z y => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hMb z y)
  have hμi : ∀ z, Integrable (μ z) := jointMasterPosterior_integrable (graphRawLaw F) ell j hc hr hs hg.continuous hgn
  have hμc : ∀ z, ∫ y, μ z y ≤ (N:ℝ) := fun z =>
    (jointMasterPosterior_mass (graphRawLaw F) ell j hc hr hs hg.continuous hgn z).le
  have hi := initial_barrier_invariant hAm hμm hM (Nat.cast_nonneg N) hZr hB hr hr1 hε hε1 hk
    hrel hquad hBsmall hsub hμn hμb hμi hμc (by exact_mod_cast hcount) hgood hbad'
  exact ⟨hcount,F,hn,hF,_,_,hi⟩

end Work_BarrierActualInitialization_barrier_scope

section Work_BarrierPullback_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis CoulombObservation

lemma IsNuclearBarrier.pullback {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {f : Ω → Ω'} (hf : Measurable f)
    {μ a p : Ω' → TFSpace → ℝ} {Z k B C r T η : ℝ}
    (old : IsNuclearBarrier (P.map f) μ Z k B C r T η a p) :
    IsNuclearBarrier P (fun sample => μ (f sample)) Z k B C r T η
      (fun sample => a (f sample)) (fun sample => p (f sample)) := by
  refine ⟨old.measurable_offset.comp (hf.prodMap measurable_id),?_,?_,
    old.measurable_error.comp (hf.prodMap measurable_id),
    fun sample x => old.nonneg_error (f sample) x,?_,
    fun sample x hx => old.support_error (f sample) x hx,?_,
    fun sample x hx => old.lower (f sample) x hx,
    fun sample x hx => old.upper (f sample) x hx,
    fun sample x hx => old.tail (f sample) x hx,?_⟩
  · intro x
    obtain ⟨L,t,ht,hL⟩ := old.uniform_lipschitz_offset x
    exact ⟨L,t,ht,fun sample => hL (f sample)⟩
  · intro K hK
    obtain ⟨L,hL⟩ := old.bound_offset K hK
    exact ⟨L,fun sample x hx => hL (f sample) x hx⟩
  · obtain ⟨L,hL⟩ := old.bounded_error
    exact ⟨L,fun sample x => hL (f sample) x⟩
  · exact ae_of_ae_map hf.aemeasurable old.weak
  · have hm : AEStronglyMeasurable (fun sample => ∫ x, p sample x) (P.map f) :=
      old.measurable_error.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    rw [←integral_map hf.aemeasurable hm]
    exact old.mass

end Work_BarrierPullback_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem original_finite_barrier_iteration {N K J : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1)
    {Z κ B C M lam1 lam2 e ξ Cinv hl hh T η A Q lam : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh)
    (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (good : ℕ → (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → Prop)
    [∀ j, DecidablePred (good j)] (hgood : ∀ j < J, MeasurableSet {sample | good j sample})
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
    (initial : IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell 0 c₁ r₀ s g) Z κ B C r₀ T η a p)
    (hcap : ∀ j < J, ∀ sample, good j sample → ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 4*M*((2:ℝ)^j*r₀) →
      nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x ≤ C/‖x‖^4)
    (hinv : ∀ j < J, ∀ sample, good j sample → ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 4*M*((2:ℝ)^j*r₀) →
      InverseComparisonAt ‖x‖
        (nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x)
        (originalMasterField μ ell j c₁ r₀ s g sample x) κ hl hh ξ Cinv)
    (hprob : ∀ j < J, (physicalObservationLaw μ K).real {sample | ¬good j sample} ≤ A*((2:ℝ)^j*r₀)^25)
    (hmoment : ∀ j < J, ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 2*((2:ℝ)^j*r₀) →
      (∫ sample, (originalMasterField μ ell j c₁ r₀ s g sample x)^2 ∂physicalObservationLaw μ K) ≤
        Q*((2:ℝ)^j*r₀)^(-12-6*masterExponent)) :
    ∃ a' p', IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell J c₁ r₀ s g) Z κ B C ((2:ℝ)^J*r₀) (max T M)
      (η+∑ j ∈ Finset.range J, (32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*
        ((2:ℝ)^j*r₀)^barrierErrorExponent) a' p' := by
  have hall : ∀ j ≤ J, ∃ a' p', IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell j c₁ r₀ s g) Z κ B C ((2:ℝ)^j*r₀) (max T M)
      (η+∑ i ∈ Finset.range j, (32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*
        ((2:ℝ)^i*r₀)^barrierErrorExponent) a' p' := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨a,p,by simpa only [pow_zero,one_mul,Finset.sum_range_zero,add_zero] using
        initial.mono_tail hr₀.le (le_max_left T M)⟩
    | succ j ih =>
      intro hj
      have hjJ : j < J := Nat.lt_of_succ_le hj
      obtain ⟨aj,pj,hjbar⟩ := ih (Nat.le_of_lt hjJ)
      obtain ⟨a',p',hnew⟩ := original_quantitative_barrier_step μ ell j hc hr₀ hs hrs hg hcg hgn
        cal (by positivity : 0 < (2:ℝ)^j*r₀) hA hQ (good j) (hgood j hjJ) hjbar
        (hcap j hjJ) (hinv j hjJ) (hprob j hjJ) (hmoment j hjJ)
      refine ⟨a',p',?_⟩
      have hnew' := hnew.mono_tail (by positivity : 0 ≤ 2*((2:ℝ)^j*r₀)) (le_max_right T M)
      convert hnew' using 1 <;> simp only [Finset.sum_range_succ,pow_succ] <;> ring
  exact hall J le_rfl

end CoulombBarrier

end

end OAI
