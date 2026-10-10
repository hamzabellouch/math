import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierActualInitializationBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierDataSelection_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma select_small_masses {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f g : Ω → ℝ}
    (hf : Integrable f P) (hg : Integrable g P)
    (hfn : ∀ sample, 0 ≤ f sample) (hgn : ∀ sample, 0 ≤ g sample)
    {A : Set Ω} (hA : MeasurableSet A) {W : Ω → Prop} (hW : ∀ᵐ sample ∂P, W sample)
    {η τ δ : ℝ} (hδ : 0 < δ) (hfm : (∫ sample, f sample ∂P) ≤ η)
    (hgm : (∫ sample, g sample ∂P) ≤ τ) (hbudget : η+τ/δ+P.real Aᶜ < 1) :
    ∃ sample, sample ∈ A ∧ W sample ∧ f sample < 1 ∧ g sample < δ := by
  let cost : Ω → ℝ := fun sample => f sample+g sample/δ+Aᶜ.indicator (fun _ => (1:ℝ)) sample
  have hi : Integrable (Aᶜ.indicator (fun _ : Ω => (1:ℝ))) P :=
    (integrable_const _).indicator hA.compl
  have hfg : Integrable (fun sample => f sample+g sample/δ) P := hf.add (hg.div_const δ)
  have hc : Integrable cost P := hfg.add hi
  have hcm : (∫ sample, cost sample ∂P) < 1 := by
    change (∫ sample, f sample+g sample/δ+Aᶜ.indicator (fun _ => (1:ℝ)) sample ∂P) < 1
    rw [integral_add hfg hi,integral_add hf (hg.div_const δ),
      integral_div,integral_indicator hA.compl,setIntegral_const,smul_eq_mul,mul_one]
    have hh := div_le_div_of_nonneg_right hgm hδ.le
    linarith
  obtain ⟨sample,hω,hcω⟩ := exists_notMem_null_le_integral hc (show P {sample | ¬ W sample} = 0 by
    simpa only [ae_iff] using hW)
  have hsmall : cost sample < 1 := hcω.trans_lt hcm
  have hgn' : 0 ≤ g sample/δ := div_nonneg (hgn sample) hδ.le
  have hin : 0 ≤ Aᶜ.indicator (fun _ => (1:ℝ)) sample := indicator_nonneg (fun _ _ => by norm_num) _
  have hmA : sample ∈ A := by
    by_contra hh
    have hi' : Aᶜ.indicator (fun _ : Ω => (1:ℝ)) sample = 1 := indicator_of_mem hh _
    dsimp only [cost] at hsmall
    rw [hi'] at hsmall
    linarith [hfn sample]
  refine ⟨sample,hmA,not_not.mp hω,?_,?_⟩
  · dsimp only [cost] at hsmall
    linarith
  · apply (div_lt_one hδ).mp
    dsimp only [cost] at hsmall
    linarith [hfn sample]

lemma IsNuclearBarrier.integrable_error_mass {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ a p : Ω → TFSpace → ℝ}
    {Z k B C r T η : ℝ} (old : IsNuclearBarrier P μ Z k B C r T η a p) :
    Integrable (fun sample => ∫ x, p sample x) P := by
  obtain ⟨L,hL⟩ := old.bounded_error
  exact (compactBound_integrable_prod old.measurable_error
    (nonneg_bounded_deterministicBound old.nonneg_error hL) old.support_error).integral_prod_left

theorem IsNuclearBarrier.select_data {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ a p : Ω → TFSpace → ℝ}
    {Z k B C r T η : ℝ} (old : IsNuclearBarrier P μ Z k B C r T η a p)
    {g : Ω → ℝ} (hg : Integrable g P) (hgn : ∀ sample, 0 ≤ g sample)
    {A : Set Ω} (hA : MeasurableSet A) {τ δ : ℝ} (hδ : 0 < δ)
    (hgm : (∫ sample, g sample ∂P) ≤ τ) (hbudget : η+τ/δ+P.real Aᶜ < 1) :
    ∃ sample, sample ∈ A ∧
      WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a sample x)
        (fun x => innerSource r (μ sample) (p sample) x+
          outerCoefficient r x*reaction k (nuclearField Z x+a sample x)) ∧
      (∫ x, p sample x) < 1 ∧ g sample < δ := by
  exact select_small_masses old.integrable_error_mass hg
    (fun sample => integral_nonneg (old.nonneg_error sample)) hgn hA old.weak hδ old.mass hgm hbudget

end Work_BarrierDataSelection_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

lemma nuclear_radius_le_of_relation {Z r s ε : ℝ} (hZ : 0 < Z) (hs : 0 ≤ s)
    (hrel : Z*r^3 = ε^3) (hscale : ε^3 ≤ Z*s^3) : r ≤ s := by
  apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hs
  apply (mul_le_mul_iff_right₀ hZ).mp
  simpa only [mul_comm r, mul_comm (s^3)] using hrel.le.trans hscale

structure InitialNumerics (Z : ℕ) (s ε G c δ : ℝ) : Prop where
  charge : 1 ≤ Z
  scale_pos : 0 < s
  scale_le : s ≤ 1
  radius_pos : 0 < ε*(Z:ℝ)^(-1/3:ℝ)
  radius_le : ε*(Z:ℝ)^(-1/3:ℝ) ≤ 1
  radius_scale : ε*(Z:ℝ)^(-1/3:ℝ) ≤ s
  radius_relation : (Z:ℝ)*(ε*(Z:ℝ)^(-1/3:ℝ))^3 = ε^3
  budget : 3*(Z:ℝ)*s^(-4:ℝ)+observationFisherConstant*(ε*(Z:ℝ)^(-1/3:ℝ))^(-2.02:ℝ)*
    (Real.log (Real.exp 1/(ε*(Z:ℝ)^(-1/3:ℝ))^40))^5+δ ≤ (Z:ℝ)^(7/3:ℝ)
  interpolation : (48*Real.pi*G*c⁻¹^3)*(ε*(Z:ℝ)^(-1/3:ℝ))^(1-3*masterExponent) ≤ 1/20

lemma initial_numerics_eventually {ι : Type*} {l : Filter ι}
    (Z : ι → ℕ) (s : ι → ℝ) (hZ : ∀ᶠ i in l, 1 ≤ Z i)
    (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hscale : Tendsto (fun i => (Z i:ℝ)*(s i)^3) l atTop)
    {ε : ℝ} (hε : 0 < ε) (G c δ : ℝ) :
    ∀ᶠ i in l, InitialNumerics (Z i) (s i) ε G c δ := by
  let r : ι → ℝ := fun i => ε*(Z i:ℝ)^(-1/3:ℝ)
  have hZr : ∀ᶠ i in l, 0 < (Z i:ℝ) := hZ.mono fun i hi => by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hi)
  have hr : ∀ᶠ i in l, 0 < r i := hZr.mono fun i hi => mul_pos hε (Real.rpow_pos_of_pos hi _)
  have hrel : ∀ᶠ i in l, (Z i:ℝ)*(r i)^3 = ε^3 :=
    hZr.mono fun _ hi => nuclear_radius_relation hi
  have hr0 : Tendsto r l (𝓝 0) := nuclear_radius_tendsto hs0 hs hscale ε
  have hr1 : ∀ᶠ i in l, r i ≤ 1 :=
    (hr0.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))).mono fun _ hi => hi.le
  have hs1 : ∀ᶠ i in l, s i ≤ 1 :=
    (hs0.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))).mono fun _ hi => hi.le
  have hrs : ∀ᶠ i in l, r i ≤ s i := by
    filter_upwards [hZr,hs,hrel,hscale.eventually (eventually_ge_atTop (ε^3))] with i hz hs hr hh
    exact nuclear_radius_le_of_relation hz hs.le hr hh
  have hbudget := initial_budget_eventually hε hZr hs hr hrel hr0 hscale δ
  have hinterp := initial_interpolation_eventually hr0 (48*Real.pi*G*c⁻¹^3)
  filter_upwards [hZ,hs,hr,hr1,hs1,hrs,hrel,hbudget,hinterp] with i hz hs hr hr1 hs1 hrs hrel hb hi
  exact ⟨hz,hs,hs1,hr,hr1,hrs,hrel,hb,hi⟩

def HasActualInitialBarrier (Z : ℕ) (s ε k B c δ : ℝ) (g : Space → ℝ) : Prop :=
  let r₀ := ε*(Z:ℝ)^(-1/3:ℝ)
  ∀ N : ℕ, PriceMinimizes (energy Z) (s^(-4:ℝ)) N →
    ∀ K j : ℕ, ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∃ a p : OriginalDatum N K (fun k => dyadicObservationWidth r₀ k) j → TFSpace → ℝ,
        IsNuclearBarrier
          ((physicalObservationLaw (graphRawLaw F) K).map
            (originalDatum (fun k => dyadicObservationWidth r₀ k) j))
          (jointMasterPosterior (graphRawLaw F) (fun k => dyadicObservationWidth r₀ k) j c r₀ s g)
          (Z:ℝ) k B (max B (32*ε^3)) r₀ 2 (5184*r₀^32) a p

lemma hasActualInitialBarrier_of_numerics {Z : ℕ} {s ε k B c δ G : ℝ}
    (hn : InitialNumerics Z s ε G c δ) (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 0 ≤ k) (hB : 0 < B) (hδ : 0 < δ)
    (hed : initialDensityConstant*ε^(6/5:ℝ) < 1/20)
    (hq : 4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20)
    (hBs : B ≤ ε^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hG : ∀ z, (g z)^2 ≤ G) (hgn : ∫ z, (g z)^2 = 1)
    (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    HasActualInitialBarrier Z s ε k B c δ g := by
  intro N hN K j
  exact (actual_initial_barrier Z hn.charge (Real.rpow_pos_of_pos hn.scale_pos _)
    hn.radius_pos hn.radius_le hn.scale_pos hn.scale_le hn.radius_scale hc hc1
    hε hε1 hk hB hn.radius_relation hed hq hBs hsub hN K j hδ hn.budget hn.interpolation
    hg hcg hG hgn hrad hgs).2

theorem actual_initial_barrier_eventually {ι : Type*} {l : Filter ι}
    (Z : ι → ℕ) (s : ι → ℝ) (hZ : ∀ᶠ i in l, 1 ≤ Z i)
    (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hscale : Tendsto (fun i => (Z i:ℝ)*(s i)^3) l atTop)
    {c₁ k δ : ℝ} (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) (hk : 0 ≤ k) (hδ : 0 < δ)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ ε B : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < B ∧
      ∀ᶠ i in l, HasActualInitialBarrier (Z i) (s i) ε k B c₁ δ g := by
  obtain ⟨ε,hε,hε1,hed,hq⟩ := exists_barrier_epsilon k
  obtain ⟨B,hB,hBs,hsub⟩ := exists_barrier_B (k := k) hε
  refine ⟨ε,B,hε,hε1,hB,?_⟩
  obtain ⟨z,hz⟩ := (hg.continuous.pow 2).norm.exists_forall_ge_of_hasCompactSupport hcg.mul_left.norm
  let G : ℝ := ‖(g z)^2‖
  have hG (y : Space) : (g y)^2 ≤ G := by
    have he : (g y)^2 = ‖(g y)^2‖ := (Real.norm_of_nonneg (sq_nonneg _)).symm
    rw [he]
    exact hz y
  filter_upwards [initial_numerics_eventually Z s hZ hs hs0 hscale hε G c₁ δ] with i hi
  exact hasActualInitialBarrier_of_numerics hi hc hc1 hε hε1.le hk hB hδ hed hq hBs hsub
    hg hcg hG hgn hrad hgs

end CoulombBarrier

end

end OAI
