import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitialBoundsBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierInitialLipschitz_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis

lemma bounded_density_potential_locallyLipschitz {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M r : ℝ} (hM : 0 ≤ M) (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hs : Function.support ρ ⊆ ball 0 r) : LocallyLipschitz (tfPotential ρ) := by
  intro x
  let S := max r (‖x‖+1)
  have hS : 0 < S := (by positivity : (0:ℝ) < ‖x‖+1).trans_le (le_max_right _ _)
  have hxS : ‖x‖ < S := (by linarith : ‖x‖ < ‖x‖+1).trans_le (le_max_right _ _)
  let K : NNReal := ⟨8*Real.pi*M*S,by positivity⟩
  refine ⟨K,ball 0 S,isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxS),?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy z hz
  rw [Real.dist_eq,dist_eq_norm]
  change |tfPotential ρ y-tfPotential ρ z| ≤ (8*Real.pi*M*S)*‖y-z‖
  exact bounded_density_potential_difference hm hM hS hn hb
      (hs.trans (ball_subset_ball (le_max_left _ _))) y z
      (mem_ball_zero_iff.mp hy).le (mem_ball_zero_iff.mp hz).le

lemma initialOffset_locallyLipschitz {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M R : ℝ} (hM : 0 ≤ M) (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hs : Function.support ρ ⊆ ball 0 R) (Z r a : ℝ) :
    LocallyLipschitz (initialOffset Z r a ρ) := by
  have hq : ContDiff ℝ 1 (fun x : TFSpace => a*‖x‖^2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  exact ((bounded_density_potential_locallyLipschitz hm hM hn hb hs).neg.sub
    (LocallyLipschitz.const ((7/10)*Z/r))).add hq.locallyLipschitz

lemma locallyLipschitz_comp_contDiffAt {E : Type*} [PseudoMetricSpace E]
    {g : E → ℝ} (hg : LocallyLipschitz g) {f : ℝ → ℝ}
    (hf : ∀ x, ContDiffAt ℝ 1 f (g x)) : LocallyLipschitz (f ∘ g) := by
  intro x
  obtain ⟨Kg,t,ht,hgL⟩ := hg x
  obtain ⟨Kf,u,hu,hfL⟩ := (hf x).exists_lipschitzOnWith
  exact ⟨Kf*Kg,t ∩ g ⁻¹' u,inter_mem ht (hg.continuous.continuousAt hu),
    hfL.comp (hgL.mono inter_subset_left) ((mapsTo_preimage g u).mono_left inter_subset_right)⟩

lemma outerOffset_locallyLipschitz (Z B : ℝ) {r : ℝ} (hr : 0 < r) :
    LocallyLipschitz (outerOffset Z B r) := by
  let f : ℝ → ℝ := fun t => B/t^4*(1-r/(8*t))-Z/t
  have hm : LocallyLipschitz (fun x : TFSpace => max r ‖x‖) :=
    lipschitzWith_one_norm.locallyLipschitz.const_max r
  apply locallyLipschitz_comp_contDiffAt hm (f := f)
  intro x
  have hp : 0 < max r ‖x‖ := hr.trans_le (le_max_left _ _)
  dsimp [f]
  fun_prop (disch := positivity)

lemma lipschitz_nhds_congr {u v : TFSpace → ℝ} {x : TFSpace}
    (hu : ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K u t) (he : u =ᶠ[𝓝 x] v) :
    ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K v t := by
  obtain ⟨K,t,ht,hL⟩ := hu
  refine ⟨K,t ∩ {y | u y = v y},inter_mem ht he,?_⟩
  intro y hy z hz
  change edist (v y) (v z) ≤ _
  rw [←hy.2,←hz.2]
  exact hL hy.1 hz.1

lemma cutMaximum_locallyLipschitz {u v : TFSpace → ℝ} {r t L R : ℝ}
    (hrt : r < t) (htL : t < L) (hLR : L < R)
    (hlo : ∀ x, r ≤ ‖x‖ → ‖x‖ < t → v x ≤ u x)
    (hhi : ∀ x, L < ‖x‖ → ‖x‖ < R → u x ≤ v x)
    (hu : LocallyLipschitz u) (hv : LocallyLipschitz v) :
    LocallyLipschitz (cutMaximum r R u v) := by
  intro x
  by_cases hx : ‖x‖ < t
  · apply lipschitz_nhds_congr (hu x)
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact (cutMaximum_inner htL hLR hlo hy).symm
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      apply lipschitz_nhds_congr (hu.max hv x)
      filter_upwards [((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hx',hR⟩] with y hy
      exact (cutMaximum_middle hy.1 hy.2).symm
    · have hL : L < ‖x‖ := hLR.trans_le (le_of_not_gt hR)
      apply lipschitz_nhds_congr (hv x)
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hL] with y hy
      exact (cutMaximum_outer hrt htL hhi hy).symm

lemma initializedOffset_locallyLipschitz {Z B r a M : ℝ} (hZ : 0 < Z)
    (hr : 0 < r) (ha : 0 ≤ a) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hquad : 4*a*r^2 ≤ Z/(20*r)) (hBsmall : B ≤ Z*r^3/10)
    {ρ : TFSpace → ℝ} (hm : Measurable ρ) (hn : ∀ x, 0 ≤ ρ x)
    (hb : ∀ x, ρ x ≤ M) (hs : Function.support ρ ⊆ ball 0 r)
    (hgood : ∀ x, r ≤ ‖x‖ → ‖x‖ ≤ (53/50)*r → tfPotential ρ x ≤ Z/(10*r)) :
    LocallyLipschitz (initializedOffset Z B r a ρ) := by
  apply cutMaximum_locallyLipschitz (t := (53/50)*r) (L := (19/10)*r)
    (by linarith) (by linarith) (by linarith) _ _
    (initialOffset_locallyLipschitz hm hM hn hb hs Z r a) (outerOffset_locallyLipschitz Z B hr)
  · intro x hx hx'
    have hh := initial_lower_overlap hZ hr ha hB hBsmall hx hx'.le (hgood x hx hx'.le)
    rw [←nuclear_outerOffset_eq (Z := Z) hx] at hh
    change nuclearField Z x+outerOffset Z B r x < nuclearField Z x+initialOffset Z r a ρ x at hh
    linarith
  · intro x hx hx'
    have hx0 : r ≤ ‖x‖ := by linarith
    have hh := initial_branch_negative hZ hr ha hquad hx hx'.le (tfPotential_nonneg (ae_of_all _ hn) x)
    have ho := (outerBarrier_bounds hB hr hx0).1
    have hp : 0 ≤ (7*B/8)/‖x‖^4 := by positivity
    rw [←nuclear_outerOffset_eq (Z := Z) hx0] at ho
    change nuclearField Z x+initialOffset Z r a ρ x < 0 at hh
    linarith

end Work_BarrierInitialLipschitz_barrier_scope

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis

def DeterministicLocalLipschitz {Ω : Type*} (u : Ω → TFSpace → ℝ) : Prop :=
  ∀ x, ∃ K : NNReal, ∃ t ∈ 𝓝 x, ∀ sample, LipschitzOnWith K (u sample) t

lemma DeterministicLocalLipschitz.locallyLipschitz {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (h : DeterministicLocalLipschitz u) (sample : Ω) : LocallyLipschitz (u sample) := by
  intro x
  obtain ⟨K,t,ht,hL⟩ := h x
  exact ⟨K,t,ht,hL sample⟩

lemma deterministicLip_spatial {Ω : Type*} {u : TFSpace → ℝ} (h : LocallyLipschitz u) :
    DeterministicLocalLipschitz (fun _ : Ω => u) := by
  intro x
  obtain ⟨K,t,ht,hL⟩ := h x
  exact ⟨K,t,ht,fun _ => hL⟩

lemma DeterministicLocalLipschitz.neg {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (h : DeterministicLocalLipschitz u) : DeterministicLocalLipschitz (fun sample x => -u sample x) := by
  intro x
  obtain ⟨K,t,ht,hL⟩ := h x
  exact ⟨K,t,ht,fun sample => (hL sample).neg⟩

lemma DeterministicLocalLipschitz.add {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample x => u sample x+v sample x) := by
  intro x
  obtain ⟨Ku,t,ht,hLu⟩ := hu x
  obtain ⟨Kv,s,hs,hLv⟩ := hv x
  refine ⟨Ku+Kv,t ∩ s,inter_mem ht hs,fun sample => ?_⟩
  exact ((hLu sample).mono inter_subset_left).add ((hLv sample).mono inter_subset_right)

lemma DeterministicLocalLipschitz.sub {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample x => u sample x-v sample x) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

lemma DeterministicLocalLipschitz.max {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample x => max (u sample x) (v sample x)) := by
  intro x
  obtain ⟨Ku,t,ht,hLu⟩ := hu x
  obtain ⟨Kv,s,hs,hLv⟩ := hv x
  refine ⟨Max.max Ku Kv,t ∩ s,inter_mem ht hs,fun sample => ?_⟩
  exact lipschitzOnWith_iff_restrict.mpr
    (((hLu sample).mono inter_subset_left).to_restrict.max ((hLv sample).mono inter_subset_right).to_restrict)

lemma deterministicLip_local_congr {Ω : Type*} {u v : Ω → TFSpace → ℝ} {x : TFSpace}
    (hu : ∃ K : NNReal, ∃ t ∈ 𝓝 x, ∀ sample, LipschitzOnWith K (u sample) t)
    (he : ∀ᶠ y in 𝓝 x, ∀ sample, u sample y = v sample y) :
    ∃ K : NNReal, ∃ t ∈ 𝓝 x, ∀ sample, LipschitzOnWith K (v sample) t := by
  obtain ⟨K,t,ht,hL⟩ := hu
  refine ⟨K,t ∩ {y | ∀ sample, u sample y = v sample y},inter_mem ht he,fun sample y hy z hz => ?_⟩
  change edist (v sample y) (v sample z) ≤ _
  rw [←hy.2 sample,←hz.2 sample]
  exact hL sample hy.1 hz.1

lemma cutMaximum_deterministicLip {Ω : Type*} {u v : Ω → TFSpace → ℝ} {r t L R : ℝ}
    (hrt : r < t) (htL : t < L) (hLR : L < R)
    (hlo : ∀ sample x, r ≤ ‖x‖ → ‖x‖ < t → v sample x ≤ u sample x)
    (hhi : ∀ sample x, L < ‖x‖ → ‖x‖ < R → u sample x ≤ v sample x)
    (hu : DeterministicLocalLipschitz u) (hv : DeterministicLocalLipschitz v) :
    DeterministicLocalLipschitz (fun sample => cutMaximum r R (u sample) (v sample)) := by
  intro x
  by_cases hx : ‖x‖ < t
  · apply deterministicLip_local_congr (hu x)
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact fun sample => (cutMaximum_inner htL hLR (hlo sample) hy).symm
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      apply deterministicLip_local_congr (hu.max hv x)
      filter_upwards [((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hx',hR⟩] with y hy
      exact fun sample => (cutMaximum_middle hy.1 hy.2).symm
    · have hL : L < ‖x‖ := hLR.trans_le (le_of_not_gt hR)
      apply deterministicLip_local_congr (hv x)
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hL] with y hy
      exact fun sample => (cutMaximum_outer hrt htL (hhi sample) hy).symm

lemma bounded_density_potential_deterministicLip {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) {M r : ℝ} (hM : 0 ≤ M)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hs : ∀ sample, Function.support (ρ sample) ⊆ ball 0 r) :
    DeterministicLocalLipschitz (fun sample => tfPotential (ρ sample)) := by
  intro x
  let S := max r (‖x‖+1)
  have hS : 0 < S := (by positivity : (0:ℝ) < ‖x‖+1).trans_le (le_max_right _ _)
  have hxS : ‖x‖ < S := (by linarith : ‖x‖ < ‖x‖+1).trans_le (le_max_right _ _)
  let K : NNReal := ⟨8*Real.pi*M*S,by positivity⟩
  refine ⟨K,ball 0 S,isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxS),fun sample => ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy z hz
  rw [Real.dist_eq,dist_eq_norm]
  change |tfPotential (ρ sample) y-tfPotential (ρ sample) z| ≤ (8*Real.pi*M*S)*‖y-z‖
  exact bounded_density_potential_difference (hm sample) hM hS (hn sample) (hb sample)
    ((hs sample).trans (ball_subset_ball (le_max_left _ _))) y z
    (mem_ball_zero_iff.mp hy).le (mem_ball_zero_iff.mp hz).le

lemma average_locallyLipschitz {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {u : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (hL : DeterministicLocalLipschitz u) : LocallyLipschitz (fun x => ∫ sample, u sample x ∂P) := by
  intro x
  obtain ⟨K,t,ht,hKt⟩ := hL x
  refine ⟨K,t,ht,?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy z hz
  rw [dist_eq_norm,←integral_sub (deterministicBound_integrable_section hm hb y)
    (deterministicBound_integrable_section hm hb z)]
  calc
    _ ≤ ∫ _ : Ω, (K:ℝ)*dist y z ∂P := norm_integral_le_of_norm_le (integrable_const _)
      (Eventually.of_forall fun sample => by
        simpa only [dist_eq_norm] using (hKt sample).dist_le_mul y hy z hz)
    _ = (K:ℝ)*dist y z := by simp

lemma initialOffset_deterministicLip {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) {M R : ℝ} (hM : 0 ≤ M)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hs : ∀ sample, Function.support (ρ sample) ⊆ ball 0 R) (Z r a : ℝ) :
    DeterministicLocalLipschitz (fun sample => initialOffset Z r a (ρ sample)) := by
  have hq : ContDiff ℝ 1 (fun x : TFSpace => a*‖x‖^2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  exact ((bounded_density_potential_deterministicLip hm hM hn hb hs).neg.sub
    (deterministicLip_spatial (LocallyLipschitz.const ((7/10)*Z/r)))).add
    (deterministicLip_spatial hq.locallyLipschitz)

lemma initializedOffset_deterministicLip {Ω : Type*} {Z B r a M : ℝ}
    (hZ : 0 < Z) (hr : 0 < r) (ha : 0 ≤ a) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hquad : 4*a*r^2 ≤ Z/(20*r)) (hBsmall : B ≤ Z*r^3/10)
    {ρ : Ω → TFSpace → ℝ} (hm : ∀ sample, Measurable (ρ sample))
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hs : ∀ sample, Function.support (ρ sample) ⊆ ball 0 r)
    (hgood : ∀ sample x, r ≤ ‖x‖ → ‖x‖ ≤ (53/50)*r → tfPotential (ρ sample) x ≤ Z/(10*r)) :
    DeterministicLocalLipschitz (fun sample => initializedOffset Z B r a (ρ sample)) := by
  apply cutMaximum_deterministicLip (t := (53/50)*r) (L := (19/10)*r)
    (by linarith) (by linarith) (by linarith) _ _
    (initialOffset_deterministicLip hm hM hn hb hs Z r a)
    (deterministicLip_spatial (outerOffset_locallyLipschitz Z B hr))
  · intro sample x hx hx'
    have hh := initial_lower_overlap hZ hr ha hB hBsmall hx hx'.le (hgood sample x hx hx'.le)
    rw [←nuclear_outerOffset_eq (Z := Z) hx] at hh
    change nuclearField Z x+outerOffset Z B r x < nuclearField Z x+initialOffset Z r a (ρ sample) x at hh
    linarith
  · intro sample x hx hx'
    have hx0 : r ≤ ‖x‖ := by linarith
    have hh := initial_branch_negative hZ hr ha hquad hx hx'.le
      (tfPotential_nonneg (ae_of_all _ (hn sample)) x)
    have ho := (outerBarrier_bounds hB hr hx0).1
    have hp : 0 ≤ (7*B/8)/‖x‖^4 := by positivity
    rw [←nuclear_outerOffset_eq (Z := Z) hx0] at ho
    change nuclearField Z x+initialOffset Z r a (ρ sample) x < 0 at hh
    linarith

lemma conditionalField_deterministicLip {Ω D : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace D]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → D)
    {u : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry u))
    (hb : DeterministicLocalBound u) (hL : DeterministicLocalLipschitz u) :
    DeterministicLocalLipschitz (conditionalField P X u) := by
  intro x
  obtain ⟨K,t,ht,hKt⟩ := hL x
  refine ⟨K,t,ht,fun d => ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy z hz
  change dist (∫ sample, u sample y ∂condDistrib id X P d) (∫ sample, u sample z ∂condDistrib id X P d) ≤ _
  rw [dist_eq_norm,←integral_sub (deterministicBound_integrable_section hm hb y)
    (deterministicBound_integrable_section hm hb z)]
  calc
    _ ≤ ∫ _ : Ω, (K:ℝ)*dist y z ∂condDistrib id X P d :=
      norm_integral_le_of_norm_le (integrable_const _)
        (Eventually.of_forall fun sample => by
          simpa only [dist_eq_norm] using (hKt sample).dist_le_mul y hy z hz)
    _ = (K:ℝ)*dist y z := by simp

end CoulombBarrier

end

end OAI
