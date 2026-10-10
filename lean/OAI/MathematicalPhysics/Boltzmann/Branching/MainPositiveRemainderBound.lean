import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterraOffAxisAE
import OAI.MathematicalPhysics.Boltzmann.Branching.NearbyMainCopies
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticWindowL1
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedCoreSelection

namespace OAI

section

/-! # Positive iteration of the selected main-core collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positiveMain_action (r s₀ η K α γ d₀ q : ℝ) (N : ℕ)
    (f : KineticPhase → ℝ≥0∞) (z : KineticPhase) :
    ChartKernel.action (positiveMainKernel r s₀ η K α γ d₀ q N) f z =
      ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N) f z+
      ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N) f z := by
  change (∫⁻ v, f (z.1,v) ∂(_+_)) = _
  rw [lintegral_add_measure]
  rfl

theorem positiveMain_action_congr_ae (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) {f g : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) :
    ChartKernel.action (positiveMainKernel r s₀ η K α γ d₀ q N) f
      =ᵐ[((volume : Measure ℝ).prod volume).prod volume]
    ChartKernel.action (positiveMainKernel r s₀ η K α γ d₀ q N) g := by
  have h := ChartKernel.action_offAxis_normalized_congr_ae hcarleman
    ((volume : Measure ℝ).prod volume) (selectedColdKernel r s₀ η K α γ d₀ N)
    (selectedCoreDensity_measurable r s₀ η K α γ d₀ N)
    (selectedColdKernel_density r s₀ η K α γ d₀ N) q hf hg hfg
  filter_upwards [h] with z hz
  rw [positiveMain_action,positiveMain_action]
  exact congrArg (fun x => x+x) hz

theorem iterate_positiveMain_congr_ae (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q a : ℝ) (N : ℕ) {f g : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) (n : ℕ) :
    PositiveIteration.iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) f n
      =ᵐ[((volume : Measure ℝ).prod volume).prod volume]
    PositiveIteration.iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) g n := by
  induction n with
  | zero => exact hfg
  | succ n ih =>
    apply PositiveIteration.step_congr_ae a _
      (PositiveIteration.iterate_measurable a _ hf n) (PositiveIteration.iterate_measurable a _ hg n)
    exact positiveMain_action_congr_ae hcarleman r s₀ η K α γ d₀ q N
      (PositiveIteration.iterate_measurable a _ hf n) (PositiveIteration.iterate_measurable a _ hg n) ih

theorem iterate_positiveMain_congr_ae_at (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q a t : ℝ) (N : ℕ) {f g : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) (n : ℕ) :
    (fun p : Velocity × Velocity => PositiveIteration.iterate a
      (positiveMainKernel r s₀ η K α γ d₀ q N) f (n+1) ((t,p.1),p.2)) =ᵐ[volume]
    (fun p => PositiveIteration.iterate a
      (positiveMainKernel r s₀ η K α γ d₀ q N) g (n+1) ((t,p.1),p.2)) := by
  apply PositiveIteration.step_congr_ae_at a t
  exact positiveMain_action_congr_ae hcarleman r s₀ η K α γ d₀ q N
    (PositiveIteration.iterate_measurable a _ hf n) (PositiveIteration.iterate_measurable a _ hg n)
    (iterate_positiveMain_congr_ae hcarleman r s₀ η K α γ d₀ q a N hf hg hfg n)

theorem iterate_positiveMain_bound {r s₀ η K α γ d₀ q a T B : ℝ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (ha : 0 < a) (hB : 0 ≤ B) (N : ℕ)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ ENNReal.ofReal B)
    (n : ℕ) (z : KineticPhase) (hz : z.1.1 ∈ Icc a T) :
    PositiveIteration.iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) f n z ≤
      ENNReal.ofReal (B*((2*JetCoreSheet.growthConstant K α γ q)*Real.log (z.1.1/a))^n) := by
  apply PositiveIteration.iterate_bound ha
    (mul_nonneg (by norm_num) (JetCoreSheet.growthConstant_nonneg hK α γ q)) hB _
    (fun w hw => positiveMainKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ N w
      (ha.trans_le hw.1)) hf n z hz

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Almost-everywhere order is preserved by the actual positive main kernel -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positiveMain_action_mono_ae (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) {f g : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : f ≤ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) :
    ChartKernel.action (positiveMainKernel r s₀ η K α γ d₀ q N) f
      ≤ᵐ[((volume : Measure ℝ).prod volume).prod volume]
    ChartKernel.action (positiveMainKernel r s₀ η K α γ d₀ q N) g := by
  have hm : (fun z => min (f z) (g z)) =ᵐ[((volume : Measure ℝ).prod volume).prod volume] f :=
    hfg.mono (fun _ h => min_eq_left h)
  have he := positiveMain_action_congr_ae hcarleman r s₀ η K α γ d₀ q N (hf.min hg) hf hm
  filter_upwards [he] with z hz
  rw [← hz]
  exact lintegral_mono (fun v => min_le_right _ _)

theorem step_positiveMain_mono_ae (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q a : ℝ) (N : ℕ) {f g : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : f ≤ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) :
    PositiveIteration.step a (positiveMainKernel r s₀ η K α γ d₀ q N) f
      ≤ᵐ[((volume : Measure ℝ).prod volume).prod volume]
    PositiveIteration.step a (positiveMainKernel r s₀ η K α γ d₀ q N) g := by
  have hm : (fun z => min (f z) (g z)) =ᵐ[((volume : Measure ℝ).prod volume).prod volume] f :=
    hfg.mono (fun _ h => min_eq_left h)
  have he := PositiveIteration.step_congr_ae a _ (hf.min hg) hf
    (positiveMain_action_congr_ae hcarleman r s₀ η K α γ d₀ q N (hf.min hg) hf hm)
  filter_upwards [he] with z hz
  rw [← hz]
  exact PositiveIteration.step_mono a _ (fun _ => min_le_right _ _) z

theorem step_positiveMain_mono_ae_at (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q a t : ℝ) (N : ℕ) {f g : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : f ≤ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) :
    (fun p : Velocity × Velocity => PositiveIteration.step a
      (positiveMainKernel r s₀ η K α γ d₀ q N) f ((t,p.1),p.2)) ≤ᵐ[volume]
    (fun p => PositiveIteration.step a (positiveMainKernel r s₀ η K α γ d₀ q N) g ((t,p.1),p.2)) := by
  have hm : (fun z => min (f z) (g z)) =ᵐ[((volume : Measure ℝ).prod volume).prod volume] f :=
    hfg.mono (fun _ h => min_eq_left h)
  have he := PositiveIteration.step_congr_ae_at a t _
    (positiveMain_action_congr_ae hcarleman r s₀ η K α γ d₀ q N (hf.min hg) hf hm)
  filter_upwards [he] with p hp
  rw [← hp]
  exact PositiveIteration.step_mono a _ (fun _ => min_le_right _ _) ((t,p.1),p.2)

theorem iterate_positiveMain_mono_ae (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q a : ℝ) (N : ℕ) {f g : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : f ≤ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) (n : ℕ) :
    PositiveIteration.iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) f n
      ≤ᵐ[((volume : Measure ℝ).prod volume).prod volume]
    PositiveIteration.iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) g n := by
  induction n with
  | zero => exact hfg
  | succ n ih =>
    exact step_positiveMain_mono_ae hcarleman r s₀ η K α γ d₀ q a N
      (PositiveIteration.iterate_measurable a _ hf n) (PositiveIteration.iterate_measurable a _ hg n) ih

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Finite positive expansions preserve the actual a.e. endpoint inequalities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positiveMain_residual_ae (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q a : ℝ) (N : ℕ) {f d : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (hd : Measurable d)
    (h : f ≤ᵐ[((volume : Measure ℝ).prod volume).prod volume]
      fun z => d z+step a (positiveMainKernel r s₀ η K α γ d₀ q N) f z) (n : ℕ) :
    ∀ᵐ z ∂((volume : Measure ℝ).prod volume).prod volume,
      f z ≤ (∑ j ∈ Finset.range n, iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) d j z)+
        iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) f n z := by
  let J := positiveMainKernel r s₀ η K α γ d₀ q N
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun z => by simp [iterate])
  | succ n ih =>
    have hi := iterate_positiveMain_mono_ae hcarleman r s₀ η K α γ d₀ q a N hf
      (hd.add (step_measurable a J hf)) h n
    filter_upwards [ih,hi] with z hz hi
    change iterate a J f n z ≤ iterate a J (d+step a J f) n z at hi
    rw [iterate_add a J hd,iterate_step] at hi
    calc
      f z ≤ (∑ j ∈ Finset.range n, iterate a J d j z)+iterate a J f n z := hz
      _ ≤ (∑ j ∈ Finset.range n, iterate a J d j z)+
          (iterate a J d n z+iterate a J f (n+1) z) := add_le_add le_rfl hi
      _ = _ := by rw [Finset.sum_range_succ,add_assoc]

theorem positiveMain_residual_ae_at (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q a t : ℝ) (N : ℕ) {f d : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (hd : Measurable d)
    (h : f ≤ᵐ[((volume : Measure ℝ).prod volume).prod volume]
      fun z => d z+step a (positiveMainKernel r s₀ η K α γ d₀ q N) f z)
    (ht : ∀ᵐ p : Velocity × Velocity, f ((t,p.1),p.2) ≤
      d ((t,p.1),p.2)+step a (positiveMainKernel r s₀ η K α γ d₀ q N) f ((t,p.1),p.2)) (n : ℕ) :
    ∀ᵐ p : Velocity × Velocity, f ((t,p.1),p.2) ≤
      (∑ j ∈ Finset.range n, iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) d j ((t,p.1),p.2))+
        iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) f n ((t,p.1),p.2) := by
  let J := positiveMainKernel r s₀ η K α γ d₀ q N
  have hm : Measurable (d+step a J f) := hd.add (step_measurable a J hf)
  have hmono (k : ℕ) : ∀ᵐ p : Velocity × Velocity,
      iterate a J f k ((t,p.1),p.2) ≤ iterate a J (d+step a J f) k ((t,p.1),p.2) := by
    cases k with
    | zero => exact ht
    | succ k =>
      exact step_positiveMain_mono_ae_at hcarleman r s₀ η K α γ d₀ q a t N
        (iterate_measurable a J hf k) (iterate_measurable a J hm k)
        (iterate_positiveMain_mono_ae hcarleman r s₀ η K α γ d₀ q a N hf hm h k)
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun p => by simp [iterate])
  | succ n ih =>
    filter_upwards [ih,hmono n] with p hp hi
    rw [iterate_add a J hd,iterate_step] at hi
    calc
      f ((t,p.1),p.2) ≤ (∑ j ∈ Finset.range n, iterate a J d j ((t,p.1),p.2))+
        iterate a J f n ((t,p.1),p.2) := hp
      _ ≤ (∑ j ∈ Finset.range n, iterate a J d j ((t,p.1),p.2))+
          (iterate a J d n ((t,p.1),p.2)+iterate a J f (n+1) ((t,p.1),p.2)) := add_le_add le_rfl hi
      _ = _ := by rw [Finset.sum_range_succ,add_assoc]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A finite residual expansion on a time slab, at each terminal time -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positiveMain_residual_on_slab (hcarleman : Published.GPV2009CarlemanInput)
    (r s₀ η K α γ d₀ q a T : ℝ) (N : ℕ) {f : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (c : ℝ≥0∞)
    (h : ∀ t ∈ Icc a T, ∀ᵐ p : Velocity × Velocity, f ((t,p.1),p.2) ≤
      c+step a (positiveMainKernel r s₀ η K α γ d₀ q N) f ((t,p.1),p.2))
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc a T) :
    ∀ᵐ p : Velocity × Velocity, f ((t,p.1),p.2) ≤
      (∑ j ∈ Finset.range n, iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) (fun _ => c) j ((t,p.1),p.2))+
        iterate a (positiveMainKernel r s₀ η K α γ d₀ q N) f n ((t,p.1),p.2) := by
  let J := positiveMainKernel r s₀ η K α γ d₀ q N
  have hs : ∀ᵐ z ∂((volume : Measure ℝ).prod volume).prod volume,
      z.1.1 ∈ Icc a T → f z ≤ c+step a J f z := by
    have hv : ∀ᵐ z : KineticPhase, z.1.1 ∈ Icc a T → f z ≤ c+step a J f z := by
      apply KineticTraceAE.of_traces ((measurableSet_Icc.preimage measurable_fst.fst).imp
        (measurableSet_le hf (measurable_const.add (step_measurable a J hf))))
      apply Filter.Eventually.of_forall
      intro u
      by_cases hu : u ∈ Icc a T
      · filter_upwards [h u hu] with p hp _
        exact hp
      · exact Filter.Eventually.of_forall (fun _ hp => (hu hp).elim)
    simpa only [Measure.volume_eq_prod] using hv
  have hglobal := onSlab_positive_inequality J c hs
  have htrace : ∀ᵐ p : Velocity × Velocity, onSlab a T f ((t,p.1),p.2) ≤
      c+step a J (onSlab a T f) ((t,p.1),p.2) := by
    filter_upwards [h t ht] with p hp
    rw [onSlab_eq f (z := ((t,p.1),p.2)) ht,step_onSlab J f (z := ((t,p.1),p.2)) ht]
    exact hp
  have he := positiveMain_residual_ae_at hcarleman r s₀ η K α γ d₀ q a t N
    (onSlab_measurable a T hf) measurable_const hglobal htrace n
  filter_upwards [he] with p hp
  rw [onSlab_eq f (z := ((t,p.1),p.2)) ht,iterate_onSlab J f n ((t,p.1),p.2) ht] at hp
  exact hp

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Bounded collision flights cannot change the retained periodic origin -/

noncomputable section

open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem scaled_flight_distance_le {r t₁ t₂ T R : ℝ} (hr : 0 ≤ r)
    (ht₂ : 0 ≤ t₂) (htt : t₂ ≤ t₁) (ht₁ : t₁ ≤ T)
    (x w : Velocity) (hw : ‖w‖ ≤ R) :
    ‖r • x-r • (x-(t₁-t₂) • w)‖ ≤ r*T*R := by
  have he : r • x-r • (x-(t₁-t₂) • w) = (r*(t₁-t₂)) • w := by module
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr (sub_nonneg.mpr htt))]
  have hdt : t₁-t₂ ≤ T := by linarith
  exact mul_le_mul (mul_le_mul_of_nonneg_left hdt hr) hw (norm_nonneg w)
    (mul_nonneg hr (ht₂.trans (htt.trans ht₁)))

theorem main_collision_same_origin {s₀ η r t₁ t₂ T R : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hr : 0 ≤ r)
    (ht₂ : 0 ≤ t₂) (htt : t₂ ≤ t₁) (ht₁ : t₁ ≤ T) (hsmall : r*T*R < 1/4)
    {x w : Velocity} (hw : ‖w‖ ≤ R) {i j : Label}
    (hi : (t₁,x) ∈ mainCoreRegion s₀ η r N i)
    (hj : (t₂,x-(t₁-t₂) • w) ∈ mainCoreRegion s₀ η r N j) :
    i.lattice = j.lattice :=
  nearby_main_regions_same_lattice hs₀ hsmax hη hi hj
    ((scaled_flight_distance_le hr ht₂ htt ht₁ x w hw).trans_lt hsmall)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The finite constant part of the actual positive residual expansion -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positiveMain_constant_sum_bound {r s₀ η K α γ d₀ q a T : ℝ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (ha : 0 < a) (N : ℕ) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (n : ℕ) {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    (∑ j ∈ Finset.range n, iterate a (positiveMainKernel r s₀ η K α γ d₀ q N)
      (fun _ => c) j z) ≤
      c*∑ j ∈ Finset.range n, ENNReal.ofReal
        (((2*JetCoreSheet.growthConstant K α γ q)*Real.log (z.1.1/a))^j) := by
  have hC := mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (JetCoreSheet.growthConstant_nonneg hK α γ q)
  have hb (w : KineticPhase) (hw : w.1.1 ∈ Icc a T) :=
    positiveMainKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ N w
      (ha.trans_le hw.1)
  calc
    _ ≤ ∑ j ∈ Finset.range n, c*ENNReal.ofReal
        (((2*JetCoreSheet.growthConstant K α γ q)*Real.log (z.1.1/a))^j) := by
      apply Finset.sum_le_sum
      intro j _
      exact iterate_const_bound ha hC _ hb c hc j hz
    _ = _ := (Finset.mul_sum _ _ _).symm

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A terminal-time independent bound for the finite positive remainder -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positiveMain_constant_sum_uniform {r s₀ η K α γ d₀ q a T : ℝ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (ha : 0 < a) (hTmax : T ≤ 1) (N : ℕ)
    (c : ℝ≥0∞) (hc : c ≠ ∞) (n : ℕ) {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    (∑ j ∈ Finset.range n, iterate a (positiveMainKernel r s₀ η K α γ d₀ q N)
      (fun _ => c) j z) ≤
      c*ENNReal.ofReal (∑ j ∈ Finset.range n,
        ((2*JetCoreSheet.growthConstant K α γ q)*Real.log (1/a))^j) := by
  apply (positiveMain_constant_sum_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax
    hq₁ hq₂ ha N c hc n hz).trans
  apply mul_le_mul' le_rfl
  have hC : 0 ≤ 2*JetCoreSheet.growthConstant K α γ q :=
    mul_nonneg (by norm_num) (JetCoreSheet.growthConstant_nonneg hK α γ q)
  have hlog0 : 0 ≤ Real.log (z.1.1/a) := Real.log_nonneg ((one_le_div ha).mpr hz.1)
  have hlog : Real.log (z.1.1/a) ≤ Real.log (1/a) :=
    Real.log_le_log (div_pos (ha.trans_le hz.1) ha)
      (div_le_div_of_nonneg_right (hz.2.trans hTmax) ha.le)
  calc
    _ ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal
        (((2*JetCoreSheet.growthConstant K α γ q)*Real.log (1/a))^j) := by
      apply Finset.sum_le_sum
      intro j _
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left₀ (mul_nonneg hC hlog0) (mul_le_mul_of_nonneg_left hlog hC) j
    _ = _ := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j _
      exact pow_nonneg (mul_nonneg hC (hlog0.trans hlog)) j

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
