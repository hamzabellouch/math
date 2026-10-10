import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitialBoundsBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma potential_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ)) :
    Measurable (fun p : Ω × TFSpace => tfPotential (ρ p.1) p.2) := by
  have h : Measurable (fun p : (Ω × TFSpace) × TFSpace => ρ p.1.1 p.2/‖p.1.2-p.2‖) :=
    (hm.comp (measurable_fst.fst.prodMk measurable_snd)).div
      (measurable_fst.snd.sub measurable_snd).norm
  exact h.stronglyMeasurable.integral_prod_right.measurable

lemma cutMaximum_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {u v : Ω → TFSpace → ℝ} (hu : Measurable (Function.uncurry u))
    (hv : Measurable (Function.uncurry v)) (r R : ℝ) :
    Measurable (fun p : Ω × TFSpace => cutMaximum r R (u p.1) (v p.1) p.2) :=
  Measurable.ite (measurableSet_lt measurable_snd.norm measurable_const) hu
    (Measurable.ite (measurableSet_lt measurable_snd.norm measurable_const) (hu.max hv) hv)

lemma initializedOffset_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ))
    (Z B a : ℝ) {r : ℝ} (hr : 0 < r) :
    Measurable (fun p : Ω × TFSpace => initializedOffset Z B r a (ρ p.1) p.2) := by
  exact cutMaximum_joint_measurable (u := fun sample => initialOffset Z r a (ρ sample))
    (v := fun _ => outerOffset Z B r)
    (((potential_joint_measurable hm).neg.sub measurable_const).add
      (measurable_const.mul (measurable_snd.norm.pow_const 2)))
    ((outerOffset_continuous Z B hr).measurable.comp measurable_snd) r (2*r)

lemma bounded_potential_deterministicBound {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) {M r : ℝ} (hM : 0 ≤ M)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hs : ∀ sample, Function.support (ρ sample) ⊆ ball 0 r) :
    DeterministicLocalBound (fun sample => tfPotential (ρ sample)) := by
  intro K hK
  obtain ⟨S,hS,hKS⟩ := hK.isBounded.exists_pos_norm_lt
  let T := max r S
  have hT : 0 < T := hS.trans_le (le_max_right _ _)
  refine ⟨8*Real.pi*M*T^2,fun sample x hx => ?_⟩
  rw [Real.norm_of_nonneg (tfPotential_nonneg (ae_of_all _ (hn sample)) x)]
  exact bounded_density_potential_le (hm sample) hM hT (hn sample) (hb sample)
    ((hs sample).trans (ball_subset_ball (le_max_left _ _))) x
    ((hKS x hx).le.trans (le_max_right _ _))

lemma DeterministicLocalBound.neg {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) : DeterministicLocalBound (fun sample x => -u sample x) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  exact ⟨C,fun sample x hx => by simpa only [norm_neg] using hC sample x hx⟩

lemma continuous_deterministicBound {Ω : Type*} {u : TFSpace → ℝ}
    (hu : Continuous u) : DeterministicLocalBound (fun _ : Ω => u) := by
  intro K hK
  obtain ⟨C,_,hC⟩ := (hK.image hu).isBounded.exists_pos_norm_lt
  exact ⟨C,fun _ x hx => (hC (u x) (mem_image_of_mem u hx)).le⟩

lemma cutMaximum_deterministicBound {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (hv : DeterministicLocalBound v) (r R : ℝ) :
    DeterministicLocalBound (fun sample => cutMaximum r R (u sample) (v sample)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  obtain ⟨D,hD⟩ := hv K hK
  refine ⟨max C D,fun sample x hx => ?_⟩
  have hu' := (hC sample x hx).trans (le_max_left C D)
  have hv' := (hD sample x hx).trans (le_max_right C D)
  change ‖if ‖x‖ < r then u sample x else if ‖x‖ < R then max (u sample x) (v sample x) else v sample x‖ ≤ _
  split_ifs
  · exact hu'
  · rcases le_total (u sample x) (v sample x) with hh|hh
    · simpa only [max_eq_right hh] using hv'
    · simpa only [max_eq_left hh] using hu'
  · exact hv'

lemma initializedOffset_deterministicBound {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hs : ∀ sample, Function.support (ρ sample) ⊆ ball 0 r) (Z B a : ℝ) :
    DeterministicLocalBound (fun sample => initializedOffset Z B r a (ρ sample)) := by
  have hp := (bounded_potential_deterministicBound hm hM hn hb hs).neg
  have hc : Continuous (fun x : TFSpace => -(7/10)*Z/r+a*‖x‖^2) :=
    continuous_const.add (continuous_const.mul (continuous_norm.pow 2))
  have hi := hp.add (continuous_deterministicBound (Ω := Ω) hc)
  have he : (fun sample x => -tfPotential (ρ sample) x+(-(7/10)*Z/r+a*‖x‖^2)) =
      (fun sample => initialOffset Z r a (ρ sample)) := by
    funext sample x
    dsimp [initialOffset]
    ring
  rw [he] at hi
  exact cutMaximum_deterministicBound hi (continuous_deterministicBound (outerOffset_continuous Z B hr)) r (2*r)

end CoulombBarrier

end

end OAI
