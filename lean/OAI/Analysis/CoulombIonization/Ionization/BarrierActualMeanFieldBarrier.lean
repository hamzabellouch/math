import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BoundedL1PoissonBarrier
import OAI.Analysis.CoulombIonization.Ionization.BarrierInitialDeterministicBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitialLipschitzBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

lemma meanFieldOffset_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Ω → TFSpace → ℝ} (hm : Measurable (Function.uncurry ρ)) (lam : ℝ) :
    Measurable (Function.uncurry (fun sample => meanFieldOffset lam (ρ sample))) :=
  (potential_joint_measurable hm).neg.sub measurable_const

lemma meanFieldOffset_deterministicBound {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) (hi : ∀ sample, Integrable (ρ sample)) {M n : ℝ}
    (hM : 0 ≤ M) (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hmass : ∀ sample, (∫ x, ρ sample x) = n) (lam : ℝ) :
    DeterministicLocalBound (fun sample => meanFieldOffset lam (ρ sample)) := by
  refine fun _ _ => ⟨2*Real.pi*M+n+|lam|,fun sample x _ => ?_⟩
  have hp := bounded_L1_potential_le (hm sample) (hi sample) hM (hn sample) (hb sample) x
  rw [hmass sample] at hp
  calc
    _ ≤ ‖-tfPotential (ρ sample) x‖+‖lam‖ := norm_sub_le _ _
    _ = tfPotential (ρ sample) x+|lam| := by
      rw [norm_neg,Real.norm_of_nonneg (tfPotential_nonneg (ae_of_all _ (hn sample)) x),Real.norm_eq_abs]
    _ ≤ _ := by linarith only [hp]

lemma meanFieldOffset_deterministicLip {Ω : Type*} {ρ : Ω → TFSpace → ℝ}
    (hm : ∀ sample, Measurable (ρ sample)) (hi : ∀ sample, Integrable (ρ sample)) {M n : ℝ}
    (hM : 0 ≤ M) (hn0 : 0 ≤ n) (hn : ∀ sample x, 0 ≤ ρ sample x) (hb : ∀ sample x, ρ sample x ≤ M)
    (hmass : ∀ sample, (∫ x, ρ sample x) = n) (lam : ℝ) :
    DeterministicLocalLipschitz (fun sample => meanFieldOffset lam (ρ sample)) := by
  intro x
  refine ⟨⟨4*Real.pi*M+n,by positivity⟩,univ,Filter.univ_mem,fun sample => ?_⟩
  have hL := bounded_L1_potential_lipschitz (hm sample) (hi sample) hM (hn sample) (hb sample)
  have hh : LipschitzWith ⟨4*Real.pi*M+n,by positivity⟩ (tfPotential (ρ sample)) := by
    simpa only [hmass sample] using hL
  apply LipschitzWith.lipschitzOnWith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hhxy := hh.dist_le_mul x y
  change ‖(-tfPotential (ρ sample) x-lam)-(-tfPotential (ρ sample) y-lam)‖ ≤ _
  rw [show (-tfPotential (ρ sample) x-lam)-(-tfPotential (ρ sample) y-lam) = -(tfPotential (ρ sample) x-tfPotential (ρ sample) y) by ring,norm_neg]
  exact hhxy

theorem original_meanField_admissible {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (Z lam : ℝ) :
    let ρ := originalMasterField μ ell j c₁ r₀ s g
    let h := fun sample => meanFieldOffset lam (ρ sample)
    Measurable (Function.uncurry h) ∧ DeterministicLocalLipschitz h ∧
    DeterministicLocalBound h ∧ Measurable (Function.uncurry ρ) ∧
    (∀ sample x, 0 ≤ ρ sample x) ∧
    (∃ D : ℝ, 0 ≤ D ∧ ∀ sample x, ρ sample x ≤ D) ∧
    (∀ sample, WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+h sample x)
      (fun x => 4*Real.pi*ρ sample x)) := by
  dsimp only
  let ρ := originalMasterField μ ell j c₁ r₀ s g
  have hm := originalMasterField_measurable μ ell j hc hr hs hg
  have hmω (sample) : Measurable (ρ sample) := hm.comp ((measurable_const (a := sample)).prodMk measurable_id)
  have hi (sample) : Integrable (ρ sample) :=
    jointMasterPosterior_integrable μ ell j hc hr hs hg hgn (originalDatum ell j sample)
  have hn (sample x) : 0 ≤ ρ sample x :=
    jointMasterPosterior_nonneg μ ell j c₁ r₀ s g (originalDatum ell j sample) x
  have hmass (sample) : (∫ x, ρ sample x) = (N:ℝ) :=
    jointMasterPosterior_mass μ ell j hc hr hs hg hgn (originalDatum ell j sample)
  obtain ⟨D,hD,hb⟩ := jointMasterPosterior_global_bound μ ell j hc hr hs hrs hg hcg
  have hb' (sample x) : ρ sample x ≤ D :=
    (le_abs_self _).trans (by
      change |jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j sample) x| ≤ D
      simpa only [Real.norm_eq_abs] using hb (originalDatum ell j sample) x)
  exact ⟨meanFieldOffset_joint_measurable hm lam,
    meanFieldOffset_deterministicLip hmω hi hD (by positivity) hn hb' hmass lam,
    meanFieldOffset_deterministicBound hmω hi hD hn hb' hmass lam,
    hm,hn,⟨D,hD,hb'⟩,fun sample => meanFieldOffset_weak_nuclear (hmω sample) (hi sample) hD (hn sample) (hb' sample) Z lam⟩

end CoulombBarrier

end

end OAI
