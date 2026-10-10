import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.EvalRealCoe
import OAI.Geometry.WeakHessian.Transport.AeProdMetricSpeed

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessianCalculus

def runningMin {X : Type*} (u : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => u 0
  | n+1 => fun x => min (runningMin u n x) (u (n+1) x)

lemma runningMin_mem {X : Type*} {S : Set (X → ℝ)} {u : ℕ → X → ℝ}
    (hu : ∀ n, u n ∈ S)
    (hmin : ∀ f ∈ S, ∀ g ∈ S, (fun x => min (f x) (g x)) ∈ S) :
    ∀ n, runningMin u n ∈ S := by
  intro n
  induction n with
  | zero => exact hu 0
  | succ n ih => exact hmin _ ih _ (hu (n+1))

lemma runningMin_antitone {X : Type*} (u : ℕ → X → ℝ) (x : X) :
    Antitone (fun n => runningMin u n x) :=
  antitone_nat_of_succ_le (fun _ => min_le_left _ _)

lemma runningMin_le {X : Type*} (u : ℕ → X → ℝ) (n : ℕ) (x : X) :
    runningMin u n x ≤ u n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_right _ _

lemma exists_ae_minimum {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (S : Set (X → ℝ)) (L : ℝ) (hS : S.Nonempty)
    (hmeas : ∀ f ∈ S, AEMeasurable f ν)
    (hbound : ∀ f ∈ S, ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hmin : ∀ f ∈ S, ∀ g ∈ S, (fun x => min (f x) (g x)) ∈ S)
    (hclosed : ∀ (u : ℕ → X → ℝ), (∀ n, u n ∈ S) → ∀ d : X → ℝ,
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (d x))) → d ∈ S) :
    ∃ d ∈ S, ∀ f ∈ S, ∀ᵐ x ∂ν, d x ≤ f x := by
  have hi : ∀ f ∈ S, Integrable f ν := by
    intro f hf
    apply (integrable_const L).mono' (hmeas f hf).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound f hf x).1] using (hbound f hf x).2
  let E : Set ℝ := (fun f : X → ℝ => ∫ x, f x ∂ν) '' S
  have hE : E.Nonempty := hS.image _
  have hEb : BddBelow E := ⟨0, by
    rintro e ⟨f, hf, rfl⟩
    exact integral_nonneg (fun x => (hbound f hf x).1)⟩
  obtain ⟨e, _heanti, helim, he⟩ := exists_seq_tendsto_sInf hE hEb
  choose u hu hue using he
  let v := runningMin u
  have hv : ∀ n, v n ∈ S := runningMin_mem hu hmin
  let d : X → ℝ := fun x => ⨅ n, v n x
  have hvb : ∀ x, BddBelow (Set.range (fun n => v n x)) := by
    intro x
    exact ⟨0, fun _ ⟨n, hn⟩ => hn ▸ (hbound _ (hv n) x).1⟩
  have hdlim : ∀ x, Tendsto (fun n => v n x) atTop (𝓝 (d x)) :=
    fun x => tendsto_atTop_ciInf (runningMin_antitone u x) (hvb x)
  have hd : d ∈ S := hclosed v hv d hdlim
  have hevle : ∀ n, (∫ x, v n x ∂ν) ≤ e n := by
    intro n
    rw [← hue n]
    exact integral_mono (hi _ (hv n)) (hi _ (hu n)) (runningMin_le u n)
  have hlow : ∀ f ∈ S, sInf E ≤ ∫ x, f x ∂ν :=
    fun f hf => csInf_le hEb ⟨f,hf,rfl⟩
  have hvilim : Tendsto (fun n => ∫ x, v n x ∂ν) atTop (𝓝 (sInf E)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds helim
      (fun n => hlow _ (hv n)) hevle
  have hlimint : Tendsto (fun n => ∫ x, v n x ∂ν) atTop (𝓝 (∫ x, d x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => L)
      (fun n => (hmeas _ (hv n)).aestronglyMeasurable) (integrable_const L)
    · intro n
      exact ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound _ (hv n) x).1] using
          (hbound _ (hv n) x).2
    · exact ae_of_all _ hdlim
  have hdenergy : (∫ x, d x ∂ν) = sInf E := tendsto_nhds_unique hlimint hvilim
  refine ⟨d, hd, ?_⟩
  intro f hf
  let z : X → ℝ := fun x => min (d x) (f x)
  have hz : z ∈ S := hmin _ hd _ hf
  have hze : (∫ x, z x ∂ν) = ∫ x, d x ∂ν := le_antisymm
    (integral_mono (hi _ hz) (hi _ hd) (fun x => min_le_left _ _))
    (hdenergy ▸ hlow _ hz)
  have hzero : (∫ x, d x - z x ∂ν) = 0 := by
    rw [integral_sub (hi _ hd) (hi _ hz), hze, sub_self]
  have hnon : ∀ᵐ x ∂ν, 0 ≤ d x - z x := ae_of_all _ fun _ => sub_nonneg.mpr (min_le_left _ _)
  have heq := (integral_eq_zero_iff_of_nonneg_ae hnon ((hi _ hd).sub (hi _ hz))).mp hzero
  filter_upwards [heq] with x hx
  exact le_trans (le_of_eq (sub_eq_zero.mp hx)) (min_le_right _ _)

end WeakHessianCalculus

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in

lemma locallyL2_of_bounded (hfinite : FiniteOnBoundedSets m) {f : X → ℝ}
    (hf : AEStronglyMeasurable f m) {L : ℝ} (hbound : ∀ᵐ x ∂m, ‖f x‖ ≤ L) :
    LocallyL2 m f := by
  intro o R _hR
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      hfinite (Metric.ball o R) Metric.isBounded_ball⟩
  exact (memLp_const L).mono' hf.restrict (ae_restrict_of_ae hbound)

lemma exists_minimalLocalWeakUpperGradient_lipschitz (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∃ D, IsMinimalLocalWeakUpperGradient m f D := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
      hfinite _ Metric.isBounded_ball⟩⟩
  obtain ⟨ν, hν, hmν, hνm⟩ := exists_isFiniteMeasure_absolutelyContinuous m
  let : IsFiniteMeasure ν := hν
  let S : Set (X → ℝ) := {D | IsLocalWeakUpperGradient m f D ∧ ∀ x, 0 ≤ D x ∧ D x ≤ L}
  have hS : S.Nonempty := ⟨fun _ => L, lipschitz_isLocalWeakUpperGradient hfinite hf,
    fun _ => ⟨L.coe_nonneg, le_rfl⟩⟩
  have hSm : ∀ D ∈ S, AEMeasurable D ν :=
    fun D hD => hD.1.1.aemeasurable.mono_ac hνm
  have hSmin : ∀ D ∈ S, ∀ E ∈ S, (fun x => min (D x) (E x)) ∈ S := by
    intro D hD E hE
    exact ⟨hD.1.min hE.1 hf, fun x => ⟨le_min (hD.2 x).1 (hE.2 x).1,
      (min_le_left _ _).trans (hD.2 x).2⟩⟩
  have hSclosed : ∀ u : ℕ → X → ℝ, (∀ n, u n ∈ S) → ∀ D : X → ℝ,
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (D x))) → D ∈ S := by
    intro u hu D hlim
    have hDb : ∀ x, 0 ≤ D x ∧ D x ≤ L := fun x =>
      ⟨ge_of_tendsto (hlim x) (Eventually.of_forall fun n => ((hu n).2 x).1),
        le_of_tendsto (hlim x) (Eventually.of_forall fun n => ((hu n).2 x).2)⟩
    have hDm : AEStronglyMeasurable D m :=
      aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => (hu n).1.1.aestronglyMeasurable) (ae_of_all _ hlim)
    have hDl : LocallyL2 m D := locallyL2_of_bounded hfinite hDm
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hDb x).1]
        using (hDb x).2)
    exact ⟨IsLocalWeakUpperGradient.of_dominated_ae_tendsto (fun n => (hu n).1) hDl
      (lipschitz_isLocalWeakUpperGradient hfinite hf).1
      (fun n => ae_of_all _ fun x => ((hu n).2 x).2) (ae_of_all _ hlim), hDb⟩
  obtain ⟨D, hD, hDmin⟩ := WeakHessianCalculus.exists_ae_minimum ν S L hS hSm
    (fun _ h => h.2) hSmin hSclosed
  refine ⟨D, hD.1, ?_⟩
  intro E hE
  let E' : X → ℝ := fun x => max 0 (min (D x) (E x))
  have hEq : (fun x => min (D x) (E x)) =ᵐ[m] E' := by
    filter_upwards [hE.2.1] with x hx
    exact (max_eq_right (le_min (hD.2 x).1 hx)).symm
  have hE' : E' ∈ S := by
    refine ⟨(hD.1.min hE hf).congr_ae Filter.EventuallyEq.rfl hEq, fun x => ?_⟩
    exact ⟨le_max_left _ _, max_le L.coe_nonneg ((min_le_left _ _).trans (hD.2 x).2)⟩
  filter_upwards [hmν.ae_le (hDmin E' hE'), hEq] with x hx heq
  exact hx.trans (heq ▸ min_le_right (D x) (E x))

end WeakHessian

end
end InlinedFile0

end OAI
