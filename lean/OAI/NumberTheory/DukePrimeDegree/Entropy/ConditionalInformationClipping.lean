import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableObservationInformation

namespace OAI

/-! # Finite present observations with a fixed conditioning sigma algebra

An integrable countable information function is the limit of the
conditional entropies of finite clips. The conditioning is kept fixed;
in the application it is the entire future together with the transverse
coordinate, rather than the future of a clipped observation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*}

lemma conditionalInformation_heightClip_eventually
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    (μ : Measure Y) (Q : Y → ℕ) (y : Y) :
    ∀ᶠ N : ℕ in atTop,
      conditionalInformation μ (heightClip Q N) m y = conditionalInformation μ Q m y := by
  filter_upwards [eventually_gt_atTop (Q y)] with N hN
  unfold conditionalInformation
  rw [heightClip_atom_eq_of_lt Q y hN]

lemma ae_conditionalInformation_heightClip_bounds
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (Q : Y → ℕ) (hQ : Measurable Q)
    (hpos : ∀ᵐ y ∂μ,
      0 < (μ[({z | Q z = Q y}.indicator (fun _ => (1 : ℝ))) | m]) y) (N : ℕ) :
    ∀ᵐ y ∂μ, 0 ≤ conditionalInformation μ (heightClip Q N) m y ∧
      conditionalInformation μ (heightClip Q N) m y ≤ conditionalInformation μ Q m y := by
  classical
  let clip (a : ℕ) : Fin (N+1) := ⟨min a N, Nat.lt_succ_of_le (min_le_right a N)⟩
  have hmono (a : ℕ) :
      μ[({z | Q z = a}.indicator (fun _ => (1 : ℝ))) | m] ≤ᵐ[μ]
        μ[({z | heightClip Q N z = clip a}.indicator (fun _ => (1 : ℝ))) | m] := by
    apply condExp_mono
      ((integrable_const (1 : ℝ)).indicator (hQ (measurableSet_singleton a)))
      ((integrable_const (1 : ℝ)).indicator
        ((heightClip_measurable hQ N) (measurableSet_singleton (clip a))))
    apply ae_of_all
    intro z
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
    by_cases hz : Q z = a
    · have hc : heightClip Q N z = clip a := by simp [hz, heightClip, clip]
      rw [ite_eq_left hz, ite_eq_left hc]
    · rw [ite_eq_right hz]
      split_ifs <;> norm_num
  have hb (a : Fin (N+1)) :=
    conditionalProbability_unit_bounds μ {z | heightClip Q N z = a} m
  filter_upwards [ae_all_iff.mpr hmono, ae_all_iff.mpr hb, hpos] with y hy hby hpy
  change 0 ≤ -Real.log _ ∧ -Real.log _ ≤ -Real.log _
  refine ⟨neg_nonneg.mpr (Real.log_nonpos (hby _).1 (hby _).2), ?_⟩
  apply neg_le_neg
  apply Real.log_le_log hpy
  exact hy (Q y)

/-- Finite present-label clips recover the mean countable information,
with no finite-Shannon-entropy assumption on the full countable label. -/
theorem conditionalSigmaEntropy_heightClip_tendsto
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (Q : Y → ℕ) (hQ : Measurable Q) (hm : m ≤ mY)
    (hpos : ∀ᵐ y ∂μ,
      0 < (μ[({z | Q z = Q y}.indicator (fun _ => (1 : ℝ))) | m]) y)
    (hint : Integrable (conditionalInformation μ Q m) μ) :
    Tendsto (fun N => conditionalSigmaEntropy μ (heightClip Q N) m) atTop
      (𝓝 (∫ y, conditionalInformation μ Q m y ∂μ)) := by
  have H := tendsto_integral_of_dominated_convergence
    (conditionalInformation μ Q m)
    (fun N => (conditionalInformation_integrable_integral m μ (heightClip Q N)
      (heightClip_measurable hQ N) hm).1.aestronglyMeasurable)
    hint
    (fun N => (ae_conditionalInformation_heightClip_bounds m μ Q hQ hpos N).mono
      (fun y hy => by simpa only [Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2))
    (ae_of_all _ (fun y => by
      apply tendsto_const_nhds.congr'
      filter_upwards [conditionalInformation_heightClip_eventually m μ Q y] with N hN
      exact hN.symm))
  convert H using 1
  funext N
  exact (conditionalInformation_integrable_integral m μ (heightClip Q N)
    (heightClip_measurable hQ N) hm).2.symm

end DukePrimeDegree

end

end OAI
