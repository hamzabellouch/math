import OAI.Probability.InvariantIsing.Arrays.TensorFieldTailBridge
import OAI.Probability.InvariantIsing.Arrays.TensorTreeLevels
import OAI.Probability.InvariantIsing.Core.FiniteTailOrder

namespace OAI

/-! Synchronized field-contact tests include the root and identify every
partition-endpoint tail without excluding atoms at those endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma spectralSpin_integral {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    (∫ x, spectralSpinArray x 0 1 ∂(Q : Measure (SpectralArray (m + 1)))) =
      pathTail (spectralSpinQuantilePath Q hP hn) 0 := by
  have hm : Measurable (fun x : SpectralArray (m + 1) => spectralSpinArray x 0 1) := by
    unfold spectralSpinArray
    fun_prop
  have he := integral_map hm.aemeasurable
    (measurable_id.aestronglyMeasurable : AEStronglyMeasurable (fun x : ℝ => x)
      (scalarOverlapLaw (Q : Measure (SpectralArray (m + 1))) spectralSpinArray))
  change (∫ x : ℝ, x ∂scalarOverlapLaw (Q : Measure (SpectralArray (m + 1))) spectralSpinArray) = _ at he
  rw [← spectralSpinQuantilePath_law Q hP hn,
    integral_map (μ := pathMeasure) (f := fun x : ℝ => x)
      (spectralSpinQuantilePath Q hP hn).measurable.aemeasurable
      measurable_id.aestronglyMeasurable] at he
  simp only [id_eq] at he
  rw [← he, pathTail, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  rfl

lemma spectralPair_depthTail_integral {m n : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (hlevel : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) (Fin.last m) : ℝ) ∈ treeLevels n)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hb : ∀ i, cut i ∈ Icc (0 : ℝ) 1)
    (htail : ∀ d : Fin n, (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(Q : Measure (SpectralArray (m + 1)))) = 1 - cut d.succ.castSucc)
    (j : Fin (n + 1)) :
    (∫ x, spectralSpinDepthTail n j x ∂(Q : Measure (SpectralArray (m + 1)))) =
      pathTail (spectralSpinQuantilePath Q hP hn) (cut j.castSucc) := by
  refine Fin.cases ?_ (fun d => ?_) j
  · simpa only [Fin.val_zero, Fin.castSucc_zero, hfirst, spectralSpinDepthTail,
      depthTail, ite_true, mul_one] using spectralSpin_integral Q hP hn
  · simpa only [spectralSpinDepthTail, Fin.val_succ, depthTail,
      Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel] using
      spectralPair_treeTail_integral Q hgg hG q hq hd hE hP hn hlevel
        (hb d.succ.castSucc) (htail d)

lemma contact_partition_tail_order {n : ℕ} (p trial : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (v : Fin (n + 1) → ℝ)
    (hv : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = v i)
    (hcontact : ∀ j : Fin (n + 1),
      (∑ i, ((cut i.succ - cut i.castSucc) * v i) *
        finiteFieldPath (Pi.single j 1) i) ≤ pathTail p (cut j.castSucc)) :
    ∀ s ∈ Icc (0 : ℝ) 1, pathTail trial s ≤ pathTail p s := by
  apply pathTail_order_of_finite_partition p trial cut hc hfirst hlast v hv
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [hlast, pathTail, intervalIntegral.integral_same, le_refl]
  · have he : (∫ s in Ioi (cut i.castSucc), trial s ∂pathMeasure) =
        ∑ k, if i.val ≤ k.val then (cut k.succ - cut k.castSucc) * v k else 0 := by
      have hstep : finiteStepFunction cut v =ᵐ[pathMeasure] trial := by
        let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
        have hne : ∀ᵐ s ∂pathMeasure, ∀ k, s ≠ cut k :=
          ae_all_iff.mpr (fun k => Measure.ae_ne pathMeasure (cut k))
        filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with s hs hns
        obtain ⟨k, hlo, hhi⟩ := finite_partition_cell cut
          (by simpa only [hfirst] using hs.1.le)
          (by simpa only [hlast] using hs.2)
        have hk : s ∈ Ioo (cut k.castSucc) (cut k.succ) :=
          ⟨lt_of_le_of_ne hlo (hns k.castSucc).symm, hhi⟩
        rw [finiteStepFunction_on_cell hc v hk]
        exact (hv k s hk).symm
      rw [← integral_congr_ae hstep.restrict]
      have ht := integral_finiteStep_tail cut hc hfirst hlast v i.castSucc
      change (∫ s in Ioi (cut i.castSucc), finiteStepFunction cut v s ∂pathMeasure) = _ at ht
      simpa only [Fin.le_def, Fin.val_castSucc] using ht
    have hb : cut i.castSucc ∈ Icc (0 : ℝ) 1 :=
      ⟨by rw [← hfirst]; exact hc.monotone (Fin.zero_le _),
       by rw [← hlast]; exact hc.monotone (Fin.le_last _)⟩
    rw [integral_pathMeasure_Ioi trial hb] at he
    rw [he]
    simpa only [finiteFieldPath_single, mul_ite, mul_one, mul_zero] using hcontact i

end InvariantIsing

end

end OAI
