import OAI.Probability.InvariantIsing.Spectral.SpectralReplicaProduct
import OAI.Probability.InvariantIsing.Core.TailOrder

namespace OAI

/-! A synchronized spin/tree pair turns a tree-level contact test into an
upper tail of the spin quantile. Atoms at partition endpoints are retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma integral_pathMeasure_Ioi (p : OverlapPath) {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ s in Ioi b, p s ∂pathMeasure) = pathTail p b := by
  have he : Ioi b ∩ Ioo (0 : ℝ) 1 = Ioo b 1 := by
    ext s
    constructor
    · intro hs; exact ⟨hs.1, hs.2.2⟩
    · intro hs; exact ⟨hs.1, hb.1.trans_lt hs.1, hs.2⟩
  rw [pathMeasure, Measure.restrict_restrict measurableSet_Ioi, he,
    pathTail, intervalIntegral.integral_of_le hb.2, integral_Ioc_eq_integral_Ioo]

theorem spectralPair_treeTail_integral {m n d : ℕ}
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
    {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (htail : (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(Q : Measure (SpectralArray (m + 1)))) = 1 - b) :
    (∫ x, spectralSpinArray x 0 1 * treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(Q : Measure (SpectralArray (m + 1)))) = pathTail (spectralSpinQuantilePath Q hP hn) b := by
  classical
  let w : Fin (m + 1) → ℝ := Pi.single (Fin.last m) 1
  have hw : ∀ a, 0 ≤ w a := by
    intro a
    simp only [w, Pi.single_apply]
    split_ifs <;> norm_num
  have hsu : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      spectralLinearArray (spectralSpinWeight m) x 0 1 ∈ Icc (0 : ℝ) 1 := by
    simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn
  have htu : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1 := by
    simpa only [w, spectralLinearArray_single, spectralCoordinateArray] using
      spectralCoordinate_unit hn (Fin.last m)
  have hm : Measurable (fun x : SpectralArray (m + 1) => spectralLinearArray w x 0 1) :=
    (continuous_spectralLinearEntry w).measurable.comp (measurable_pi_apply (0,1))
  have hms : Measurable (fun x : SpectralArray (m + 1) =>
      spectralLinearArray (spectralSpinWeight m) x 0 1) :=
    (continuous_spectralLinearEntry _).measurable.comp (measurable_pi_apply (0,1))
  have htL : ∀ᵐ s ∂spectralLinearLaw Q w, s ∈ treeLevels n := by
    change ∀ᵐ s ∂(Q : Measure _).map (fun x => spectralLinearArray w x 0 1), s ∈ treeLevels n
    apply (ae_map_iff hm.aemeasurable (isClosed_treeLevels n).measurableSet).mpr
    change ∀ᵐ x ∂(Q : Measure _), spectralLinearArray w x 0 1 ∈ treeLevels n
    filter_upwards [hlevel] with x hx
    simpa only [w, spectralLinearArray_single, spectralCoordinateArray] using hx
  have htM : (∫ s, treeTail n d s ∂spectralLinearLaw Q w) = 1 - b := by
    rw [spectralLinearLaw, integral_map hm.aemeasurable
      (continuous_treeTail n d).aestronglyMeasurable]
    simpa only [w, spectralLinearArray_single, spectralCoordinateArray] using htail
  have htq := quantile_treeTail (spectralLinearLaw_unit Q w htu) htL htM
  have hp := spectralQuantilePath_pair_law hgg hG q hq hd hE
    (spectralSpinWeight m) w (spectralSpinWeight_nonneg m) hw hsu htu
  let F : ℝ × ℝ → ℝ := fun z => z.1 * treeTail n d z.2
  have hF : AEStronglyMeasurable F
      (pathMeasure.map (fun s => (spectralQuantilePath Q (spectralSpinWeight m) hsu s,
        spectralQuantilePath Q w htu s))) := by
    exact (continuous_fst.mul ((continuous_treeTail n d).comp continuous_snd)).aestronglyMeasurable
  have hi := integral_map
    ((spectralQuantilePath Q (spectralSpinWeight m) hsu).measurable.prodMk
      (spectralQuantilePath Q w htu).measurable).aemeasurable hF
  rw [hp] at hi
  have hiF : AEStronglyMeasurable F ((Q : Measure _).map
      (fun x => (spectralLinearArray (spectralSpinWeight m) x 0 1,
        spectralLinearArray w x 0 1))) := by
    exact (continuous_fst.mul ((continuous_treeTail n d).comp continuous_snd)).aestronglyMeasurable
  rw [integral_map (hms.prodMk hm).aemeasurable hiF] at hi
  have he : (∫ s, spectralSpinQuantilePath Q hP hn s *
      treeTail n d (spectralQuantilePath Q w htu s) ∂pathMeasure) =
      ∫ s in Ioi b, spectralSpinQuantilePath Q hP hn s ∂pathMeasure := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [htq] with s hs
    change _ * treeTail n d (quantileFunction (spectralLinearLaw Q w) s) = _
    rw [hs]
    by_cases hbs : b < s <;> simp [hbs]
  rw [integral_pathMeasure_Ioi _ hb] at he
  simpa only [F, spectralLinearArray_spinWeight, w, spectralLinearArray_single,
    spectralCoordinateArray, spectralSpinQuantilePath] using hi.trans he

end InvariantIsing

end

end OAI
