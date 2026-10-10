import OAI.MeasureTheory.SelfSimilar.Attractor
import OAI.MeasureTheory.SelfSimilar.NoOverlaps

namespace OAI

universe uι

open scoped BigOperators ENNReal Topology
open MeasureTheory Set Filter

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

noncomputable def similaritySum (S : System ι) (s : ℝ) : ℝ := ∑ i, |S.ratio i| ^ s

theorem similaritySum_strictAnti (S : System ι) : StrictAnti (similaritySum S) := by
  intro a b hab
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    (fun i _ => Real.rpow_lt_rpow_of_exponent_gt (S.ratio_pos i) (S.ratio_lt_one i) hab)

/-- Includes the one-symbol boundary: no assumption of at least two symbols. -/
theorem existsUnique_similarityDimension (S : System ι) :
    ∃! s : ℝ, 0 ≤ s ∧ similaritySum S s = 1 := by
  have hcont : Continuous (similaritySum S) :=
    continuous_finsetSum _ (fun i _ => Real.continuous_const_rpow (S.ratio_pos i).ne')
  have hlim : Tendsto (similaritySum S) atTop (𝓝 0) := by
    change Tendsto (fun s : ℝ => ∑ i, |S.ratio i| ^ s) atTop (𝓝 0)
    have hh : Tendsto (fun s : ℝ => ∑ i, |S.ratio i| ^ s) atTop
        (𝓝 (∑ _i : ι, (0 : ℝ))) :=
      tendsto_finsetSum Finset.univ (fun i _ =>
        tendsto_rpow_atTop_of_base_lt_one |S.ratio i|
          (lt_trans (by norm_num : (-1 : ℝ) < 0) (S.ratio_pos i))
          (S.ratio_lt_one i))
    simpa only [Finset.sum_const_zero] using hh
  obtain ⟨b, hb, hb0⟩ :=
    ((hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).and
      (eventually_ge_atTop (0 : ℝ))).exists
  have hzero : 1 ≤ similaritySum S 0 := by
    simpa [similaritySum] using (show (1 : ℝ) ≤ Fintype.card ι by
      exact_mod_cast Fintype.card_pos (α := ι))
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' hb0 hcont.continuousOn
    (show (1 : ℝ) ∈ Set.Icc (similaritySum S b) (similaritySum S 0) from ⟨hb.le, hzero⟩)
  refine ⟨s, ⟨hs.1, he⟩, ?_⟩
  intro t ht
  exact (similaritySum_strictAnti S).injective (ht.2.trans he.symm)

noncomputable def similarityDimension (S : System ι) : ℝ :=
  (existsUnique_similarityDimension S).exists.choose

theorem similarityDimension_nonneg (S : System ι) : 0 ≤ similarityDimension S :=
  (existsUnique_similarityDimension S).exists.choose_spec.1

theorem similarityDimension_equation (S : System ι) :
    ∑ i, |S.ratio i| ^ similarityDimension S = 1 :=
  (existsUnique_similarityDimension S).exists.choose_spec.2

theorem similarityDimension_single_symbol (S : System ι) (hcard : Fintype.card ι = 1) :
    similarityDimension S = 0 := by
  apply (similaritySum_strictAnti S).injective
  rw [show similaritySum S (similarityDimension S) = 1 from similarityDimension_equation S]
  simp [similaritySum, hcard]

noncomputable def similaritySystem (S : System ι) {s : ℝ}
    (hroot : ∑ i, |S.ratio i| ^ s = 1) : System ι where
  ratio := S.ratio
  offset := S.offset
  weight := fun i => |S.ratio i| ^ s
  ratio_pos := S.ratio_pos
  ratio_lt_one := S.ratio_lt_one
  weight_pos := fun i => Real.rpow_pos_of_pos (S.ratio_pos i) s
  weight_sum := hroot

omit [Nonempty ι] in
theorem similaritySystem_attractor (S : System ι) {s : ℝ}
    (hroot : ∑ i, |S.ratio i| ^ s = 1) :
    attractor (similaritySystem S hroot) = attractor S := rfl

omit [Nonempty ι] in
theorem similaritySystem_noExactOverlaps (S : System ι) {s : ℝ}
    (hroot : ∑ i, |S.ratio i| ^ s = 1) (h : NoExactOverlaps S) :
    NoExactOverlaps (similaritySystem S hroot) := by
  have heq : ∀ u : List ι, (similaritySystem S hroot).wordAffine u = S.wordAffine u := by
    intro u
    induction u with
    | nil => rfl
    | cons i u ih =>
      exact congrArg (fun z : ℝ × ℝ =>
        (S.ratio i * z.1, S.ratio i * z.2 + S.offset i)) ih
  intro u v huv
  apply h
  rw [← heq u, ← heq v]
  exact huv

omit [Nonempty ι] in
theorem similaritySystem_entropy (S : System ι) {s : ℝ}
    (hroot : ∑ i, |S.ratio i| ^ s = 1) :
    symbolEntropy (similaritySystem S hroot) =
      s * naturalLyapunov (similaritySystem S hroot) := by
  simp only [symbolEntropy, naturalLyapunov, similaritySystem, Real.negMulLog,
    Real.log_rpow (S.ratio_pos _), mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem naturalLyapunov_pos (S : System ι) : 0 < naturalLyapunov S := by
  have h := S.lyapunov_pos
  rw [lyapunov_eq_naturalLyapunov] at h
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact ((div_pos_iff.mp h).resolve_right (fun hh => (not_lt_of_ge h2.le) hh.2)).1

theorem coding_law_attractor_mass [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) : Coding.law S (attractor S) = 1 := by
  rw [Coding.law, Measure.map_apply (Coding.point_measurable S)
    (attractor_compact S).measurableSet]
  have he : Coding.point S ⁻¹' attractor S = Set.univ := by
    ext ω
    simp [attractor]
  rw [he, measure_univ]

theorem coding_law_dimension_le_attractor [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) : lowerHausdorffDimension (Coding.law S) ≤ dimH (attractor S) := by
  exact iInf_le_of_le (attractor S) (iInf_le_of_le (attractor_compact S).measurableSet
    (iInf_le_of_le (by rw [coding_law_attractor_mass]; exact zero_lt_one) le_rfl))

/-- The set-dimension corollary for an arbitrary normalized similarity exponent. -/
theorem no_exact_overlaps_attractor_dimension_of_root (S : System ι) {s : ℝ}
    (hs : 0 ≤ s) (hroot : ∑ i, |S.ratio i| ^ s = 1) (h : NoExactOverlaps S) :
    dimH (attractor S) = ENNReal.ofReal (min 1 s) := by
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let T := similaritySystem S hroot
  apply le_antisymm
  · rw [ENNReal.ofReal_min]
    exact le_min (by simpa using attractor_dim_le_one S) (attractor_dim_le_similarity S hs hroot)
  · have hd := no_exact_overlaps_dimension T (Coding.law T) (Coding.law_selfSimilar T)
      (similaritySystem_noExactOverlaps S hroot h)
    rw [similaritySystem_entropy S hroot,
      mul_div_cancel_right₀ _ (naturalLyapunov_pos T).ne'] at hd
    rw [← hd]
    exact coding_law_dimension_le_attractor T

/-- Source corollary `cor:set`, with the genuine compact coding attractor and the
uniquely constructed similarity dimension; the one-map case is included. -/
theorem no_exact_overlaps_attractor_dimension (S : System ι) (h : NoExactOverlaps S) :
    dimH (attractor S) = ENNReal.ofReal (min 1 (similarityDimension S)) :=
  no_exact_overlaps_attractor_dimension_of_root S (similarityDimension_nonneg S)
    (similarityDimension_equation S) h

end EntropyRateDimension.Extensions

end OAI
