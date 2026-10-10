import OAI.MeasureTheory.SelfSimilar.Model

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem weight_nonneg (S : System ι) (i : ι) : 0 ≤ S.weight i :=
  (S.weight_pos i).le

theorem weight_le_one (S : System ι) (i : ι) : S.weight i ≤ 1 := by
  rw [← S.weight_sum]
  exact Finset.single_le_sum (fun j _ => S.weight_nonneg j) (Finset.mem_univ i)

theorem affine_continuous (S : System ι) (i : ι) : Continuous (S.affine i) := by
  unfold affine
  fun_prop

theorem wordWeight_pos (S : System ι) {n : ℕ} (w : Fin n → ι) :
    0 < S.wordWeight w :=
  Finset.prod_pos (fun i _ => S.weight_pos (w i))

theorem wordWeight_sum (S : System ι) (n : ℕ) :
    ∑ w : Fin n → ι, S.wordWeight w = 1 := by
  classical
  simpa [wordWeight, S.weight_sum] using
    (Fintype.prod_sum (fun (_ : Fin n) i => S.weight i)).symm

theorem mapMass_nonneg (S : System ι) (n : ℕ) (g : ℝ × ℝ) :
    0 ≤ S.mapMass n g := by
  classical
  exact Finset.sum_nonneg (fun w _ => (S.wordWeight_pos w).le)

theorem mapMass_sum (S : System ι) (n : ℕ) :
    ∑ g ∈ S.mapSupport n, S.mapMass n g = 1 := by
  classical
  simp only [mapSupport, mapMass]
  rw [Finset.sum_fiberwise_of_maps_to]
  · exact S.wordWeight_sum n
  · exact fun w hw => Finset.mem_image_of_mem _ hw

theorem mapMass_pos (S : System ι) {n : ℕ} {g : ℝ × ℝ}
    (hg : g ∈ S.mapSupport n) : 0 < S.mapMass n g := by
  classical
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hg
  apply lt_of_lt_of_le (S.wordWeight_pos w)
  apply Finset.single_le_sum (fun v _ => (S.wordWeight_pos v).le)
  simp

theorem mapMass_le_one (S : System ι) (n : ℕ) (g : ℝ × ℝ) :
    S.mapMass n g ≤ 1 := by
  classical
  rw [mapMass, ← S.wordWeight_sum n]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun w _ _ => (S.wordWeight_pos w).le)

theorem walkEntropy_nonneg (S : System ι) (n : ℕ) : 0 ≤ S.walkEntropy n := by
  apply div_nonneg _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  apply Finset.sum_nonneg
  intro g _
  exact Real.negMulLog_nonneg (S.mapMass_nonneg n g) (S.mapMass_le_one n g)

theorem entropyRate_nonneg (S : System ι) : 0 ≤ S.entropyRate := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact div_nonneg (S.walkEntropy_nonneg _) (by positivity)

theorem entropyRate_le (S : System ι) (n : ℕ) :
    S.entropyRate ≤ S.walkEntropy (n + 1) / (n + 1 : ℕ) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact div_nonneg (S.walkEntropy_nonneg _) (by positivity)
  · exact ⟨n, rfl⟩

theorem lyapunov_pos [Nonempty ι] (S : System ι) : 0 < S.lyapunov := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lyapunov, neg_pos]
  apply Finset.sum_neg
  · intro i _
    exact mul_neg_of_pos_of_neg (S.weight_pos i)
      (div_neg_of_neg_of_pos (Real.log_neg (S.ratio_pos i) (S.ratio_lt_one i)) hlog)
  · exact Finset.univ_nonempty

end System

theorem lowerHausdorffDimension_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    lowerHausdorffDimension μ ≤ 1 := by
  calc
    lowerHausdorffDimension μ ≤ dimH (Set.univ : Set ℝ) :=
      iInf_le_of_le Set.univ (iInf_le_of_le MeasurableSet.univ
        (iInf_le_of_le (by simp : 0 < μ Set.univ) le_rfl))
    _ = 1 := Real.dimH_univ

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem exists_uniform_bounds (S : System ι) :
    ∃ c T : ℝ, 0 < c ∧ c < 1 ∧ 0 ≤ T ∧
      (∀ i, |S.ratio i| ≤ c) ∧ (∀ i, |S.offset i| ≤ T) := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i => |S.ratio i|)
    Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun i => |S.offset i|)
    Finset.univ_nonempty
  exact ⟨|S.ratio i|, |S.offset j|, S.ratio_pos i, S.ratio_lt_one i,
    abs_nonneg _, fun k => hi k (Finset.mem_univ k), fun k => hj k (Finset.mem_univ k)⟩

omit [Nonempty ι] in
theorem selfSimilar_apply (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ)
    {E : Set ℝ} (hE : MeasurableSet E) :
    μ E = ∑ i, ENNReal.ofReal (S.weight i) * μ ((S.affine i) ⁻¹' E) := by
  classical
  conv_lhs => rw [hμ]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (S.affine_continuous _).measurable hE]

theorem selfSimilar_compact (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : ∃ B : ℝ, 0 < B ∧ μ (Set.Icc (-B) B)ᶜ = 0 := by
  classical
  obtain ⟨c,T,hc,hc1,hT,hr,ht⟩ := S.exists_uniform_bounds
  let R := T/(1-c)
  have hR : 0 ≤ R := div_nonneg hT (sub_pos.mpr hc1).le
  have hRc : c*R+T = R := by
    dsimp only [R]
    field_simp [ne_of_gt (sub_pos.mpr hc1)]
    ring
  let a : ℕ → ℝ := fun n => R+(1/c)^n
  let E : ℕ → Set ℝ := fun n => {x | a n < |x|}
  have ha : ∀ n, c*a (n+1)+T = a n := by
    intro n
    dsimp only [a]
    rw [pow_succ]
    field_simp
    nlinarith [hRc]
  have hcInv : 1 < 1/c := (one_lt_div hc).mpr hc1
  have hm : Antitone E := by
    intro n m hnm x hx
    have hp := pow_le_pow_right₀ hcInv.le hnm
    change R+(1/c)^m < |x| at hx
    change R+(1/c)^n < |x|
    linarith
  have hE : ∀ n, MeasurableSet (E n) := fun n => measurableSet_lt measurable_const measurable_abs
  have hpre : ∀ n i, S.affine i ⁻¹' E n ⊆ E (n+1) := by
    intro n i x hx
    have hb : |S.affine i x| ≤ c*|x|+T := calc
      _ ≤ |S.ratio i*x|+|S.offset i| := abs_add_le _ _
      _ ≤ c*|x|+T := by rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_right (hr i) (abs_nonneg x)) (ht i)
    change a n < |S.affine i x| at hx
    change a (n+1) < |x|
    nlinarith [ha n]
  have hinc : ∀ n, μ (E n) ≤ μ (E (n+1)) := by
    intro n
    rw [S.selfSimilar_apply μ hμ (hE n)]
    calc
      _ ≤ ∑ i, ENNReal.ofReal (S.weight i)*μ (E (n+1)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl (measure_mono (hpre n i)))
      _ = μ (E (n+1)) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => S.weight_nonneg i), S.weight_sum,
          ENNReal.ofReal_one, one_mul]
  have hzero : (⋂ n, E n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hpow := (tendsto_pow_atTop_atTop_of_one_lt hcInv).eventually
      (Filter.eventually_gt_atTop (|x|-R))
    obtain ⟨n,hn⟩ := hpow.exists
    have he := Set.mem_iInter.mp hx n
    change R+(1/c)^n < |x| at he
    linarith
  have hlim := tendsto_measure_iInter_atTop (fun n => (hE n).nullMeasurableSet) hm
    ⟨0, measure_ne_top μ (E 0)⟩
  rw [hzero, measure_empty] at hlim
  have hb : ∀ n, μ (E 0) ≤ μ (E n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact ih.trans (hinc n)
  have hz : μ (E 0) = 0 := le_antisymm (ge_of_tendsto' hlim hb) bot_le
  refine ⟨R+1, by linarith, ?_⟩
  have heq : (Set.Icc (-(R+1)) (R+1))ᶜ = E 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, E, a, pow_zero, Set.mem_ofPred_eq,
      ← abs_le, not_le]
  rw [heq, hz]

end System

theorem binaryEntropy_quadratic_concave :
    ConcaveOn ℝ (Set.Icc 0 1) (fun x : ℝ => Real.binEntropy x+2*x^2) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun x =>
    Real.log (1-x)-Real.log x+4*x) (f'' := fun x => -(1-x)⁻¹-x⁻¹+4)
    (convex_Icc 0 1) (Real.binEntropy_continuous.add (by fun_prop)).continuousOn
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hd := (Real.hasDerivAt_binEntropy (ne_of_gt hx.1) (ne_of_lt hx.2)).add
      (((hasDerivAt_id x).pow 2).const_mul 2)
    exact (hd.congr_deriv (by dsimp; ring)).hasDerivWithinAt
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hd := (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log (by linarith : 1-x ≠ 0)).sub
      ((hasDerivAt_id x).log (ne_of_gt hx.1))
    exact ((hd.add ((hasDerivAt_id x).const_mul 4)).congr_deriv (by dsimp; ring)).hasDerivWithinAt
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hpos : 0 < x*(1-x) := mul_pos hx.1 (by linarith)
    have he : -(1-x)⁻¹-x⁻¹+4 = (4*x*(1-x)-1)/(x*(1-x)) := by
      field_simp [ne_of_gt hx.1, ne_of_gt (sub_pos.mpr hx.2)]
      ring
    rw [he]
    apply div_nonpos_of_nonpos_of_nonneg _ hpos.le
    nlinarith [sq_nonneg (2*x-1)]

theorem binaryEntropy_midpoint_gap (a b : ℝ) (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) :
    (a-b)^2/2 ≤ Real.binEntropy ((a+b)/2)-
      (Real.binEntropy a+Real.binEntropy b)/2 := by
  have hh := binaryEntropy_quadratic_concave.2 ha hb
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  simp only [smul_eq_mul] at hh
  have he : (1/2 : ℝ)*a+(1/2)*b=(a+b)/2 := by ring
  rw [he] at hh
  nlinarith [hh]

end EntropyRateDimension
end

end OAI
