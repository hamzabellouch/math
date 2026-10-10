import OAI.MeasureTheory.SelfSimilar.EntropyDimension

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace EntropyRateDimension.LocalMass
open MeasureEntropy

theorem dim_le_of_uniform_lower_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : Set ℝ) {B e R : ℝ} (he : 0 ≤ e) (hR : 0 < R)
    (hE : E ⊆ Icc (-B) B)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
      (r/2)^e ≤ μ.real (ball x r)) : dimH E ≤ ENNReal.ofReal e := by
  classical
  let a : ℝ → Finset ℤ := fun s =>
    (Finset.Icc ⌊-B/s⌋ ⌊B/s⌋).filter (fun i => ∃ x ∈ E, label s 0 x=i)
  let cell : ℝ → ℤ → Set ℝ := fun s i => Icc (s*(i : ℝ)) (s*((i : ℝ)+1))
  have hdiam : ∀ s i, ediam (cell s i)=ENNReal.ofReal s := by
    intro s i
    change ediam (Icc (s*(i : ℝ)) (s*((i : ℝ)+1)))=ENNReal.ofReal s
    rw [Real.ediam_Icc]
    congr 1
    ring
  have hcover : ∀ s : ℝ, 0 < s → E ⊆ ⋃ i : a s, cell s i.val := by
    intro s hs x hx
    have hi : label s 0 x ∈ a s := by
      apply Finset.mem_filter.mpr
      refine ⟨?_,x,hx,rfl⟩
      simpa only [add_zero] using label_in_interval (u := 0) hs (hE hx)
    apply mem_iUnion.mpr
    refine ⟨⟨label s 0 x,hi⟩,?_⟩
    change s*(label s 0 x : ℝ) ≤ x ∧ x ≤ s*((label s 0 x : ℝ)+1)
    simp only [label,add_zero]
    constructor
    · have hh := (le_div_iff₀ hs).mp (Int.floor_le (x/s))
      simpa only [mul_comm] using hh
    · have hh := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (x/s))
      simpa only [mul_comm] using hh.le
  have hcount : ∀ s : ℝ, 0 < s → s < R →
      ((a s).card : ℝ)*s^e ≤ 3*(4 : ℝ)^e := by
    intro s hs hsR
    have has : ∀ i ∈ a s, ∃ x ∈ E, label s 0 x=i :=
      fun i hi => (Finset.mem_filter.mp hi).2
    let x : ℤ → ℝ := fun i => if hi : i ∈ a s then (has i hi).choose else 0
    have hx : ∀ i ∈ a s, x i ∈ E ∧ label s 0 (x i)=i := by
      intro i hi
      simp only [x,dite_eq_left hi]
      exact (has i hi).choose_spec
    have hh := good_labels_card_bound μ hs (a s) x (fun i hi => (hx i hi).2)
      (q := (s/4)^e) (fun i hi => by
        have hh := hball (x i) (hx i hi).1 (s/2) (by positivity) (by linarith)
        simpa only [show s/2/2=s/4 by ring] using hh)
    have h4 : (4 : ℝ)^e ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    calc
      ((a s).card : ℝ)*s^e = (((a s).card : ℝ)*(s/4)^e)*(4 : ℝ)^e := by
        rw [Real.div_rpow hs.le (by norm_num)]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by norm_num) _)
  let s : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hs : ∀ n, 0 < s n := fun n => by dsimp [s]; positivity
  have hsz : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrz : Tendsto (fun n => ENNReal.ofReal (s n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsz
  have hh := Measure.hausdorffMeasure_le_liminf_sum e E
    (fun n => ENNReal.ofReal (s n)) hrz (fun n (i : a (s n)) => cell (s n) i.val)
    (Eventually.of_forall (fun n i => (hdiam _ _).le))
    (Eventually.of_forall (fun n => hcover _ (hs n)))
  have hlim : liminf (fun n => ∑ i : a (s n), ediam (cell (s n) i.val)^e) atTop ≤
      ENNReal.ofReal (3*(4 : ℝ)^e) := by
    refine liminf_le_of_frequently_le ?_ (by isBoundedDefault)
    apply Filter.Eventually.frequently
    filter_upwards [hsz.eventually (gt_mem_nhds hR)] with n hn
    calc
      (∑ i : a (s n), ediam (cell (s n) i.val)^e) =
          ENNReal.ofReal (((a (s n)).card : ℝ)*(s n)^e) := by
        simp only [hdiam,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
          ENNReal.ofReal_rpow_of_pos (hs n)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hcount _ (hs n) hn)
  have hfin : Measure.hausdorffMeasure e E ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hh.trans hlim)
  have hdim := dimH_le_of_hausdorffMeasure_ne_top (d := ⟨e,he⟩) hfin
  exact hdim.trans_eq (ENNReal.coe_nnreal_eq ⟨e,he⟩)

theorem lower_dim_eq_of_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : CompactlyCarried μ) {d : ℝ} (hd : 0 ≤ d)
    (hlim : ∀ᵐ x ∂μ, Tendsto
      (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r) (𝓝[>] 0) (𝓝 d)) :
    lowerHausdorffDimension μ = ENNReal.ofReal d := by
  apply le_antisymm _ (lower_dim_ge_of_limit μ hlim)
  have hub : ∀ e : ℝ, d < e → lowerHausdorffDimension μ ≤ ENNReal.ofReal e := by
    intro e hde
    have he := hd.trans hde.le
    obtain ⟨E,hE,hEc,R,hR,hball⟩ := large_uniform_mass_set μ he (by norm_num : (0 : ℝ)<1/2) (by
      filter_upwards [hlim,μ.support_mem_ae] with x hx hs
      exact eventual_lower_of_limit μ hs hde hx)
    obtain ⟨B,_,hB⟩ := hc
    let F := E ∩ Icc (-B) B
    have hF : MeasurableSet F := hE.inter measurableSet_Icc
    have hpos : 0 < μ F := by
      by_contra hn
      have hz : μ F=0 := le_antisymm (le_of_not_gt hn) bot_le
      have hEF : E =ᵐ[μ] F := by
        filter_upwards [show ∀ᵐ x ∂μ, x ∈ Icc (-B) B from ae_iff.mpr hB] with x hx
        apply propext
        exact ⟨fun h => ⟨h,hx⟩,fun h => h.1⟩
      have hez : μ E=0 := (measure_congr hEF).trans hz
      have hec : μ.real Eᶜ=1 := by simp [Measure.real,measure_compl hE (measure_ne_top μ E),hez]
      linarith
    calc
      lowerHausdorffDimension μ ≤ dimH F :=
        iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le hpos le_rfl))
      _ ≤ ENNReal.ofReal e := dim_le_of_uniform_lower_mass μ F he hR inter_subset_right
        (fun x hx r hr hrR => hball x hx.1 r hr hrR)
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (d+1/((n : ℝ)+1))) atTop
      (𝓝 (ENNReal.ofReal d)) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    simpa only [add_zero] using (tendsto_const_nhds (x := d)).add tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto ht (Eventually.of_forall (fun n => hub _ (by
    have : 0 < 1/((n : ℝ)+1) := by positivity
    linarith)))

end EntropyRateDimension.LocalMass

end

end OAI
