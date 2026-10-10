import OAI.Probability.FirstPassage.OrientedProbability

namespace OAI

namespace PlanarFPP
open Finset Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def badContourEvent (G : Vertex → Set Ω) {n : ℕ} (c : EnclosingLoop n) : Set Ω :=
  {ω | ∀ v ∈ c.val.badSites, ω ∉ G v}

omit [MeasurableSpace Ω] in
theorem no_infinite_path_subset_contours (G : Vertex → Set Ω) :
    {ω | ¬infiniteOrientedPath (fun v => ω ∈ G v) 0} ⊆
      ⋃ n : ℕ, ⋃ c : EnclosingLoop n, badContourEvent G c := by
  intro ω hω
  obtain ⟨m,hm,c,hn,hw,hbad,_⟩ :=
    no_infinite_path_enclosing_contour (fun v => ω ∈ G v) 0 hω
  cases m with
  | zero => omega
  | succ n =>
    exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨⟨c,hw,hn⟩,hbad⟩⟩

omit [IsProbabilityMeasure P] in
theorem bad_contours_fixed_length (G : Vertex → Set Ω) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (hbad : ∀ v, P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2)) (n : ℕ) :
    P (⋃ c : EnclosingLoop n, badContourEvent G c) ≤
      9*(1/64 : ℝ≥0∞)^(n+1) := by
  classical
  have hc (c : EnclosingLoop n) : P (badContourEvent G c) ≤ (1/1024 : ℝ≥0∞)^(n+1) :=
    contour_bad_probability c.val c.property.2 G k hind _ (by norm_num) hbad
  have hcard : (Fintype.card (EnclosingLoop n) : ℝ≥0∞) ≤ 9*16^(n+1) := by
    exact_mod_cast enclosingLoop_card_geometric n
  calc
    _ ≤ ∑' c : EnclosingLoop n, P (badContourEvent G c) := measure_iUnion_le _
    _ = ∑ c : EnclosingLoop n, P (badContourEvent G c) := tsum_fintype _
    _ ≤ ∑ _c : EnclosingLoop n, (1/1024 : ℝ≥0∞)^(n+1) := sum_le_sum (fun c _ => hc c)
    _ = (Fintype.card (EnclosingLoop n) : ℝ≥0∞)*(1/1024)^(n+1) := by simp [nsmul_eq_mul]
    _ ≤ (9*16^(n+1))*(1/1024 : ℝ≥0∞)^(n+1) := by simpa only [mul_comm] using mul_le_mul_right hcard ((1/1024 : ℝ≥0∞)^(n+1))
    _ = _ := by
      rw [mul_assoc, ← mul_pow]
      have he : (16 : ℝ≥0∞)*(1/1024) = 1/64 := by
        apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by norm_num) (by norm_num)) (by simp)).mp
        norm_num
      rw [he]

omit [IsProbabilityMeasure P] in

theorem no_infinite_path_probability (G : Vertex → Set Ω) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (hbad : ∀ v, P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2)) :
    P {ω | ¬infiniteOrientedPath (fun v => ω ∈ G v) 0} ≤ (1/7 : ℝ≥0∞) := by
  calc
    _ ≤ P (⋃ n : ℕ, ⋃ c : EnclosingLoop n, badContourEvent G c) :=
      measure_mono (no_infinite_path_subset_contours G)
    _ ≤ ∑' n : ℕ, P (⋃ c : EnclosingLoop n, badContourEvent G c) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, 9*(1/64 : ℝ≥0∞)^(n+1) :=
      ENNReal.tsum_le_tsum (bad_contours_fixed_length G k hind hbad)
    _ = _ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
      have hlt : (1/64 : ℝ≥0∞) < 1 := by norm_num
      have hsub : (1 - 1/64 : ℝ≥0∞) ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hlt)
      apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (by norm_num) (by simpa using hsub))) (by simp)).mp
      norm_num [ENNReal.toReal_sub_of_le hlt.le]

theorem high_density_oriented_paths (G : Vertex → Set Ω)
    (hG : ∀ v, MeasurableSet (G v)) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (hbad : ∀ v, P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2)) :
    0 < P {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} := by
  have hb := no_infinite_path_probability G k hind hbad
  have hm := measurableSet_infiniteOrientedPath G hG 0
  by_contra hn
  have hz : P {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} = 0 :=
    le_antisymm (le_of_not_gt hn) bot_le
  change P ({ω | infiniteOrientedPath (fun v => ω ∈ G v) 0}ᶜ) ≤ _ at hb
  rw [measure_compl hm (measure_ne_top P _), measure_univ, hz] at hb
  norm_num at hb

theorem high_density_oriented_paths_real_bound (k : ℕ) (G : Vertex → Set Ω)
    (hG : ∀ v, MeasurableSet (G v)) (hi : SeparatedGoodIndependent P G k)
    (hb : ∀ v, P.real (G v)ᶜ ≤ (1/1024 : ℝ)^(8*(2*k+1)^2)) :
    0 < P.real {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} := by
  have hb' (v : Vertex) : P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2) := by
    have hh := ENNReal.ofReal_le_ofReal (hb v)
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)] at hh
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/1024),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1024),
      ENNReal.ofReal_one, ENNReal.ofReal_natCast] using hh
  have hp := high_density_oriented_paths G hG k hi hb'
  exact ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top P _)

theorem high_density_oriented_paths_real (k : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ G : Vertex → Set Ω,
      (∀ v, MeasurableSet (G v)) → SeparatedGoodIndependent P G k →
      (∀ v, P.real (G v)ᶜ ≤ ζ) →
      0 < P.real {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} :=
  ⟨(1/1024 : ℝ)^(8*(2*k+1)^2),pow_pos (by norm_num) _,
    fun G hG hi hb => high_density_oriented_paths_real_bound k G hG hi hb⟩

theorem high_density_oriented_paths_uniform (k : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ (Ω' : Type*) [MeasurableSpace Ω']
      (P' : Measure Ω') [IsProbabilityMeasure P'] (G : Vertex → Set Ω'),
      (∀ v, MeasurableSet (G v)) → SeparatedGoodIndependent P' G k →
      (∀ v, P'.real (G v)ᶜ ≤ ζ) →
      0 < P'.real {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} := by
  refine ⟨(1/1024 : ℝ)^(8*(2*k+1)^2),pow_pos (by norm_num) _,?_⟩
  intro Ω' _ P' _ G hG hi hb
  exact high_density_oriented_paths_real_bound k G hG hi hb

end PlanarFPP

end OAI
