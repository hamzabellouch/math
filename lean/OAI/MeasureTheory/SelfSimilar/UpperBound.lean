import OAI.MeasureTheory.SelfSimilar.ExactDimension

namespace OAI

universe uι uM

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem sum_words_cons {M : Type uM} [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n+1) → ι) → M) :
    (∑ w, f w) = ∑ i, ∑ w : Fin n → ι, f (Fin.cons i w) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ι)).sum_comp f,Fintype.sum_prod_type]
  rfl

theorem completeMap_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.completeMap (Fin.cons i w) = (S.ratio i*(S.completeMap w).1,
      S.ratio i*(S.completeMap w).2+S.offset i) := by
  simp only [completeMap,List.ofFn_cons,wordAffine]

theorem wordWeight_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.wordWeight (Fin.cons i w) = S.weight i*S.wordWeight w := by
  simp only [wordWeight,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

def wordMap (S : System ι) {n : ℕ} (w : Fin n → ι) (x : ℝ) : ℝ :=
  (S.completeMap w).1*x+(S.completeMap w).2

theorem wordMap_measurable (S : System ι) {n : ℕ} (w : Fin n → ι) :
    Measurable (S.wordMap w) := by unfold wordMap; fun_prop

theorem wordMap_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.wordMap (Fin.cons i w) = S.affine i ∘ S.wordMap w := by
  funext x
  simp only [wordMap,completeMap_cons,affine,Function.comp_apply]
  ring

theorem selfSimilar_words (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ) (n : ℕ) :
    μ = ∑ w : Fin n → ι, ENNReal.ofReal (S.wordWeight w) • μ.map (S.wordMap w) := by
  classical
  induction n with
  | zero =>
    have hm : S.wordMap (default : Fin 0 → ι) = id := by
      funext x
      simp [wordMap,completeMap,wordAffine]
    simp [wordWeight,hm]
  | succ n ih =>
    rw [sum_words_cons]
    calc
      μ = ∑ i, ENNReal.ofReal (S.weight i) • μ.map (S.affine i) := hμ
      _ = ∑ i, ∑ w : Fin n → ι,
          ENNReal.ofReal (S.wordWeight (Fin.cons i w)) • μ.map (S.wordMap (Fin.cons i w)) := by
        apply Finset.sum_congr rfl
        intro i _
        conv_lhs => rw [ih]
        rw [Measure.map_finset_sum (S.affine_continuous i).measurable.aemeasurable,Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro w _
        rw [Measure.map_smul _ (S.affine_continuous i).measurable.aemeasurable,
          smul_smul,wordWeight_cons,ENNReal.ofReal_mul (S.weight_nonneg i),
          Measure.map_map (S.affine_continuous i).measurable (S.wordMap_measurable w),wordMap_cons]

theorem mapMass_dot (S : System ι) (n : ℕ) (f : ℝ × ℝ → ℝ) :
    (∑ g ∈ S.mapSupport n, S.mapMass n g*f g) = ∑ w : Fin n → ι, S.wordWeight w*f (S.completeMap w) := by
  classical
  exact FiniteEntropy.sum_mass_mul _ _ _ _ _ (fun w hw => Finset.mem_image_of_mem _ hw)

theorem wordWeight_expect_sum (S : System ι) (f : ι → ℝ) (n : ℕ) :
    (∑ w : Fin n → ι, S.wordWeight w * ∑ j, f (w j)) =
      (n : ℝ)*∑ i, S.weight i*f i := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_words_cons]
    simp only [wordWeight_cons,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,
      mul_add,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
      S.wordWeight_sum,one_mul,ih,S.weight_sum]
    push_cast
    ring

theorem completeMap_log_slope (S : System ι) {n : ℕ} (w : Fin n → ι) :
    Real.log |(S.completeMap w).1| = ∑ j, Real.log |S.ratio (w j)| := by
  rw [completeMap_slope,Finset.abs_prod,Real.log_prod]
  exact fun j _ => (S.ratio_pos (w j)).ne'

theorem completeMap_abs_lt_one (S : System ι) {n : ℕ} (hn : 0 < n) (w : Fin n → ι) :
    |(S.completeMap w).1| < 1 := by
  rw [completeMap_slope,Finset.abs_prod]
  calc
    _ < ∏ j : Fin n, (1 : ℝ) := Finset.prod_lt_prod_of_nonempty₀
      (fun j _ => S.ratio_pos (w j)) (fun j _ => S.ratio_lt_one (w j))
      ⟨⟨0,hn⟩,Finset.mem_univ _⟩
    _ = 1 := by simp

noncomputable def compressed (S : System ι) {n : ℕ} (hn : 0 < n) : System (S.mapSupport n) where
  ratio g := g.val.1
  offset g := g.val.2
  weight g := S.mapMass n g.val
  ratio_pos g := by
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp g.property
    rw [← hw]
    exact abs_pos.mpr (S.completeMap_slope_ne_zero w)
  ratio_lt_one g := by
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp g.property
    rw [← hw]
    exact S.completeMap_abs_lt_one hn w
  weight_pos g := S.mapMass_pos g.property
  weight_sum := by
    classical
    rw [← Finset.sum_subtype (S.mapSupport n) (fun _ => Iff.rfl)]
    exact S.mapMass_sum n

theorem selfSimilar_compressed (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ)
    {n : ℕ} (hn : 0 < n) : (S.compressed hn).SelfSimilar μ := by
  classical
  change μ = ∑ g : S.mapSupport n, ENNReal.ofReal (S.mapMass n g.val) •
    μ.map (fun x => g.val.1*x+g.val.2)
  rw [Finset.sum_coe_sort (S.mapSupport n) (fun g => ENNReal.ofReal (S.mapMass n g) •
    μ.map (fun x => g.1*x+g.2))]
  simp only [mapMass,ENNReal.ofReal_sum_of_nonneg (fun w _ => (S.wordWeight_pos w).le),Finset.sum_smul]
  have he : ∀ g ∈ S.mapSupport n,
      (∑ w ∈ (Finset.univ : Finset (Fin n → ι)).filter (S.completeMap · = g),
        ENNReal.ofReal (S.wordWeight w) • μ.map (fun x => g.1*x+g.2)) =
      ∑ w ∈ (Finset.univ : Finset (Fin n → ι)).filter (S.completeMap · = g),
        ENNReal.ofReal (S.wordWeight w) • μ.map (S.wordMap w) := by
    intro g _
    apply Finset.sum_congr rfl
    intro w hw
    rw [← (Finset.mem_filter.mp hw).2]
    rfl
  simp_rw [Finset.sum_congr rfl he]
  rw [Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S.mapSupport n)
    (g := S.completeMap (n := n)) (fun w hw => Finset.mem_image_of_mem _ hw)]
  exact S.selfSimilar_words μ hμ n

theorem compressed_lyapunov (S : System ι) {n : ℕ} (hn : 0 < n) :
    (S.compressed hn).lyapunov = (n : ℝ)*S.lyapunov := by
  classical
  change -(∑ g : S.mapSupport n, S.mapMass n g.val*(Real.log |g.val.1|/Real.log 2)) = _
  rw [Finset.sum_coe_sort (S.mapSupport n) (fun g => S.mapMass n g*(Real.log |g.1|/Real.log 2)),
    S.mapMass_dot]
  simp_rw [completeMap_log_slope,Finset.sum_div]
  rw [S.wordWeight_expect_sum (fun i => Real.log |S.ratio i|/Real.log 2)]
  simp only [lyapunov]
  ring

theorem compressed_symbol_entropy (S : System ι) {n : ℕ} (hn : 0 < n) :
    (∑ g : S.mapSupport n, Real.negMulLog ((S.compressed hn).weight g)) =
      S.walkEntropy n*Real.log 2 := by
  classical
  change (∑ g : S.mapSupport n, Real.negMulLog (S.mapMass n g.val)) = _
  rw [Finset.sum_coe_sort (S.mapSupport n) (fun g => Real.negMulLog (S.mapMass n g)),walkEntropy,
    div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne']

end EntropyRateDimension.System

namespace EntropyRateDimension.Coding
open MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

theorem exponent_symbol_entropy_bound (S : System ι) :
    exponent S * S.lyapunov * Real.log 2 ≤ ∑ i, Real.negMulLog (S.weight i) := by
  have hc : 0 ≤ ∫ ω, clippedLimit S ω ∂addressMeasure S :=
    integral_nonneg (fun ω => le_max_left 0 _)
  have hw : (∫ ω, weightObs S ω ∂addressMeasure S) =
      ∑ i, Real.negMulLog (S.weight i) := by
    change (∫ ω, -Real.log (S.weight (ω 0)) ∂addressMeasure S) = _
    rw [head_integral S (fun i => -Real.log (S.weight i))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Real.negMulLog]
    ring
  have he : exponent S*S.lyapunov*Real.log 2=infoRate S := by
    unfold exponent
    field_simp [S.lyapunov_pos.ne', (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne']
  rw [he,infoRate,hw]
  linarith

end EntropyRateDimension.Coding

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

theorem mapSupport_nonempty (S : System ι) (n : ℕ) : (S.mapSupport n).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

theorem exponent_le_walkEntropy (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {n : ℕ} (hn : 0 < n) :
    Coding.exponent S*S.lyapunov ≤ S.walkEntropy n/(n : ℝ) := by
  classical
  have : Nonempty (S.mapSupport n) := (S.mapSupport_nonempty n).to_subtype
  have he : Coding.exponent S = Coding.exponent (S.compressed hn) := by
    apply (ENNReal.ofReal_eq_ofReal_iff (Coding.exponent_nonneg S) (Coding.exponent_nonneg _)).mp
    rw [← S.selfSimilar_dimension μ hμ, ← (S.compressed hn).selfSimilar_dimension μ
      (S.selfSimilar_compressed μ hμ hn)]
  have hb := Coding.exponent_symbol_entropy_bound (S.compressed hn)
  rw [compressed_lyapunov,compressed_symbol_entropy,← he] at hb
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : Coding.exponent S*S.lyapunov*(n : ℝ) ≤ S.walkEntropy n := by
    apply (mul_le_mul_iff_left₀ hlog).mp
    nlinarith [hb]
  exact (le_div_iff₀ (by exact_mod_cast hn)).mpr hmul

theorem exponent_le_rate (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : Coding.exponent S ≤ S.entropyRate/S.lyapunov := by
  apply (le_div_iff₀ S.lyapunov_pos).mpr
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨n,rfl⟩
  exact S.exponent_le_walkEntropy μ hμ (Nat.succ_pos n)

theorem exponent_le_one (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : Coding.exponent S ≤ 1 := by
  have hh := lowerHausdorffDimension_le_one μ
  rw [S.selfSimilar_dimension μ hμ] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa only [ENNReal.ofReal_one] using hh)

theorem main_upper_bound (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    lowerHausdorffDimension μ ≤ ENNReal.ofReal (min 1 (S.entropyRate/S.lyapunov)) := by
  rw [S.selfSimilar_dimension μ hμ]
  exact ENNReal.ofReal_le_ofReal (le_min (S.exponent_le_one μ hμ) (S.exponent_le_rate μ hμ))

end EntropyRateDimension.System

end OAI
