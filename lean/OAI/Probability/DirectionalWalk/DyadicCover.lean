import OAI.Probability.DirectionalWalk.BandContacts

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma dyadic_band_cover (H : ℕ → ℕ) (a b h : ℕ) (hab : a ≤ b)
    (ha : H (4*2^a) < h) (hb : h ≤ H (8*2^b)) :
    ∃ j ∈ Finset.Icc a b, H (4*2^j) < h ∧ h ≤ H (8*2^j) := by
  induction b,hab using Nat.le_induction with
  | base => exact ⟨a,Finset.mem_Icc.mpr ⟨le_rfl,le_rfl⟩,ha,hb⟩
  | succ b hab ih =>
    by_cases hh : h ≤ H (8*2^b)
    · obtain ⟨j,hj,hjlo,hjhi⟩ := ih hh
      exact ⟨j,Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2.trans (Nat.le_succ b)⟩,hjlo,hjhi⟩
    · refine ⟨b+1,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩,?_,hb⟩
      have hp : 4*2^(b+1) = 8*2^b := by rw [pow_succ];omega
      rw [hp]
      exact lt_of_not_ge hh

lemma coveredDepthBand_le_index_sum {d : ℕ} (e : Step d)
    (ν : Bool → Measure (Word d)) [∀ b, IsProbabilityMeasure (ν b)]
    (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < placedWidth e b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut (placedWidth e) H)
    (hi : Integrable (fun Z => (firstCommonWidth (placedWidth e) Z : ℝ)) (twoTapeLaw ν))
    (a b low high : ℕ) (hab : a ≤ b) (hlow : 0 < low) (hhigh : high ≤ 8*2^b) :
    twoTapeLaw ν (coveredDepthBand e low high) ≤
      ((4*2^a : ℕ) : ℝ≥0∞) * ENNReal.ofReal (∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν) / (low : ℝ≥0∞) +
      ∑ j ∈ Finset.Icc a b, twoTapeLaw ν (commonBandContact e (2^j)) := by
  let B := {Z | low ≤ commonDepth (placedWidth e) Z (4*2^a)}
  have hh : twoTapeLaw ν (coveredDepthBand e low high) ≤
      twoTapeLaw ν B + twoTapeLaw ν (⋃ j ∈ Finset.Icc a b, commonBandContact e (2^j)) := by
    refine (measure_mono_ae (t := B ∪ ⋃ j ∈ Finset.Icc a b, commonBandContact e (2^j)) ?_).trans (measure_union_le _ _)
    filter_upwards [ae_common_iterates ν (placedWidth e) hL he] with Z hZ
    intro hcov
    by_cases hbad : Z ∈ B
    · exact Or.inl hbad
    apply Or.inr
    obtain ⟨h,hlo,hhi,hcon⟩ := hcov
    have hmon := commonDepth_strictMono (placedWidth e) Z hZ
    obtain ⟨j,hj,hja,hjb⟩ := dyadic_band_cover (commonDepth (placedWidth e) Z) a b h hab
      ((lt_of_not_ge hbad).trans_le hlo) (hhi.le.trans (hhigh.trans (hmon.id_le _)))
    exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,h,hja,hjb,hcon⟩⟩
  exact hh.trans (add_le_add (commonDepth_markov ν (placedWidth e) hL he hi (4*2^a) low hlow)
    (measure_biUnion_finset_le _ _))

lemma sum_shift_four_sub (h : ℕ → ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, (h (j+4)-h j)) =
      h J+h (J+1)+h (J+2)+h (J+3)-h 0-h 1-h 2-h 3 := by
  induction J with
  | zero => simp;ring
  | succ J ih =>
    rw [Finset.sum_range_succ,ih]
    have h1 : J+1+1 = J+2 := by omega
    have h2 : J+1+2 = J+3 := by omega
    have h3 : J+1+3 = J+4 := by omega
    simp only [h1,h2,h3]
    ring

lemma sum_shift_four_le (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) (hm : Monotone h) (J : ℕ) :
    (∑ j ∈ Finset.range J, (h (j+4)-h j)) ≤ 4*h (J+3) := by
  rw [sum_shift_four_sub]
  have ha := hm (show J ≤ J+3 by omega)
  have hb := hm (show J+1 ≤ J+3 by omega)
  have hc := hm (show J+2 ≤ J+3 by omega)
  linarith [h0 0,h0 1,h0 2,h0 3]

lemma log_nat_pow_two_add_one (j : ℕ) :
    Real.log (((2:ℕ)^j : ℝ)+1) ≤ (j+1)*Real.log 2 := by
  have hp : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hh : ((2:ℕ)^j : ℝ)+1 ≤ (2:ℝ)^(j+1) := by
    push_cast
    rw [pow_succ]
    linarith
  have ht := Real.log_le_log (by positivity : (0:ℝ) < ((2:ℕ)^j : ℝ)+1) hh
  rw [Real.log_pow] at ht
  simpa only [Nat.cast_add,Nat.cast_one] using ht

lemma entropy_dyadic_telescope {q : ℕ} (ν : Measure (Fin q → ℤ)) [IsProbabilityMeasure ν]
    (hi : ∀ i, Integrable (fun x => |(x i : ℝ)|) ν) (a : ℝ) (ha : 0 < a)
    (hb : ∀ i, (∫ x, |(x i : ℝ)| ∂ν) ≤ a) (J : ℕ) :
    (∑ j ∈ Finset.range J, (entropyOf (sumLaw ν (14*2^j)) id-entropyOf (sumLaw ν (2^j)) id)) ≤
      4*q*(1+Real.log 2+Real.log (a+1)+(J+4)*Real.log 2) := by
  let h := fun j => entropyOf (sumLaw ν (2^j)) id
  have hall (n : ℕ) := (sumLaw_lattice_entropy ν hi a ha hb n).1
  have hm := sumLaw_entropy_monotone ν hall
  have hmono : Monotone h := by
    intro m n hmn
    apply hm
    exact Nat.pow_le_pow_right (by norm_num) hmn
  have hsum : (∑ j ∈ Finset.range J, (entropyOf (sumLaw ν (14*2^j)) id-entropyOf (sumLaw ν (2^j)) id)) ≤
      ∑ j ∈ Finset.range J, (h (j+4)-h j) := by
    apply Finset.sum_le_sum
    intro j hj
    apply sub_le_sub_right
    apply hm
    rw [pow_add]
    omega
  refine hsum.trans ((sum_shift_four_le h (fun _ => entropyOf_nonneg _ _) hmono J).trans ?_)
  have hh := (sumLaw_lattice_entropy ν hi a ha hb (2^(J+3))).2
  have hl := log_nat_pow_two_add_one (J+3)
  have hq : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hb' : h (J+3) ≤ q*(1+Real.log 2+Real.log (a+1)+(J+4)*Real.log 2) := by
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ hq)
    have he : ((J+3 : ℕ) : ℝ)+1 = (J:ℝ)+4 := by push_cast;ring
    rw [he] at hl
    push_cast at *
    linarith
  nlinarith

lemma kl_event_scale_bound {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hfin : InformationTheory.klDiv P Q ≠ ∞) (E : Set Ω) (hE : MeasurableSet E)
    (B : ℝ) (hB : 1 ≤ B) :
    Real.log B * P.real E ≤ (InformationTheory.klDiv P Q).toReal + Real.log 2 +
      Real.log B * B * Q.real E := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hkl : 0 ≤ (InformationTheory.klDiv P Q).toReal := ENNReal.toReal_nonneg
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hq : Q.real E = 0
  · have hq' : Q E = 0 := (ENNReal.toReal_eq_zero_iff _).mp hq |>.resolve_right (measure_ne_top Q E)
    have hp := (InformationTheory.klDiv_ne_top_iff.mp hfin).1 hq'
    simp only [measureReal_def,hp,hq',ENNReal.toReal_zero,mul_zero]
    linarith
  by_cases hsmall : Q.real E ≤ B⁻¹
  · have hq0 : 0 < Q.real E := lt_of_le_of_ne measureReal_nonneg (Ne.symm hq)
    have hh := Real.log_le_log hq0 hsmall
    rw [Real.log_inv] at hh
    have hb := kl_event_bound P Q hfin E hE
    have hp := mul_le_mul_of_nonneg_left (neg_le_neg hh) (measureReal_nonneg (μ := P) (s := E))
    have ht : 0 ≤ Real.log B*B*Q.real E := mul_nonneg (mul_nonneg hlog hB0.le) measureReal_nonneg
    nlinarith
  · have ht : 1 ≤ B*Q.real E := by
      have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hsmall) hB0.le
      simpa only [mul_inv_cancel₀ hB0.ne'] using hh
    have hp := measureReal_le_one (μ := P) (s := E)
    nlinarith [mul_le_mul_of_nonneg_left ht hlog]

lemma placed_cut_positive {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) (H : ℕ) (b : Bool) :
    Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection (placedAxis e b)))
      (renewalCut (placedWidth e b) H) ≠ 0 := by
  rw [show Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection (placedAxis e b)))
      (renewalCut (placedWidth e b) H) = axisReachProb μ (placedAxis e b) H from
      axis_tapeCut_mass μ hell _ (hp b) H]
  exact ne_of_gt ((hp b).trans_le (axisReachProb_lower μ hell _ _))

lemma experiment_probability {α G : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [AddCommGroup G] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G) (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (experimentLaw ν L D n) :=
  probabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma reference_probability {α G : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [AddCommGroup G] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G)
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (n : ℕ) [NeZero n] : IsProbabilityMeasure (experimentReference ν L D n) := by
  let := experiment_probability ν L D n
  let : IsMarkovKernel (signedThreeKernel (ν false) (L false)) := signedThreeKernel_markov _ _ (fun H => hu H false)
  let : IsMarkovKernel (signedThreeKernel (ν true) (L true)) := signedThreeKernel_markov _ _ (fun H => hu H true)
  unfold experimentReference
  infer_instance

lemma placed_reference_summable {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    Summable (fun j => (experimentReference (fun b => slabLaw μ (axisDirection (placedAxis e b)))
      (placedWidth e) (fun _ => wordEnd) (2^j)).real (experimentContact e)) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) := fun b => slabLaw_probability μ _ (hp b)
  let := slabLaw_probability μ (axisDirection e) (hp false)
  let := slabLaw_probability μ (axisDirection (oppositeStep e)) (hp true)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  obtain ⟨he,hi⟩ := placed_common_data μ hell e hp
  let W := ∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν
  let C := ((annealed μ 0 (nonBacktracking (axisDirection e))).toReal)⁻¹^2 *
    ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e)))).toReal)⁻¹^2 * 24 * W
  have hc : Summable (fun j => C*((2:ℝ)^j*(axisWidthTail μ e (2^j)).toReal+
      (2:ℝ)^j*(axisWidthTail μ (oppositeStep e) (2^j)).toReal)) :=
    ((summable_dyadic_axisWidthTail μ hell e (hp false)).add
      (summable_dyadic_axisWidthTail μ hell (oppositeStep e) (hp true))).mul_left C
  apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) _ hc
  intro j
  let : NeZero ((2:ℕ)^j) := ⟨pow_ne_zero _ (by norm_num)⟩
  let := reference_probability ν (placedWidth e) (fun _ => wordEnd) (placed_cut_positive μ hell e hp) (2^j)
  have hb := experimentReference_contact_bound μ hell e hp he hi (2^j)
  have hW : 0 ≤ W := integral_nonneg (fun Z => Nat.cast_nonneg _)
  have ht := ENNReal.toReal_mono (show
      ((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)^2 *
      ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)^2 * 2 *
      ENNReal.ofReal (12*(2^j : ℕ)*W) *
      (axisWidthTail μ e (2^j)+axisWidthTail μ (oppositeStep e) (2^j)) ≠ ∞ by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · apply ENNReal.mul_ne_top
            · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ne_of_gt (hp false))))
                (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ne_of_gt (hp true))))
            · norm_num
          · exact ENNReal.ofReal_ne_top
        · exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,measure_ne_top _ _⟩) hb
  have hFa : axisWidthTail μ e (2^j) ≠ ∞ := measure_ne_top _ _
  have hFb : axisWidthTail μ (oppositeStep e) (2^j) ≠ ∞ := measure_ne_top _ _
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat,
    ENNReal.toReal_add hFa hFb] at ht
  rw [ENNReal.toReal_ofReal (by positivity)] at ht
  push_cast at ht
  change _ ≤ C*((2:ℝ)^j*(axisWidthTail μ e (2^j)).toReal+
      (2:ℝ)^j*(axisWidthTail μ (oppositeStep e) (2^j)).toReal)
  calc
    _ ≤ _ := ht
    _ = _ := by dsimp only [C];ring

lemma placed_kl_bounds {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
    (∀ j, InformationTheory.klDiv (experimentLaw ν (placedWidth e) (fun _ => wordEnd) (2^j))
      (experimentReference ν (placedWidth e) (fun _ => wordEnd) (2^j)) ≠ ∞) ∧
    ∃ A : ℝ, 0 ≤ A ∧ ∀ J,
      (∑ j ∈ Finset.range J, (InformationTheory.klDiv
        (experimentLaw ν (placedWidth e) (fun _ => wordEnd) (2^j))
        (experimentReference ν (placedWidth e) (fun _ => wordEnd) (2^j))).toReal) ≤ A*J := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) := fun b => slabLaw_probability μ _ (hp b)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  obtain ⟨he,hW⟩ := placed_common_data μ hell e hp
  let ρ := commonGapLaw ν (placedWidth e) (fun _ => wordEnd)
  have hi : ∀ i, Integrable (fun x : Site d => |(x i : ℝ)|) ρ :=
    commonGapLaw_lattice_integrable ν (placedWidth e) (placed_slab_positive μ hell e hp)
      he hW (fun _ => wordEnd) (placed_wordEnd_integrable μ hell e hp)
  let c := ((annealed μ 0 (nonBacktracking (axisDirection e))) *
    (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))).toReal
  have hc : 0 < c := ENNReal.toReal_pos (mul_ne_zero (ne_of_gt (hp false)) (ne_of_gt (hp true)))
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
  have hlo (H : ℕ) : ENNReal.ofReal c ≤ renewalPairMass ν (placedWidth e) H := by
    rw [show ENNReal.ofReal c = annealed μ 0 (nonBacktracking (axisDirection e))*
      annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))) from
      ENNReal.ofReal_toReal (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
    simpa only [commonCut_mass,renewalPairMass,Fintype.prod_bool,ν,mul_comm] using placed_common_lower μ hell e hp H
  let C := 6*(1+Real.log (8*((∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν)+1)+1))+1+Real.log 16
  have hb (j : ℕ) : InformationTheory.klDiv (experimentLaw ν (placedWidth e) (fun _ => wordEnd) (2^j))
      (experimentReference ν (placedWidth e) (fun _ => wordEnd) (2^j)) ≠ ∞ ∧
      (InformationTheory.klDiv (experimentLaw ν (placedWidth e) (fun _ => wordEnd) (2^j))
      (experimentReference ν (placedWidth e) (fun _ => wordEnd) (2^j))).toReal ≤
      C+(entropyOf (sumLaw ρ (14*2^j)) id-entropyOf (sumLaw ρ (2^j)) id) := by
    let : NeZero ((2:ℕ)^j) := ⟨pow_ne_zero _ (by norm_num)⟩
    have hh := lattice_experiment_kl_comparison ν (placedWidth e) (placed_slab_positive μ hell e hp)
      he hW (placed_cut_positive μ hell e hp) c hc hlo (fun _ => wordEnd)
      (placed_wordEnd_integrable μ hell e hp) (2^j)
    exact ⟨hh.1,by dsimp [C,ρ];linarith [hh.2]⟩
  refine ⟨fun j => (hb j).1,?_⟩
  let a := 1+∑ i : Fin d, ∫ x, |(x i : ℝ)| ∂ρ
  have ha : 0 < a := by
    have hh : 0 ≤ ∑ i : Fin d, ∫ x, |(x i : ℝ)| ∂ρ := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => abs_nonneg _))
    dsimp [a];linarith
  have hia (i : Fin d) : (∫ x, |(x i : ℝ)| ∂ρ) ≤ a := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin d => ∫ x, |(x i : ℝ)| ∂ρ)
      (fun i _ => integral_nonneg (fun x => abs_nonneg _)) (Finset.mem_univ i)
    dsimp [a];linarith
  let B := 1+Real.log 2+Real.log (a+1)+4*Real.log 2
  refine ⟨|C|+4*d*(|B|+Real.log 2),by have := Real.log_nonneg (by norm_num : (1:ℝ)≤2);positivity,?_⟩
  intro J
  by_cases hJ : J = 0
  · subst J;simp
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast Nat.pos_of_ne_zero hJ
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range J) => (hb j).2)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have ht := entropy_dyadic_telescope ρ hi a ha hia J
  have hC := le_abs_self C
  have hB := le_abs_self B
  have hBB : |B| ≤ |B| * J := le_mul_of_one_le_right (abs_nonneg _) hJ1
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hcJ := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg J)
  have hbJ := mul_le_mul_of_nonneg_left (hB.trans hBB) (by positivity : (0:ℝ)≤4*d)
  dsimp only [B] at hbJ
  nlinarith

lemma commonBand_entropy_upper {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (J L : ℕ),
      (L*Real.log 2)*(∑ j ∈ Finset.range J, (twoTapeLaw ν).real (commonBandContact e (2^j))) ≤
        A*J+(L*Real.log 2)*(2:ℝ)^L*B := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) := fun b => slabLaw_probability μ _ (hp b)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  have : Countable (Word d) := inferInstance
  have : Countable (TapeList (Word d)) := inferInstance
  have : Countable (ThreeLists (Word d)) := inferInstance
  let Q (j : ℕ) := experimentReference ν (placedWidth e) (fun _ => wordEnd) (2^j)
  let P (j : ℕ) := experimentLaw ν (placedWidth e) (fun _ => wordEnd) (2^j)
  have hne (j : ℕ) : NeZero ((2:ℕ)^j) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hP (j : ℕ) : IsProbabilityMeasure (P j) := by let := hne j;exact experiment_probability ν (placedWidth e) (fun _ => wordEnd) _
  have hQ (j : ℕ) : IsProbabilityMeasure (Q j) := by let := hne j;exact reference_probability ν (placedWidth e) (fun _ => wordEnd) (placed_cut_positive μ hell e hp) _
  obtain ⟨hfin,A,hA,hbound⟩ := placed_kl_bounds μ hell e hp
  have hsum := placed_reference_summable μ hell e hp
  let B := ∑' j, (Q j).real (experimentContact e)
  have hB : 0 ≤ B := tsum_nonneg (fun _ => measureReal_nonneg)
  refine ⟨A+Real.log 2,B,add_nonneg hA (Real.log_nonneg (by norm_num)),hB,?_⟩
  intro J L
  have hlog : 0 ≤ (L:ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have he := (placed_common_data μ hell e hp).1
  have hpoint (j : ℕ) : (L*Real.log 2)*(twoTapeLaw ν).real (commonBandContact e (2^j)) ≤
      (InformationTheory.klDiv (P j) (Q j)).toReal+Real.log 2+(L*Real.log 2)*(2:ℝ)^L*(Q j).real (experimentContact e) := by
    let := hne j
    let := hP j
    let := hQ j
    have hdom := commonBand_probability_le_experiment e ν
      (fun b => ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero _) (hp b)) he (2^j)
    have hdr := ENNReal.toReal_mono (measure_ne_top (P j) _) hdom
    have hkl := kl_event_scale_bound (P j) (Q j) (hfin j) (experimentContact e)
      (Set.to_countable _).measurableSet ((2:ℝ)^L) (one_le_pow₀ (by norm_num))
    rw [Real.log_pow] at hkl
    exact (mul_le_mul_of_nonneg_left hdr hlog).trans hkl
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range J) => hpoint j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    ← Finset.mul_sum] at hh
  have hqs : (∑ j ∈ Finset.range J, (Q j).real (experimentContact e)) ≤ B :=
    Summable.sum_le_tsum (Finset.range J) (fun _ _ => measureReal_nonneg) hsum
  have ht := mul_le_mul_of_nonneg_left hqs (mul_nonneg hlog (by positivity : (0:ℝ) ≤ (2:ℝ)^L))
  have hk := hbound J
  dsimp only [P,Q] at hh ht
  nlinarith

lemma commonBand_lower_real {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b))))
    (s N low high m a b : ℕ) (hs : 0 < s) (hsN : s ≤ N) (hls : low ≤ s) (hsh : s < high)
    (hab : a ≤ b) (hlow : 0 < low) (hhigh : high ≤ 8*2^b)
    (hΔ : axisReachProb μ e (s-low)-axisReachProb μ e s ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
    (annealed μ 0).real (nonBacktracking (axisDirection e))^2 ≤
      (4*2^a : ℕ) * (∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν) / low +
      (∑ j ∈ Finset.Icc a b, (twoTapeLaw ν).real (commonBandContact e (2^j))) +
      (∫ a, slabRadius a ∂ν false) / N +
      ((annealed μ 0).real (nonBacktracking (axisDirection e)))⁻¹ *
      ((annealed μ 0).real (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ((24 / posteriorExponent)*Real.log (Fintype.card (AxisCubeSite e N (N^2+1))+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) := fun b => slabLaw_probability μ _ (hp b)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  obtain ⟨he,hi⟩ := placed_common_data μ hell e hp
  have hbnd := coveredDepthBand_lower μ hell e hp s N low high m hs hsN hls hsh hΔ
  have hidx := coveredDepthBand_le_index_sum e ν (placed_slab_positive μ hell e hp) he hi a b low high hab hlow hhigh
  have hh := hbnd.trans (add_le_add (add_le_add hidx le_rfl) le_rfl)
  have hR := ofReal_integral_eq_lintegral_ofReal (placed_slabRadius_integrable μ hell e hp false)
    (Filter.Eventually.of_forall (fun a => slabRadius_nonneg a))
  change ENNReal.ofReal (∫ x, slabRadius x ∂slabLaw μ (axisDirection e)) =
    ∫⁻ x, ENNReal.ofReal (slabRadius x) ∂slabLaw μ (axisDirection e) at hR
  rw [← hR] at hh
  have hfin : ((4*2^a : ℕ) : ℝ≥0∞) * ENNReal.ofReal (∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν) / (low : ℝ≥0∞) +
      (∑ j ∈ Finset.Icc a b, twoTapeLaw ν (commonBandContact e (2^j))) +
      ENNReal.ofReal (∫ a, slabRadius a ∂ν false) / (N : ℝ≥0∞) +
      (annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹ *
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (Fintype.card (AxisCubeSite e N (N^2+1))+1)*(m+1)^2*(1/2 : ℝ)^m) ≠ ∞ := by
    have hN : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le hs hsN).ne'
    have hl : (low : ℝ≥0∞) ≠ 0 := by exact_mod_cast hlow.ne'
    have hp0 : annealed μ 0 (nonBacktracking (axisDirection e)) ≠ 0 := ne_of_gt (hp false)
    have hp1 : annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))) ≠ 0 := ne_of_gt (hp true)
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_,?_⟩,?_⟩,?_⟩
    · exact ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) hl
    · exact ENNReal.sum_ne_top.mpr (fun j _ => measure_ne_top _ _)
    · exact ENNReal.div_ne_top ENNReal.ofReal_ne_top hN
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp0)
        (ENNReal.inv_ne_top.mpr hp1)) ENNReal.ofReal_ne_top
  have ht := ENNReal.toReal_mono hfin hh
  have hW : 0 ≤ ∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν := integral_nonneg (fun Z => Nat.cast_nonneg _)
  have hr : 0 ≤ ∫ a, slabRadius a ∂ν false := integral_nonneg slabRadius_nonneg
  have hlog : 0 ≤ Real.log (Fintype.card (AxisCubeSite e N (N^2+1))+1) := Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hE : 0 ≤ (24/posteriorExponent)*Real.log (Fintype.card (AxisCubeSite e N (N^2+1))+1)*(m+1)^2*(1/2 : ℝ)^m := by
    have := posteriorExponent_pos
    positivity
  have hadd (x y : ℝ≥0∞) (h : x+y ≠ ∞) : (x+y).toReal = x.toReal+y.toReal :=
    ENNReal.toReal_add (ENNReal.add_ne_top.mp h).1 (ENNReal.add_ne_top.mp h).2
  rw [hadd _ _ hfin] at ht
  rw [hadd _ _ (ENNReal.add_ne_top.mp hfin).1] at ht
  rw [hadd _ _ (ENNReal.add_ne_top.mp (ENNReal.add_ne_top.mp hfin).1).1] at ht
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_sum (fun j _ => measure_ne_top _ _),
    ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofReal hW,ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal hE] at ht
  exact ht

end DirectionalZeroOne

end OAI
