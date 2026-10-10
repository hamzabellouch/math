import OAI.Probability.DirectionalWalk.RadiusMoment

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def wordOffset {α : Type*} (D : α → ℝ) (Z : ℕ → α) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, D (Z i)

def wordSequenceEscape {α : Type*} (D F : α → ℝ) : Set (ℕ → α) :=
  {Z | Tendsto (fun k => wordOffset D Z k + F (Z k)) atTop atTop}

lemma wordOffset_add {α : Type*} (D : α → ℝ) (Z : ℕ → α) (n k : ℕ) :
    wordOffset D Z (n+k) = wordOffset D Z n + wordOffset D (fun i => Z (n+i)) k := by
  simp only [wordOffset,Finset.sum_range_add]

lemma wordSequenceEscape_shift {α : Type*} (D F : α → ℝ) (Z : ℕ → α) (n : ℕ) :
    (fun i => Z (n+i)) ∈ wordSequenceEscape D F ↔ Z ∈ wordSequenceEscape D F := by
  change Tendsto _ atTop atTop ↔ Tendsto _ atTop atTop
  have heq : (fun k => wordOffset D Z (n+k)+F (Z (n+k))) =
      fun k => wordOffset D Z n + (wordOffset D (fun i => Z (n+i)) k + F (Z (n+k))) := by
    funext k; rw [wordOffset_add]; ring
  have hh := tendsto_add_atTop_iff_nat (f := fun k => wordOffset D Z k + F (Z k)) (l := atTop) n
  simp only [Nat.add_comm] at hh
  rw [heq] at hh
  have hc : Tendsto (fun k => wordOffset D Z n +
      (wordOffset D (fun i => Z (n+i)) k + F (Z (n+k)))) atTop atTop ↔
      Tendsto (fun k => wordOffset D (fun i => Z (n+i)) k + F (Z (n+k))) atTop atTop := by
    constructor <;> intro ht <;> apply tendsto_atTop.mpr <;> intro b
    · filter_upwards [(tendsto_atTop.mp ht) (wordOffset D Z n+b)] with k hk
      linarith
    · filter_upwards [(tendsto_atTop.mp ht) (b-wordOffset D Z n)] with k hk
      linarith
  exact hc.symm.trans hh

lemma measurableSet_wordSequenceEscape {α : Type*} [MeasurableSpace α]
    (D F : α → ℝ) (hD : Measurable D) (hF : Measurable F) :
    MeasurableSet (wordSequenceEscape D F) := by
  apply measurableSet_tendsto
  intro k
  exact (Finset.measurable_sum _ (fun i _ => hD.comp (measurable_pi_apply i))).add
    (hF.comp (measurable_pi_apply k))

lemma wordSequenceEscape_zero_one {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (Z : ℕ → Ω → α) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (D F : α → ℝ) (hD : Measurable D) (hF : Measurable F) :
    P {x | (fun i => Z i x) ∈ wordSequenceEscape D F} = 0 ∨
      P {x | (fun i => Z i x) ∈ wordSequenceEscape D F} = 1 := by
  apply measure_zero_or_one_of_measurableSet_limsup_atTop
    (fun n => (hZ n).comap_le) hind
  rw [limsup_eq_iInf_iSup_of_nat,MeasurableSpace.measurableSet_iInf]
  intro n
  have hm : @Measurable Ω (ℕ → α) (⨆ i ≥ n, MeasurableSpace.comap (Z i) inferInstance)
      inferInstance (fun x k => Z (n+k) x) := by
    exact @Measurable.of_eval Ω ℕ (fun _ => α)
      (⨆ i ≥ n, MeasurableSpace.comap (Z i) inferInstance) (fun _ => inferInstance)
      (fun x k => Z (n+k) x) (fun k => (comap_measurable (Z (n+k))).mono
      (le_iSup_of_le (n+k) (le_iSup_of_le (by omega : n ≤ n+k) le_rfl)) le_rfl)
  have hh := hm (measurableSet_wordSequenceEscape D F hD hF)
  convert hh using 1
  ext x
  exact (wordSequenceEscape_shift D F (fun i => Z i x) n).symm

noncomputable def heightBound {d : ℕ} (w : Fin d → ℝ) : ℝ := ∑ i, |w i|

lemma heightBound_nonneg {d : ℕ} (w : Fin d → ℝ) : 0 ≤ heightBound w :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma abs_height_le_norm {d : ℕ} (w : Fin d → ℝ) (x : Site d) :
    |height w x| ≤ heightBound w * ‖euclideanSite x‖ := by
  calc
    _ ≤ ∑ i, |(x i : ℝ)*w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| *‖euclideanSite x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,mul_comm]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [euclideanSite] using PiLp.norm_apply_le (euclideanSite x) i
    _ = _ := by rw [← Finset.sum_mul]; rfl

noncomputable def slabFloor {d : ℕ} (w : Fin d → ℝ) (γ : Word d) : ℝ :=
  (Finset.range (γ.1+1)).inf' ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun j => height w (wordPath γ j))

lemma slabFloor_le {d : ℕ} (w : Fin d → ℝ) (γ : Word d) {j : ℕ} (hj : j ≤ γ.1) :
    slabFloor w γ ≤ height w (wordPath γ j) :=
  Finset.inf'_le _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

lemma abs_word_height_le_radius {d : ℕ} (w : Fin d → ℝ) (γ : Word d)
    (h0 : wordPath γ 0 = 0) {j : ℕ} (hj : j ≤ γ.1) :
    |height w (wordPath γ j)| ≤ heightBound w * slabRadius γ := by
  have hh := norm_wordPath_le_radius γ hj
  rw [h0,sub_zero] at hh
  exact (abs_height_le_norm w _).trans (mul_le_mul_of_nonneg_left hh (heightBound_nonneg w))

lemma abs_slabFloor_le_radius {d : ℕ} (w : Fin d → ℝ) (γ : Word d)
    (h0 : wordPath γ 0 = 0) : |slabFloor w γ| ≤ heightBound w * slabRadius γ := by
  apply abs_le.mpr
  constructor
  · apply Finset.le_inf'
    intro j hj
    exact (abs_le.mp (abs_word_height_le_radius w γ h0 (by simpa using hj))).1
  · have hh := slabFloor_le w γ (j := 0) (Nat.zero_le _)
    rw [h0,height_zero] at hh
    exact hh.trans (mul_nonneg (heightBound_nonneg w) (slabRadius_nonneg γ))

lemma height_at_slabTime_projection {d : ℕ} (v w : Fin d → ℝ) (X : Path d)
    (h0 : X 0 = 0) (k : ℕ) :
    height w (X (slabTime v X k)) = wordOffset (slabWidth w) (slabs v X) k := by
  induction k with
  | zero => simp [slabTime_zero,wordOffset,h0,height_zero]
  | succ k ih =>
    have hh := iterated_cutSuffix v X h0 k (slabs v X k).1
    rw [← slab_word_path v X k le_rfl,← slabTime_succ] at hh
    have hh' := congrArg (height w) hh
    rw [height_sub,ih] at hh'
    change slabWidth w (slabs v X k) = height w (X (slabTime v X (k+1))) - _ at hh'
    rw [wordOffset,Finset.sum_range_succ]
    change height w (X (slabTime v X (k+1))) = wordOffset (slabWidth w) (slabs v X) k + _
    linarith

lemma height_in_slab_projection {d : ℕ} (v w : Fin d → ℝ) (X : Path d)
    (h0 : X 0 = 0) (k j : ℕ) (hj : j ≤ (slabs v X k).1) :
    height w (X (slabTime v X k+j)) = wordOffset (slabWidth w) (slabs v X) k +
      height w (wordPath (slabs v X k) j) := by
  have hh := congrArg (height w) (iterated_cutSuffix v X h0 k j)
  rw [← slab_word_path v X k hj,height_sub,height_at_slabTime_projection v w X h0] at hh
  linarith

lemma escape_iff_wordSequenceEscape {d : ℕ} (v w : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) :
    X ∈ escape w ↔ slabs v X ∈ wordSequenceEscape (slabWidth w) (slabFloor w) := by
  constructor
  · intro ht
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) b)
    refine eventually_atTop.mpr ⟨N,fun k hk => ?_⟩
    have hf : b-wordOffset (slabWidth w) (slabs v X) k ≤ slabFloor w (slabs v X k) := by
      apply Finset.le_inf'
      intro j hj
      have hn : N ≤ slabTime v X k+j := (hk.trans ((slabTime_strictMono v X hX).id_le k)).trans (Nat.le_add_right _ _)
      have hh := hN _ hn
      change b ≤ height w (X _) at hh
      rw [height_in_slab_projection v w X hX.1 k j (by simpa using hj)] at hh
      linarith
    linarith
  · intro ht
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨K,hK⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) b)
    refine eventually_atTop.mpr ⟨slabTime v X K,fun n hn => ?_⟩
    obtain ⟨k,hkn,hnk⟩ := slab_location v X hX n
    have hk : K ≤ k := by
      by_contra hh
      have hh' : k+1 ≤ K := by omega
      have hh'' := (slabTime_strictMono v X hX).monotone hh'
      omega
    have hj : n-slabTime v X k ≤ (slabs v X k).1 := by
      rw [slabTime_succ] at hnk
      omega
    have hp := height_in_slab_projection v w X hX.1 k (n-slabTime v X k) hj
    rw [Nat.add_sub_of_le hkn] at hp
    change b ≤ height w (X n)
    rw [hp]
    exact (hK k hk).trans (add_le_add le_rfl (slabFloor_le w _ hj))

lemma conditioned_escape_zero_one {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (w : Fin d → ℝ) :
    conditioned μ v (escape w) = 0 ∨ conditioned μ v (escape w) = 1 := by
  have heq : conditioned μ v (escape w) = conditioned μ v
      {X | slabs v X ∈ wordSequenceEscape (slabWidth w) (slabFloor w)} := by
    apply measure_congr
    filter_upwards [ae_goodSlabPath μ hell v hv hp] with X hX
    exact propext (escape_iff_wordSequenceEscape v w X hX)
  rw [heq]
  exact wordSequenceEscape_zero_one (conditioned μ v) (fun k X => slabs v X k)
    (fun k => (measurable_pi_apply k).comp (measurable_slabs v))
    (slabs_iid μ hell v hv hp) _ _ (measurable_of_countable _) (measurable_of_countable _)

lemma tendsto_term_div_nat_of_average (f : ℕ → ℝ) {m : ℝ}
    (h : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f i) / n) atTop (𝓝 m)) :
    Tendsto (fun n : ℕ => f n/n) atTop (𝓝 0) := by
  have hs := h.comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun n : ℕ => ((n:ℝ)+1)/n) atTop (𝓝 1) := by
    simpa only [inv_div,inv_one] using (tendsto_natCast_div_add_atTop (1:ℝ)).inv₀ (by norm_num)
  have ht := (hs.mul hr).sub h
  simp only [mul_one,sub_self] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  dsimp [Function.comp_def]
  rw [Finset.sum_range_succ]
  push_cast
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

lemma tendsto_atTop_of_positive_slope (f : ℕ → ℝ) {m : ℝ} (hm : 0 < m)
    (h : Tendsto (fun n : ℕ => f n/n) atTop (𝓝 m)) : Tendsto f atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (b/(m/2)))
  have hn1 : (1:ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNb : b < (m/2)*N := by
    have hh := (div_lt_iff₀ (half_pos hm)).mp (lt_of_le_of_lt (le_max_right _ _) hN)
    nlinarith only [hh]
  filter_upwards [h.eventually (lt_mem_nhds (half_lt_self hm)),eventually_ge_atTop N] with n hn hnN
  have hn0 : (0:ℝ) < n := by
    have hh : (N:ℝ) ≤ n := Nat.cast_le.mpr hnN
    linarith
  have hh := (lt_div_iff₀ hn0).mp hn
  have hhN := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnN) (half_pos hm).le
  exact (hNb.trans_le hhN).le.trans hh.le

lemma relativeTail_escape_iff {d : ℕ} (w : Fin d → ℝ) (X : Path d) (n : ℕ) :
    relativeTail n X ∈ escape w ↔ X ∈ escape w := by
  change Tendsto (fun k => height w (relativeTail n X k)) atTop atTop ↔
    Tendsto (fun k => height w (X k)) atTop atTop
  simp only [relativeTail_apply,height_sub]
  have hh := tendsto_add_atTop_iff_nat (f := fun k => height w (X k)) (l := atTop) n
  simp only [Nat.add_comm] at hh
  have hc : Tendsto (fun k => height w (X (n+k))-height w (X n)) atTop atTop ↔
      Tendsto (fun k => height w (X (n+k))) atTop atTop := by
    constructor <;> intro ht <;> apply tendsto_atTop.mpr <;> intro b
    · filter_upwards [(tendsto_atTop.mp ht) (b-height w (X n))] with k hk
      linarith
    · filter_upwards [(tendsto_atTop.mp ht) (b+height w (X n))] with k hk
      linarith
  exact hc.trans hh

lemma annealed_shift_back {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) {E : Set (Path d)} (hE : MeasurableSet E) :
    annealed μ x (shiftPath (-x) ⁻¹' E) = annealed μ 0 E := by
  have hh := congrArg (fun P : Measure (Path d) => P (shiftPath (-x) ⁻¹' E))
    (annealed_shift μ 0 x)
  rw [Measure.map_apply (measurable_shiftPath _) ((measurable_shiftPath _) hE),zero_add] at hh
  have he : shiftPath x ⁻¹' (shiftPath (-x) ⁻¹' E) = E := by
    ext X
    simp only [Set.mem_preimage]
    have hX : shiftPath (-x) (shiftPath x X) = X := by
      funext n
      simp [shiftPath]
    rw [hX]
  rw [he] at hh
  exact hh.symm

lemma annealed_relativeTail_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (y : Site d) (n : ℕ) {E : Set (Path d)} (hE : MeasurableSet E)
    (hzero : annealed μ 0 E = 0) : annealed μ y (relativeTail n ⁻¹' E) = 0 := by
  have hsub : relativeTail n ⁻¹' E ⊆ ⋃ x : Site d,
      {X | X n = x} ∩ tailPath n ⁻¹' (shiftPath (-x) ⁻¹' E) := by
    intro X hX
    exact Set.mem_iUnion.mpr ⟨X n,rfl,hX⟩
  apply measure_mono_null hsub
  apply measure_iUnion_null
  intro x
  apply annealed_tail_start_null μ y x n ((measurable_shiftPath _) hE)
  rw [annealed_shift_back μ x hE,hzero]

lemma conditioned_null_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v))
    {E : Set (Path d)} (hE : MeasurableSet E)
    (hinv : ∀ X n, relativeTail n X ∈ E ↔ X ∈ E)
    (hz : conditioned μ v E = 0) : annealed μ 0 (escape v ∩ E) = 0 := by
  have hDE : annealed μ 0 (E ∩ nonBacktracking v) = 0 := by
    unfold conditioned at hz
    rw [cond_apply (measurableSet_nonBacktracking v)] at hz
    have hh := (mul_eq_zero.mp hz).resolve_left (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    simpa only [Set.inter_comm] using hh
  have ht (n : ℕ) := annealed_relativeTail_null μ 0 n
    (hE.inter (measurableSet_nonBacktracking v)) hDE
  have halls : ∀ᵐ X ∂annealed μ 0, ∀ n, relativeTail n X ∉ E ∩ nonBacktracking v :=
    ae_all_iff.mpr (fun n => (measure_eq_zero_iff_ae_notMem).mp (ht n))
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [halls,ae_infinitely_trueCuts μ 0 v hp] with X hX hc hXE
  have hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b := by
    rintro ⟨b,hb⟩
    obtain ⟨n,hn⟩ := ((tendsto_atTop.mp hXE.1) (b+1)).exists
    change b+1 ≤ height v (X n) at hn
    have hh := hb n
    linarith
  obtain ⟨n,_,hn⟩ := hc hu 0
  exact hX n ⟨(hinv X n).mpr hXE.2,(relativeTail_nonBacktracking_iff v X n).mpr hn.2⟩

lemma conditioned_ae_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v))
    {E : Set (Path d)} (hE : MeasurableSet E)
    (hinv : ∀ X n, relativeTail n X ∈ E ↔ X ∈ E)
    (h : ∀ᵐ X ∂conditioned μ v, X ∈ E) :
    ∀ᵐ X ∂annealed μ 0, X ∈ escape v → X ∈ E := by
  have hz : conditioned μ v Eᶜ = 0 := by
    exact ae_iff.mp h
  have hh := conditioned_null_transfer μ v hp hE.compl
    (fun X n => not_congr (hinv X n)) hz
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hh] with X hX hAv
  by_contra hn
  exact hX ⟨hAv,hn⟩

lemma integrable_slabProjection {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hR : Integrable slabRadius (slabLaw μ v)) (w : Fin d → ℝ) :
    Integrable (slabWidth w) (slabLaw μ v) := by
  apply (hR.const_mul (heightBound w)).mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [ae_slabLaw_regeneration μ hell v hv hp] with γ hγ
  exact abs_word_height_le_radius w γ hγ.2.1 le_rfl

lemma ae_slabRadius_sublinear {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hR : Integrable slabRadius (slabLaw μ v)) :
    ∀ᵐ X ∂conditioned μ v,
      Tendsto (fun n : ℕ => slabRadius (slabs v X n)/n) atTop (𝓝 0) := by
  filter_upwards [slabObservable_strongLaw μ hell v hv hp _ hR] with X hX
  exact tendsto_term_div_nat_of_average _ hX

lemma conditioned_escape_of_positive_mean {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hR : Integrable slabRadius (slabLaw μ v)) (w : Fin d → ℝ)
    (hw : 0 < ∫ γ, slabWidth w γ ∂slabLaw μ v) :
    ∀ᵐ X ∂conditioned μ v, X ∈ escape w := by
  filter_upwards [ae_goodSlabPath μ hell v hv hp,ae_slabRadius_sublinear μ hell v hv hp hR,
    slabObservable_strongLaw μ hell v hv hp _ (integrable_slabProjection μ hell v hv hp hR w)]
    with X hX hsub hsum
  apply (escape_iff_wordSequenceEscape v w X hX).mpr
  change Tendsto (fun n => wordOffset (slabWidth w) (slabs v X) n + slabFloor w (slabs v X n)) atTop atTop
  apply tendsto_atTop_of_positive_slope _ hw
  have hfloor : Tendsto (fun n : ℕ => slabFloor w (slabs v X n)/n) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    have ht := hsub.const_mul (heightBound w)
    rw [mul_zero] at ht
    apply squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) ht
    rw [abs_div,show |(n:ℝ)| = (n:ℝ) from abs_of_nonneg (Nat.cast_nonneg n),← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact abs_slabFloor_le_radius w _ (hX.2 n).2.1
  simpa only [add_div,add_zero,wordOffset] using hsum.add hfloor

noncomputable def slabMean {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∫ γ, (wordPath γ γ.1 i : ℝ) ∂slabLaw μ v

noncomputable def directionDot {d : ℕ} (v w : Fin d → ℝ) : ℝ := ∑ i, v i*w i

lemma integral_slabProjection {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v))
    (hR : Integrable slabRadius (slabLaw μ v)) (w : Fin d → ℝ) :
    (∫ γ, slabWidth w γ ∂slabLaw μ v) = directionDot (slabMean μ v) w := by
  have hi (i : Fin d) : Integrable (fun γ : Word d => (wordPath γ γ.1 i : ℝ)) (slabLaw μ v) := by
    have hh := integrable_slabProjection μ hell v hv hp hR (Pi.single i 1)
    have he : slabWidth (Pi.single i 1) = (fun γ : Word d => (wordPath γ γ.1 i : ℝ)) := by
      funext γ
      simp [slabWidth,height,Pi.single_apply]
    rwa [he] at hh
  unfold slabWidth height directionDot slabMean
  rw [integral_finsetSum _ (fun i _ => (hi i).mul_const (w i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const]

lemma directionDot_add_right {d : ℕ} (a b c : Fin d → ℝ) :
    directionDot a (b+c) = directionDot a b + directionDot a c := by
  simp [directionDot,mul_add,Finset.sum_add_distrib]

lemma directionDot_self_pos {d : ℕ} (a : Fin d → ℝ) (ha : a ≠ 0) :
    0 < directionDot a a := by
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact ha (funext hh)
  apply Finset.sum_pos'
  · intro j _
    exact mul_self_nonneg _
  · exact ⟨i,Finset.mem_univ _,mul_self_pos.mpr hi⟩

lemma escape_not_opposite {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (h : X ∈ escape v) : X ∉ escape (-v) := by
  intro hn
  have hh := ((tendsto_atTop.mp h) 1).and ((tendsto_atTop.mp hn) 1)
  obtain ⟨n,hp,hm⟩ := hh.exists
  change 1 ≤ height v (X n) at hp
  change 1 ≤ height (-v) (X n) at hm
  rw [height_neg_direction] at hm
  linarith

lemma escape_zero_one_of_full_direction {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (w : Fin d → ℝ) (hw : w ≠ 0)
    (hfull : annealed μ 0 (escape w) = 1) (v : Fin d → ℝ) :
    annealed μ 0 (escape v) = 0 ∨ annealed μ 0 (escape v) = 1 := by
  have hp := positive_nonBacktracking μ w (hfull ▸ zero_lt_one)
  have hwfull := (mem_ae_iff_prob_eq_one (measurableSet_escape w)).mpr hfull
  let := conditioned_probability μ w hp
  rcases conditioned_escape_zero_one μ hell w hw hp v with hz | ho
  · left
    have he := conditioned_null_transfer μ w hp (measurableSet_escape v)
      (relativeTail_escape_iff v) hz
    calc
      _ = annealed μ 0 (escape w ∩ escape v) := by
        apply measure_congr
        filter_upwards [hwfull] with X hX
        exact propext ⟨fun hv => ⟨hX,hv⟩,fun hh => hh.2⟩
      _ = 0 := he
  · right
    have he := conditioned_ae_transfer μ w hp (measurableSet_escape v)
      (relativeTail_escape_iff v)
      ((mem_ae_iff_prob_eq_one (measurableSet_escape v)).mpr ho)
    apply (mem_ae_iff_prob_eq_one (measurableSet_escape v)).mp
    filter_upwards [he,hwfull] with X hX hWX
    exact hX hWX

lemma not_zero_one_of_opposite_positive {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (escape v))
    (hm : 0 < annealed μ 0 (escape (-v))) :
    ¬(annealed μ 0 (escape v) = 0 ∨ annealed μ 0 (escape v) = 1) := by
  rintro (hz|ho)
  · exact hp.ne' hz
  · have he := (mem_ae_iff_prob_eq_one (measurableSet_escape v)).mpr ho
    have hz : annealed μ 0 (escape (-v)) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [he] with X hX
      exact escape_not_opposite v X hX
    exact hm.ne' hz

lemma positive_raw_of_conditioned_ae {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v))
    {E : Set (Path d)} (hE : MeasurableSet E) (he : ∀ᵐ X ∂conditioned μ v, X ∈ E) :
    0 < annealed μ 0 E := by
  let := conditioned_probability μ v hp
  by_contra hh
  have hz : annealed μ 0 E = 0 := le_antisymm (le_of_not_gt hh) (zero_le)
  have hac : conditioned μ v ≪ annealed μ 0 := cond_absolutelyContinuous
  have hh' := hac hz
  have ho := (mem_ae_iff_prob_eq_one hE).mp he
  rw [hh'] at ho
  exact zero_ne_one ho

lemma coordinate_direction_ne_zero {d : ℕ} (i : Fin d) :
    (Pi.single i (1:ℝ) : Fin d → ℝ) ≠ 0 := by
  intro hh
  have hh' := congr_fun hh i
  simp at hh'

lemma exists_mixed_coordinate {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hvunit : ∃ i, |v i| = 1)
    (hp : 0 < annealed μ 0 (escape v)) (hm : 0 < annealed μ 0 (escape (-v))) :
    ∃ i : Fin d, 0 < annealed μ 0 (escape (Pi.single i 1)) ∧
      0 < annealed μ 0 (escape (-Pi.single i 1)) := by
  have hpD := positive_nonBacktracking μ v hp
  have hmD := positive_nonBacktracking μ (-v) hm
  have hvn : -v ≠ 0 := neg_ne_zero.mpr hv
  have hvnn : ∀ i, |(-v) i| ≤ 1 := by simpa only [Pi.neg_apply,abs_neg] using hvnorm
  obtain ⟨hR,hR'⟩ := integrable_slabRadius_normalized μ hell v hv hvnorm hvunit hpD hmD
  let a := slabMean μ v
  let b := slabMean μ (-v)
  have ha : a ≠ 0 := by
    have hh := integral_slabWidth_pos μ hell v hv hvnorm hpD
    rw [integral_slabProjection μ hell v hv hpD hR] at hh
    intro hz
    change 0 < directionDot a v at hh
    simp [hz,directionDot] at hh
  have hb : b ≠ 0 := by
    have hh := integral_slabWidth_pos μ hell (-v) hvn hvnn hmD
    rw [integral_slabProjection μ hell (-v) hvn hmD hR'] at hh
    intro hz
    change 0 < directionDot b (-v) at hh
    simp [hz,directionDot] at hh
  have hex : ∃ i, a i*b i < 0 := by
    by_contra hh
    push Not at hh
    let w := a+b
    have hacross : 0 ≤ directionDot a b := Finset.sum_nonneg (fun i _ => hh i)
    have hbcross : 0 ≤ directionDot b a := by
      simpa only [directionDot,mul_comm] using hacross
    have hwa : 0 < directionDot a w := by
      rw [directionDot_add_right]
      exact add_pos_of_pos_of_nonneg (directionDot_self_pos a ha) hacross
    have hwb : 0 < directionDot b w := by
      rw [directionDot_add_right]
      exact add_pos_of_nonneg_of_pos hbcross (directionDot_self_pos b hb)
    have hwn : w ≠ 0 := by
      intro hz
      simp [hz,directionDot] at hwa
    have hwA : ∀ᵐ X ∂conditioned μ v, X ∈ escape w := by
      apply conditioned_escape_of_positive_mean μ hell v hv hpD hR w
      rwa [integral_slabProjection μ hell v hv hpD hR]
    have hwB : ∀ᵐ X ∂conditioned μ (-v), X ∈ escape w := by
      apply conditioned_escape_of_positive_mean μ hell (-v) hvn hmD hR' w
      rwa [integral_slabProjection μ hell (-v) hvn hmD hR']
    have hfull : annealed μ 0 (escape w) = 1 := by
      apply (mem_ae_iff_prob_eq_one (measurableSet_escape w)).mp
      filter_upwards [ae_escape_or_opposite μ hell 0 v hv hpD,
        conditioned_ae_transfer μ v hpD (measurableSet_escape w) (relativeTail_escape_iff w) hwA,
        conditioned_ae_transfer μ (-v) hmD (measurableSet_escape w) (relativeTail_escape_iff w) hwB]
        with X hXC hXA hXB
      exact hXC.elim hXA hXB
    exact not_zero_one_of_opposite_positive μ v hp hm
      (escape_zero_one_of_full_direction μ hell w hwn hfull v)
  obtain ⟨i,hi⟩ := hex
  have hproj (u : Fin d → ℝ) (hun : u ≠ 0)
      (huD : 0 < annealed μ 0 (nonBacktracking u))
      (huR : Integrable slabRadius (slabLaw μ u)) (w : Fin d → ℝ)
      (huw : 0 < directionDot (slabMean μ u) w) : 0 < annealed μ 0 (escape w) := by
    apply positive_raw_of_conditioned_ae μ u huD (measurableSet_escape w)
    apply conditioned_escape_of_positive_mean μ hell u hun huD huR w
    rwa [integral_slabProjection μ hell u hun huD huR]
  have hdoti (c : Fin d → ℝ) : directionDot c (Pi.single i 1) = c i := by
    simp [directionDot,Pi.single_apply]
  have hdotni (c : Fin d → ℝ) : directionDot c (-Pi.single i 1) = -c i := by
    simp [directionDot,Pi.single_apply,Finset.sum_neg_distrib]
  refine ⟨i,?_⟩
  rcases mul_neg_iff.mp hi with ⟨hia,hib⟩|⟨hia,hib⟩
  · exact ⟨hproj v hv hpD hR _ (by rw [hdoti]; exact hia),
      hproj (-v) hvn hmD hR' _ (by rw [hdotni]; exact neg_pos.mpr hib)⟩
  · exact ⟨hproj (-v) hvn hmD hR' _ (by rw [hdoti]; exact hib),
      hproj v hv hpD hR _ (by rw [hdotni]; exact neg_pos.mpr hia)⟩

lemma height_scale_direction {d : ℕ} (v : Fin d → ℝ) (c : ℝ) (x : Site d) :
    height (c • v) x = c * height v x := by
  simp only [height, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma escape_scale_direction {d : ℕ} (v : Fin d → ℝ) {c : ℝ} (hc : 0 < c) :
    escape (c • v) = escape v := by
  ext X
  change Tendsto (fun n => height (c • v) (X n)) atTop atTop ↔ _
  simp only [height_scale_direction]
  exact tendsto_const_mul_atTop_of_pos hc

lemma direction_normalization {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0) :
    ∃ (c : ℝ), 0 < c ∧ (∀ i, |(c • v) i| ≤ 1) ∧ ∃ i, |(c • v) i| = 1 := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hv (funext hh)
  obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|)
    (show (Finset.univ : Finset (Fin d)).Nonempty from ⟨j,Finset.mem_univ _⟩)
  have hi : 0 < |v i| := (abs_pos.mpr hj).trans_le (hmax j (Finset.mem_univ _))
  refine ⟨|v i|⁻¹, inv_pos.mpr hi, ?_, i, ?_⟩
  · intro k
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_abs]
    rw [inv_mul_le_iff₀ hi, mul_one]
    exact hmax k (Finset.mem_univ _)
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_abs]
    exact inv_mul_cancel₀ hi.ne'

lemma mixed_direction_has_mixed_coordinate {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (h0 : 0 < annealed μ 0 (escape v)) (h1 : annealed μ 0 (escape v) < 1) :
    ∃ i : Fin d, 0 < annealed μ 0 (escape (Pi.single i 1)) ∧
      0 < annealed μ 0 (escape (-Pi.single i 1)) := by
  obtain ⟨c,hc,hcn,hcu⟩ := direction_normalization v hv
  have hcv : c • v ≠ 0 := smul_ne_zero hc.ne' hv
  have hp : 0 < annealed μ 0 (escape (c • v)) := by
    rwa [escape_scale_direction v hc]
  have hm : 0 < annealed μ 0 (escape (-(c • v))) := by
    have hpD := positive_nonBacktracking μ (c • v) hp
    have hu : annealed μ 0 (escape (c • v) ∪ escape (-(c • v))) = 1 :=
      (mem_ae_iff_prob_eq_one ((measurableSet_escape _).union (measurableSet_escape _))).mp
        (ae_escape_or_opposite μ hell 0 (c • v) hcv hpD)
    by_contra hh
    have hz : annealed μ 0 (escape (-(c • v))) = 0 := le_antisymm (not_lt.mp hh) bot_le
    have hle := measure_union_le (escape (c • v)) (escape (-(c • v))) (μ := annealed μ 0)
    rw [hu,hz,add_zero,escape_scale_direction v hc] at hle
    exact not_le_of_gt h1 hle
  exact exists_mixed_coordinate μ hell (c • v) hcv hcn hcu hp hm

end DirectionalZeroOne

end OAI
