import OAI.MeasureTheory.SelfSimilar.DigitSumset

namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FiniteEntropy

theorem entropy_le_mass_log_card {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    entropy s p ≤ Real.negMulLog (∑ a ∈ s, p a)+
      (∑ a ∈ s, p a)*Real.log (max 1 (s.card : ℝ)) := by
  let P := ∑ a ∈ s, p a
  have hP : 0 ≤ P := Finset.sum_nonneg hp
  rw [entropy_normalize s p hp]
  change Real.negMulLog P+P*entropy s (fun a => p a/P) ≤
    Real.negMulLog P+P*Real.log (max 1 (s.card : ℝ))
  rcases eq_or_lt_of_le hP with he | he
  · simp only [← he,zero_mul,add_zero,le_refl]
  have hs : 0 < s.card := Finset.card_pos.mpr (by
    by_contra h
    have hse : s=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [P,hse,Finset.sum_empty] at he
    exact lt_irrefl _ he)
  have hh := entropy_le_log_card s (fun a => p a/P)
    (fun a ha => div_nonneg (hp a ha) hP) (by rw [← Finset.sum_div]; exact div_self he.ne')
  have hcard : max 1 (s.card : ℝ)=(s.card : ℝ) := max_eq_right (by exact_mod_cast hs)
  rw [hcard]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hh hP) _

theorem entropy_split_bound {α : Type uα} [DecidableEq α] (s a : Finset α)
    (p : α → ℝ) (ha : a ⊆ s) (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i=1) :
    entropy s p ≤ Real.log 2+Real.log (max 1 (a.card : ℝ))+
      (∑ i ∈ s\a, p i)*Real.log (max 1 (s.card : ℝ)) := by
  classical
  let P := ∑ i ∈ a, p i
  let Q := ∑ i ∈ s\a, p i
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i hi => hp i (ha hi))
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i hi => hp i (Finset.mem_sdiff.mp hi).1)
  have hPQ : P+Q=1 := by
    change (∑ i ∈ a, p i)+(∑ i ∈ s\a, p i)=1
    rw [add_comm,Finset.sum_sdiff ha,hp1]
  have hPa := entropy_le_mass_log_card a p (fun i hi => hp i (ha hi))
  have hQb := entropy_le_mass_log_card (s\a) p (fun i hi => hp i (Finset.mem_sdiff.mp hi).1)
  have hnum := entropy_le_log_card (Finset.univ : Finset (Fin 2))
    (fun i => if i=0 then P else Q) (by intro i _; split <;> assumption)
    (by simpa [Fin.sum_univ_two] using hPQ)
  have hn : Real.negMulLog P+Real.negMulLog Q ≤ Real.log 2 := by
    simpa [entropy,Fin.sum_univ_two] using hnum
  have hlogA : 0 ≤ Real.log (max 1 (a.card : ℝ)) := Real.log_nonneg (le_max_left _ _)
  have hlogB : Real.log (max 1 ((s\a).card : ℝ)) ≤ Real.log (max 1 (s.card : ℝ)) := by
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact max_le_max_left 1 (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := s) (t := a)))
  have he : entropy s p=entropy a p+entropy (s\a) p := by
    unfold entropy
    rw [add_comm,Finset.sum_sdiff ha]
  rw [he]
  change entropy a p ≤ Real.negMulLog P+P*_ at hPa
  change entropy (s\a) p ≤ Real.negMulLog Q+Q*_ at hQb
  change _ ≤ Real.log 2+_+Q*_
  nlinarith [mul_le_mul_of_nonneg_left hlogB hQ,mul_nonneg hQ hlogA]

end FiniteEntropy

namespace MeasureEntropy

theorem entropy_subset_bound {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (hf : Measurable f)
    (s a : Finset β) (ha : a ⊆ s) (hs : ∀ᵐ x ∂μ, f x ∈ s) {η : ℝ}
    (hη : μ.real {x | f x ∉ a} ≤ η) :
    entropy μ f ≤ Real.log 2+Real.log (max 1 (a.card : ℝ))+
      η*Real.log (max 1 (s.card : ℝ)) := by
  have hh := FiniteEntropy.entropy_split_bound s a (mass μ f) ha
    (fun i _ => mass_nonneg μ f i) (mass_sum μ f hf s hs)
  have hm : ∑ i ∈ s\a, mass μ f i = μ.real {x | f x ∉ a} := by
    have hd : (↑(s\a) : Set β).PairwiseDisjoint (fun b => {x | f x=b}) := by
      intro b _ c _ hbc
      exact Set.disjoint_left.mpr (fun _ hx hy => hbc (hx.symm.trans hy))
    have hie : (⋃ b ∈ s\a, {x | f x=b}) = {x | f x ∈ s\a} := by
      ext x
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
      constructor
      · rintro ⟨b,hb,hxb⟩
        exact hxb ▸ hb
      · intro hx
        exact ⟨f x,hx,rfl⟩
    have he : (⋃ b ∈ s\a, {x | f x=b}) =ᵐ[μ] {x | f x ∉ a} := by
      rw [hie]
      filter_upwards [hs] with x hx
      apply propext
      simp only [Finset.mem_sdiff,hx,true_and]
    unfold mass
    rw [← measureReal_biUnion_finset (μ := μ) hd (fun b _ => hf (measurableSet_singleton b))]
    exact measureReal_congr he
  rw [entropy_eq_sum μ f s hs]
  rw [hm] at hh
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right hη
    (Real.log_nonneg (le_max_left _ _))) _)

theorem card_mul_mass_le_one {α : Type uα} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Finset α) (x : α → ℝ) {r q : ℝ}
    (hd : (↑s : Set α).PairwiseDisjoint (fun i => Metric.ball (x i) r))
    (hq : ∀ i ∈ s, q ≤ μ.real (Metric.ball (x i) r)) :
    (s.card : ℝ)*q ≤ 1 := by
  calc
    (s.card : ℝ)*q = ∑ i ∈ s, q := by simp
    _ ≤ ∑ i ∈ s, μ.real (Metric.ball (x i) r) := Finset.sum_le_sum hq
    _ = μ.real (⋃ i ∈ s, Metric.ball (x i) r) :=
      (measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)).symm
    _ ≤ 1 := (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)

theorem label_ball_disjoint {s u x y : ℝ} (hs : 0 < s)
    (hne : label s u x ≠ label s u y) (hmod : label s u x % 3=label s u y % 3) :
    Disjoint (Metric.ball x (s/2)) (Metric.ball y (s/2)) := by
  have hd : s ≤ dist x y := by
    rw [Real.dist_eq]
    have hx1 := Int.floor_le (x/s+u)
    have hx2 := Int.lt_floor_add_one (x/s+u)
    have hy1 := Int.floor_le (y/s+u)
    have hy2 := Int.lt_floor_add_one (y/s+u)
    have hdiff : label s u x+3 ≤ label s u y ∨ label s u y+3 ≤ label s u x := by omega
    rcases hdiff with h | h
    · have h' : (label s u x : ℝ)+3 ≤ (label s u y : ℝ) := by exact_mod_cast h
      change (⌊x/s+u⌋ : ℝ)+3 ≤ (⌊y/s+u⌋ : ℝ) at h'
      have hxy : 2 < y/s-x/s := by linarith
      have hmul := (lt_div_iff₀ hs).mp (by simpa only [← sub_div] using hxy)
      rw [abs_of_nonpos (by linarith : x-y ≤ 0)]
      linarith
    · have h' : (label s u y : ℝ)+3 ≤ (label s u x : ℝ) := by exact_mod_cast h
      change (⌊y/s+u⌋ : ℝ)+3 ≤ (⌊x/s+u⌋ : ℝ) at h'
      have hxy : 2 < x/s-y/s := by linarith
      have hmul := (lt_div_iff₀ hs).mp (by simpa only [← sub_div] using hxy)
      rw [abs_of_nonneg (by linarith : 0 ≤ x-y)]
      linarith
  apply Set.disjoint_left.mpr
  intro z hz hzy
  have hz1 := Metric.mem_ball.mp hz
  have hz2 := Metric.mem_ball.mp hzy
  have ht := dist_triangle_left x y z
  linarith

theorem good_labels_card_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s u q : ℝ} (hs : 0 < s) (a : Finset ℤ) (x : ℤ → ℝ)
    (hx : ∀ i ∈ a, label s u (x i)=i)
    (hq : ∀ i ∈ a, q ≤ μ.real (Metric.ball (x i) (s/2))) :
    (a.card : ℝ)*q ≤ 3 := by
  let color : ℤ → Fin 3 := fun i => ⟨(i%3).toNat, by omega⟩
  have hc : ∀ c : Fin 3,
      (((a.filter (fun i => color i=c)).card : ℕ) : ℝ)*q ≤ 1 := by
    intro c
    apply card_mul_mass_le_one μ _ x
    · intro i hi j hj hij
      have hia := (Finset.mem_filter.mp hi).1
      have hja := (Finset.mem_filter.mp hj).1
      apply label_ball_disjoint hs
      · rwa [hx i hia,hx j hja]
      · rw [hx i hia,hx j hja]
        have he := congrArg Fin.val ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
        dsimp [color] at he
        omega
    · intro i hi
      exact hq i (Finset.mem_filter.mp hi).1
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hc c)
  have he : ∑ c : Fin 3, (((a.filter (fun i => color i=c)).card : ℕ) : ℝ) = (a.card : ℝ) := by
    simp only [← Nat.cast_sum]
    congr 1
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
      (Finset.sum_fiberwise a color (fun _ => (1 : ℕ)))
  rw [← Finset.sum_mul,he] at hsum
  simpa using hsum

theorem grid_le_of_ball_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {B s u q η : ℝ} (hs : 0 < s) (hq : 0 < q)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (E : Set ℝ) (hη : μ.real Eᶜ ≤ η)
    (hball : ∀ x ∈ E, q ≤ μ.real (Metric.ball x (s/2))) :
    grid μ s u ≤ Real.log 2+Real.log (max 1 (3/q))+
      η*Real.log (max 1 ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)) := by
  classical
  let t := Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋
  let a := t.filter (fun i => ∃ x ∈ E, label s u x=i)
  have ha : a ⊆ t := Finset.filter_subset _ _
  have has : ∀ i ∈ a, ∃ x ∈ E, label s u x=i := fun i hi => (Finset.mem_filter.mp hi).2
  let x : ℤ → ℝ := fun i => if hi : i ∈ a then (has i hi).choose else 0
  have hx : ∀ i ∈ a, x i ∈ E ∧ label s u (x i)=i := by
    intro i hi
    dsimp only [x]
    rw [dite_eq_left hi]
    exact (has i hi).choose_spec
  have hcard := good_labels_card_bound μ hs a x
    (fun i hi => (hx i hi).2) (fun i hi => hball _ (hx i hi).1)
  have hm : μ.real {z | label s u z ∉ a} ≤ η := by
    have hae : {z | label s u z ∉ a} ≤ᵐ[μ] Eᶜ := by
      filter_upwards [label_ae_uniform μ hs hB hu] with z hz hza
      intro hzE
      exact hza (Finset.mem_filter.mpr ⟨hz,⟨z,hzE,rfl⟩⟩)
    exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hae)).trans hη
  have hh := entropy_subset_bound μ (label s u) (label_measurable s u) t a ha
    (label_ae_uniform μ hs hB hu) hm
  have hlog : Real.log (max 1 (a.card : ℝ)) ≤ Real.log (max 1 (3/q)) := by
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact max_le_max_left _ ((le_div_iff₀ hq).mpr hcard)
  exact hh.trans (by dsimp only [t]; linarith)

theorem grid_support_card_le {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1) :
    ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ) ≤ (2*B+3)/s := by
  have hf : ⌊-B/s⌋ ≤ ⌊B/s+1⌋ := Int.floor_le_floor (by
    have := div_nonneg hB hs.le
    simp only [neg_div]
    linarith)
  rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega : 0 ≤ ⌊B/s+1⌋+1-⌊-B/s⌋)]
  push_cast
  have h1 := Int.floor_le (B/s+1)
  have h2 := Int.lt_floor_add_one (-B/s)
  have h3 : (3 : ℝ) ≤ 3/s := (le_div_iff₀ hs).mpr (by nlinarith)
  calc
    (⌊B/s+1⌋ : ℝ)+1-⌊-B/s⌋ ≤ 2*B/s+3 := by
      simp only [neg_div] at h2 ⊢
      rw [mul_div_assoc]
      linarith
    _ ≤ (2*B+3)/s := by rw [add_div]; linarith

theorem grid_le_of_power_ball_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {B s u d η : ℝ} (hB0 : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1)
    (hd : 0 ≤ d) (hη0 : 0 ≤ η)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (E : Set ℝ) (hη : μ.real Eᶜ ≤ η)
    (hball : ∀ x ∈ E, (s/2)^d ≤ μ.real (Metric.ball x (s/2))) :
    grid μ s u ≤ Real.log 6+d*Real.log 2+η*Real.log (2*B+3)+
      (d+η)*Real.log (1/s) := by
  have hq : 0 < (s/2)^d := Real.rpow_pos_of_pos (by positivity) _
  have hq1 : (s/2)^d ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) hd
  have hh := grid_le_of_ball_mass μ hs hq hB hu E hη hball
  have hq3 : 1 ≤ 3/(s/2)^d := (le_div_iff₀ hq).mpr (by linarith)
  rw [max_eq_right hq3] at hh
  have hnum : 0 < 2*B+3 := by linarith
  have hcard := grid_support_card_le hB0 hs hs1
  have hbase : 1 ≤ (2*B+3)/s := (le_div_iff₀ hs).mpr (by linarith)
  have hlog : Real.log (max 1 ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)) ≤
      Real.log ((2*B+3)/s) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hbase hcard)
  have hm := mul_le_mul_of_nonneg_left hlog hη0
  have he : Real.log 2+Real.log (3/(s/2)^d)+η*Real.log ((2*B+3)/s) =
      Real.log 6+d*Real.log 2+η*Real.log (2*B+3)+(d+η)*Real.log (1/s) := by
    rw [Real.log_div (by norm_num) hq.ne',Real.log_rpow (by positivity),
      Real.log_div hs.ne' (by norm_num),Real.log_div hnum.ne' hs.ne',
      Real.log_div (by norm_num) hs.ne',Real.log_one]
    have h6 : Real.log (6 : ℝ)=Real.log 2+Real.log 3 := by
      rw [show (6 : ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    rw [h6]
    ring
  rw [← he]
  linarith

end MeasureEntropy
end EntropyRateDimension

end OAI
