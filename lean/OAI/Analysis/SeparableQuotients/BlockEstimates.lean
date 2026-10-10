import OAI.Analysis.SeparableQuotients.PartitionBlocks

namespace OAI

noncomputable section

namespace SeparableQuotient.RecordGrowth
open Filter
open scoped Topology

/-- The logarithmic parameter limit implies unboundedness above every smaller power. -/
lemma div_rpow_tendsto_atTop {a b : ℕ → ℝ} {p e : ℝ}
    (ha : ∀ n, 1 < a n) (hb : ∀ n, 0 < b n)
    (hA : Tendsto a atTop atTop)
    (hlog : Tendsto (fun n => Real.log (b n) / Real.log (a n)) atTop (𝓝 p))
    (he : e < p) : Tendsto (fun n => b n / (a n)^e) atTop atTop := by
  let δ := (p-e)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hep : e+δ < p := by dsimp [δ]; linarith
  have hev := hlog.eventually (eventually_gt_nhds hep)
  refine tendsto_atTop_mono' atTop (f₁ := fun n => (a n)^δ) ?_
    ((tendsto_rpow_atTop hδ).comp hA)
  filter_upwards [hev] with n hn
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith [ha n]) e)).mpr
  rw [← Real.rpow_add (by linarith [ha n])]
  apply (Real.rpow_le_iff_le_log (by linarith [ha n]) (hb n)).mpr
  have := (lt_div_iff₀ (Real.log_pos (ha n))).mp hn
  nlinarith

/-- A record ratio over a finite initial segment, with a prescribed large
value of a(k), precisely as in the partition-block argument. -/
lemma exists_record (a : ℕ → ℝ) (e M : ℝ) (he : 0 ≤ e) (hM : 0 ≤ M)
    (hunbounded : ∀ R : ℝ, ∃ k : ℕ, 1 ≤ k ∧ R < a k / (k : ℝ)^e) :
    ∃ k : ℕ, 1 ≤ k ∧ M ≤ a k ∧
      ∀ l : ℕ, 1 ≤ l → l ≤ k → a l ≤ a k * ((l : ℝ)/(k : ℝ))^e := by
  obtain ⟨n, hn, hAn⟩ := hunbounded M
  obtain ⟨k, hk, hmax⟩ := (Finset.Icc 1 n).exists_max_image
    (fun l => a l / (l : ℝ)^e) ⟨n, Finset.mem_Icc.mpr ⟨hn, le_rfl⟩⟩
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hpow : 1 ≤ (k : ℝ)^e := Real.one_le_rpow (by exact_mod_cast hk1) he
  have hAk : M < a k / (k : ℝ)^e :=
    hAn.trans_le (hmax n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩))
  have hMk : M ≤ a k := by
    have hmul := (lt_div_iff₀ (Real.rpow_pos_of_pos hk0 e)).mp hAk
    exact (le_mul_of_one_le_right hM hpow).trans hmul.le
  refine ⟨k, hk1, hMk, ?_⟩
  intro l hl hlk
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hrat := hmax l (Finset.mem_Icc.mpr ⟨hl, hlk.trans hkn⟩)
  rw [Real.div_rpow hl0.le hk0.le]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hl0 e)).mp hrat |>.trans_eq
  ring

/-- A slightly smaller reciprocal exponent can be chosen uniformly for all
of the finitely many partition sizes under consideration. -/
lemma choose_exponent (s N : ℝ) (hs : 1 < s) (hN : 1 ≤ N) :
    ∃ e : ℝ, 0 < e ∧ e < 1/s ∧
      ∀ d : ℝ, 1 ≤ d → d ≤ N → d^(1-e) ≤ 2*d^(1-1/s) := by
  let δ := min (1/(2*s)) (Real.log 2 / (Real.log N+1))
  have hs0 : 0 < s := by linarith
  have hln : 0 ≤ Real.log N := Real.log_nonneg hN
  have hδ : 0 < δ := lt_min (by positivity) (by positivity [Real.log_pos (by norm_num : (1:ℝ)<2)])
  have hδs : δ ≤ 1/(2*s) := min_le_left _ _
  have hδN : δ ≤ Real.log 2 / (Real.log N+1) := min_le_right _ _
  have hs2 : 1/(2*s) = (1/s)/2 := by ring
  have hinv : 0 < 1/s := one_div_pos.mpr hs0
  refine ⟨1/s-δ, by linarith, by linarith, ?_⟩
  intro d hd hdN
  have hd0 : 0 < d := by linarith
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hdδ : d^δ ≤ 2 := by
    apply (Real.rpow_le_iff_le_log hd0 (by norm_num)).mpr
    have hm := (le_div_iff₀ (by linarith : 0 < Real.log N+1)).mp hδN
    have hmn := mul_le_mul_of_nonneg_left (Real.log_le_log hd0 hdN) hδ.le
    nlinarith
  calc
    d^(1-(1/s-δ)) = d^δ * d^(1-1/s) := by
      rw [← Real.rpow_add hd0]; congr 1; ring
    _ ≤ 2*d^(1-1/s) := mul_le_mul_of_nonneg_right hdδ (Real.rpow_nonneg hd0.le _)

/-- The finite concave power bound (Hölder) in the unit-block partition proof. -/
lemma sum_rpow_le_card {ι : Type*} [Fintype ι] (w : ι → ℝ) (e : ℝ)
    (he : 0 < e) (he1 : e < 1) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ 1) :
    ∑ i, (w i)^e ≤ (Fintype.card ι : ℝ)^(1-e) := by
  have hpq : Real.HolderConjugate (1/e) (1/(1-e)) := {
    inv_add_inv_eq_inv := by simp
    left_pos := by positivity
    right_pos := by positivity }
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ (f := fun i => (w i)^e)
    (g := fun _ => (1 : ℝ)) hpq (fun i _ => Real.rpow_nonneg (hw i) e) (fun _ _ => zero_le_one)
  have hpow (i : ι) : ((w i)^e)^(1/e) = w i := by
    rw [← Real.rpow_mul (hw i), mul_one_div_cancel he.ne', Real.rpow_one]
  simp only [mul_one, hpow, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, one_div_one_div] at hh
  have hs0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hle : (∑ i, w i)^e ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hs0 hs he.le
  exact hh.trans ((mul_le_mul_of_nonneg_right hle
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq (one_mul _))

end SeparableQuotient.RecordGrowth

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma blockSumSup_div_rpow_unbounded {f : Family} (z : BlockSequence f) (a : ℕ)
    (e : ℝ) (he : e < 1/(f.s : ℝ)) :
    ∀ R : ℝ, ∃ k : ℕ, 1 ≤ k ∧ R < blockSumSup f (z.tailSpan a) k / (k : ℝ)^e := by
  have hL : Tendsto (fun n => (Parameters.L f.s n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Parameters.L_strict f.s_ge_two).tendsto_atTop
  have hL1 (n : ℕ) : (1 : ℝ) < Parameters.L f.s n := by
    have hn : 1 < Parameters.L f.s n := by
      apply Nat.one_lt_pow
      · positivity [Family.s_ge_two f, Parameters.t_pos f.s n]
      · norm_num
    exact_mod_cast hn
  have hb (n : ℕ) : (0 : ℝ) < (Parameters.L f.s n : ℝ)/(Parameters.m f.s n : ℝ) :=
    div_pos (by exact_mod_cast Parameters.L_pos f.s n) (by exact_mod_cast Parameters.m_pos f.s n)
  have hg := RecordGrowth.div_rpow_tendsto_atTop hL1 hb hL
    (Parameters.parameter_growth f.s_ge_two) he
  intro R
  obtain ⟨n, hn⟩ := (hg.eventually (eventually_gt_atTop (2*R))).exists
  refine ⟨f.L (n+1), f.L_pos _, ?_⟩
  have hlo := (z.unitBlocks a (f.L (n+1))).norm_sum_lower (n+1) (by omega)
  have hsup := (z.unitBlocks a (f.L (n+1))).norm_sum_le_sup
  change (2*R) < (f.L (n+1) : ℝ)/(f.m (n+1) : ℝ)/(f.L (n+1) : ℝ)^e at hn
  have hp : 0 < (f.L (n+1) : ℝ)^e := Real.rpow_pos_of_pos (by exact_mod_cast f.L_pos _) e
  have hle := (div_le_div_of_nonneg_right (hlo.trans hsup) hp.le)
  have hid : (f.L (n+1) : ℝ)/(2*(f.m (n+1) : ℝ))/(f.L (n+1) : ℝ)^e =
      ((f.L (n+1) : ℝ)/(f.m (n+1) : ℝ)/(f.L (n+1) : ℝ)^e)/2 := by ring
  rw [hid] at hle
  linarith

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.IntervalIncidence
open scoped Classical

variable {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- Only the first and last members of a successive finite family can partly
intersect one order-convex interval. -/
lemma partial_intersections_le_two (s : Finset α) (F : α → Finset β)
    (hF : ∀ i j, i < j → ∀ a ∈ F i, ∀ b ∈ F j, a < b)
    (I : Set β) (hI : Set.OrdConnected I) :
    (s.filter (fun i => (∃ a ∈ F i, a ∈ I) ∧ ¬ (↑(F i) : Set β) ⊆ I)).card ≤ 2 := by
  let t := s.filter (fun i => (∃ a ∈ F i, a ∈ I) ∧ ¬ (↑(F i) : Set β) ⊆ I)
  change t.card ≤ 2
  by_cases ht : t.Nonempty
  · have hsub : t ⊆ {t.min' ht, t.max' ht} := by
      intro i hi
      by_cases hmin : i = t.min' ht
      · simp [hmin]
      by_cases hmax : i = t.max' ht
      · simp [hmax]
      have h1 : t.min' ht < i := lt_of_le_of_ne (t.min'_le i hi) (Ne.symm hmin)
      have h2 : i < t.max' ht := lt_of_le_of_ne (t.le_max' i hi) hmax
      obtain ⟨a, ha, haI⟩ := (Finset.mem_filter.mp (t.min'_mem ht)).2.1
      obtain ⟨b, hb, hbI⟩ := (Finset.mem_filter.mp (t.max'_mem ht)).2.1
      have hn := (Finset.mem_filter.mp hi).2.2
      exact (hn (fun c hc => hI.out haI hbI ⟨(hF _ _ h1 a ha c hc).le, (hF _ _ h2 c hc b hb).le⟩)).elim
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  · simp [Finset.not_nonempty_iff_eq_empty.mp ht]

/-- A noncrossing incidence matrix has at most two multichild rows incident to each fixed child. -/
lemma noncrossing_multichild_column_le_two (s : Finset α) (t : Finset β) (R : α → β → Prop)
    (hR : ∀ i ∈ s, ∀ j ∈ s, i < j → ∀ a ∈ t, ∀ b ∈ t, R i a → R j b → a ≤ b)
    (a : β) (ha : a ∈ t) :
    (s.filter (fun i => R i a ∧ 2 ≤ (t.filter (R i)).card)).card ≤ 2 := by
  let v := s.filter (fun i => R i a ∧ 2 ≤ (t.filter (R i)).card)
  change v.card ≤ 2
  by_cases hv : v.Nonempty
  · have hsub : v ⊆ {v.min' hv, v.max' hv} := by
      intro i hi
      by_cases hmin : i = v.min' hv
      · simp [hmin]
      by_cases hmax : i = v.max' hv
      · simp [hmax]
      have h1 : v.min' hv < i := lt_of_le_of_ne (v.min'_le i hi) (Ne.symm hmin)
      have h2 : i < v.max' hv := lt_of_le_of_ne (v.le_max' i hi) hmax
      have hi' := Finset.mem_filter.mp hi
      have hm := Finset.mem_filter.mp (v.min'_mem hv)
      have hx := Finset.mem_filter.mp (v.max'_mem hv)
      have hs : t.filter (R i) ⊆ {a} := by
        intro b hb
        have hb' := Finset.mem_filter.mp hb
        exact Finset.mem_singleton.mpr (le_antisymm
          (hR _ hi'.1 _ hx.1 h2 b hb'.1 a ha hb'.2 hx.2.1)
          (hR _ hm.1 _ hi'.1 h1 a ha b hb'.1 hm.2.1 hb'.2))
      have hc : (t.filter (R i)).card ≤ 1 := (Finset.card_le_card hs).trans (by simp)
      omega
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp hv]

lemma noncrossing_boundary_incidence (s : Finset α) (t : Finset β) (R : α → β → Prop)
    (hR : ∀ i ∈ s, ∀ j ∈ s, i < j → ∀ a ∈ t, ∀ b ∈ t, R i a → R j b → a ≤ b) :
    ∑ i ∈ s.filter (fun i => 2 ≤ (t.filter (R i)).card), (t.filter (R i)).card ≤ 2 * t.card := by
  calc
    _ = ∑ i ∈ s, ∑ a ∈ t, if R i a ∧ 2 ≤ (t.filter (R i)).card then 1 else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 2 ≤ (t.filter (R i)).card
      · simp only [hi, ↓reduceIte, and_true]
        rw [Finset.card_filter]
      · simp only [hi, ↓reduceIte, and_false, Finset.sum_const_zero]
    _ = ∑ a ∈ t, (s.filter (fun i => R i a ∧ 2 ≤ (t.filter (R i)).card)).card := by
      rw [Finset.sum_comm]
      simp only [Finset.card_filter]
    _ ≤ ∑ a ∈ t, 2 := Finset.sum_le_sum (fun a ha => noncrossing_multichild_column_le_two s t R hR a ha)
    _ = _ := by simp; omega

end SeparableQuotient.IntervalIncidence

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma intervalProjection_fixed (I : Set Γ) (hI : Set.OrdConnected I) (x : Γ →₀ ℝ)
    (hx : (x.support : Set Γ) ⊆ I) :
    intervalProjection I hI (norming.includeFinite x) = norming.includeFinite x := by
  apply coordinate_ext
  intro a
  simp only [intervalProjection, coordinate_projection, Crop.ordinalSet_set,
    norming.coordinate_includeFinite]
  split_ifs with ha
  · rfl
  · exact (Finsupp.notMem_support_iff.mp (fun h => ha (hx h))).symm

lemma intervalProjection_eq_zero (I : Set Γ) (hI : Set.OrdConnected I) (x : Γ →₀ ℝ)
    (hx : ∀ a ∈ x.support, a ∉ I) :
    intervalProjection I hI (norming.includeFinite x) = 0 := by
  apply coordinate_ext
  intro a
  simp only [intervalProjection, coordinate_projection, Crop.ordinalSet_set,
    norming.coordinate_includeFinite, map_zero]
  split_ifs with ha
  · exact Finsupp.notMem_support_iff.mp (fun h => hx a h ha)
  · rfl

lemma UnitBlocks.interval_norm_le {f S k} (v : UnitBlocks f S k)
    (I : Set Γ) (hI : Set.OrdConnected I) :
    ‖intervalProjection I hI (norming.includeFinite (∑ i, v.vector i))‖ ≤
      ‖norming.includeFinite (∑ i ∈ Finset.univ.filter (fun i => ((v.vector i).support : Set Γ) ⊆ I), v.vector i)‖ + 2 := by
  let F := Finset.univ.filter (fun i => ((v.vector i).support : Set Γ) ⊆ I)
  let B := Finset.univ.filter (fun i => (∃ a ∈ (v.vector i).support, a ∈ I) ∧
    ¬ ((v.vector i).support : Set Γ) ⊆ I)
  have hB : B.card ≤ 2 := IntervalIncidence.partial_intersections_le_two _ (fun i => (v.vector i).support)
    (fun i j hij a ha b hb => (v.successive i j hij a ha b hb).1) I hI
  have heq : intervalProjection I hI (norming.includeFinite (∑ i, v.vector i)) =
      norming.includeFinite (∑ i ∈ F, v.vector i) +
        ∑ i ∈ B, intervalProjection I hI (norming.includeFinite (v.vector i)) := by
    simp only [map_sum, F, B, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ((v.vector i).support : Set Γ) ⊆ I
    · simp only [hi, not_true_eq_false, and_false, ↓reduceIte, add_zero]
      exact intervalProjection_fixed I hI _ hi
    · by_cases hh : ∃ a ∈ (v.vector i).support, a ∈ I
      · simp only [hi, hh, not_false_eq_true, true_and, ↓reduceIte, map_zero, zero_add]
      · have hz : ∀ a ∈ (v.vector i).support, a ∉ I := by simpa only [not_exists, not_and] using hh
        simp only [hi, hh, false_and, ↓reduceIte, map_zero, add_zero]
        exact intervalProjection_eq_zero I hI _ hz
  rw [heq]
  apply (norm_add_le _ _).trans
  apply add_le_add_right
  calc
    ‖∑ i ∈ B, intervalProjection I hI (norming.includeFinite (v.vector i))‖ ≤
        ∑ i ∈ B, ‖intervalProjection I hI (norming.includeFinite (v.vector i))‖ := norm_sum_le B _
    _ ≤ ∑ _i ∈ B, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_projection_le _ _).trans_eq (v.unit i)
    _ = B.card := by simp
    _ ≤ 2 := by exact_mod_cast hB

lemma UnitBlocks.full_card_sum_le {f S k} (v : UnitBlocks f S k) (d : ℕ)
    (I : Fin d → Set Γ)
    (hIs : ∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b) :
    ∑ b : Fin d, (Finset.univ.filter (fun i => ((v.vector i).support : Set Γ) ⊆ I b)).card ≤ k := by
  let F := fun b : Fin d => Finset.univ.filter (fun i => ((v.vector i).support : Set Γ) ⊆ I b)
  have hd : ((Finset.univ : Finset (Fin d)) : Set (Fin d)).PairwiseDisjoint F := by
    intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hb := (Finset.mem_filter.mp hi).2
    have hc := (Finset.mem_filter.mp hj).2
    obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr (v.nonzero i)
    rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact (lt_irrefl a) (hIs b c hbc a (hb ha) a (hc ha))
    · exact (lt_irrefl a) (hIs c b hcb a (hc ha) a (hb ha))
  change ∑ b, (F b).card ≤ k
  rw [← Finset.card_biUnion hd]
  simpa using (Finset.card_le_univ (Finset.univ.biUnion F))

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma UnitBlocks.subsum_record {f S k} (v : UnitBlocks f S k) (t : Finset (Fin k))
    (e : ℝ) (he : 0 < e) (_hk : 1 ≤ k)
    (hrec : ∀ l : ℕ, 1 ≤ l → l ≤ k →
      blockSumSup f S l ≤ blockSumSup f S k * ((l : ℝ)/(k : ℝ))^e) :
    ‖norming.includeFinite (∑ i ∈ t, v.vector i)‖ ≤ blockSumSup f S k * ((t.card : ℝ)/(k : ℝ))^e := by
  by_cases ht : t.Nonempty
  · exact v.norm_subsum_le_sup t |>.trans (hrec t.card ht.card_pos (by simpa using t.card_le_univ))
  · rw [Finset.not_nonempty_iff_eq_empty.mp ht]
    simp [Real.zero_rpow he.ne']

lemma UnitBlocks.partition_sum_record {f S k} (v : UnitBlocks f S k)
    (e : ℝ) (he : 0 < e) (he1 : e < 1) (hk : 1 ≤ k)
    (hrec : ∀ l : ℕ, 1 ≤ l → l ≤ k →
      blockSumSup f S l ≤ blockSumSup f S k * ((l : ℝ)/(k : ℝ))^e)
    (d : ℕ) (I : Fin d → Set Γ) (hI : ∀ b, Set.OrdConnected (I b))
    (hIs : ∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b) :
    ∑ b, ‖intervalProjection (I b) (hI b) (norming.includeFinite (∑ i, v.vector i))‖ ≤
      blockSumSup f S k * (d : ℝ)^(1-e) + 2*d := by
  let F := fun b : Fin d => Finset.univ.filter (fun i => ((v.vector i).support : Set Γ) ⊆ I b)
  have ha : 0 ≤ blockSumSup f S k := blockSumSup_nonneg ⟨v⟩
  have hw0 (b : Fin d) : 0 ≤ ((F b).card : ℝ)/(k : ℝ) := by positivity
  have hws : ∑ b, ((F b).card : ℝ)/(k : ℝ) ≤ 1 := by
    rw [← Finset.sum_div, div_le_one (by exact_mod_cast hk : (0 : ℝ) < k)]
    exact_mod_cast v.full_card_sum_le d I hIs
  have hp := RecordGrowth.sum_rpow_le_card (fun b => ((F b).card : ℝ)/(k : ℝ)) e he he1 hw0 hws
  simp only [Fintype.card_fin] at hp
  calc
    _ ≤ ∑ b, (blockSumSup f S k * (((F b).card : ℝ)/(k : ℝ))^e + 2) := by
      apply Finset.sum_le_sum
      intro b _
      exact (v.interval_norm_le (I b) (hI b)).trans (add_le_add_left (v.subsum_record (F b) e he hk hrec) 2)
    _ = blockSumSup f S k * ∑ b, (((F b).card : ℝ)/(k : ℝ))^e + 2*d := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp; ring
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hp ha) _

lemma UnitBlocks.normalized_partition {f S k} (v : UnitBlocks f S k)
    (N : ℕ) (hN : 1 ≤ N) (e : ℝ) (he : 0 < e) (he1 : e < 1) (hk : 1 ≤ k)
    (hrec : ∀ l : ℕ, 1 ≤ l → l ≤ k →
      blockSumSup f S l ≤ blockSumSup f S k * ((l : ℝ)/(k : ℝ))^e)
    (hlarge : (N : ℝ) ≤ blockSumSup f S k)
    (hnear : blockSumSup f S k / 2 < ‖norming.includeFinite (∑ i, v.vector i)‖)
    (hexp : ∀ d : ℝ, 1 ≤ d → d ≤ N → d^(1-e) ≤ 2*d^(1/f.r)) :
    PartitionBound (‖norming.includeFinite (∑ i, v.vector i)‖⁻¹ • norming.includeFinite (∑ i, v.vector i)) N 8 f.r := by
  let x := norming.includeFinite (∑ i, v.vector i)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hnearX : blockSumSup f S k / 2 < ‖x‖ := hnear
  have hx : 0 < ‖x‖ := by linarith
  intro d hd hdN I hI hIs
  have hb : ∑ b, ‖intervalProjection (I b) (hI b) x‖ ≤
      blockSumSup f S k * (d : ℝ)^(1-e) + 2*d := v.partition_sum_record e he he1 hk hrec d I hI hIs
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdN' : (d : ℝ) ≤ N := by exact_mod_cast hdN
  have hdexp := hexp d hd0 hdN'
  have hpow : 1 ≤ (d : ℝ)^(1/f.r) := Real.one_le_rpow hd0 (one_div_nonneg.mpr f.r_pos.le)
  have hm : 0 ≤ blockSumSup f S k := by linarith
  have hprod : blockSumSup f S k * (d : ℝ)^(1-e) ≤
      4*‖x‖*(d : ℝ)^(1/f.r) := by
    have hh := mul_le_mul_of_nonneg_left hdexp hm
    have hnear' : blockSumSup f S k ≤ 2*‖x‖ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hnear' (by positivity : 0 ≤ 2*(d : ℝ)^(1/f.r))
    nlinarith
  have hdlarge : 2*(d : ℝ) ≤ 4*‖x‖ := by linarith
  have hsum : ∑ b, ‖intervalProjection (I b) (hI b) x‖ ≤ 8*‖x‖*(d : ℝ)^(1/f.r) := by
    have hnorm := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4*‖x‖)
    nlinarith
  simp only [map_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm, ← Finset.mul_sum]
  change ‖x‖⁻¹ * (∑ b, ‖intervalProjection (I b) (hI b) x‖) ≤ _
  calc
    _ ≤ ‖x‖⁻¹ * (8*‖x‖*(d : ℝ)^(1/f.r)) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hx.le)
    _ = _ := by field_simp

/-- The constant-eight interval partition estimate in any prescribed algebraic tail of a block sequence. -/
theorem BlockSequence.exists_partition_unit {f : Family} (z : BlockSequence f)
    (a N : ℕ) (hN : 1 ≤ N) :
    ∃ u : Γ →₀ ℝ, u ∈ z.tailSpan a ∧ ‖norming.includeFinite u‖ = 1 ∧
      PartitionBound (norming.includeFinite u) N 8 f.r := by
  have hs : 1 < (f.s : ℝ) := by exact_mod_cast (show 1 < f.s from f.s_ge_two)
  obtain ⟨e, he, hes, hexp⟩ := RecordGrowth.choose_exponent (f.s : ℝ) N hs (by exact_mod_cast hN)
  have he1 : e < 1 := hes.trans ((div_lt_one (by linarith : (0 : ℝ) < f.s)).mpr hs)
  obtain ⟨k, hk, hklarge, hkrec⟩ := RecordGrowth.exists_record
    (blockSumSup f (z.tailSpan a)) e N he.le (Nat.cast_nonneg _)
    (blockSumSup_div_rpow_unbounded z a e hes)
  have hnon : Nonempty (UnitBlocks f (z.tailSpan a) k) := ⟨z.unitBlocks a k⟩
  have hak : 0 < blockSumSup f (z.tailSpan a) k := lt_of_lt_of_le (by exact_mod_cast hN) hklarge
  obtain ⟨v, hv⟩ := unitBlocks_near_sup hnon hak
  let w := ∑ i, v.vector i
  have hvw : blockSumSup f (z.tailSpan a) k / 2 < ‖norming.includeFinite w‖ := hv
  have hw : 0 < ‖norming.includeFinite w‖ := by linarith
  refine ⟨‖norming.includeFinite w‖⁻¹ • w, Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun i _ => v.mem i)), ?_, ?_⟩
  · rw [map_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ hw.ne']
  · rw [map_smul]
    apply v.normalized_partition N hN e he he1 hk hkrec hklarge hv
    intro d hd hdN
    have hconj := Parameters.s_r_conjugate f.s_ge_two
    have heq : 1/f.r = 1 - 1/(f.s : ℝ) := (eq_sub_iff_add_eq).mpr
      (by simpa only [Family.r, one_div] using hconj.symm.inv_add_inv_eq_one)
    simpa only [heq] using hexp d hd hdN

end SeparableQuotient.ActualSpace

end

end OAI
