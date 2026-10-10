import OAI.Geometry.CylinderCovering.Radial.RiemannDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialRiemann
open Set MeasureTheory Filter
open scoped Interval Topology

lemma step_pos {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) :
    0 < step a b N := by
  exact div_pos (sub_pos.mpr hab) (Nat.cast_pos.mpr hN)

lemma count_step {a b : ℝ} {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * step a b N = b - a := by
  dsimp [step]
  field_simp

lemma point_zero (a b : ℝ) (N : ℕ) : point a b N 0 = a := by
  simp [point]

lemma point_last {a b : ℝ} {N : ℕ} (hN : 0 < N) : point a b N N = b := by
  rw [point, count_step hN]
  ring

lemma point_succ (a b : ℝ) (N i : ℕ) :
    point a b N (i + 1) - point a b N i = step a b N := by
  simp only [point, Nat.cast_add, Nat.cast_one]
  ring

lemma point_mem {a b : ℝ} (hab : a < b) {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    point a b N i ∈ Icc a b := by
  have hd := (step_pos hab hN).le
  have hiR : (i : ℝ) ≤ N := by exact_mod_cast hi
  have hprod := mul_le_mul_of_nonneg_right hiR hd
  rw [count_step hN] at hprod
  constructor
  · dsimp [point]; exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hd)
  · dsimp [point]; linarith

lemma cell_subset {a b : ℝ} (hab : a < b) {N : ℕ} (i : Fin N) :
    cell a b N i ⊆ Icc a b := by
  have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
  have hl := point_mem hab hN i.isLt.le
  have hr := point_mem hab hN (Nat.succ_le_of_lt i.isLt)
  intro x hx
  exact ⟨hl.1.trans hx.1, hx.2.trans hr.2⟩

lemma cell_nonempty {a b : ℝ} (hab : a < b) {N : ℕ} (i : Fin N) :
    (cell a b N i).Nonempty := by
  refine ⟨point a b N i, le_rfl, ?_⟩
  have hs := point_succ a b N i
  have hd := step_pos hab (Nat.zero_lt_of_lt i.isLt)
  linarith

lemma cell_dist_le {a b : ℝ} {N : ℕ} {i : Fin N} {x y : ℝ}
    (hx : x ∈ cell a b N i) (hy : y ∈ cell a b N i) :
    dist x y ≤ step a b N := by
  rw [Real.dist_eq, abs_le]
  have hs := point_succ a b N i
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma step_tendsto (a b : ℝ) :
    Tendsto (step a b) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  change Tendsto (fun N : ℕ => (b - a) / (N : ℝ)) atTop (𝓝 0)
  simpa [div_eq_mul_inv] using hi.const_mul (b - a)

lemma diagonal_continuous {a b : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Icc a b) ×ˢ (Icc a b))) :
    ContinuousOn (fun t => F t t) (Icc a b) := by
  exact hF.comp (continuousOn_id.prodMk continuousOn_id) (fun _ ht => ⟨ht, ht⟩)

lemma diagonal_cell_integrable {a b : ℝ} (hab : a < b) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Icc a b) ×ˢ (Icc a b)))
    {N : ℕ} (i : Fin N) :
    IntervalIntegrable (fun t => F t t) volume (point a b N i) (point a b N (i+1)) := by
  have hle : point a b N i ≤ point a b N (i+1) := by
    have hs := point_succ a b N i
    have hd := step_pos hab (Nat.zero_lt_of_lt i.isLt)
    linarith
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hle]
  exact (diagonal_continuous hF).mono (cell_subset hab i)

lemma integral_mesh_sum {a b : ℝ} (hab : a < b) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Icc a b) ×ˢ (Icc a b)))
    {N : ℕ} (hN : 0 < N) :
    (∑ i : Fin N, ∫ t in point a b N i..point a b N (i+1), F t t) =
      ∫ t in a..b, F t t := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ∫ t in point a b N i..point a b N (i+1), F t t) N]
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun i hi => diagonal_cell_integrable hab hF (⟨i, hi⟩ : Fin N))]
  rw [point_zero, point_last hN]

lemma mixedSum_error {a b E : ℝ} (hab : a < b) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Icc a b) ×ˢ (Icc a b)))
    {N : ℕ} (hN : 0 < N) (leftTag rightTag : Fin N → ℝ)
    (hbound : ∀ i, ∀ t ∈ cell a b N i, |F (leftTag i) (rightTag i) - F t t| ≤ E) :
    |mixedSum F a b N leftTag rightTag - (∫ t in a..b, F t t)| ≤ E * (b-a) := by
  have hi := integral_mesh_sum hab hF hN
  rw [← hi, mixedSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin N, |step a b N * F (leftTag i) (rightTag i) -
      (∫ t in point a b N i..point a b N (i+1), F t t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, E * step a b N := by
      apply Finset.sum_le_sum
      intro i _
      have hle : point a b N i ≤ point a b N (i+1) := by
        have hs := point_succ a b N i
        have hd := step_pos hab hN
        linarith
      have hu : ∀ t ∈ Ι (point a b N i) (point a b N (i+1)),
          ‖F (leftTag i) (rightTag i) - F t t‖ ≤ E := by
        intro t ht
        rw [uIoc_of_le hle] at ht
        exact (hbound i t ⟨ht.1.le, ht.2⟩)
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hu
      rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
        (diagonal_cell_integrable hab hF i), intervalIntegral.integral_const,
        Real.norm_eq_abs, smul_eq_mul, point_succ,
        abs_of_nonneg (step_pos hab hN).le] at h
      exact h
    _ = E * (b-a) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (N : ℝ) * (E * step a b N) = E * ((N : ℝ) * step a b N) := by ring
        _ = E * (b-a) := by rw [count_step hN]

theorem mixedSum_tendsto {a b : ℝ} (hab : a < b) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Icc a b) ×ˢ (Icc a b)))
    (leftTag rightTag : (N : ℕ) → Fin N → ℝ)
    (hleft : ∀ N, IsTagged a b N (leftTag N))
    (hright : ∀ N, IsTagged a b N (rightTag N)) :
    Tendsto (fun N => mixedSum F a b N (leftTag N) (rightTag N)) atTop
      (𝓝 (∫ t in a..b, F t t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlen : 0 < b-a := sub_pos.mpr hab
  have hE : 0 < ε / (2 * (b-a)) := div_pos hε (by positivity)
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hF
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc _ hE
  filter_upwards [(step_tendsto a b).eventually_lt_const hδ,
    eventually_gt_atTop (0 : ℕ)] with N hsmall hN
  rw [Real.dist_eq]
  have he := mixedSum_error hab hF hN (leftTag N) (rightTag N) (E := ε / (2*(b-a)))
    (by
      intro i t ht
      have hl := hleft N i
      have hr := hright N i
      have hdist : dist (leftTag N i, rightTag N i) (t,t) < δ := by
        rw [Prod.dist_eq]
        exact lt_of_le_of_lt (max_le (cell_dist_le hl ht) (cell_dist_le hr ht)) hsmall
      exact (hclose _ ⟨cell_subset hab i hl, cell_subset hab i hr⟩
        _ ⟨cell_subset hab i ht, cell_subset hab i ht⟩ hdist).le)
  refine he.trans_lt ?_
  have hcancel : ε / (2*(b-a)) * (b-a) = ε / 2 := by field_simp
  rw [hcancel]
  linarith

lemma exists_capMax_tag {a b : ℝ} (hab : a < b) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) {N : ℕ} (i : Fin N) :
    ∃ t ∈ cell a b N i, R t = capMax R a b N i := by
  have hc : IsCompact (cell a b N i) := isCompact_Icc
  have hi := hc.image_of_continuousOn (hR.mono (cell_subset hab i))
  have hm := hi.sSup_mem ((cell_nonempty hab i).image R)
  exact hm

lemma collarSum_eq_mixed {a b K : ℝ} {R W : ℝ → ℝ} {N : ℕ}
    (maxTag tag : Fin N → ℝ) (hmax : ∀ i, R (maxTag i) = capMax R a b N i) :
    collarSum R W K a b N tag =
      mixedSum (fun r c => R r ^ 2 * W c) a b N maxTag tag +
      (2 * (K * step a b N)) * mixedSum (fun r c => R r * W c) a b N maxTag tag +
      (K * step a b N)^2 * mixedSum (fun _ c => W c) a b N maxTag tag := by
  simp only [collarSum, mixedSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hmax i]
  ring

theorem collarSum_tendsto {a b : ℝ} (hab : a < b) {R W : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) (hW : ContinuousOn W (Icc a b)) (K : ℝ)
    (tag : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged a b N (tag N)) :
    Tendsto (fun N => collarSum R W K a b N (tag N)) atTop
      (𝓝 (∫ t in a..b, R t ^ 2 * W t)) := by
  choose maxTag hmaxmem hmaxeq using
    (fun N (i : Fin N) => exists_capMax_tag hab hR i)
  have hmaxtag : ∀ N, IsTagged a b N (maxTag N) := hmaxmem
  have hRp : ContinuousOn (fun p : ℝ × ℝ => R p.1)
      ((Icc a b) ×ˢ (Icc a b)) :=
    hR.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hWp : ContinuousOn (fun p : ℝ × ℝ => W p.2)
      ((Icc a b) ×ˢ (Icc a b)) :=
    hW.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have h0 := mixedSum_tendsto hab (F := fun r c => R r ^ 2 * W c) ((hRp.pow 2).mul hWp) maxTag tag hmaxtag htag
  have h1 := mixedSum_tendsto hab (F := fun r c => R r * W c) (hRp.mul hWp) maxTag tag hmaxtag htag
  have h2 := mixedSum_tendsto hab (F := fun _ c => W c) hWp maxTag tag hmaxtag htag
  have hkd : Tendsto (fun N => K * step a b N) atTop (𝓝 0) := by
    simpa using (step_tendsto a b).const_mul K
  have hlim := (h0.add ((hkd.const_mul 2).mul h1)).add ((hkd.pow 2).mul h2)
  have heq : (fun N => collarSum R W K a b N (tag N)) =
      (fun N => mixedSum (fun r c => R r ^ 2 * W c) a b N (maxTag N) (tag N) +
      (2 * (K * step a b N)) * mixedSum (fun r c => R r * W c) a b N (maxTag N) (tag N) +
      (K * step a b N)^2 * mixedSum (fun _ c => W c) a b N (maxTag N) (tag N)) := by
    funext N
    exact collarSum_eq_mixed (maxTag N) (tag N) (hmaxeq N)
  rw [heq]
  simpa using hlim

lemma le_capMax {a b : ℝ} (hab : a < b) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) {N : ℕ} {i : Fin N} {t : ℝ}
    (ht : t ∈ cell a b N i) : R t ≤ capMax R a b N i := by
  exact le_csSup (isCompact_Icc.bddAbove_image (hR.mono (cell_subset hab i)))
    ⟨t, ht, rfl⟩

lemma capMax_nonneg {a b : ℝ} (hab : a < b) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) (hR0 : ∀ t ∈ Icc a b, 0 ≤ R t)
    {N : ℕ} (i : Fin N) : 0 ≤ capMax R a b N i := by
  obtain ⟨t, ht, heq⟩ := exists_capMax_tag hab hR i
  rw [← heq]
  exact hR0 t (cell_subset hab i ht)

lemma capMax_le {a b M : ℝ} (hab : a < b) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) {N : ℕ} (i : Fin N)
    (hM : ∀ t ∈ cell a b N i, R t ≤ M) : capMax R a b N i ≤ M := by
  obtain ⟨t, ht, heq⟩ := exists_capMax_tag hab hR i
  rw [← heq]
  exact hM t ht

lemma projection_weight_continuousOn {E : Type*} [SeminormedAddGroup E]
    {a b : ℝ} {w : ℝ → E} (hw : ContinuousOn w (Icc a b)) :
    ContinuousOn (fun t => 1 / Real.sqrt (1 + ‖w t‖^2)) (Icc a b) := by
  apply continuousOn_const.div ((hw.norm.pow 2).const_add 1).sqrt
  intro t _
  change Real.sqrt (1 + ‖w t‖^2) ≠ 0
  exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg ‖w t‖]))

theorem physical_collar_tendsto {E : Type*} [SeminormedAddGroup E]
    {a b : ℝ} (hab : a < b) {R : ℝ → ℝ} {w : ℝ → E}
    (hR : ContinuousOn R (Icc a b)) (hw : ContinuousOn w (Icc a b)) (K κ : ℝ)
    (tag : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged a b N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N,
      κ * step a b N * (capMax R a b N i + K * step a b N)^2 /
        (2 * Real.sqrt (1 + ‖w (tag N i)‖^2))) atTop
      (𝓝 (κ * ∫ t in a..b, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2)))) := by
  have h := (collarSum_tendsto hab hR (projection_weight_continuousOn hw) K tag htag).const_mul (κ/2)
  convert h using 1
  · funext N
    simp only [collarSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · congr 1
    have hi : (∫ t in a..b, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2))) =
        (1/2 : ℝ) * ∫ t in a..b, R t^2 * (1 / Real.sqrt (1 + ‖w t‖^2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hi]
    ring

theorem taggedSum_tendsto {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (tag : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged a b N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N, step a b N * f (tag N i)) atTop
      (𝓝 (∫ t in a..b, f t)) := by
  have hfp : ContinuousOn (fun p : ℝ × ℝ => f p.2)
      ((Icc a b) ×ˢ (Icc a b)) :=
    hf.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  exact mixedSum_tendsto hab (F := fun _ c => f c) hfp tag tag htag htag

lemma leftTagged {a b : ℝ} (hab : a < b) (N : ℕ) :
    IsTagged a b N (fun i => point a b N i) := by
  intro i
  refine ⟨le_rfl, ?_⟩
  have hs := point_succ a b N i
  have hd := step_pos hab (Nat.zero_lt_of_lt i.isLt)
  linarith

theorem leftSum_tendsto {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun N => step a b N * ∑ i : Fin N, f (point a b N i)) atTop
      (𝓝 (∫ t in a..b, f t)) := by
  simpa only [Finset.mul_sum] using
    taggedSum_tendsto hab hf (fun N i => point a b N i) (leftTagged hab)

lemma exists_adjacent_interval (f : ℕ → ℝ) {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Icc (f 0) (f N)) :
    ∃ i : Fin N, x ∈ Icc (f i) (f (i+1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hzero : N = 0
    · subst N
      exact ⟨⟨0, by decide⟩, hx⟩
    · by_cases hlast : x ≤ f N
      · obtain ⟨i, hi⟩ := ih (Nat.pos_of_ne_zero hzero) ⟨hx.1, hlast⟩
        exact ⟨⟨i, Nat.lt_trans i.isLt (Nat.lt_succ_self N)⟩, hi⟩
      · exact ⟨⟨N, Nat.lt_succ_self N⟩, (lt_of_not_ge hlast).le, hx.2⟩

lemma exists_cell {a b : ℝ} {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Icc a b) : ∃ i : Fin N, x ∈ cell a b N i := by
  apply exists_adjacent_interval (point a b N) hN
  simpa only [point_zero, point_last hN] using hx

theorem maxPowerSum_tendsto {a b : ℝ} (hab : a < b) {R W : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) (hW : ContinuousOn W (Icc a b)) (n : ℕ)
    (tag : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged a b N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N, step a b N * (capMax R a b N i)^n * W (tag N i))
      atTop (𝓝 (∫ t in a..b, R t^n * W t)) := by
  choose maxTag hmaxmem hmaxeq using
    (fun N (i : Fin N) => exists_capMax_tag hab hR i)
  have hRp : ContinuousOn (fun p : ℝ × ℝ => R p.1)
      ((Icc a b) ×ˢ (Icc a b)) :=
    hR.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hWp : ContinuousOn (fun p : ℝ × ℝ => W p.2)
      ((Icc a b) ×ˢ (Icc a b)) :=
    hW.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have h := mixedSum_tendsto hab (F := fun r c => R r^n * W c)
    ((hRp.pow n).mul hWp) maxTag tag hmaxmem htag
  simpa only [mixedSum, hmaxeq, mul_assoc] using h

theorem maxPolynomialSum_tendsto {a b : ℝ} (hab : a < b) {R W : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) (hW : ContinuousOn W (Icc a b)) (A B C : ℝ)
    (tag : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged a b N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N,
      (A * step a b N * (capMax R a b N i)^2 +
       B * (step a b N)^2 * capMax R a b N i + C * (step a b N)^3) * W (tag N i))
      atTop (𝓝 (A * ∫ t in a..b, R t^2 * W t)) := by
  have h2 := maxPowerSum_tendsto hab hR hW 2 tag htag
  have h1 := maxPowerSum_tendsto hab hR hW 1 tag htag
  have h0 := maxPowerSum_tendsto hab hR hW 0 tag htag
  have hd := step_tendsto a b
  have hlim := ((h2.const_mul A).add (((hd.const_mul B)).mul h1)).add
    (((hd.pow 2).const_mul C).mul h0)
  have heq : (fun N => ∑ i : Fin N,
      (A * step a b N * (capMax R a b N i)^2 +
       B * (step a b N)^2 * capMax R a b N i + C * (step a b N)^3) * W (tag N i)) =
      (fun N => A * (∑ i : Fin N, step a b N * (capMax R a b N i)^2 * W (tag N i)) +
       (B * step a b N) * (∑ i : Fin N, step a b N * (capMax R a b N i)^1 * W (tag N i)) +
       (C * (step a b N)^2) * (∑ i : Fin N, step a b N * (capMax R a b N i)^0 * W (tag N i))) := by
    funext N
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  simpa using hlim

theorem mixedSum_lipschitz_error {a b : ℝ} (hab : a < b) {F : ℝ → ℝ → ℝ}
    {C : NNReal} (hF : LipschitzOnWith C (fun p : ℝ × ℝ => F p.1 p.2)
      ((Icc a b) ×ˢ (Icc a b))) {N : ℕ} (hN : 0 < N)
    (leftTag rightTag : Fin N → ℝ) (hleft : IsTagged a b N leftTag)
    (hright : IsTagged a b N rightTag) :
    |mixedSum F a b N leftTag rightTag - (∫ t in a..b, F t t)| ≤
      (C : ℝ) * step a b N * (b-a) := by
  apply mixedSum_error hab hF.continuousOn hN leftTag rightTag
  intro i t ht
  have hdist : dist (leftTag i, rightTag i) (t,t) ≤ step a b N := by
    rw [Prod.dist_eq]
    exact max_le (cell_dist_le (hleft i) ht) (cell_dist_le (hright i) ht)
  have h := hF.dist_le_mul (leftTag i, rightTag i)
    ⟨cell_subset hab i (hleft i), cell_subset hab i (hright i)⟩
    (t,t) ⟨cell_subset hab i ht, cell_subset hab i ht⟩
  exact h.trans (mul_le_mul_of_nonneg_left hdist C.coe_nonneg)

theorem maxPowerSum_lipschitz_error {a b : ℝ} (hab : a < b) {R W : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) (n : ℕ) {C : NNReal}
    (hF : LipschitzOnWith C (fun p : ℝ × ℝ => (R p.1)^n * W p.2)
      ((Icc a b) ×ˢ (Icc a b))) {N : ℕ} (hN : 0 < N)
    (tag : Fin N → ℝ) (htag : IsTagged a b N tag) :
    |(∑ i : Fin N, step a b N * (capMax R a b N i)^n * W (tag i)) -
      (∫ t in a..b, R t^n * W t)| ≤ (C : ℝ) * step a b N * (b-a) := by
  choose maxTag hmaxmem hmaxeq using (fun i : Fin N => exists_capMax_tag hab hR i)
  have h := mixedSum_lipschitz_error hab (F := fun r c => R r^n * W c)
    hF hN maxTag tag hmaxmem htag
  simpa only [mixedSum, hmaxeq, mul_assoc] using h

end CylinderCovering.RadialRiemann

end

end OAI
