import Mathlib
import OAI.Geometry.CAT0Fillings.Calculus.PositiveBivariate
import OAI.Geometry.CAT0Fillings.Powers.PolynomialBound

namespace OAI

section
open Set Filter
open scoped Topology

namespace CAT0Fillings.ClosedCalculus
noncomputable def lowerCut (j : ℕ) : ℝ := 1/((j:ℝ)+2)
noncomputable def upperCut (j : ℕ) : ℝ := (j:ℝ)+2
lemma lowerCut_pos (j : ℕ) : 0 < lowerCut j := by unfold lowerCut; positivity
lemma lowerCut_le_one (j : ℕ) : lowerCut j ≤ 1 := by
  rw [lowerCut,div_le_iff₀ (by positivity : 0 < (j:ℝ)+2)]
  have := Nat.cast_nonneg (α := ℝ) j
  linarith
lemma lowerCut_lt_upperCut (j : ℕ) : lowerCut j < upperCut j := by
  apply (lowerCut_le_one j).trans_lt
  dsimp [upperCut]
  have := Nat.cast_nonneg (α := ℝ) j
  linarith
lemma lowerCut_tendsto : Tendsto lowerCut atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => 1/((j:ℝ)+2)) atTop (𝓝 0)
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  simpa only [lowerCut,Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h
lemma upperCut_tendsto : Tendsto upperCut atTop atTop := by
  exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
lemma cut_eventually {t : ℝ} (ht : 0 < t) :
    ∀ᶠ j in atTop, lowerCut j < t ∧ t < upperCut j :=
  (lowerCut_tendsto.eventually (eventually_lt_nhds ht)).and
    (upperCut_tendsto.eventually (eventually_gt_atTop t))
lemma clamp_tendsto {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun j => max (min t (upperCut j)) (lowerCut j)) atTop (𝓝 t) := by
  by_cases hp : 0 < t
  · apply (tendsto_congr' ((cut_eventually hp).mono fun j hj => ?_)).mpr tendsto_const_nhds
    rw [min_eq_left hj.2.le,max_eq_left hj.1.le]
  · have he : t = 0 := le_antisymm (le_of_not_gt hp) ht
    subst t
    have hh (j : ℕ) : 0 < upperCut j := (lowerCut_pos j).trans (lowerCut_lt_upperCut j)
    apply (tendsto_congr (fun j => ?_)).mpr lowerCut_tendsto
    rw [min_eq_left (hh j).le,max_eq_right (lowerCut_pos j).le]
lemma clamp_pos (j : ℕ) (t : ℝ) : 0 < max (min t (upperCut j)) (lowerCut j) :=
  (lowerCut_pos j).trans_le (le_max_right _ _)
lemma clamp_power_bound {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (j : ℕ) :
    1+(max (min t (upperCut j)) (lowerCut j))^a ≤ 2*(1+t^a) := by
  have hy : max (min t (upperCut j)) (lowerCut j) ≤ max t 1 :=
    max_le_max (min_le_left _ _) (lowerCut_le_one j)
  have hp : (max (min t (upperCut j)) (lowerCut j))^a ≤ 1+t^a := by
    apply (Real.rpow_le_rpow (clamp_pos j t).le hy ha).trans
    rcases le_total t 1 with h | h
    · rw [max_eq_right h,Real.one_rpow]
      exact le_add_of_nonneg_right (Real.rpow_nonneg ht _)
    · rw [max_eq_left h]
      linarith
  nlinarith [Real.rpow_nonneg ht a]
end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_positive_polynomial (hz : IsCycle T)
    {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r) {R : ℝ}
    (hrange : ∀ x, 0 ≤ r x ∧ r x ≤ R)
    {F : ℝ × ℝ → ℝ} (hFm : Measurable F)
    (hF : ContDiffOn ℝ 1 F {z | 0 < z.2})
    (hF0 : ∀ z ∈ Icc (0:ℝ) R, F (z,0) = 0)
    (hFcont : ∀ z ∈ Icc (0:ℝ) R,
      Tendsto (fun t => F (z,t)) (𝓝[>] (0:ℝ)) (𝓝 0))
    (hDcont : ∀ z ∈ Icc (0:ℝ) R,
      Tendsto (fun t => fderiv ℝ F (z,t) (1,0)) (𝓝[>] (0:ℝ)) (𝓝 0))
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hgrowth : ∀ z ∈ Icc (0:ℝ) R, ∀ t : ℝ, 0 < t →
      |F (z,t)| ≤ C*(1+t^a) ∧
      |fderiv ℝ F (z,t) (1,0)| ≤ C*(1+t^a) ∧
      |fderiv ℝ F (z,t) (0,1)| ≤ C*(1+t^a))
    (P : q.Sobolev)
    (hp : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion P) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hw : MemLp (fun w => (q.inclusion P (q.atlasParam w))^a • q.closedGradient P w) 2 q.atlasMeasure) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => if 0 < q.inclusion P (q.atlasParam w) then
          fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (1,0) • q.gradient hr w +
          fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (0,1) • q.closedGradient P w else 0) := by
  choose Q hQ hG using (fun j : ℕ => q.closed_positive_clamped_bivariate hz hr hrange hF P
    (lowerCut_pos j) (lowerCut_lt_upperCut j))
  let b (x : X) := (2*C)*(1+(q.inclusion P x)^a)
  let c (w : ℕ × Euc (k+1)) := (2*C)*(1+(q.inclusion P (q.atlasParam w))^a)*(K+‖q.closedGradient P w‖)
  let f (x : X) := F (r x,q.inclusion P x)
  let g (w : ℕ × Euc (k+1)) := if 0 < q.inclusion P (q.atlasParam w) then
    fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (1,0) • q.gradient hr w +
    fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (0,1) • q.closedGradient P w else 0
  have hpair := hr.continuous.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable (q.inclusion P))
  have hpairA := hpair.comp_measurePreserving q.atlas_preserving
  have hPA := (Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hf : AEStronglyMeasurable f (MassMeasure.currentMassMeasure hT) :=
    (hFm.comp_aemeasurable hpair.aemeasurable).aestronglyMeasurable
  have hg : AEStronglyMeasurable g q.atlasMeasure := by
    apply AEStronglyMeasurable.indicator₀
    · exact (((measurable_fderiv_apply_const ℝ F (1,0)).comp_aemeasurable hpairA.aemeasurable).aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable (q.gradient hr))).add
        (((measurable_fderiv_apply_const ℝ F (0,1)).comp_aemeasurable hpairA.aemeasurable).aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable (q.closedGradient P)))
    · exact aestronglyMeasurable_const.nullMeasurableSet_lt hPA
  have hpa := q.atlas_preserving.quasiMeasurePreserving.ae
    (p := fun x : X => 0 ≤ q.inclusion P x) hp
  have hscalar := power_memLp_two hp hm ha
  have hb : MemLp b 2 (MassMeasure.currentMassMeasure hT) := ((memLp_const (1:ℝ)).add hscalar).const_mul (2*C)
  have hc : MemLp c 2 q.atlasMeasure := polynomial_domination_memLp hpa
    (hscalar.comp_measurePreserving q.atlas_preserving) (Lp.memLp (q.closedGradient P)) hw (2*C) K
  have hdr : ∀ᵐ w ∂q.atlasMeasure, ‖q.gradient hr w‖ ≤ K := by
    filter_upwards [(q.memLp_gradientFunction hr).coeFn_toLp,q.ae_gradientFunction_bound hr] with w he hb
    change q.gradient hr w = _ at he
    rw [he]
    exact hb
  have hdom {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : 0 < s)
      (ha' : 1+s^a ≤ 2*(1+t^a)) : C*(1+s^a) ≤ (2*C)*(1+t^a) := by
    nlinarith [mul_le_mul_of_nonneg_left ha' hC]
  have hbound {w : ℕ × Euc (k+1)} {t : ℝ} {U : Euc (k+1)}
      (hpw : 0 ≤ q.inclusion P (q.atlasParam w)) (ht : 0 < t)
      (hle : 1+t^a ≤ 2*(1+(q.inclusion P (q.atlasParam w))^a))
      (hd : ‖q.gradient hr w‖ ≤ K) (hU : ‖U‖ ≤ ‖q.closedGradient P w‖) :
      ‖fderiv ℝ F (r (q.atlasParam w),t) (1,0) • q.gradient hr w +
        fderiv ℝ F (r (q.atlasParam w),t) (0,1) • U‖ ≤ c w := by
    have hh := hgrowth (r (q.atlasParam w)) (hrange _) t ht
    exact norm_binary_bound (mul_nonneg (mul_nonneg (by norm_num) hC)
      (add_nonneg zero_le_one (Real.rpow_nonneg hpw _)))
      (hh.2.1.trans (hdom hpw ht hle)) (hh.2.2.trans (hdom hpw ht hle)) hd hU
  apply q.closed_of_ae_domination Q f g hf hg b c hb hc
  · filter_upwards [hp] with x hx
    by_cases hx0 : 0 < q.inclusion P x
    · exact ((hgrowth (r x) (hrange x) _ hx0).1.trans
        (hdom hx hx0 (by nlinarith [Real.rpow_nonneg hx a]))).trans (le_abs_self _)
    · have he : q.inclusion P x = 0 := le_antisymm (le_of_not_gt hx0) hx
      simp only [f,he,hF0 _ (hrange x),norm_zero]
      exact norm_nonneg _
  · filter_upwards [hpa,hdr] with w hp hd
    dsimp [g]
    split_ifs with ht
    · exact (hbound hp ht (by nlinarith [Real.rpow_nonneg hp a]) hd le_rfl).trans (le_abs_self (c w))
    · simpa only [norm_zero] using (abs_nonneg (c w))
  · intro j
    filter_upwards [hp,hQ j] with x hx hq
    rw [hq,Real.norm_eq_abs]
    exact ((hgrowth (r x) (hrange x) _ (clamp_pos j _)).1.trans
      (hdom hx (clamp_pos j _) (clamp_power_bound hx ha j))).trans (le_abs_self _)
  · intro j
    filter_upwards [hpa,hdr,hG j] with w hp hd hg
    rw [hg]
    apply (hbound hp (clamp_pos j _) (clamp_power_bound hp ha j) hd ?_).trans (le_abs_self (c w))
    split_ifs
    · exact le_rfl
    · simp
  · filter_upwards [ae_all_iff.mpr hQ,hp] with x hx hp
    by_cases ht : 0 < q.inclusion P x
    · apply (tendsto_congr' ((cut_eventually ht).mono fun j hj => ?_)).mpr tendsto_const_nhds
      rw [hx j,min_eq_left hj.2.le,max_eq_left hj.1.le]
    · have he : q.inclusion P x = 0 := le_antisymm (le_of_not_gt ht) hp
      have hl : Tendsto lowerCut atTop (𝓝[>] (0:ℝ)) :=
        tendsto_nhdsWithin_iff.mpr ⟨lowerCut_tendsto,Eventually.of_forall lowerCut_pos⟩
      have hh := (hFcont (r x) (hrange x)).comp hl
      simpa only [f,he,hF0 _ (hrange x)] using
        (tendsto_congr (fun j => by rw [hx j,he,min_eq_left (show 0 ≤ upperCut j from (lowerCut_pos j).le.trans (lowerCut_lt_upperCut j).le),max_eq_right (lowerCut_pos j).le]; rfl)).mpr hh
  · filter_upwards [ae_all_iff.mpr hG,hpa] with w hw hp
    by_cases ht : 0 < q.inclusion P (q.atlasParam w)
    · apply (tendsto_congr' ((cut_eventually ht).mono fun j hj => ?_)).mpr tendsto_const_nhds
      rw [hw j,min_eq_left hj.2.le,max_eq_left hj.1.le,ite_eq_left hj]
      simp only [g,ite_eq_left ht]
    · have he : q.inclusion P (q.atlasParam w) = 0 := le_antisymm (le_of_not_gt ht) hp
      have hl : Tendsto lowerCut atTop (𝓝[>] (0:ℝ)) :=
        tendsto_nhdsWithin_iff.mpr ⟨lowerCut_tendsto,Eventually.of_forall lowerCut_pos⟩
      have hh := ((hDcont (r (q.atlasParam w)) (hrange _)).comp hl).smul_const (q.gradient hr w)
      simp only [zero_smul] at hh
      simp only [g,ite_eq_right ht]
      apply (tendsto_congr (fun j => ?_)).mpr hh
      rw [hw j,he,min_eq_left (show 0 ≤ upperCut j from (lowerCut_pos j).le.trans (lowerCut_lt_upperCut j).le),max_eq_right (lowerCut_pos j).le]
      simp only [not_lt.mpr (lowerCut_pos j).le,false_and,ite_false,smul_zero,add_zero]
      rfl
end CAT0Fillings.ChartGeometry
end

end OAI
