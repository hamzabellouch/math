import OAI.Analysis.SignedDisk.DiskScales2

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace DiskScales

def directionTailConstant (Cs κ : ℝ) : ℝ := (1+errorGapConstant Cs/κ)*sizeTailConstant

lemma directionTailConstant_pos {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    0 < directionTailConstant Cs κ := by
  unfold directionTailConstant
  have hh := errorGapConstant_pos hCs
  exact mul_pos (by positivity) sizeTailConstant_pos

end DiskScales

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales

/-- A genuine superlevel bound with exponent 34/25 > 1 for all neighborhood
maxima, independent of the number of positive or cancelling pieces. -/
theorem direction_tail {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {ι : Type*} [Fintype ι] {e : ℂ} (a : ConeDensity e κ)
      (b : ι → ErrorPiece Cs), ‖e‖ = 1 →
      0 < errorPrice b (1/100) → ∀ t : ℝ, L*errorPrice b (1/100) ≤ t →
      ∀ g : ℂ → ℝ, ContDiff ℝ 1 g →
      ∃ E : Set ℂ, MeasurableSet E ∧
        volume E ≤ ENNReal.ofReal (directionTailConstant Cs κ*(errorPrice b (1/100)/t)^(34/25 : ℝ)) ∧
        ∀ x ∉ E,
          (∀ᵐ y, y ∈ Metric.ball x 3 → a.density y+∑ j, (b j).density y = gradient g y) →
          ∀ r, NeighborhoodRadius g x r →
            max 0 (-inner ℝ e (∫ y in Metric.ball x r, gradient g y)) ≤ t := by
  obtain ⟨d₀,hd0,hdq,hgeom,hsmall⟩ := exists_direction_parameters Cs κ
  have hL : 1 ≤ (1 : ℝ)/d₀ := (le_div_iff₀ hd0).mpr (by linarith)
  refine ⟨1/d₀,hL,?_⟩
  intro ι _ e a b he hA t ht g hg
  let A := errorPrice b (1/100)
  let H := errorGapConstant Cs/κ
  have hH : 0 ≤ H := div_nonneg (errorGapConstant_pos hCs).le hκ.le
  have hH1 : 0 ≤ 1+H := by linarith
  have hAt : A ≤ t := (le_mul_of_one_le_left hA.le hL).trans ht
  have ht0 : 0 < t := lt_of_lt_of_le hA hAt
  have hqd : A/t ≤ d₀ := by
    apply (div_le_iff₀ ht0).mpr
    have hh : A/d₀ ≤ t := by simpa only [A,one_div, div_eq_mul_inv, mul_comm, mul_one] using ht
    have hh' := (div_le_iff₀ hd0).mp hh
    linarith
  have hq0 : 0 < A/t := div_pos hA ht0
  have hq1 : A/t ≤ 1 := by linarith
  have hqq : A/t ≤ 1/4 := hqd.trans hdq
  obtain ⟨E,hE,hEv,hEst⟩ := direction_raw a b he hκ hCs hq0 hqq
    (fun δ hδ hδq => hgeom δ hδ (hδq.trans hqd)) ht0 hAt hg
  refine ⟨E,hE,?_,?_⟩
  · apply hEv.trans
    calc
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (1+H)*ENNReal.ofReal
          (156*(A/t)^2*(width (A/t) n)^(14/25 : ℝ)+
            2424*Real.pi*(A/t)*(width (A/t) n)^(9/25 : ℝ)) := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [← ENNReal.ofReal_mul hH1]
        apply direction_shell_tail_scaled hA.le ht0 (width_pos hq0 n)
          ((width_le hq0.le n).trans hq1) (coarseMass_nonneg b _ _) hH
        have hw0 := width_pos hq0 n
        have hh := coarseMass_bound b (by norm_num : (0 : ℝ) ≤ 1/100) hw0
        norm_num at hh
        rw [Real.rpow_neg hw0.le]
        exact hh
      _ = ENNReal.ofReal (1+H)*ENNReal.ofReal
          ((156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*(A/t)^(64/25 : ℝ)+
            (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*(A/t)^(34/25 : ℝ)) := by
        rw [ENNReal.tsum_mul_left,geometric_tail_sum hA.le ht0 hq0.le, starting_width_tail hA ht0]
      _ ≤ ENNReal.ofReal (1+H)*ENNReal.ofReal (sizeTailConstant*(A/t)^(34/25 : ℝ)) := by
        gcongr
        exact collapse_size_tail hq0 hq1
      _ = _ := by rw [← ENNReal.ofReal_mul hH1]; congr 1; dsimp only [directionTailConstant,H,A]; ring
  · intro x hx hh r hr
    apply (hEst x hx hh r hr).trans
    rw [direction_start_identity hA ht0]
    exact (mul_le_mul_of_nonneg_left (hsmall _ hq0 hqd) ht0.le).trans_eq (mul_one t)

lemma cone_ball_nonneg {e : ℂ} {κ : ℝ} (a : ConeDensity e κ) (hκ : 0 ≤ κ) (x : ℂ) (r : ℝ) :
    0 ≤ inner ℝ e (∫ y in Metric.ball x r, a.density y) := by
  rw [← integral_inner a.integrable.integrableOn e]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_of_ae a.cone] with y hy
  exact (mul_nonneg hκ (norm_nonneg _)).trans hy

/-- Full Borel integrable directional price. This is the hard local
cancellation estimate, not an assumed maximal-operator endpoint. -/
theorem direction_majorant {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {e : ℂ} (a : ConeDensity e κ)
      (b : ι → ErrorPiece Cs), ‖e‖ = 1 →
      ∀ g : ℂ → ℝ, ContDiff ℝ 1 g → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
      ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
        (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
        ∀ x, (∀ᵐ y, y ∈ Metric.ball x 3 → a.density y+∑ j, (b j).density y = gradient g y) →
          ∀ r, NeighborhoodRadius g x r →
            ENNReal.ofReal (max 0 (-inner ℝ e (∫ y in Metric.ball x r, gradient g y))) ≤ F x := by
  obtain ⟨L,hL,hdir⟩ := direction_tail hCs hκ
  let c : ℝ := (1/2 : ℝ)^(34/25 : ℝ)
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hc1 : 2*c < 1 := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 34/25)
    norm_num at hh
    linarith
  let C := L*(1+2*directionTailConstant Cs κ/(1-2*c))
  have hD := directionTailConstant_pos hCs hκ
  have hC : 0 < C := mul_pos (by linarith) (by
    have := sub_pos.mpr hc1
    positivity)
  refine ⟨C,hC,?_⟩
  intro ι _ e a b he g hg Q hQ
  let A := errorPrice b (1/100)
  by_cases hAz : A = 0
  · refine ⟨0,measurable_const,?_,?_⟩
    · simp only [Pi.zero_apply, lintegral_zero, A, hAz, mul_zero, ENNReal.ofReal_zero, le_refl]
    · intro x hh r hr
      have hz := errorPrice_zero b hAz
      have hs : (∑ j, ∫ y in Metric.ball x r, (b j).density y) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact integral_eq_zero_of_ae (ae_restrict_of_ae (hz j))
      have hb := mixed_ball_pairing_decomposition b a.integrable x (by linarith [hr.1.2] : r ≤ 3) hh
      rw [← hb,hs,add_zero,max_eq_left (neg_nonpos.mpr (cone_ball_nonneg a hκ.le x r)),ENNReal.ofReal_zero]
      exact le_refl _
  · have hA : 0 < A := lt_of_le_of_ne (errorPrice_nonneg b _) (Ne.symm hAz)
    have ht : 0 < L*A := mul_pos (by linarith) hA
    have hts (n : ℕ) : L*A ≤ L*A*2^n := le_mul_of_one_le_right ht.le (one_le_pow₀ (by norm_num))
    choose E hE hEv hbound using fun n : ℕ => hdir a b he hA (L*A*2^n) (hts n) g hg
    refine ⟨DyadicMajorant.price (L*A) E, DyadicMajorant.measurable_price _ hE,?_,?_⟩
    · have htail (n : ℕ) : volume (E n) ≤ ENNReal.ofReal (directionTailConstant Cs κ*c^n) := by
        apply (hEv n).trans
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ hD.le
        calc
          _ ≤ ((1/2 : ℝ)^n)^(34/25 : ℝ) := Real.rpow_le_rpow (by positivity) (dyadic_ratio hA hL n) (by norm_num)
          _ = c^n := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (n : ℝ),
              Real.rpow_mul (by norm_num), Real.rpow_natCast]
      have hi := DyadicMajorant.lintegral_price_geometric volume (by norm_num : (0 : ℝ) ≤ 1) hQ ht.le
        hD.le hc hc1 hE htail
      convert hi using 1
      congr 1
      dsimp [C,A]
      ring
    · intro x hh r hr
      apply DyadicMajorant.majorizes ht
      intro n hn
      exact hbound n x hn hh r hr

end LocalCancellation

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace DiskMaximalTools

lemma volume_dilate_five (x : ℂ) (r : ℝ) :
    volume (ball x (5*r)) = 25 * volume (ball x r) := by
  rw [Complex.volume_ball, Complex.volume_ball, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]
  norm_num [mul_pow]
  ring

/-- The actual Vitali weak-(1,1) estimate, with no assumed maximal inequality. -/
theorem weak_bound_bounded_family {ι : Type*} (t : Set ι) (x : ι → ℂ) (r : ι → ℝ)
    (ν : Measure ℂ) {R a : ℝ} (ha : 0 < a)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R)
    (hav : ∀ i ∈ t, ENNReal.ofReal a * volume (ball (x i) (r i)) ≤ ν (ball (x i) (r i))) :
    volume (⋃ i ∈ t, ball (x i) (r i)) ≤ (25 / ENNReal.ofReal a) * ν univ := by
  obtain ⟨u,hut,hdisj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    t x r R hR 5 (by norm_num)
  have huc : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun i hi => ⟨x i,mem_ball_self (hr i (hut hi))⟩)
  have : Countable u := huc.to_subtype
  have hsub : (⋃ i ∈ t, ball (x i) (r i)) ⊆ ⋃ i : u, ball (x i) (5*r i) := by
    intro y hy
    obtain ⟨i,hi,hy⟩ := mem_iUnion₂.mp hy
    obtain ⟨j,hj,hij⟩ := hcover i hi
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,hij hy⟩
  have hmass : (∑' i : u, ν (ball (x i) (r i))) ≤ ν univ := by
    rw [← measure_iUnion (fun (i j : u) hij => hdisj i.property j.property (fun h => hij (Subtype.ext h)))
      (fun _ => measurableSet_ball)]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ volume (⋃ i : u, ball (x i) (5*r i)) := measure_mono hsub
    _ ≤ ∑' i : u, volume (ball (x i) (5*r i)) := measure_iUnion_le _
    _ = ∑' i : u, 25 * volume (ball (x i) (r i)) := by simp_rw [volume_dilate_five]
    _ ≤ ∑' i : u, (25 / ENNReal.ofReal a) * ν (ball (x i) (r i)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      have hb := hav i (hut i.property)
      calc
        _ = (25 / ENNReal.ofReal a) * (ENNReal.ofReal a * volume (ball (x i) (r i))) := by
          rw [← mul_assoc, ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top]
        _ ≤ _ := by gcongr
    _ = (25 / ENNReal.ofReal a) * ∑' i : u, ν (ball (x i) (r i)) := by rw [ENNReal.tsum_mul_left]
    _ ≤ _ := by gcongr

lemma volume_disk_real (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball x r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [Complex.volume_ball,ENNReal.ofReal_mul Real.pi_nonneg,ENNReal.ofReal_pow hr]
  rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (NNReal.pi : ℝ) = (NNReal.pi : ℝ≥0∞))]
  exact mul_comm _ _

/-- All high-average balls of a finite measure have a common finite radius
bound; the bounded-family Vitali argument therefore controls every radius. -/
theorem weak_bound {ν : Measure ℂ} [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a) :
    volume {x : ℂ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal a * volume (ball x r) ≤ ν (ball x r)} ≤
      (25 / ENNReal.ofReal a) * ν univ := by
  let t : Set (ℂ × ℝ) := {p | 0 < p.2 ∧
    ENNReal.ofReal a * volume (ball p.1 p.2) ≤ ν (ball p.1 p.2)}
  let B : ℝ := (ν univ).toReal/(a*Real.pi)
  have hB : 0 ≤ B := div_nonneg ENNReal.toReal_nonneg (mul_pos ha Real.pi_pos).le
  have hR : ∀ p ∈ t, p.2 ≤ B+1 := by
    intro p hp
    have hh := hp.2.trans (measure_mono (subset_univ _))
    rw [volume_disk_real _ hp.1.le,← ENNReal.ofReal_mul ha.le] at hh
    have hh' : a*(Real.pi*p.2^2) ≤ (ν univ).toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hh
    have hs : p.2^2 ≤ B := (le_div_iff₀ (mul_pos ha Real.pi_pos)).mpr (by nlinarith)
    nlinarith [sq_nonneg (p.2-1)]
  have hweak := weak_bound_bounded_family t Prod.fst Prod.snd ν ha
    (fun _ hp => hp.1) hR (fun _ hp => hp.2)
  apply le_trans (measure_mono ?_) hweak
  intro x hx
  obtain ⟨r,hr,havg⟩ := hx
  exact mem_iUnion₂.mpr ⟨(x,r),⟨hr,havg⟩,mem_ball_self hr⟩

/-- A countable measurable envelope, sufficiently rich for every actual disk. -/
def rationalMaximal (ν : Measure ℂ) (x : ℂ) : ℝ≥0∞ :=
  ⨆ (q : ℚ) (_ : 0 < q), ν (ball x q) / volume (ball x q)

lemma measurable_ball_mass (ν : Measure ℂ) [SFinite ν] (r : ℝ) :
    Measurable (fun x : ℂ => ν (ball x r)) := by
  have hm : MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 < r} :=
    isOpen_lt (continuous_snd.dist continuous_fst) continuous_const |>.measurableSet
  exact measurable_measure_prodMk_left hm

lemma measurable_rationalMaximal (ν : Measure ℂ) [SFinite ν] :
    Measurable (rationalMaximal ν) := by
  unfold rationalMaximal
  apply Measurable.iSup
  intro q
  apply Measurable.iSup
  intro _
  have hd : Measurable (fun x : ℂ => volume (ball x (q:ℝ))) := by
    simp only [Complex.volume_ball]
    exact measurable_const
  exact (measurable_ball_mass ν (q:ℝ)).div hd

lemma weak_rationalMaximal {ν : Measure ℂ} [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < rationalMaximal ν x} ≤
      (25 / ENNReal.ofReal a) * ν univ := by
  apply le_trans (measure_mono ?_) (weak_bound ha)
  intro x hx
  change ENNReal.ofReal a < ⨆ (q : ℚ) (_ : 0 < q), ν (ball x q) / volume (ball x q) at hx
  obtain ⟨q,hh⟩ := lt_iSup_iff.mp hx
  obtain ⟨hq,hh⟩ := lt_iSup_iff.mp hh
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  refine ⟨q,hq',?_⟩
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  exact ((ENNReal.lt_div_iff_mul_lt (Or.inl hv0) (Or.inl measure_ball_lt_top.ne)).mp hh).le

lemma disk_average_le_rationalMaximal (ν : Measure ℂ) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ν (ball x r) / volume (ball x r) ≤ 4*rationalMaximal ν x := by
  obtain ⟨q,hqr,hrq⟩ := exists_rat_btwn (show r < 2*r by linarith)
  have hq : (0 : ℝ) < q := hr.trans hqr
  have hqRat : (0:ℚ) < q := by exact_mod_cast hq
  have hd : volume (ball x (q:ℝ)) ≤ 4*volume (ball x r) := by
    rw [volume_disk_real _ hq.le,volume_disk_real _ hr.le,
      ← show ENNReal.ofReal (4:ℝ) = 4 by norm_num,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    apply ENNReal.ofReal_le_ofReal
    have hs : (q:ℝ)^2 ≤ 4*r^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs Real.pi_nonneg]
  have hv0 : volume (ball x r) ≠ 0 := by
    rw [volume_disk_real _ hr.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hr)))
  have hvq0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq)))
  have hav : ν (ball x (q:ℝ)) / volume (ball x (q:ℝ)) ≤ rationalMaximal ν x :=
    le_iSup_of_le q (le_iSup_of_le hqRat le_rfl)
  have hnum : ν (ball x r) ≤ rationalMaximal ν x * (4*volume (ball x r)) := by
    calc
      _ ≤ ν (ball x (q:ℝ)) := measure_mono (ball_subset_ball hqr.le)
      _ ≤ rationalMaximal ν x * volume (ball x (q:ℝ)) :=
        (ENNReal.div_le_iff hvq0 measure_ball_lt_top.ne).mp hav
      _ ≤ _ := by gcongr
  apply (ENNReal.div_le_iff hv0 measure_ball_lt_top.ne).mpr
  convert hnum using 1
  ring

/-- Truncating an input below half the testing height sharpens weak type by
charging only its large values. This is the interpolation mechanism. -/
lemma weak_split {ν η : Measure ℂ} [IsFiniteMeasure η] {a : ℝ} (ha : 0 < a)
    (hsplit : ∀ x r, 0 < r → ν (ball x r) ≤ η (ball x r)+
      ENNReal.ofReal (a/2)*volume (ball x r)) :
    volume {x | ENNReal.ofReal a < rationalMaximal ν x} ≤
      (25 / ENNReal.ofReal (a/2)) * η univ := by
  apply le_trans (measure_mono ?_) (weak_bound (by linarith : 0 < a/2))
  intro x hx
  change ENNReal.ofReal a < ⨆ (q : ℚ) (_ : 0 < q), ν (ball x q) / volume (ball x q) at hx
  obtain ⟨q,hh⟩ := lt_iSup_iff.mp hx
  obtain ⟨hq,hh⟩ := lt_iSup_iff.mp hh
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  have hh' := (ENNReal.lt_div_iff_mul_lt (Or.inl hv0) (Or.inl measure_ball_lt_top.ne)).mp hh
  refine ⟨q,hq',?_⟩
  by_contra h
  have hη : η (ball x (q:ℝ)) ≤ ENNReal.ofReal (a/2)*volume (ball x (q:ℝ)) := (lt_of_not_ge h).le
  have hfull := (hsplit x q hq').trans (add_le_add hη le_rfl)
  have hsum : ENNReal.ofReal (a/2)+ENNReal.ofReal (a/2) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_add (by linarith : 0 ≤ a/2) (by linarith : 0 ≤ a/2)]
    congr 1
    ring
  rw [← add_mul,hsum] at hfull
  exact (not_lt_of_ge hfull) hh'

lemma weak_truncated {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    [IsFiniteMeasure (volume.withDensity f)] {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < rationalMaximal (volume.withDensity f) x} ≤
      (25 / ENNReal.ofReal (a/2)) *
        ∫⁻ x, {x | ENNReal.ofReal (a/2) < f x}.indicator f x := by
  let H := {x | ENNReal.ofReal (a/2) < f x}
  let η := volume.withDensity (H.indicator f)
  have hle : η ≤ volume.withDensity f := withDensity_mono (ae_of_all _ (indicator_le_self _ _))
  have : IsFiniteMeasure η := isFiniteMeasure_of_le _ hle
  have hweak := weak_split (ν := volume.withDensity f) (η := η) ha ?_
  · simpa only [η,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ] using hweak
  · intro x r _
    rw [withDensity_apply _ measurableSet_ball,show η = volume.withDensity (H.indicator f) from rfl,
      withDensity_apply _ measurableSet_ball]
    calc
      _ ≤ ∫⁻ y in ball x r, H.indicator f y+ENNReal.ofReal (a/2) := by
        apply lintegral_mono
        intro y
        dsimp only
        by_cases hy : y ∈ H
        · rw [indicator_of_mem hy]
          exact le_add_right le_rfl
        · rw [indicator_of_notMem hy,zero_add]
          exact le_of_not_gt hy
      _ = _ := by
        rw [lintegral_add_left (hf.indicator (measurableSet_lt measurable_const hf))]
        simp only [lintegral_const,Measure.restrict_apply_univ]
        rfl

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DiskMaximalTools

lemma lintegral_rpow_Ioo {b s : ℝ} (hb : 0 ≤ b) (hs : -1 < s) :
    (∫⁻ t in Ioo 0 b, ENNReal.ofReal (t^s)) = ENNReal.ofReal (b^(s+1)/(s+1)) := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp [Real.zero_rpow (by linarith : s+1 ≠ 0)]
  · have hi : IntegrableOn (fun t : ℝ => t^s) (Ioo 0 b) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mpr hs
    rw [← ofReal_integral_eq_lintegral_ofReal hi]
    · rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hb.le,
        integral_rpow (Or.inl hs)]
      simp [Real.zero_rpow (by linarith : s+1 ≠ 0)]
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
      exact Real.rpow_nonneg ht.1.le _

lemma truncation_layer_single {b p : ℝ} (hb : 0 ≤ b) (hp : 1 < p) :
    (∫⁻ t in Ioi 0, (if t < 2*b then ENNReal.ofReal b else 0)*ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal (2^(p-1)/(p-1))*ENNReal.ofReal (b^p) := by
  have heq : (fun t : ℝ => (if t < 2*b then ENNReal.ofReal b else 0)*ENNReal.ofReal (t^(p-2))) =
      (Iio (2*b)).indicator (fun t => ENNReal.ofReal b * ENNReal.ofReal (t^(p-2))) := by
    funext t
    by_cases ht : t < 2*b <;> simp [ht]
  rw [heq,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hi : Iio (2*b) ∩ Ioi (0:ℝ) = Ioo 0 (2*b) := by ext t; simp [and_comm]
  rw [hi,lintegral_const_mul'' _ (by fun_prop)]
  rw [lintegral_rpow_Ioo (by positivity : 0 ≤ 2*b) (by linarith : -1 < p-2)]
  have hpp : p-2+1 = p-1 := by ring
  rw [hpp]
  have h2 : 0 ≤ (2:ℝ)^(p-1)/(p-1) := div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
  rw [← ENNReal.ofReal_mul hb,← ENNReal.ofReal_mul h2]
  congr 1
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hb]
  have hp0 : 0 < p-1 := by linarith
  have hpow : b*b^(p-1) = b^p := by
    rcases eq_or_lt_of_le hb with rfl | hb
    · simp [Real.zero_rpow hp0.ne',Real.zero_rpow (by linarith : p ≠ 0)]
    · calc
        b*b^(p-1) = b^(1:ℝ)*b^(p-1) := by rw [Real.rpow_one]
        _ = b^(1+(p-1)) := (Real.rpow_add hb _ _).symm
        _ = b^p := by congr 1; ring
  calc
    b * (2^(p-1)*b^(p-1)/(p-1)) = (2^(p-1)/(p-1))*(b*b^(p-1)) := by ring
    _ = _ := by rw [hpow]

/-- Exact Tonelli computation behind strong maximal interpolation, for every
p > 1. The singularity at testing height zero is actually integrated. -/
theorem truncation_layer_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) :
    (∫⁻ t in Ioi 0,
      (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0 ∂μ)*ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal (2^(p-1)/(p-1))*(∫⁻ x, ENNReal.ofReal ((f x)^p) ∂μ) := by
  have hm : Measurable (fun z : ℝ × α =>
      (if z.1 < 2*f z.2 then ENNReal.ofReal (f z.2) else 0)*ENNReal.ofReal (z.1^(p-2))) := by
    apply Measurable.mul
    · exact ((hf.comp measurable_snd).ennreal_ofReal).ite
        (measurableSet_lt measurable_fst ((hf.comp measurable_snd).const_mul 2)) measurable_const
    · exact (measurable_fst.pow_const _).ennreal_ofReal
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x,
        (if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2)) ∂μ := by
      apply lintegral_congr
      intro t
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ x, (∫⁻ t in Ioi 0,
        (if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal (2^(p-1)/(p-1))*ENNReal.ofReal ((f x)^p) ∂μ := by
      apply lintegral_congr
      intro x
      exact truncation_layer_single (hf0 x) hp
    _ = _ := lintegral_const_mul'' _ ((hf.pow_const _).ennreal_ofReal.aemeasurable)

end DiskMaximalTools

end SignedDisk

end

end OAI
