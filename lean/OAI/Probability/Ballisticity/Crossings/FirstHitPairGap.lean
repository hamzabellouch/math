import Mathlib
import OAI.Probability.Ballisticity.Estimates.CommonWidthProcess
import OAI.Probability.Ballisticity.Renewal.RenewalCountBounds

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma recordIndexTime_zero {d : ℕ} (ℓ : Vector d) (X : Path d) : recordIndexTime ℓ 0 X = 0 := by
  classical
  have hn : ¬ ∃ n, X ∈ RecordIndexPrefix ℓ 0 n := by
    rintro ⟨n,hn,hr,hc,_⟩
    have hh := recordCount_lt_of_strictRecord ℓ X hn hr
    simp only [recordCount_zero,hc,lt_self_iff_false] at hh
  simp only [recordIndexTime,dite_eq_right hn]

lemma recordCount_commonTimes_second {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep1 : ∀ n, height (P.1 (n+1)) ≤ height (P.1 n)+1)
    (hstep2 : ∀ n, height (P.2 (n+1)) ≤ height (P.2 n)+1) (n : ℕ) :
    recordCount ℓ P.2 (commonTimes ℓ P n).2 =
      renewalSum (fun j => commonWidthProcess ℓ j P) n := by
  have ht := commonTimes_true ℓ P h0 h0' hP n
  have h1 := recordCount_eq_height_at_record ℓ height hproj P.1 hstep1 ht.1.1
  have h2 := recordCount_eq_height_at_record ℓ height hproj P.2 hstep2 ht.2.1.1
  have he := ht.2.2
  rw [hproj,hproj] at he
  have he' : height (P.1 (commonTimes ℓ P n).1) = height (P.2 (commonTimes ℓ P n).2) := by
    exact_mod_cast he
  rw [h1,h2,h0,h0',add_right_inj] at he'
  have hc : recordCount ℓ P.1 (commonTimes ℓ P n).1 = recordCount ℓ P.2 (commonTimes ℓ P n).2 := by
    exact_mod_cast he'
  rw [← hc,recordCount_commonTimes ℓ P h0 h0' hP n]
  rfl

lemma recordTime_between {d : ℕ} (ℓ : Vector d) (X : Path d) {h j k n : ℕ}
    (hj : StrictRecord ℓ X j) (hn : X ∈ RecordIndexPrefix ℓ h n)
    (hl : recordCount ℓ X j ≤ h) (hu : h < recordCount ℓ X k) : j ≤ n ∧ n < k := by
  constructor
  · by_contra! hh
    have := recordCount_lt_of_strictRecord ℓ X hh hj
    rw [hn.2.2.1] at this
    omega
  · by_contra! hh
    have := recordCount_mono ℓ X hh
    rw [hn.2.2.1] at this
    omega

lemma coordinate_prefix_bound {d : ℕ} (e : Direction d) (X : Path d)
    (w : List (Direction d)) {j n : ℕ}
    (hw : ∀ k ≤ w.length, X (j+k)-X j = wordPath 0 w k)
    (hl : j ≤ n) (hu : n ≤ j+w.length) :
    |signedCoordinate e (X n)-signedCoordinate e (X j)| ≤ wordRadius w := by
  rw [← signedCoordinate_sub]
  have hk : n-j ≤ w.length := by omega
  have he := hw (n-j) hk
  rw [Nat.add_sub_of_le hl] at he
  rw [he]
  exact (signedCoordinate_abs_le_norm e _).trans (wordRadius_bound w hk)

lemma firstHit_common_boundary_error {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (P : Path d × Path d) (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep1 : ∀ n, height (P.1 (n+1)) ≤ height (P.1 n)+1)
    (hstep2 : ∀ n, height (P.2 (n+1)) ≤ height (P.2 n)+1)
    {h : ℕ} (hs1 : 0 < h → P.1 ∈ RecordIndexPrefix ℓ h (recordIndexTime ℓ h P.1))
    (hs2 : 0 < h → P.2 ∈ RecordIndexPrefix ℓ h (recordIndexTime ℓ h P.2)) :
    |(signedCoordinate e (recordIndexPosition ℓ h P.1)-
      signedCoordinate e (recordIndexPosition ℓ h P.2))-
      realPartialSum (fun j => commonIncrementProcess ℓ e j P)
        (renewalCount (fun j => commonWidthProcess ℓ j P) h)| ≤
      wordRadius (commonWords ℓ P (renewalCount (fun j => commonWidthProcess ℓ j P) h)).1 +
      wordRadius (commonWords ℓ P (renewalCount (fun j => commonWidthProcess ℓ j P) h)).2 := by
  by_cases hh : h = 0
  · subst h
    simpa only [recordIndexPosition,recordIndexTime_zero,h0,h0',sub_self,renewalCount_zero,
      realPartialSum_zero,abs_zero] using add_nonneg
        (wordRadius_nonneg (commonWords ℓ P 0).1) (wordRadius_nonneg (commonWords ℓ P 0).2)
  have hh' : 0 < h := Nat.pos_of_ne_zero hh
  let k := renewalCount (fun j => commonWidthProcess ℓ j P) h
  have hpos (j : ℕ) : 0 < commonWidthProcess ℓ j P := commonWordWidth_positive ℓ _ _ (hP j)
  have hlow := renewalCount_lower (fun j => commonWidthProcess ℓ j P) h
  have hupp := renewalCount_upper (fun j => commonWidthProcess ℓ j P) hpos h
  have hc1 (n : ℕ) : recordCount ℓ P.1 (commonTimes ℓ P n).1 =
      renewalSum (fun j => commonWidthProcess ℓ j P) n :=
    recordCount_commonTimes ℓ P h0 h0' hP n
  have hc2 := recordCount_commonTimes_second ℓ P h0 h0' hP height hproj hstep1 hstep2
  have ht := commonTimes_true ℓ P h0 h0' hP k
  have hb1 := recordTime_between ℓ P.1 ht.1.1 (hs1 hh')
    (by rw [hc1]; exact hlow) (k := (commonTimes ℓ P (k+1)).1) (by rw [hc1]; exact hupp)
  have hb2 := recordTime_between ℓ P.2 ht.2.1.1 (hs2 hh')
    (by rw [hc2]; exact hlow) (k := (commonTimes ℓ P (k+1)).2) (by rw [hc2]; exact hupp)
  have he := iterate_renewPairSuffix_eq ℓ P h0 h0' k
  have hw1 := (hP k).2.1.1
  have hw2 := (hP k).2.1.2
  rw [he] at hw1 hw2
  have herr1 := coordinate_prefix_bound e P.1 (commonWords ℓ P k).1 hw1 hb1.1
    (by rw [commonTimes_succ] at hb1; exact hb1.2.le)
  have herr2 := coordinate_prefix_bound e P.2 (commonWords ℓ P k).2 hw2 hb2.1
    (by rw [commonTimes_succ] at hb2; exact hb2.2.le)
  rw [← common_coordinate_sum ℓ e P h0 h0' hP k]
  change |(_-_)-(_-_)| ≤ _
  calc
    _ = |(signedCoordinate e (P.1 (recordIndexTime ℓ h P.1))-
        signedCoordinate e (P.1 (commonTimes ℓ P k).1))-
        (signedCoordinate e (P.2 (recordIndexTime ℓ h P.2))-
        signedCoordinate e (P.2 (commonTimes ℓ P k).2))| := by dsimp only [recordIndexPosition]; congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add herr1 herr2)

noncomputable def firstHitPairGap {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (h : ℕ) (P : Path d × Path d) : ℝ :=
  signedCoordinate e (recordIndexPosition ℓ h P.1)-
    signedCoordinate e (recordIndexPosition ℓ h P.2)

lemma measurable_firstHitPairGap {d : ℕ} (ℓ : Vector d) (e : Direction d) (h : ℕ) :
    Measurable (firstHitPairGap ℓ e h) :=
  ((measurable_of_countable (signedCoordinate e)).comp
    ((measurable_recordIndexPosition ℓ h).comp measurable_fst)).sub
    ((measurable_of_countable (signedCoordinate e)).comp
    ((measurable_recordIndexPosition ℓ h).comp measurable_snd))

lemma independent_firstHit_decoration_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ h : ℕ,
      |firstHitPairGap ℓ e h P-realPartialSum (fun j => commonIncrementProcess ℓ e j P)
        (renewalCount (fun j => commonWidthProcess ℓ j P) h)| ≤
      wordRadius (commonWords ℓ P (renewalCount (fun j => commonWidthProcess ℓ j P) h)).1 +
      wordRadius (commonWords ℓ P (renewalCount (fun j => commonWidthProcess ℓ j P) h)).2 := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  have hNN := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_nearest_neighbor ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_nearest_neighbor ν)))
  have hs : ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ h, 0 < h →
      X ∈ RecordIndexPrefix ℓ h (recordIndexTime ℓ h X) := by
    apply ae_all_iff.mpr
    intro h
    by_cases hh : 0 < h
    · exact (conditioned_recordIndexTime_spec ν ℓ htrans hh).mono (fun _ hX _ => hX)
    · exact Eventually.of_forall (fun _ hh' => (hh hh').elim)
  have hs' := (Measure.quasiMeasurePreserving_fst.ae hs).and (Measure.quasiMeasurePreserving_snd.ae hs)
  filter_upwards [h0,hNN,hs',independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep]
    with P h0 hNN hs' hP h
  apply firstHit_common_boundary_error ℓ e P h0.1 h0.2 hP height hproj _ _ (hs'.1 h) (hs'.2 h)
  · intro n
    obtain ⟨u,hu⟩ := hNN.1 n
    rw [hu]
    exact hstep _ _
  · intro n
    obtain ⟨u,hu⟩ := hNN.2 n
    rw [hu]
    exact hstep _ _

theorem independent_firstHit_decoration_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (h : ℕ → ℕ) :
    TendstoInMeasure (independentConditionedPairLaw ν ℓ) (fun i P =>
      (firstHitPairGap ℓ e (h i) P-realPartialSum (fun j => commonIncrementProcess ℓ e j P)
        (renewalCount (fun j => commonWidthProcess ℓ j P) (h i)))/r i) atTop 0 := by
  let μ := independentConditionedPairLaw ν ℓ
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let W := fun k P => commonWords ℓ P k
  let R := fun wv : List (Direction d) × List (Direction d) => wordRadius wv.1+wordRadius wv.2
  have hpos : ∀ᵐ P ∂μ, ∀ k, 0 < commonWordWidth ℓ (W k P) := by
    filter_upwards [independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep] with P hP k
    exact commonWordWidth_positive ℓ _ _ (hP k)
  have ht := renewal_selected_mark_small μ W
    (fun k => (measurable_firstPairWord ℓ).comp ((measurable_renewPairSuffix ℓ).iterate k))
    (common_words_independent ν ℓ htrans height hproj hstep)
    (common_words_identDistrib ν ℓ htrans height hproj hstep)
    (commonWordWidth ℓ) (measurable_of_countable _) hpos
    (independent_commonWordWidth_integrable ν ℓ htrans height hproj hstep).1
    R (measurable_of_countable _) r hr h
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have ht' := tendstoInMeasure_iff_measureReal_norm.mp ht ε hε
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at ht' ⊢
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ ht'
  apply Eventually.of_forall
  intro i
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae _)
  filter_upwards [independent_firstHit_decoration_bound ν ℓ e htrans height hproj hstep] with P hP ha
  refine ha.trans ?_
  rw [abs_div,abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact (hP (h i)).trans (le_abs_self _)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
