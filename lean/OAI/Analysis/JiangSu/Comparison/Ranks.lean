import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzRankMonotone
import OAI.Analysis.JiangSu.CStarAlgebras.CutoffRank
import OAI.Analysis.JiangSu.Comparison.CompactComparison
import OAI.Analysis.JiangSu.TraceCone.CuntzIdentities
import OAI.Analysis.JiangSu.Comparison.CuntzBasic

namespace OAI

noncomputable section

namespace DirectComparison
open Pureness
open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def directCutoff (η : ℝ) (h : A) : A := cfc (fun t : ℝ => min (t/η) 1) h

def directPositiveCut (η : ℝ) (h : A) : A := cfc (fun t : ℝ => max (t-η) 0) h

lemma directPositiveCut_nonneg (η : ℝ) (h : A) : 0 ≤ directPositiveCut η h := by
  exact cfc_nonneg (fun t _ => le_max_right _ _)

omit [PartialOrder A] [StarOrderedRing A] in
lemma directCutoff_fixes_cut (η : ℝ) (hη : 0 < η) (h : A) :
    directCutoff η h * directPositiveCut η h = directPositiveCut η h := by
  have hf : Continuous (fun t : ℝ => min (t/η) 1) :=
    (continuous_id.div_const η).min continuous_const
  have hg : Continuous (fun t : ℝ => max (t-η) 0) :=
    (continuous_id.sub continuous_const).max continuous_const
  change cfc _ h*cfc _ h = cfc _ h
  rw [←cfc_mul _ _ h hf.continuousOn hg.continuousOn]
  apply cfc_congr
  intro t _
  change min (t/η) 1 * max (t-η) 0 = max (t-η) 0
  by_cases ht : t ≤ η
  · simp only [max_eq_right (sub_nonpos.mpr ht),mul_zero]
  · rw [min_eq_right ((le_div_iff₀ hη).mpr (by linarith)),one_mul]

lemma hereditary_fixed_by_cutoff {b k : A} (hb : 0 ≤ b) (hk : IsSelfAdjoint k)
    (hkb : k*b=b) {p : A} (hp : p ∈ hereditaryCarrier b) :
    k*p=p ∧ p*k=p := by
  have hbk : b*k=b := by
    have he := congrArg star hkb
    simpa only [star_mul,hb.isSelfAdjoint.star_eq,hk.star_eq] using he
  have hclosed : IsClosed {z : A | k*z=z ∧ z*k=z} :=
    (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
      (isClosed_eq (continuous_id.mul continuous_const) continuous_id)
  apply (closure_minimal ?_ hclosed) hp
  rintro z ⟨w,rfl⟩
  constructor
  · simp only [←mul_assoc,hkb]
  · simp only [mul_assoc,hbk]

theorem directCutoff_fixes_hereditary (η : ℝ) (hη : 0 < η) (h : A)
    {p : A} (hp : p ∈ hereditaryCarrier (directPositiveCut η h)) :
    directCutoff η h*p=p ∧ p*directCutoff η h=p := by
  apply hereditary_fixed_by_cutoff (directPositiveCut_nonneg η h)
    (cfc_predicate _ h) (directCutoff_fixes_cut η hη h) hp

end DirectComparison

namespace DirectComparison
open Pureness Filter
open scoped Topology ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_sub_directPositiveCut_le (a : A) (ha : 0 ≤ a) (η : ℝ) (hη : 0 ≤ η) :
    ‖a-directPositiveCut η a‖ ≤ η := by
  have he : a-directPositiveCut η a = cfc (fun t : ℝ => t-max (t-η) 0) a := by
    rw [cfc_sub _ _ a (by fun_prop) (by fun_prop),cfc_id' ℝ a ha.isSelfAdjoint]
    rfl
  rw [he]
  apply norm_cfc_le hη
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg ha ht
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hm : max (t-η) 0 ≤ t := max_le (by linarith) ht0
    linarith
  · have hm := le_max_left (t-η) 0
    linarith

lemma directPositiveCut_tendsto (a : A) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => directPositiveCut (1 / ((n : ℝ)+1)) a) atTop (𝓝 a) := by
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro n
  rw [norm_sub_rev]
  exact norm_sub_directPositiveCut_le a ha _ (by positivity)

theorem rank_le_iSup_directPositiveCut (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    normalizedRootRank τ a ≤
      ⨆ n : ℕ, normalizedRootRank τ (directPositiveCut (1 / ((n : ℝ)+1)) a) := by
  exact rank_le_of_tendsto τ (fun n => directPositiveCut_nonneg _ _) ha
    (directPositiveCut_tendsto a ha) (fun n => le_iSup (fun k : ℕ => normalizedRootRank τ
      (directPositiveCut (1 / ((k : ℝ)+1)) a)) n)

lemma directPositiveCut_mem_hereditary (a : A) (ha : 0 ≤ a)
    (η : ℝ) (hη : 0 ≤ η) : directPositiveCut η a ∈ hereditaryCarrier a := by
  have hf0 : (fun t : ℝ => max (t-η) 0) 0 = 0 := by simp [hη]
  change cfc (fun t : ℝ => max (t-η) 0) a ∈ hereditarySubalgebra a ha
  rw [←cfcₙ_eq_cfc (f := fun t : ℝ => max (t-η) 0) (hf0 := hf0)]
  exact cfcₙ_mem _ (self_mem_hereditary a ha)

lemma rank_directPositiveCut_le (τ : TracialState A) (a : A) (ha : 0 ≤ a)
    (η : ℝ) (hη : 0 ≤ η) :
    normalizedRootRank τ (directPositiveCut η a) ≤ normalizedRootRank τ a :=
  hereditary_rank_domination τ a _ ha (directPositiveCut_nonneg _ _)
    (directPositiveCut_mem_hereditary a ha η hη)

lemma directPositiveCut_shift (a : A) (ha : 0 ≤ a) (δ η : ℝ) (hδη : δ ≤ η) :
    directPositiveCut η a = directPositiveCut (η-δ) (directPositiveCut δ a) := by
  unfold directPositiveCut
  rw [←cfc_comp _ _ a ha.isSelfAdjoint]
  apply cfc_congr
  intro t _
  change max (t-η) 0 = max (max (t-δ) 0-(η-δ)) 0
  by_cases ht : t ≤ δ
  · rw [max_eq_right (show t-η ≤ 0 by linarith),
      max_eq_right (show t-δ ≤ 0 by linarith),
      max_eq_right (show (0 : ℝ)-(η-δ) ≤ 0 by linarith)]
  · rw [max_eq_left (by linarith : 0 ≤ t-δ)]
    congr 1
    ring

lemma rank_directPositiveCut_antitone (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    Antitone (fun η : ℝ => normalizedRootRank τ (directPositiveCut η a)) := by
  intro δ η hδη
  change normalizedRootRank τ (directPositiveCut η a) ≤ normalizedRootRank τ (directPositiveCut δ a)
  rw [directPositiveCut_shift a ha δ η hδη]
  exact rank_directPositiveCut_le τ _ (directPositiveCut_nonneg _ _) _ (sub_nonneg.mpr hδη)

theorem rank_eq_iSup_directPositiveCut (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    normalizedRootRank τ a =
      ⨆ n : ℕ, normalizedRootRank τ (directPositiveCut (1 / ((n : ℝ)+1)) a) := by
  apply le_antisymm (rank_le_iSup_directPositiveCut τ a ha)
  apply iSup_le
  intro n
  exact rank_directPositiveCut_le τ a ha _ (by positivity)

end DirectComparison

namespace DirectComparison
open Pureness
open scoped ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma directRank_ne_top (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    normalizedRootRank τ a ≠ ∞ :=
  ne_of_lt ((normalizedRootRank_le_one τ a ha).trans_lt ENNReal.one_lt_top)

lemma direct_isOpen_lt_rank (a : A) (F : TracialState A → ℝ≥0∞) (hF : Continuous F) :
    IsOpen {τ : TracialState A | F τ < normalizedRootRank τ a} := by
  have hopen : IsOpen (⋃ n : ℕ, {τ : TracialState A |
      F τ < ENNReal.ofReal (τ.functional (normalizedRoot a n)).re}) :=
    isOpen_iUnion fun n => isOpen_lt hF (ENNReal.continuous_ofReal.comp
      (Complex.continuous_re.comp (TracialState.continuous_eval (normalizedRoot a n))))
  convert hopen using 2
  ext τ
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, normalizedRootRank, lt_iSup_iff]

lemma direct_isOpen_lt_realRank (a : A) (ha : 0 ≤ a)
    (F : TracialState A → ℝ) (hF : Continuous F) :
    IsOpen {τ : TracialState A | F τ < (normalizedRootRank τ a).toReal} := by
  have he : {τ : TracialState A | F τ < (normalizedRootRank τ a).toReal} =
      {τ | F τ < 0} ∪ {τ | ENNReal.ofReal (F τ) < normalizedRootRank τ a} := by
    ext τ
    simp only [Set.mem_ofPred_eq,Set.mem_union]
    by_cases h : F τ < 0
    · exact ⟨fun _ => Or.inl h,fun _ => h.trans_le ENNReal.toReal_nonneg⟩
    · simp only [h,false_or]
      exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt h) (directRank_ne_top τ a ha)).symm
  rw [he]
  exact (isOpen_lt hF continuous_const).union
    (direct_isOpen_lt_rank a _ (ENNReal.continuous_ofReal.comp hF))

theorem uniform_direct_positive_cut (a : A) (ha : 0 ≤ a)
    (F : TracialState A → ℝ) (hF : Continuous F)
    (hgap : ∀ τ, F τ < (normalizedRootRank τ a).toReal) :
    ∃ η : ℝ, 0 < η ∧ ∀ τ : TracialState A,
      F τ < (normalizedRootRank τ (directPositiveCut η a)).toReal := by
  let U : ℕ → Set (TracialState A) := fun n =>
    {τ | F τ < (normalizedRootRank τ (directPositiveCut (1/((n : ℝ)+1)) a)).toReal}
  have hopen : ∀ n, IsOpen (U n) := fun n =>
    direct_isOpen_lt_realRank _ (directPositiveCut_nonneg _ _) F hF
  have hmono : Monotone U := by
    intro n m hnm τ hτ
    change F τ < (normalizedRootRank τ (directPositiveCut (1/((n : ℝ)+1)) a)).toReal at hτ
    change F τ < (normalizedRootRank τ (directPositiveCut (1/((m : ℝ)+1)) a)).toReal
    apply lt_of_lt_of_le hτ
    apply ENNReal.toReal_mono (directRank_ne_top τ _ (directPositiveCut_nonneg _ _))
    apply rank_directPositiveCut_antitone τ a ha
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hcover : ∀ τ, ∃ n, τ ∈ U n := by
    intro τ
    by_cases hneg : F τ < 0
    · exact ⟨0,hneg.trans_le ENNReal.toReal_nonneg⟩
    have h := (ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt hneg)
      (directRank_ne_top τ a ha)).mpr (hgap τ)
    rw [rank_eq_iSup_directPositiveCut τ a ha] at h
    obtain ⟨n,hn⟩ := lt_iSup_iff.mp h
    exact ⟨n,(ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt hneg)
      (directRank_ne_top τ _ (directPositiveCut_nonneg _ _))).mp hn⟩
  obtain ⟨n,hn⟩ := uniform_index_of_increasing_open_cover U hopen hmono hcover
  exact ⟨1/((n : ℝ)+1),by positivity,hn⟩

end DirectComparison

namespace DirectComparison
open Pureness
open scoped NNReal ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma directPositiveCut_eq_traceConeCut (a : A) (ha : 0 ≤ a) (ε : ℝ≥0) :
    directPositiveCut ε a = (TraceCone.Positive.cut ε ⟨a,ha⟩).1 := by
  change cfc (fun t : ℝ => max (t-ε) 0) a = cfcₙ (fun t : ℝ => max (t-ε) 0) a
  exact (cfcₙ_eq_cfc (f := fun t : ℝ => max (t-ε) 0) (hf0 := by simp)).symm

lemma direct_rank_le_of_traceCone_comparison (τ : TracialState A)
    (a b : TraceCone.Positive A) (hab : TraceCone.CuntzBelow a b) :
    normalizedRootRank τ a.1 ≤ normalizedRootRank τ b.1 := by
  apply Pureness.CuntzSubequiv.rank_le _ a.2 b.2 τ
  apply (cuntzSubequiv_iff_norm _ _).mpr
  intro ε hε
  obtain ⟨v,hv⟩ := hab ε hε
  exact ⟨v,by simpa only [norm_sub_rev] using hv⟩

lemma direct_cut_rank_of_perturbation (τ : TracialState A)
    (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) (ε : ℝ) (hε : 0 < ε)
    (hab : ‖a-b‖ < ε) :
    normalizedRootRank τ (directPositiveCut ε a) ≤ normalizedRootRank τ b := by
  let e : ℝ≥0 := ⟨ε,hε.le⟩
  have h := TraceCone.cut_cuntzBelow_of_norm_sub_lt ⟨a,ha⟩ ⟨b,hb⟩ e hε hab
  have hr := direct_rank_le_of_traceCone_comparison τ _ _ h
  rw [←directPositiveCut_eq_traceConeCut] at hr
  exact hr

theorem direct_perturbed_cut_ranks (τ : TracialState A) (v w : A)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (t : ℝ) (ht : 0 < t) (hvw : ‖w-v‖ < t) :
    normalizedRootRank τ (directPositiveCut (3*t) v) ≤
        normalizedRootRank τ (directPositiveCut (2*t) w) ∧
      normalizedRootRank τ (directPositiveCut t w) ≤ normalizedRootRank τ v := by
  constructor
  · apply direct_cut_rank_of_perturbation τ v _ hv (directPositiveCut_nonneg _ _)
      (3*t) (by positivity)
    have hc := norm_sub_directPositiveCut_le w hw (2*t) (by positivity)
    have hn : ‖v-directPositiveCut (2*t) w‖ ≤ ‖v-w‖+‖w-directPositiveCut (2*t) w‖ :=
      by simpa only [sub_add_sub_cancel] using
        (norm_add_le (v-w) (w-directPositiveCut (2*t) w))
    rw [norm_sub_rev v w] at hn
    linarith
  · exact direct_cut_rank_of_perturbation τ w v hw hv t ht hvw

theorem direct_cut_rank_star_mul_self (τ : TracialState A) (x : A) (s : ℝ) :
    normalizedRootRank τ (directPositiveCut s (star x * x)) =
      normalizedRootRank τ (directPositiveCut s (x * star x)) := by
  rw [←cutoffTraceSup_eq_rank τ _ (directPositiveCut_nonneg _ _),
    ←cutoffTraceSup_eq_rank τ _ (directPositiveCut_nonneg _ _)]
  unfold cutoffTraceSup
  congr 1
  funext n
  congr 2
  change τ.functional (cfc (fun t : ℝ => min (((n : ℝ)+1)*t) 1)
      (cfc (fun t : ℝ => max (t-s) 0) (star x*x))) =
    τ.functional (cfc (fun t : ℝ => min (((n : ℝ)+1)*t) 1)
      (cfc (fun t : ℝ => max (t-s) 0) (x*star x)))
  rw [←cfc_comp (fun t : ℝ => min (((n : ℝ)+1)*t) 1)
      (fun t : ℝ => max (t-s) 0) (star x*x) (star_mul_self_nonneg x).isSelfAdjoint,
    ←cfc_comp (fun t : ℝ => min (((n : ℝ)+1)*t) 1)
      (fun t : ℝ => max (t-s) 0) (x*star x) (mul_star_self_nonneg x).isSelfAdjoint]
  exact trace_cfc_eq_of_moments τ _ _ (star_mul_self_nonneg x).isSelfAdjoint
    (mul_star_self_nonneg x).isSelfAdjoint (trace_star_mul_self_pow τ x) _ (by fun_prop)

end DirectComparison

namespace DirectComparison
open Pureness Filter
open scoped Topology ComplexOrder ENNReal

lemma positive_contraction_defect_nonneg
    {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {p : D} (hp : 0 ≤ p) (hpn : ‖p‖ ≤ 1) : 0 ≤ p-p*p := by
  have hp1 : p ≤ 1 := hp.isSelfAdjoint.le_algebraMap_norm_self.trans (by
    simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
      (smul_le_smul_of_nonneg_right hpn (zero_le_one : (0 : D) ≤ 1)))
  have hc : Commute p (1-p) := (Commute.one_right p).sub_right (Commute.refl p)
  simpa only [mul_sub,mul_one] using Commute.mul_nonneg hp (sub_nonneg.mpr hp1) hc

end DirectComparison

namespace DirectComparison
open Pureness
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma directCutoff_nonneg (η : ℝ) (hη : 0 < η) (a : A) (ha : 0 ≤ a) :
    0 ≤ directCutoff η a := by
  exact cfc_nonneg (fun t ht => le_min
    (div_nonneg (spectrum_nonneg_of_nonneg ha ht) hη.le) zero_le_one)

lemma directCutoff_le_one (η : ℝ) (a : A) : directCutoff η a ≤ 1 :=
  cfc_le_one _ _ (fun _ _ => min_le_right _ _)

lemma directCutoff_mem_hereditary (η : ℝ) (a : A) (ha : 0 ≤ a) :
    directCutoff η a ∈ hereditaryCarrier a := by
  change cfc (fun t : ℝ => min (t/η) 1) a ∈ hereditarySubalgebra a ha
  rw [←cfcₙ_eq_cfc (f := fun t : ℝ => min (t/η) 1) (hf0 := by simp)]
  exact cfcₙ_mem _ (self_mem_hereditary a ha)

lemma rank_le_trace_of_fixation (τ : TracialState A) (b e : A) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hefix : e*b=b) :
    normalizedRootRank τ b ≤ ENNReal.ofReal (τ.functional e).re := by
  apply iSup_le
  intro n
  have hm := normalizedRoot_mem_hereditary hb (self_mem_hereditary b hb) hb n
  have hfix : e * normalizedRoot b n = normalizedRoot b n :=
    (hereditary_fixed_by_cutoff hb he.isSelfAdjoint hefix hm).1
  have h := trace_mul_contraction_le τ e (normalizedRoot b n) he
    (normalizedRoot_le_one b hb n)
  rw [hfix] at h
  exact ENNReal.ofReal_le_ofReal h.1

def directSoftProjection (t : ℝ) (w : A) : A :=
  directCutoff t (directPositiveCut t w)

lemma directSoftProjection_nonneg (t : ℝ) (ht : 0 < t) (w : A) :
    0 ≤ directSoftProjection t w :=
  directCutoff_nonneg t ht _ (directPositiveCut_nonneg _ _)

lemma directSoftProjection_norm_le (t : ℝ) (ht : 0 < t) (w : A) :
    ‖directSoftProjection t w‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (directSoftProjection_nonneg t ht w)).mpr
    (directCutoff_le_one _ _)

lemma directSoftProjection_fixes (t : ℝ) (ht : 0 < t) (w : A) (hw : 0 ≤ w) :
    directSoftProjection t w * directPositiveCut (2*t) w = directPositiveCut (2*t) w := by
  have hcut : directPositiveCut (2*t) w = directPositiveCut t (directPositiveCut t w) := by
    have hs : 2*t-t=t := by ring
    simpa only [hs] using directPositiveCut_shift w hw t (2*t) (by linarith)
  rw [hcut]
  exact directCutoff_fixes_cut t ht _

theorem directSoftProjection_trace_bounds (τ : TracialState A)
    (t : ℝ) (ht : 0 < t) (w : A) (hw : 0 ≤ w) :
    let p := directSoftProjection t w
    (normalizedRootRank τ (directPositiveCut (2*t) w)).toReal ≤ (τ.functional p).re ∧
    (τ.functional p).re ≤ (normalizedRootRank τ (directPositiveCut t w)).toReal ∧
    0 ≤ (τ.functional (p-p*p)).re ∧
    (τ.functional (p-p*p)).re ≤
      (normalizedRootRank τ (directPositiveCut t w)).toReal -
        (normalizedRootRank τ (directPositiveCut (2*t) w)).toReal := by
  dsimp only
  let p := directSoftProjection t w
  have hp : 0 ≤ p := directSoftProjection_nonneg t ht w
  have hpn : ‖p‖ ≤ 1 := directSoftProjection_norm_le t ht w
  have hp2 : 0 ≤ p*p := by simpa only [hp.isSelfAdjoint.star_eq] using star_mul_self_nonneg p
  have hb := directPositiveCut_nonneg (2*t) w
  have hc := directPositiveCut_nonneg t w
  have hf : p*directPositiveCut (2*t) w=directPositiveCut (2*t) w :=
    directSoftProjection_fixes t ht w hw
  have hf2 : (p*p)*directPositiveCut (2*t) w=directPositiveCut (2*t) w := by
    rw [mul_assoc,hf,hf]
  have hu := trace_le_rank_of_mem_hereditary τ (directPositiveCut t w) p hc
    (directCutoff_mem_hereditary t _ hc) (directCutoff_le_one _ _)
  have huf := ne_of_lt ((normalizedRootRank_le_one τ _ hc).trans_lt ENNReal.one_lt_top)
  have hur := ENNReal.toReal_mono huf hu
  rw [ENNReal.toReal_ofReal (τ.functional.map_nonneg hp).1] at hur
  have hl := ENNReal.toReal_mono ENNReal.ofReal_ne_top (rank_le_trace_of_fixation τ _ p hb hp hf)
  rw [ENNReal.toReal_ofReal (τ.functional.map_nonneg hp).1] at hl
  have hl2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (rank_le_trace_of_fixation τ _ (p*p) hb hp2 hf2)
  rw [ENNReal.toReal_ofReal (τ.functional.map_nonneg hp2).1] at hl2
  have hd := (τ.functional.map_nonneg (positive_contraction_defect_nonneg hp hpn)).1
  refine ⟨hl,hur,hd,?_⟩
  rw [map_sub,Complex.sub_re]
  linarith

end DirectComparison

namespace DirectComparison
open Pureness
open scoped ENNReal ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma directSoftProjection_mem_hereditary_of_mem (b w : A) (hb : 0 ≤ b)
    (hw : w ∈ hereditaryCarrier b) (t : ℝ) (ht : 0 < t) :
    directSoftProjection t w ∈ hereditaryCarrier b := by
  have hc : directPositiveCut t w ∈ hereditarySubalgebra b hb := by
    change cfc (fun s : ℝ => max (s-t) 0) w ∈ hereditarySubalgebra b hb
    rw [←cfcₙ_eq_cfc (f := fun s : ℝ => max (s-t) 0)
      (hf0 := by simp [max_eq_right (by linarith : -t ≤ 0)])]
    exact cfcₙ_mem _ hw
  change cfc (fun s : ℝ => min (s/t) 1) (directPositiveCut t w) ∈
    hereditarySubalgebra b hb
  rw [←cfcₙ_eq_cfc (f := fun s : ℝ => min (s/t) 1) (hf0 := by simp)]
  exact cfcₙ_mem _ hc

theorem direct_scalar_almost_projection_step (b v x : A) (hb : 0 ≤ b) (hv : 0 ≤ v)
    (t δ : ℝ) (ht : 0 < t)
    (happrox : ‖star (CFC.sqrt b*x)*(CFC.sqrt b*x)-v‖ < t)
    (hlow : ∀ τ : TracialState A, (τ.functional b).re-2*δ <
      (normalizedRootRank τ (directPositiveCut (3*t) v)).toReal)
    (hup : ∀ τ : TracialState A, (normalizedRootRank τ v).toReal ≤ (τ.functional b).re) :
    ∃ p : A, p ∈ hereditaryCarrier b ∧ 0 ≤ p ∧ ‖p‖ ≤ 1 ∧
      ∀ τ : TracialState A,
        (τ.functional b).re-2*δ < (τ.functional p).re ∧
        (τ.functional p).re ≤ (τ.functional b).re ∧
        0 ≤ (τ.functional (p-p*p)).re ∧ (τ.functional (p-p*p)).re < 2*δ := by
  let a := CFC.sqrt b*x
  let w := a*star a
  have hw : 0 ≤ w := mul_star_self_nonneg a
  have hwm : w ∈ hereditaryCarrier b := by
    have he : w = CFC.sqrt b*(x*star x)*CFC.sqrt b := by
      simp only [w,a,star_mul,(CFC.sqrt_nonneg b).star_eq,mul_assoc]
    rw [he]
    exact sqrt_sandwich_mem_hereditary b _ hb
  refine ⟨directSoftProjection t w,
    directSoftProjection_mem_hereditary_of_mem b w hb hwm t ht,
    directSoftProjection_nonneg t ht w, directSoftProjection_norm_le t ht w, ?_⟩
  intro τ
  obtain ⟨hrlo,hrup⟩ := direct_perturbed_cut_ranks τ v (star a*a) hv
    (star_mul_self_nonneg a) t ht happrox
  rw [direct_cut_rank_star_mul_self] at hrlo hrup
  have hfin (z : A) (hz : 0 ≤ z) : normalizedRootRank τ z ≠ ⊤ :=
    ne_of_lt ((normalizedRootRank_le_one τ z hz).trans_lt ENNReal.one_lt_top)
  have hlo := ENNReal.toReal_mono (hfin _ (directPositiveCut_nonneg _ _)) hrlo
  have hhi := ENNReal.toReal_mono (hfin _ hv) hrup
  obtain ⟨hp₁,hp₂,hp₃,hp₄⟩ := directSoftProjection_trace_bounds τ t ht w hw
  have h₁ := hlow τ
  have h₂ := hup τ
  refine ⟨by linarith, by linarith, hp₃, by linarith⟩

end DirectComparison
end

end OAI
