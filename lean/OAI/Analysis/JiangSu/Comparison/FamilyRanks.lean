import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.Ranks
import OAI.Analysis.JiangSu.Nonunital.Hereditary

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness
open scoped ENNReal ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [TopologicalSpace ι] [CompactSpace ι]

omit [CompactSpace ι] in
lemma family_isOpen_lt_rank (θ : ι → TracialState A)
    (hθ : ∀ a, Continuous (fun i => (θ i).functional a))
    (a : A) (F : ι → ℝ≥0∞) (hF : Continuous F) :
    IsOpen {i | F i < normalizedRootRank (θ i) a} := by
  have hopen : IsOpen (⋃ n : ℕ, {i | F i < ENNReal.ofReal ((θ i).functional (normalizedRoot a n)).re}) :=
    isOpen_iUnion fun n => isOpen_lt hF (ENNReal.continuous_ofReal.comp
      (Complex.continuous_re.comp (hθ (normalizedRoot a n))))
  convert hopen using 2
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, normalizedRootRank, lt_iSup_iff]

omit [CompactSpace ι] in
lemma family_isOpen_lt_realRank (θ : ι → TracialState A)
    (hθ : ∀ a, Continuous (fun i => (θ i).functional a))
    (a : A) (ha : 0 ≤ a) (F : ι → ℝ) (hF : Continuous F) :
    IsOpen {i | F i < (normalizedRootRank (θ i) a).toReal} := by
  have he : {i | F i < (normalizedRootRank (θ i) a).toReal} =
      {i | F i < 0} ∪ {i | ENNReal.ofReal (F i) < normalizedRootRank (θ i) a} := by
    ext i
    simp only [Set.mem_ofPred_eq,Set.mem_union]
    by_cases h : F i < 0
    · exact ⟨fun _ => Or.inl h,fun _ => h.trans_le ENNReal.toReal_nonneg⟩
    · simp only [h,false_or]
      exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt h) (directRank_ne_top (θ i) a ha)).symm
  rw [he]
  exact (isOpen_lt hF continuous_const).union
    (family_isOpen_lt_rank θ hθ a _ (ENNReal.continuous_ofReal.comp hF))

theorem family_uniform_positive_cut (θ : ι → TracialState A)
    (hθ : ∀ a, Continuous (fun i => (θ i).functional a))
    (a : A) (ha : 0 ≤ a) (F : ι → ℝ) (hF : Continuous F)
    (hgap : ∀ i, F i < (normalizedRootRank (θ i) a).toReal) :
    ∃ η : ℝ, 0 < η ∧ ∀ i,
      F i < (normalizedRootRank (θ i) (directPositiveCut η a)).toReal := by
  let U : ℕ → Set ι := fun n =>
    {i | F i < (normalizedRootRank (θ i) (directPositiveCut (1/((n : ℝ)+1)) a)).toReal}
  have hopen : ∀ n, IsOpen (U n) := fun n =>
    family_isOpen_lt_realRank θ hθ _ (directPositiveCut_nonneg _ _) F hF
  have hmono : Monotone U := by
    intro n m hnm i hi
    change F i < (normalizedRootRank (θ i) (directPositiveCut (1/((n : ℝ)+1)) a)).toReal at hi
    change F i < (normalizedRootRank (θ i) (directPositiveCut (1/((m : ℝ)+1)) a)).toReal
    apply lt_of_lt_of_le hi
    apply ENNReal.toReal_mono (directRank_ne_top (θ i) _ (directPositiveCut_nonneg _ _))
    apply rank_directPositiveCut_antitone (θ i) a ha
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hcover : ∀ i, ∃ n, i ∈ U n := by
    intro i
    by_cases hneg : F i < 0
    · exact ⟨0,hneg.trans_le ENNReal.toReal_nonneg⟩
    have h := (ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt hneg)
      (directRank_ne_top (θ i) a ha)).mpr (hgap i)
    rw [rank_eq_iSup_directPositiveCut (θ i) a ha] at h
    obtain ⟨n,hn⟩ := lt_iSup_iff.mp h
    exact ⟨n,(ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_gt hneg)
      (directRank_ne_top (θ i) _ (directPositiveCut_nonneg _ _))).mp hn⟩
  obtain ⟨n,hn⟩ := uniform_index_of_increasing_open_cover U hopen hmono hcover
  exact ⟨1/((n : ℝ)+1),by positivity,hn⟩

theorem family_scalar_almost_projection_step {κ : Type*} (θ : κ → TracialState A) (b v x : A) (hb : 0 ≤ b) (hv : 0 ≤ v)
    (t δ : ℝ) (ht : 0 < t)
    (happrox : ‖star (CFC.sqrt b*x)*(CFC.sqrt b*x)-v‖ < t)
    (hlow : ∀ i : κ, ((θ i).functional b).re-2*δ <
      (normalizedRootRank (θ i) (directPositiveCut (3*t) v)).toReal)
    (hup : ∀ i : κ, (normalizedRootRank (θ i) v).toReal ≤ ((θ i).functional b).re) :
    ∃ p : A, p ∈ hereditaryCarrier b ∧ 0 ≤ p ∧ ‖p‖ ≤ 1 ∧
      ∀ i : κ,
        ((θ i).functional b).re-2*δ < ((θ i).functional p).re ∧
        ((θ i).functional p).re ≤ ((θ i).functional b).re ∧
        0 ≤ ((θ i).functional (p-p*p)).re ∧ ((θ i).functional (p-p*p)).re < 2*δ := by
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
  intro i
  let τ := θ i
  obtain ⟨hrlo,hrup⟩ := direct_perturbed_cut_ranks τ v (star a*a) hv
    (star_mul_self_nonneg a) t ht happrox
  rw [direct_cut_rank_star_mul_self] at hrlo hrup
  have hfin (z : A) (hz : 0 ≤ z) : normalizedRootRank (θ i) z ≠ ⊤ :=
    directRank_ne_top (θ i) z hz
  have hlo := ENNReal.toReal_mono (hfin _ (directPositiveCut_nonneg _ _)) hrlo
  have hhi := ENNReal.toReal_mono (hfin _ hv) hrup
  obtain ⟨hp₁,hp₂,hp₃,hp₄⟩ := directSoftProjection_trace_bounds τ t ht w hw
  have h₁ := hlow i
  have h₂ := hup i
  refine ⟨h₁.trans_le (hlo.trans hp₁), hp₂.trans (hhi.trans h₂), hp₃, ?_⟩
  linarith

end DirectComparison

end
end

end OAI
