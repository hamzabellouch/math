import OAI.Analysis.LipschitzHilbert.Geometry.TopDilationPacking
import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedTopWeakTwo

namespace OAI

/-! The actual smooth count of popular tops satisfies weak L2 on the
localization strip. The only published input is Lacey--Li; geometric
admissibility, thin/fat splitting, dilation packing, and summation have
all been proved for the actual slope boxes. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem popular_top_count_weak_two (hLL : LaceyLiInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox)
      (l r R : ℝ), 1 ≤ R → (∀ i, |(T i).slope| ≤ 1) →
      ∀ (u : Plane → ℝ) (K α : ℝ≥0), LipschitzWith K u → 0 < α → α ≤ 1 →
      300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation R) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal ((α:ℝ)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      ∀ (P d : ℝ), 0 < P → P ≤ R → 4 ≤ d →
      ∀ t : ℝ, 0 < t →
      (volume.prod volume) ({z | z.1 ∈ Icc l r} ∩ {z | t < ∑ i, (T i).weight P d z}) ≤
        ENNReal.ofReal ((2*4^d*(C/(α:ℝ))*Real.sqrt (∑ i, (T i).area)*R^3)^2/t^2) := by
  classical
  obtain ⟨C,hC,hpack⟩ := top_dilation_packing hLL
  refine ⟨C,hC,?_⟩
  intro ι _ T l r R hR hs u K α hu hα hα1 hlength E hEmeas hdisj hE hclose hsize
    P d hP hPR hd t ht
  by_cases hne : Nonempty ι
  · let := hne
    have hS : 0 < ∑ i, (T i).area :=
      Finset.sum_pos (fun i _ => (T i).area_pos) Finset.univ_nonempty
    have hb := top_count_weak_two_on_set T {z | z.1 ∈ Icc l r}
      (measurableSet_Icc.preimage measurable_fst) P R d
      ((C/(α:ℝ))*Real.sqrt (∑ i, (T i).area)) hP hPR hd (by positivity) (by
        intro Q hQ hQfin hQsub n
        have hRn : 1 ≤ R*2^n := one_le_mul_of_one_le_of_one_le hR
          (one_le_pow₀ (by norm_num))
        have hED (i : ι) (z : ℝ × ℝ) (hz : z ∈ E i) :
            z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation (R*2^n) := by
          refine ⟨(hE i z hz).1, ?_⟩
          change (T i).radius z ≤ R*2^n
          exact ((hE i z hz).2 : (T i).radius z ≤ R).trans
            (le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num)))
        have hp := hpack ι T l r (R*2^n) hRn hs u K α hu hα hα1 hlength E hEmeas hdisj hED hclose
          hsize hS Q hQ hQfin (fun z hz => hQsub hz)
        convert hp using 1) t ht
    convert hb using 1
    congr 1
    ring
  · let : IsEmpty ι := not_nonempty_iff.mp hne
    have he : {z : ℝ × ℝ | t < ∑ i, (T i).weight P d z} = ∅ := by
      ext z
      simp only [Finset.univ_eq_empty, Finset.sum_empty, mem_ofPred_eq, mem_empty_iff_false,
        iff_false]
      exact not_lt_of_ge ht.le
    rw [he, inter_empty, measure_empty]
    exact zero_le

end LipschitzHilbert

end

end OAI
