import OAI.Analysis.HenonEmden.SpatialEndpoints

namespace OAI

section SourceEndpoints

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap WeightedLayers

 def endpointConstant (q B : ℝ) : ℝ := 2*(|-B/q| *2^|-B/q-1| *2^|-B/q|)
lemma endpointConstant_nonneg (q B : ℝ) : 0 ≤ endpointConstant q B := by
  unfold endpointConstant; positivity

def endpointAverage {n : ℕ} (u : Space n → ℝ) (f : Space n → ℝ)
    (z : sphere (0:Space n) 1 × (Space n × ℝ)) : ℝ :=
  (u (lowerPoint f z)+u (upperPoint f z))/2

lemma measurable_endpointAverage {n : ℕ} {u f : Space n → ℝ} (hu : Measurable u)
    (hf : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    Measurable (endpointAverage u f) :=
  ((hu.comp (measurable_lowerPoint hf)).add (hu.comp (measurable_upperPoint hf))).div_const 2

lemma source_endpoint_error {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ} {q B κ δ : ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x)
    (hq : 0 < q) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    {z : sphere (0:Space n) 1 × (Space n × ℝ)}
    (hχ : 0 < lineWeight volume (source u q B) κ δ z) :
    |endpointAverage u (source u q B) z-(z.2.2/‖z.2.1‖^B)^(1/q)| ≤
      endpointConstant q B*δ*d z.2.1*u z.2.1 := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hf := isOpen_source_subgraph hu hup q B
  have hfc (y : Space n) (hy : y ≠ 0) : ContinuousAt (source u q B) y :=
    (regular_source hu hup q B).continuousOn.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hy)
  have hb := positive_lineWeight_base volume hχ
  have hw : 0 < weight volume κ z.1 z.2.1 := hχ.trans_le (lineWeight_le volume _ κ δ z)
  have hx1 : 1 < ‖z.2.1‖ := by
    by_contra hh
    rw [weight_inner volume κ z.1 (not_lt.mp hh)] at hw
    exact lt_irrefl _ hw
  have hx2 : ‖z.2.1‖ < 2 := by
    by_contra hh
    rw [weight_outer volume κ z.1 (not_lt.mp hh)] at hw
    exact lt_irrefl _ hw
  have hx0 : z.2.1 ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hroot := layer_root_bounds (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx0) B)
    (hup z.2.1) hq hb.1.le (by rw [← source_off_zero _ _ _ hx0]; exact hb.2.1.le)
  have he (s : ℝ) (hs : s=lowerOffset (source u q B) z ∨ s=upperOffset (source u q B) z) :
      |u (z.2.1+s • z.1.1)-(z.2.2/‖z.2.1‖^B)^(1/q)| ≤
        endpointConstant q B*δ*d z.2.1*u z.2.1 := by
    obtain ⟨hy1,hy2,hlev,hdist⟩ := endpoint_spec volume hf hfc hκ hκ1 hδ hχ hs
    have hy0 : z.2.1+s • z.1.1 ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    rw [source_level_root hq hup hy0 hlev]
    have hh := radial_layer_endpoint_error (q := q) (B := B) ⟨hx1.le,hx2.le⟩ ⟨hy1.le,hy2.le⟩ hb.1.le
    calc
      _ ≤ (|-B/q| *2^|-B/q-1| *2^|-B/q|)*dist (z.2.1+s • z.1.1) z.2.1*
          (z.2.2/‖z.2.1‖^B)^(1/q) := hh
      _ ≤ (|-B/q| *2^|-B/q-1| *2^|-B/q|)*(2*δ*d z.2.1)*u z.2.1 := by
        have hd0 := d_nonneg z.2.1
        exact mul_le_mul (mul_le_mul_of_nonneg_left hdist (by positivity)) hroot.2 hroot.1 (by positivity)
      _ = _ := by unfold endpointConstant; ring
  exact average_endpoint_error (he _ (Or.inl rfl)) (he _ (Or.inr rfl))

end HenonLaneEmden.SpatialComponents
end
end SourceEndpoints

end OAI
