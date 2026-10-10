import OAI.Probability.InvariantIsing.Fields.FieldTail
import OAI.Probability.InvariantIsing.Spectral.SpectralBallQuantizer

namespace OAI

/-! Finite field quantizers with null boundaries and a uniform tail bound. -/
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology Classical
namespace InvariantIsing

def fieldBallSimple {n : ℕ} (c r : Fin n → ℝ) : SimpleFunc ℝ ℝ := by
  let : MeasurableSpace (Option (Fin n)) := ⊤
  exact (SimpleFunc.ofFinite (fun i : Option (Fin n) => i.elim 0 c)).comp
    (spectralPartitionIndex (spectralBallCell (fun i => ball (c i) (r i))) (spectralBallCell_cover _))
    (measurable_spectralPartitionIndex _ (spectralBallCell_cover _) (spectralBallCell_disjoint _)
      (spectralBallCell_measurable _ (fun _ => measurableSet_ball)))

lemma fieldBallSimple_apply {n : ℕ} (c r : Fin n → ℝ) (x : ℝ) :
    fieldBallSimple c r x=spectralBallQuantizer c r 0 x := rfl

lemma fieldBallSimple_bound {n : ℕ} (c r : Fin n → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hc : ∀ i, c i∈Icc (-2*M) (2*M)) (x : ℝ) :
    |fieldBallSimple c r x| ≤ 2*M := by
  have hh := spectralBallQuantizer_mem c r 0 (Icc (-2*M) (2*M)) hc
    (by constructor <;> nlinarith) x
  rw [fieldBallSimple_apply,abs_le]
  exact ⟨by nlinarith [hh.1],hh.2⟩

lemma fieldBallSimple_error {n : ℕ} (c r : Fin n → ℝ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hc : ∀ i, c i∈Icc (-2*M) (2*M))
    (hr : ∀ i, r i ≤ δ) (hcover : Icc (-2*M) (2*M) ⊆ ⋃ i, ball (c i) (r i)) (x : ℝ) :
    |fieldBallSimple c r x-x| ≤ δ+4*fieldTail M x := by
  by_cases hx : |x| ≤ 2*M
  · have hm : x∈Icc (-2*M) (2*M) := by
      obtain ⟨hl,hu⟩ := abs_le.mp hx
      exact ⟨by nlinarith,hu⟩
    have he := spectralBallQuantizer_close c r 0 δ x hr (hcover hm)
    have he' : |fieldBallSimple c r x-x| ≤ δ := by
      simpa only [fieldBallSimple_apply,Real.dist_eq] using he
    linarith [fieldTail_nonneg M x]
  · have hxb : 2*M < |x| := lt_of_not_ge hx
    have he := (abs_sub (fieldBallSimple c r x) x).trans (add_le_add (fieldBallSimple_bound c r hM hc x) le_rfl)
    have ht : |x|-M ≤ fieldTail M x := le_max_left _ _
    nlinarith

lemma exists_field_ball_quantizer (μ : Measure ℝ) [SFinite μ] {M δ : ℝ}
    (hδ : 0 < δ) :
    ∃ n : ℕ, ∃ c r : Fin n → ℝ,
      (∀ i, c i∈Icc (-2*M) (2*M)) ∧ (∀ i, r i ≤ δ) ∧
      (∀ i, μ (frontier (ball (c i) (r i)))=0) ∧
      Icc (-2*M) (2*M) ⊆ ⋃ i, ball (c i) (r i) := by
  obtain ⟨n,c,r,hc,hr,hn,hcover⟩ := spectral_null_boundary_cover μ
    (Icc (-2*M) (2*M)) isCompact_Icc δ hδ
  exact ⟨n,c,r,hc,(fun i => (hr i).2.le),hn,hcover⟩

end InvariantIsing

end

end OAI
