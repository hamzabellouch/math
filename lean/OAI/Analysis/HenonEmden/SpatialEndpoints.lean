import OAI.Analysis.HenonEmden.WeightedEndpoints

namespace OAI

universe uE

section SpatialEndpoints

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents WeightedLayers
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def lowerOffset (f : E → ℝ) (p : sphere (0:E) 1 × (E × ℝ)) : ℝ :=
  -(backwardExit (lineLayer f) p).toReal
def upperOffset (f : E → ℝ) (p : sphere (0:E) 1 × (E × ℝ)) : ℝ :=
  (forwardExit (lineLayer f) p).toReal
def lowerPoint (f : E → ℝ) (p : sphere (0:E) 1 × (E × ℝ)) : E :=
  p.2.1+lowerOffset f p • p.1.1
def upperPoint (f : E → ℝ) (p : sphere (0:E) 1 × (E × ℝ)) : E :=
  p.2.1+upperOffset f p • p.1.1

omit [Nontrivial E] in
lemma measurable_lowerPoint {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    Measurable (lowerPoint f) :=
  measurable_snd.fst.add (((measurable_backwardExit (isOpen_lineLayer hf)).ennreal_toReal.neg).smul measurable_fst.subtype_val)
omit [Nontrivial E] in
lemma measurable_upperPoint {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    Measurable (upperPoint f) :=
  measurable_snd.fst.add (((measurable_forwardExit (isOpen_lineLayer hf)).ennreal_toReal).smul measurable_fst.subtype_val)

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma positive_lineWeight_base {f : E → ℝ} {κ δ : ℝ} {p : sphere (0:E) 1 × (E × ℝ)}
    (hχ : 0 < lineWeight μ f κ δ p) :
    0 < p.2.2 ∧ p.2.2 < f p.2.1 ∧ componentLength (lineLayer f) p ≠ ⊤ := by
  unfold lineWeight componentWeight at hχ
  split_ifs at hχ with hh
  · have hb := hh.1
    simp only [lineLayer,Set.mem_ofPred_eq,zero_smul,add_zero] at hb
    exact ⟨hb.1,hb.2,hh.2.1⟩
  · simp at hχ

lemma endpoint_spec {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    (hfc : ∀ y ≠ 0, ContinuousAt f y) {κ δ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    {p : sphere (0:E) 1 × (E × ℝ)} (hχ : 0 < lineWeight μ f κ δ p)
    {s : ℝ} (hs : s=lowerOffset f p ∨ s=upperOffset f p) :
    1 < ‖p.2.1+s • p.1.1‖ ∧ ‖p.2.1+s • p.1.1‖ < 2 ∧
      f (p.2.1+s • p.1.1)=p.2.2 ∧ dist (p.2.1+s • p.1.1) p.2.1 ≤ 2*δ*d p.2.1 := by
  obtain ⟨ht,htf,hfin⟩ := positive_lineWeight_base μ hχ
  let U := {s : ℝ | 0 < p.2.2 ∧ p.2.2 < f (p.2.1+s • p.1.1)}
  have hp : (p,0) ∈ lineLayer f := by simpa only [lineLayer,Set.mem_ofPred_eq,zero_smul,add_zero] using And.intro ht htf
  have he : connectedComponentIn U 0 = Ioo (lowerOffset f p) (upperOffset f p) :=
    component_eq_Ioo (isOpen_lineLayer hf) hp (ENNReal.add_ne_top.mp hfin).1 (ENNReal.add_ne_top.mp hfin).2
  have h0 : 0 ∈ U := hp
  have h0I := mem_connectedComponentIn h0
  have hab : lowerOffset f p < upperOffset f p := by
    rw [he] at h0I
    exact h0I.1.trans h0I.2
  have hsc : s ∈ closure (connectedComponentIn U 0) := by
    rw [he,closure_Ioo hab.ne]
    rcases hs with rfl | rfl <;> exact ⟨by linarith,by linarith⟩
  have hwe : lineWeight μ f κ δ p = (setWeight (fun r => weight μ κ p.1 (p.2.1+r • p.1.1))
      (fun r => d (p.2.1+r • p.1.1)) δ (connectedComponentIn U 0)).toReal :=
    lineWeight_eq_setWeight μ hf hκ hκ1 δ p.1 p.2.1 p.2.2
  have hle := setWeight_le_on_closure (d := fun r => d (p.2.1+r • p.1.1)) (δ := δ)
    ((continuous_weight μ hκ hκ1 p.1).comp (show Continuous (fun r : ℝ => p.2.1+r • p.1.1) by fun_prop))
    (fun r _ => weight_nonneg μ κ p.1 _) hsc
  simp only [Function.comp_def] at hle
  rw [← hwe] at hle
  have hw : 0 < weight μ κ p.1 (p.2.1+s • p.1.1) := hχ.trans_le hle
  have h1 : 1 < ‖p.2.1+s • p.1.1‖ := by
    by_contra hh
    rw [weight_inner μ κ p.1 (not_lt.mp hh)] at hw
    exact lt_irrefl _ hw
  have h2 : ‖p.2.1+s • p.1.1‖ < 2 := by
    by_contra hh
    rw [weight_outer μ κ p.1 (not_lt.mp hh)] at hw
    exact lt_irrefl _ hw
  have hy0 : p.2.1+s • p.1.1 ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hval : f (p.2.1+s • p.1.1)=p.2.2 :=
    value_eq_level_at_endpoint (O := {r : ℝ | 0 < p.2.2}) h0 he hs ht
      ((hfc _ hy0).comp (f := fun r : ℝ => p.2.1+r • p.1.1) (show ContinuousAt (fun r : ℝ => p.2.1+r • p.1.1) s by fun_prop))
  have hdist := endpoints_distance_bound he (mem_connectedComponentIn h0) hδ
    (d_nonneg (p.2.1+(0:ℝ) • p.1.1)) (by rw [← hwe]; exact hχ)
  simp only [zero_smul,add_zero,sub_zero] at hdist
  have hd : |s| ≤ 2*δ*d p.2.1 := hs.elim (fun hh => hh ▸ hdist.1) (fun hh => hh ▸ hdist.2)
  refine ⟨h1,h2,hval,?_⟩
  have hd' := dist_line p.1 p.2.1 s 0
  simp only [zero_smul,add_zero,Real.dist_eq,sub_zero] at hd'
  exact hd'.trans_le hd

end HenonLaneEmden.SpatialComponents
end
end SpatialEndpoints

end OAI
