import OAI.Analysis.HenonEmden.Angular

namespace OAI

universe uE

section SpatialComponents

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def lineLayer (f : E → ℝ) : Set ((sphere (0:E) 1 × (E × ℝ)) × ℝ) :=
  {z | 0 < z.1.2.2 ∧ z.1.2.2 < f (z.1.2.1+z.2 • z.1.1.1)}
def lineWeight (f : E → ℝ) (κ δ : ℝ) (p : sphere (0:E) 1 × (E × ℝ)) : ℝ :=
  (componentWeight (lineLayer f) (fun z => weight μ κ z.1.1 (z.1.2.1+z.2 • z.1.1.1))
    (fun z => d (z.1.2.1+z.2 • z.1.1.1)) δ p).toReal

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma isOpen_lineLayer {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    IsOpen (lineLayer f) := by
  exact hf.preimage (show Continuous (fun z : (sphere (0:E) 1 × (E × ℝ)) × ℝ =>
    (z.1.2.1+z.2 • z.1.1.1,z.1.2.2)) by fun_prop)

lemma measurable_lineWeight {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) :
    Measurable (lineWeight μ f κ δ) := by
  unfold lineWeight
  apply Measurable.ennreal_toReal
  apply measurable_componentWeight (isOpen_lineLayer hf)
  · exact (measurable_weight μ hκ hκ1).comp
      (show Measurable (fun z : (sphere (0:E) 1 × (E × ℝ)) × ℝ =>
        (z.1.1,z.1.2.1+z.2 • z.1.1.1)) by fun_prop)
  · exact continuous_d.measurable.comp
      (show Measurable (fun z : (sphere (0:E) 1 × (E × ℝ)) × ℝ =>
        z.1.2.1+z.2 • z.1.1.1) by fun_prop)

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma lineWeight_nonneg (f : E → ℝ) (κ δ : ℝ) (p : sphere (0:E) 1 × (E × ℝ)) :
    0 ≤ lineWeight μ f κ δ p := ENNReal.toReal_nonneg

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma lineWeight_le (f : E → ℝ) (κ δ : ℝ) (p : sphere (0:E) 1 × (E × ℝ)) :
    lineWeight μ f κ δ p ≤ weight μ κ p.1 p.2.1 := by
  have he := componentWeight_le_base
    (U := lineLayer f) (fun z => weight μ κ z.1.1 (z.1.2.1+z.2 • z.1.1.1))
    (fun z => d (z.1.2.1+z.2 • z.1.1.1)) δ p
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [lineWeight,zero_smul,add_zero,ENNReal.toReal_ofReal (weight_nonneg μ _ _ _)] using hr

lemma lineWeight_eq_setWeight {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (e : sphere (0:E) 1)
    (x : E) (t : ℝ) :
    lineWeight μ f κ δ (e,x,t) =
      (setWeight (fun s => weight μ κ e (x+s • (e:E))) (fun s => d (x+s • (e:E))) δ
        (connectedComponentIn {s | 0 < t ∧ t < f (x+s • (e:E))} 0)).toReal := by
  have hh : Continuous (fun s : ℝ => weight μ κ e (x+s • (e:E))) :=
    (continuous_weight μ hκ hκ1 e).comp (by fun_prop)
  have hd : Continuous (fun s : ℝ => d (x+s • (e:E))) := continuous_d.comp (by fun_prop)
  exact congrArg ENNReal.toReal (componentWeight_eq_setWeight (isOpen_lineLayer hf)
    (p := (e,x,t))
    (h := fun z => weight μ κ z.1.1 (z.1.2.1+z.2 • z.1.1.1))
    (d := fun z => d (z.1.2.1+z.2 • z.1.1.1)) hh hd δ)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma dist_line (e : sphere (0:E) 1) (x : E) (s t : ℝ) :
    dist (x+s • (e:E)) (x+t • (e:E)) = dist s t := by
  have hn : ‖(e:E)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using e.2
  rw [dist_eq_norm,show x+s • (e:E)-(x+t • (e:E)) = (s-t) • (e:E) by module,
    norm_smul,hn,mul_one,Real.norm_eq_abs,Real.dist_eq]

lemma short_loss {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/2)
    (e : sphere (0:E) 1) {x : E} (hd : 0 < d x) {t : ℝ} (ht : 0 < t) (htf : t < f x)
    (hlen : componentLength (lineLayer f) (e,x,t) ≤
      ENNReal.ofReal (δ*(d x)^(m (Module.finrank ℝ E)))) :
    weight μ κ e x-lineWeight μ f κ δ (e,x,t) ≤
      oscillationConstant μ κ*δ*(d x)^(N (Module.finrank ℝ E)) := by
  let U := {s : ℝ | 0 < t ∧ t < f (x+s • (e:E))}
  have hU : IsOpen U := isOpen_section (isOpen_lineLayer hf) (e,x,t)
  have h0 : 0 ∈ U := by simpa only [U,Set.mem_ofPred_eq,zero_smul,add_zero] using And.intro ht htf
  have hvol : volume (connectedComponentIn U 0) ≤ ENNReal.ofReal (δ*(d x)^(m (Module.finrank ℝ E))) := by
    have hh := volume_component_all (isOpen_lineLayer hf) (show ((e,x,t),0) ∈ lineLayer f from h0)
    exact hh.trans_le hlen
  rw [lineWeight_eq_setWeight μ hf hκ hκ1]
  have hd0 : d (x+(0:ℝ) • (e:E)) = d x := by rw [zero_smul,add_zero]
  have hh0 : weight μ κ e (x+(0:ℝ) • (e:E)) = weight μ κ e x := by rw [zero_smul,add_zero]
  have hp := pow_d_le_self x (show 1 ≤ m (Module.finrank ℝ E) by unfold m; omega)
  have he := short_component_loss hU h0 hδ hδ1 (by rw [hd0]; exact hd.le)
    (weight_nonneg μ κ e _) (mul_nonneg hδ (pow_nonneg hd.le _))
    (by rw [hd0]; exact mul_le_mul_of_nonneg_left hp hδ) hvol
    (h := fun s => weight μ κ e (x+s • (e:E)))
    (d := fun s => d (x+s • (e:E)))
    (ε := oscillationConstant μ κ*δ*(d x)^(N (Module.finrank ℝ E)))
    (by
      intro s hs
      have hh := (abs_le.mp (d_oscillation x (x+s • (e:E)))).2
      have hdist : dist x (x+s • (e:E)) = dist s 0 := by
        simpa only [zero_smul,add_zero,dist_comm] using dist_line e x 0 s
      rw [hd0]
      rw [hdist] at hh
      linarith)
    (by
      intro s hs
      rw [hh0]
      apply weight_short_oscillation μ hκ hκ1 hδ hδ1 hd _ e
      simpa only [← dist_line e x s 0,zero_smul,add_zero,dist_comm] using hs)
  simpa only [hh0] using he

end HenonLaneEmden.SpatialComponents
end
end SpatialComponents

end OAI
