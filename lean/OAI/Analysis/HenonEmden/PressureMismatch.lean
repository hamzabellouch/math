import OAI.Analysis.HenonEmden.PDEPressure

namespace OAI

section PressureMismatch

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LayerTonelli

lemma weighted_potential_loss {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (κ δ : ℝ) (e : sphere (0:Space n) 1) (z : Space n × ℝ) :
    ENNReal.ofReal (weight volume κ e z.1-lineWeight volume (source u q B) κ δ (e,z))*
        potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) z.1 =
      ENNReal.ofReal ((weight volume κ e z.1-lineWeight volume (source u q B) κ δ (e,z))*u z.1) := by
  have hnχ := sub_nonneg.mpr (lineWeight_le volume (source u q B) κ δ (e,z))
  by_cases hx : z.1 = 0
  · have hh : weight volume κ e z.1 = 0 := weight_inner volume κ e (by simp [hx])
    have hχ : lineWeight volume (source u q B) κ δ (e,z) = 0 :=
      le_antisymm ((lineWeight_le volume _ _ _ _).trans_eq hh) (lineWeight_nonneg volume _ _ _ _)
    simp [hh,hχ]
  · rw [h.newton_potential_u hn hq hx,ENNReal.ofReal_mul hnχ]

lemma IsSolution_pairMismatch_bound {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:Space n) 1) :
    pairMismatchIntegral (source u q B) (source v p A) κ δ e ≤
      capMismatchIntegral (source u q B) (source v p A) κ e+
      (lossIntegral u (source u q B) κ δ e+lossIntegral v (source v p A) κ δ e) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hf := isOpen_source_subgraph h.regular_u h.positive_u q B
  have hg := isOpen_source_subgraph h.regular_v h.positive_v p A
  have hfM := measurable_source h.continuous_u q B
  have hgM := measurable_source h.continuous_v p A
  have hm1 : Measurable (fun z : Space n × ℝ => lineWeight volume (source u q B) κ δ (e,z)) :=
    (measurable_lineWeight volume hf hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hm2 : Measurable (fun z : Space n × ℝ => lineWeight volume (source v p A) κ δ (e,z)) :=
    (measurable_lineWeight volume hg hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hh : Measurable (weight volume κ e : Space n → ℝ) := (continuous_weight volume hκ hκ1 e).measurable
  let lf (z : Space n × ℝ) := weight volume κ e z.1-lineWeight volume (source u q B) κ δ (e,z)
  let lg (z : Space n × ℝ) := weight volume κ e z.1-lineWeight volume (source v p A) κ δ (e,z)
  have hlf (z) : 0 ≤ lf z := sub_nonneg.mpr (lineWeight_le volume _ _ _ _)
  have hlg (z) : 0 ≤ lg z := sub_nonneg.mpr (lineWeight_le volume _ _ _ _)
  have hlfM : Measurable lf := by unfold lf; fun_prop
  have hlgM : Measurable lg := by unfold lg; fun_prop
  have hpoint (z : (Space n × ℝ) × (Space n × ℝ)) :
      ENNReal.ofReal (|lineWeight volume (source u q B) κ δ (e,z.1)-lineWeight volume (source v p A) κ δ (e,z.2)| *
        newtonKernel n (z.1.1,z.2.1)) ≤
      ENNReal.ofReal (|weight volume κ e z.1.1-weight volume κ e z.2.1|)*ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1))+
        (ENNReal.ofReal (lf z.1)+ENNReal.ofReal (lg z.2))*ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1)) := by
    rw [← add_mul,← ENNReal.ofReal_add (hlf _) (hlg _),← ENNReal.ofReal_add (abs_nonneg _) (add_nonneg (hlf _) (hlg _)),
      ← ENNReal.ofReal_mul (add_nonneg (abs_nonneg _) (add_nonneg (hlf _) (hlg _)))]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (newtonKernel_nonneg hn _)
    apply abs_le.mpr
    have h1 := le_abs_self (weight volume κ e z.1.1-weight volume κ e z.2.1)
    have h2 := neg_le_abs (weight volume κ e z.1.1-weight volume κ e z.2.1)
    dsimp [lf,lg] at *
    have h3 := lineWeight_le volume (source u q B) κ δ (e,z.1)
    have h4 := lineWeight_le volume (source v p A) κ δ (e,z.2)
    constructor <;> linarith
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (|weight volume κ e z.1.1-weight volume κ e z.2.1|)*ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1))+
        (ENNReal.ofReal (lf z.1)+ENNReal.ofReal (lg z.2))*ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1))
        ∂(layerMeasure volume (source u q B)).prod (layerMeasure volume (source v p A)) := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left (by fun_prop [measurable_newtonKernel]),
        lintegral_pair_interaction hfM hgM (F := fun z => ENNReal.ofReal (|weight volume κ e z.1-weight volume κ e z.2|)) (by fun_prop),
        lintegral_pair_weight_sum volume hfM hgM (measurable_newtonKernel n).ennreal_ofReal
          (fun x y => congrArg ENNReal.ofReal (newtonKernel_symm n x y)) hlfM.ennreal_ofReal hlgM.ennreal_ofReal]
      dsimp only [lf,lg]
      simp_rw [weighted_potential_loss (by omega) h hq κ δ e,weighted_potential_loss (by omega) h.swap hp κ δ e]
      rfl

end HenonLaneEmden.SpatialComponents
end
end PressureMismatch

end OAI
