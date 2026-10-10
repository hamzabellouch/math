import OAI.Analysis.HenonEmden.PairPressure

namespace OAI

section PairRecovery

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LayerTonelli

def positionIntegral {n : ℕ} (u f : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (lineWeight volume f κ δ (e,z)*u z.1) ∂layerMeasure volume f

def endpointIntegral {n : ℕ} (u f : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (lineWeight volume f κ δ (e,z)*endpointAverage u f (e,z)) ∂layerMeasure volume f

def lossIntegral {n : ℕ} (u f : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((weight volume κ e z.1-lineWeight volume f κ δ (e,z))*u z.1) ∂layerMeasure volume f

def capPressureIntegral {n : ℕ} (f g : Space n → ℝ) (κ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (((n:ℝ)-2)*weight volume κ e z.1*directionalFactor e z) ∂interaction f g

def pairMismatchIntegral {n : ℕ} (f g : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (|lineWeight volume f κ δ (e,z.1)-lineWeight volume g κ δ (e,z.2)| *
    newtonKernel n (z.1.1,z.2.1)) ∂(layerMeasure volume f).prod (layerMeasure volume g)

def capMismatchIntegral {n : ℕ} (f g : Space n → ℝ) (κ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (|weight volume κ e z.1-weight volume κ e z.2|) ∂interaction f g

lemma weighted_potential_position {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (κ δ : ℝ) (e : sphere (0:Space n) 1) (z : Space n × ℝ) :
    ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z))*
        potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) z.1 =
      ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*u z.1) := by
  have hnχ := lineWeight_nonneg volume (source u q B) κ δ (e,z)
  by_cases hχ : 0 < lineWeight volume (source u q B) κ δ (e,z)
  · have hb := positive_lineWeight_base volume hχ
    have hx : z.1 ≠ 0 := by
      intro hx; rw [hx,source_zero] at hb; linarith [hb.1,hb.2.1]
    rw [h.newton_potential_u hn hq hx,ENNReal.ofReal_mul hnχ]
  · rw [le_antisymm (not_lt.mp hχ) hnχ]
    simp

lemma weighted_potential_endpoint {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    (e : sphere (0:Space n) 1) (z : Space n × ℝ) :
    ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z))*
        ((potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) (lowerPoint (source u q B) (e,z))+
          potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) (upperPoint (source u q B) (e,z)))/2) =
      ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*endpointAverage u (source u q B) (e,z)) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hnχ := lineWeight_nonneg volume (source u q B) κ δ (e,z)
  by_cases hχ : 0 < lineWeight volume (source u q B) κ δ (e,z)
  · have hf := isOpen_source_subgraph h.regular_u h.positive_u q B
    have hfc (y : Space n) (hy : y ≠ 0) : ContinuousAt (source u q B) y :=
      (regular_source h.regular_u h.positive_u q B).continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hy)
    have hlo := (endpoint_spec volume hf hfc hκ hκ1 hδ hχ (Or.inl rfl)).1
    have hhi := (endpoint_spec volume hf hfc hκ hκ1 hδ hχ (Or.inr rfl)).1
    have hlo0 : lowerPoint (source u q B) (e,z) ≠ 0 := norm_ne_zero_iff.mp (by change ‖z.1+_ • (e:Space n)‖ ≠ 0; linarith)
    have hhi0 : upperPoint (source u q B) (e,z) ≠ 0 := norm_ne_zero_iff.mp (by change ‖z.1+_ • (e:Space n)‖ ≠ 0; linarith)
    rw [h.newton_potential_u hn hq hlo0,h.newton_potential_u hn hq hhi0]
    unfold endpointAverage
    rw [ENNReal.ofReal_mul hnχ,ENNReal.ofReal_div_of_pos (by norm_num),
      ENNReal.ofReal_add (h.positive_u _).le (h.positive_u _).le,ENNReal.ofReal_ofNat]
  · rw [le_antisymm (not_lt.mp hχ) hnχ]
    simp

lemma IsSolution_pairLeft_recovery {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (e : sphere (0:Space n) 1) :
    (∫⁻ z, ENNReal.ofReal (spatialPairLeft (source u q B) (source v p A) κ δ e z)
      ∂(layerMeasure volume (source u q B)).prod (layerMeasure volume (source v p A))) =
      positionIntegral u (source u q B) κ δ e+positionIntegral v (source v p A) κ δ e := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hf := isOpen_source_subgraph h.regular_u h.positive_u q B
  have hg := isOpen_source_subgraph h.regular_v h.positive_v p A
  have hfM := measurable_source h.continuous_u q B
  have hgM := measurable_source h.continuous_v p A
  have hm1 : Measurable (fun z : Space n × ℝ => lineWeight volume (source u q B) κ δ (e,z)) :=
    (measurable_lineWeight volume hf hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hm2 : Measurable (fun z : Space n × ℝ => lineWeight volume (source v p A) κ δ (e,z)) :=
    (measurable_lineWeight volume hg hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  unfold spatialPairLeft
  simp_rw [ENNReal.ofReal_mul (add_nonneg (lineWeight_nonneg volume _ _ _ _) (lineWeight_nonneg volume _ _ _ _)),
    ENNReal.ofReal_add (lineWeight_nonneg volume _ _ _ _) (lineWeight_nonneg volume _ _ _ _)]
  rw [lintegral_pair_weight_sum volume hfM hgM (measurable_newtonKernel n).ennreal_ofReal
    (fun x y => congrArg ENNReal.ofReal (newtonKernel_symm n x y)) hm1.ennreal_ofReal hm2.ennreal_ofReal]
  simp_rw [weighted_potential_position hn h hq κ δ e,weighted_potential_position hn h.swap hp κ δ e]
  rfl

end HenonLaneEmden.SpatialComponents
end
end PairRecovery

end OAI
