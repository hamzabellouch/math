import Mathlib
import OAI.Probability.Ballisticity.Geometry.HeightPolygon

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma gaussianPathFiniteLaw_smul (T a : ℝ) (I : Finset unitInterval) :
    (gaussianPathFiniteLaw T I).map (fun x => a • x) = gaussianPathFiniteLaw (a^2*T) I := by
  unfold gaussianPathFiniteLaw
  let v := fun j : Fin I.card => Real.toNNReal (T*((orderedTimes I j.succ:ℝ)-orderedTimes I j.castSucc))
  have he (j : Fin I.card) : (gaussianReal 0 (v j)).map (fun x : ℝ => a*x) =
      gaussianReal 0 (Real.toNNReal ((a^2*T)*((orderedTimes I j.succ:ℝ)-orderedTimes I j.castSucc))) := by
    rw [gaussianReal_map_const_mul,mul_zero]
    congr 1
    have hsq : NNReal.mk (a^2) (sq_nonneg a) = Real.toNNReal (a^2) := by
      apply NNReal.eq
      simp only [NNReal.coe_mk,Real.coe_toNNReal']
      exact (max_eq_left (sq_nonneg a)).symm
    rw [hsq,← Real.toNNReal_mul (sq_nonneg a)]
    congr 1
    ring
  have hpi := Measure.pi_map_pi (μ := fun j : Fin I.card => gaussianReal 0 (v j))
    (f := fun _ (x : ℝ) => a*x) (fun _ => by fun_prop)
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [show (fun x => a • x) ∘ incrementCumsum I = incrementCumsum I ∘ (fun x => a • x) by ext x; simp]
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  change (Measure.pi (fun j => gaussianReal 0 (v j))).map (fun x i => a*x i) = _
  rw [hpi]
  congr 1
  funext j
  exact he j

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma median_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (b r : ℝ)
    (hb : (1/2 : ℝ≥0∞) ≤ μ {x | F x ≤ b} ∧ (1/2 : ℝ≥0∞) ≤ μ {x | b ≤ F x}) :
    (1/2 : ℝ≥0∞) ≤ (μ.map (fun x => F x/r)) (Set.Iic (b/r)) ∧
    (1/2 : ℝ≥0∞) ≤ (μ.map (fun x => F x/r)) (Set.Ici (b/r)) := by
  rw [Measure.map_apply (hF.div_const r) measurableSet_Iic,
    Measure.map_apply (hF.div_const r) measurableSet_Ici]
  rcases lt_trichotomy r 0 with hr|hr|hr
  · simpa only [Set.preimage,Set.mem_Iic,Set.mem_Ici,div_le_div_right_of_neg hr] using hb.symm
  · subst r
    simp
  · simpa only [Set.preimage,Set.mem_Iic,Set.mem_Ici,div_le_div_iff_of_pos_right hr] using hb

noncomputable def heightPathLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Ω → ℝ) (hF : ∀ k, Measurable (F k)) (r n T : ℝ) : ProbabilityMeasure C(unitInterval,ℝ) :=
  ⟨μ.map (fun x => heightPolygon (fun k => F k x) r n T),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_heightPolygon F hF r n T).aemeasurable).2 inferInstance⟩

lemma heightPathLaw_iid_difference {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Ω → ℝ) (hF : ∀ k, Measurable (F k)) (r n T : ℝ) :
    (((heightPathLaw μ F hF r n T : Measure C(unitInterval,ℝ)).prod
      (heightPathLaw μ F hF r n T)).map (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2)) =
      (μ.prod μ).map (fun p => heightPolygon (fun k => F k p.1-F k p.2) r n T) := by
  change ((μ.map _).prod (μ.map _)).map _ = _
  rw [Measure.map_prod_map _ _ (measurable_heightPolygon F hF _ _ _) (measurable_heightPolygon F hF _ _ _),
    Measure.map_map (by fun_prop) ((measurable_heightPolygon F hF _ _ _).prodMap (measurable_heightPolygon F hF _ _ _))]
  congr 1
  ext p t
  exact congrArg (fun g : C(unitInterval,ℝ) => g t) (heightPolygon_sub _ _ _ _ _).symm

lemma heightPathLaw_restrict {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Ω → ℝ) (hF : ∀ k, Measurable (F k)) (r n T S : ℝ)
    (hn : 0 ≤ n) (hT : 0 ≤ T) (hS : 0 ≤ S) (a : unitInterval) (ha : S*(a:ℝ) = T) :
    (heightPathLaw μ F hF r n S).map (pathRestrictScale a) =
      heightPathLaw μ F hF r n T := by
  apply Subtype.ext
  change (μ.map _).map _ = _
  rw [Measure.map_map (pathRestrictScale a).measurable (measurable_heightPolygon F hF _ _ _)]
  congr 1
  funext x
  exact heightPolygon_restrict _ _ _ _ _ hn hT hS a ha

theorem height_median_path_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → Ω → ℝ)
    (hF : ∀ k, Measurable (F k)) (b : ℕ → ℝ)
    (hb : ∀ k, (1/2 : ℝ≥0∞) ≤ μ {x | F k x ≤ b k} ∧ (1/2 : ℝ≥0∞) ≤ μ {x | b k ≤ F k x})
    (r n : ℕ → ℝ) (hn : ∀ i, 0 ≤ n i) (hnlim : Tendsto n atTop atTop) (c : ℝ)
    (hd : ∀ S : ℝ, 0 ≤ S → ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      Tendsto (fun i => ((heightPathLaw μ F hF (r i) (n i) S).prod
        (heightPathLaw μ F hF (r i) (n i) S)).map
          (fun pair => pair.1-pair.2)) atTop (𝓝 W) ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (S/c) I)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i x => heightPolygon (fun k => F k x-b k) (r i) (n i) T)
        atTop id (fun _ => μ) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (T/(2*c)) I := by
  let S := T+1
  have hS : 0 < S := by dsimp [S]; linarith
  let a : unitInterval := ⟨T/S,div_nonneg hT hS.le,(div_le_one hS).2 (by dsimp [S]; linarith)⟩
  have ha : (a:ℝ) < 1 := (div_lt_one hS).2 (by dsimp [S]; linarith)
  have haS : S*(a:ℝ) = T := by dsimp [a]; field_simp
  obtain ⟨WS,hWS,hWSf⟩ := hd S hS.le
  obtain ⟨WT,hWT,hWTf⟩ := hd T hT
  have hrestrict : WS.map (pathRestrictScale a) = WT := by
    have h := (ProbabilityMeasure.continuous_map (pathRestrictScale a).continuous).tendsto WS |>.comp hWS
    have he (i : ℕ) : (((heightPathLaw μ F hF (r i) (n i) S).prod
        (heightPathLaw μ F hF (r i) (n i) S)).map
          (fun pair => pair.1-pair.2)).map
        (pathRestrictScale a) =
      ((heightPathLaw μ F hF (r i) (n i) T).prod
        (heightPathLaw μ F hF (r i) (n i) T)).map
          (fun pair => pair.1-pair.2) := by
      apply Subtype.ext
      change (((heightPathLaw μ F hF (r i) (n i) S : Measure C(unitInterval,ℝ)).prod
        (heightPathLaw μ F hF (r i) (n i) S : Measure C(unitInterval,ℝ))).map
          (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2)).map (pathRestrictScale a) =
        ((heightPathLaw μ F hF (r i) (n i) T : Measure C(unitInterval,ℝ)).prod
          (heightPathLaw μ F hF (r i) (n i) T : Measure C(unitInterval,ℝ))).map
            (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2)
      rw [heightPathLaw_iid_difference,Measure.map_map (pathRestrictScale a).measurable (measurable_heightPolygon (fun k (p : Ω × Ω) => F k p.1-F k p.2) (fun k => ((hF k).comp measurable_fst).sub ((hF k).comp measurable_snd)) (r i) (n i) S),
        heightPathLaw_iid_difference]
      congr 1
      funext p
      exact heightPolygon_restrict _ _ _ _ _ (hn i) hT hS.le a haS
    exact tendsto_nhds_unique (by simpa only [Function.comp_def,he] using h) hWT
  let Q := fun i => heightPathLaw μ F hF (r i) (n i) S
  let B := fun i => heightPolygon b (r i) (n i) S
  let s := Real.sqrt (1/2)
  have hs : s^2 = 1/2 := Real.sq_sqrt (by norm_num)
  have hlim := path_grid_median_limit_from_iid_difference Q WS (S/c) hWSf hWS
    (fun i => S*n i) (hnlim.const_mul_atTop hS)
    (fun i => ?_) B (fun i => heightPolygon_gridLinear b _ _ _ (mul_nonneg hS.le (hn i)))
    (fun i j t ht => ?_) s hs a ha
  · let W := WT.map (fun path : C(unitInterval,ℝ) => s • path)
    refine ⟨W,⟨fun i => (measurable_heightPolygon (fun k x => F k x-b k)
      (fun k => (hF k).sub_const _) _ _ _).aemeasurable,measurable_id.aemeasurable,?_⟩,?_⟩
    · have he (i : ℕ) : (Q i).map (fun path => pathRestrictScale a (path-B i)) =
        (⟨μ.map (fun x => heightPolygon (fun k => F k x-b k) (r i) (n i) T),
          (Measure.isProbabilityMeasure_map_iff
            (measurable_heightPolygon _ (fun k => (hF k).sub_const _) _ _ _).aemeasurable).2 inferInstance⟩ :
            ProbabilityMeasure C(unitInterval,ℝ)) := by
        apply Subtype.ext
        change (μ.map _).map _ = _
        rw [Measure.map_map (by fun_prop) (measurable_heightPolygon F hF _ _ _)]
        congr 1
        funext x
        change pathRestrictScale a (heightPolygon (fun k => F k x) (r i) (n i) S-B i) = _
        rw [← heightPolygon_sub]
        exact heightPolygon_restrict _ _ _ _ _ (hn i) hT hS.le a haS
      have heW : WS.map (fun path => s • pathRestrictScale a path) = W := by
        rw [show W = (WS.map (pathRestrictScale a)).map
          (fun path : C(unitInterval,ℝ) => s • path) by rw [hrestrict]]
        apply Subtype.ext
        exact (Measure.map_map (by fun_prop) (pathRestrictScale a).measurable).symm
      change Tendsto _ atTop (𝓝 (W.map id))
      have hid : W.map id = W := by apply Subtype.ext; exact Measure.map_id
      rw [hid]
      simpa only [he,heW] using hlim
    · intro I
      change ((WT : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => s • g)).map _ = _
      rw [Measure.map_map (continuous_path_restrict I).measurable (by fun_prop)]
      have he : (fun g : C(unitInterval,ℝ) => I.restrict (s • g)) =
          (fun x : I → ℝ => s • x) ∘ (fun g : C(unitInterval,ℝ) => I.restrict g) := rfl
      change (WT : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict (s • g)) = _
      rw [he,← Measure.map_map (by fun_prop) (continuous_path_restrict I).measurable,hWTf,
        gaussianPathFiniteLaw_smul,hs]
      congr 1
      ring
  · change ∀ᵐ f ∂μ.map (fun x => heightPolygon (fun k => F k x) (r i) (n i) S), GridLinear (S*n i) f
    rw [ae_map_iff (measurable_heightPolygon F hF _ _ _).aemeasurable
      (isClosed_gridLinear _).measurableSet]
    exact ae_of_all _ (fun x => heightPolygon_gridLinear _ _ _ _ (mul_nonneg hS.le (hn i)))
  · change (1/2 : ℝ≥0∞) ≤ ((μ.map (fun x => heightPolygon (fun k => F k x) (r i) (n i) S)).map
        (fun g => g t)) (Set.Iic (B i t)) ∧
      (1/2 : ℝ≥0∞) ≤ ((μ.map (fun x => heightPolygon (fun k => F k x) (r i) (n i) S)).map
        (fun g => g t)) (Set.Ici (B i t))
    rw [Measure.map_map (continuous_eval_const t).measurable (measurable_heightPolygon F hF _ _ _)]
    have he : (fun g : C(unitInterval,ℝ) => g t) ∘ (fun x => heightPolygon (fun k => F k x) (r i) (n i) S) =
        fun x => F j x/r i := by
      funext x
      exact heightPolygon_grid _ _ _ _ (mul_nonneg hS.le (hn i)) j t ht
    rw [he,show B i t = b j/r i from heightPolygon_grid _ _ _ _ (mul_nonneg hS.le (hn i)) j t ht]
    exact median_div μ (F j) (hF j) (b j) (r i) (hb j)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
