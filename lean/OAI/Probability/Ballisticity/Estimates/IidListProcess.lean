import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicyAlignment

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma iid_list_hasLaw {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : PMF G) (X : ℕ → Ω → G)
    (hX : ∀ k, Measurable (X k)) (hLaw : ∀ k, HasLaw (X k) p.toMeasure μ)
    (hind : iIndepFun X μ) (n : ℕ) :
    HasLaw (fun ω => List.ofFn (fun i : Fin n => X i ω)) (iidListPMF p n).toMeasure μ := by
  have hfin := hind.precomp (f := X) (g := fun i : Fin n => (i:ℕ)) Fin.val_injective
  have hm : Measurable (fun ω => fun i : Fin n => X i ω) := Measurable.of_eval (fun index => hX index)
  have he := (iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin n => (hX i).aemeasurable)).mp hfin
  simp only [(hLaw _).map_eq] at he
  constructor
  · exact ((measurable_of_countable List.ofFn).comp hm).aemeasurable
  · rw [iidListPMF,← PMF.toMeasure_map _ _ (measurable_of_countable List.ofFn),Measure.toPMF_toMeasure,
      ← he,Measure.map_map (measurable_of_countable List.ofFn) hm]
    rfl

lemma partialSumMax_initial_congr (X Y : ℕ → ℝ) (n : ℕ) (h : ∀ k < n, X k=Y k) :
    partialSumMax X n = partialSumMax Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [partialSumMax]
    rw [ih (fun k hk => h k (by omega))]
    congr 1
    congr 1
    exact Finset.sum_congr rfl (fun k hk => h k (Finset.mem_range.mp hk))

noncomputable def listCenteredMax {G : Type*} (F : G → ℝ) (c : ℝ) (w : List G) : ℝ :=
  partialSumMax (fun k => if h : k < w.length then F (w.get ⟨k,h⟩)-c else 0) w.length

lemma listCenteredMax_ofFn {G : Type*} (F : G → ℝ) (c : ℝ) (X : ℕ → G) (n : ℕ) :
    listCenteredMax F c (List.ofFn (fun i : Fin n => X i)) =
      partialSumMax (fun k => F (X k)-c) n := by
  unfold listCenteredMax
  simp only [List.length_ofFn]
  apply partialSumMax_initial_congr
  intro k hk
  simp only [dite_eq_left hk,List.get_ofFn,Fin.val_cast]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def symmetricClip (w : ℝ≥0) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => max (-(w:ℝ)) (min (w:ℝ) z),by fun_prop⟩ (2*w)
    (fun x y => by
      rw [Real.dist_eq]
      change |max (-(w:ℝ)) (min (w:ℝ) x)-max (-(w:ℝ)) (min (w:ℝ) y)| ≤ 2*(w:ℝ)
      apply abs_le.mpr
      have hw : -(w:ℝ) ≤ (w:ℝ) := by linarith [w.coe_nonneg]
      have hx0 := le_max_left (-(w:ℝ)) (min (w:ℝ) x)
      have hy0 := le_max_left (-(w:ℝ)) (min (w:ℝ) y)
      have hx1 : max (-(w:ℝ)) (min (w:ℝ) x) ≤ w := max_le hw (min_le_left _ _)
      have hy1 : max (-(w:ℝ)) (min (w:ℝ) y) ≤ w := max_le hw (min_le_left _ _)
      constructor <;> linarith)

lemma symmetricClip_apply (w : ℝ≥0) (z : ℝ) : symmetricClip w z = max (-(w:ℝ)) (min (w:ℝ) z) := rfl

lemma symmetricClip_bound (w : ℝ≥0) (z : ℝ) : |symmetricClip w z| ≤ w := by
  rw [symmetricClip_apply,abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [w.coe_nonneg]) (min_le_left _ _)⟩

lemma symmetricClip_neg (w : ℝ≥0) (z : ℝ) : symmetricClip w (-z) = -symmetricClip w z := by
  simp only [symmetricClip_apply]
  have hw : -(w:ℝ) ≤ (w:ℝ) := by linarith [w.coe_nonneg]
  by_cases hlo : z ≤ -(w:ℝ)
  · rw [min_eq_right (hlo.trans hw),max_eq_left hlo,
      min_eq_left (by linarith : (w:ℝ) ≤ -z),max_eq_right hw]
    ring
  · by_cases hhi : (w:ℝ) ≤ z
    · rw [min_eq_left hhi,max_eq_right hw,
        min_eq_right (by linarith : -z ≤ (w:ℝ)),
        max_eq_left (by linarith : -z ≤ -(w:ℝ))]
    · rw [min_eq_right (le_of_not_ge hhi),max_eq_right (le_of_not_ge hlo),
        min_eq_right (by linarith : -z ≤ (w:ℝ)),max_eq_right (by linarith : -(w:ℝ) ≤ -z)]

lemma symmetricClip_uniformContinuous (w : ℝ≥0) : UniformContinuous (symmetricClip w) := by
  have h : LipschitzWith 1 (fun z : ℝ => max (-(w:ℝ)) (min (w:ℝ) z)) := by
    convert (LipschitzWith.const (-(w:ℝ))).max ((LipschitzWith.const (w:ℝ)).min LipschitzWith.id) using 1
    · norm_num
    · rfl
  exact h.uniformContinuous

lemma symmetricClip_gaussian_integral (w : ℝ≥0) (v : ℝ≥0) :
    (∫ z, symmetricClip w z ∂gaussianReal 0 v) = 0 := by
  have hm : (gaussianReal 0 v).map (fun z => -z) = gaussianReal 0 v := by
    simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := v))
  have hi : (∫ z, symmetricClip w (-z) ∂gaussianReal 0 v) = ∫ z, symmetricClip w z ∂gaussianReal 0 v := by
    rw [← integral_map (by fun_prop : Measurable (fun z : ℝ => -z)).aemeasurable
      (symmetricClip w).continuous.aestronglyMeasurable,hm]
  simp only [symmetricClip_neg,integral_neg] at hi
  linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma symmetricClip_eq_self (w : ℝ≥0) {z : ℝ} (hz : |z|≤w) : symmetricClip w z=z := by
  obtain ⟨hl,hr⟩ := abs_le.mp hz
  simp only [symmetricClip_apply,min_eq_right hr,max_eq_right hl]

lemma symmetricClip_nat_eventually (z : ℝ) : ∀ᶠ n : ℕ in atTop, symmetricClip n z=z := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop |z|] with n hn
  exact symmetricClip_eq_self n hn

noncomputable def clippedBCF (F : ℝ →ᵇ ℝ) (w : ℝ≥0) : ℝ →ᵇ ℝ :=
  F.compContinuous (symmetricClip w).toContinuousMap

lemma clippedBCF_apply (F : ℝ →ᵇ ℝ) (w : ℝ≥0) (z : ℝ) : clippedBCF F w z=F (symmetricClip w z) := rfl

lemma clippedBCF_uniformContinuous (F : ℝ →ᵇ ℝ) (w : ℝ≥0) : UniformContinuous (clippedBCF F w) := by
  have hF := isCompact_Icc.uniformContinuousOn_of_continuous (F.continuous.continuousOn (s := Set.Icc (-(w:ℝ)) w))
  have h := hF.comp (symmetricClip_uniformContinuous w).uniformContinuousOn (s := Set.univ) (by
    intro z hz
    exact abs_le.mp (symmetricClip_bound w z))
  exact uniformContinuousOn_univ.mp h

lemma clippedBCF_norm_bound (F : ℝ →ᵇ ℝ) (w : ℝ≥0) (z : ℝ) : ‖clippedBCF F w z‖≤‖F‖ :=
  F.norm_coe_le_norm _

lemma clippedBCF_nat_tendsto (F : ℝ →ᵇ ℝ) (z : ℝ) :
    Tendsto (fun n : ℕ => clippedBCF F n z) atTop (𝓝 (F z)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [symmetricClip_nat_eventually z] with n hn
  simp only [clippedBCF_apply,hn]

lemma integral_clippedBCF_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (F : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, clippedBCF F n (X ω) ∂μ) atTop (𝓝 (∫ ω, F (X ω) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (clippedBCF F n).continuous.measurable.comp hX |>.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all μ (fun ω => clippedBCF_norm_bound F n (X ω))
  · exact ae_of_all μ (fun ω => clippedBCF_nat_tendsto F (X ω))

lemma integral_weighted_clippedBCF_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X A : Ω → ℝ) (hX : Measurable X) (hA : Measurable A)
    (C : ℝ) (hC : 0≤C) (hAb : ∀ ω, ‖A ω‖≤C) (F : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, A ω*clippedBCF F n (X ω) ∂μ) atTop
      (𝓝 (∫ ω, A ω*F (X ω) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => C*‖F‖)
  · intro n
    exact (hA.mul ((clippedBCF F n).continuous.measurable.comp hX)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply ae_of_all
    intro ω
    rw [norm_mul]
    exact mul_le_mul (hAb ω) (clippedBCF_norm_bound F n (X ω)) (norm_nonneg _) hC
  · exact ae_of_all μ (fun ω => tendsto_const_nhds.mul (clippedBCF_nat_tendsto F (X ω)))

end DirectionalTransience

end

end

end OAI
