import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

def leftMeshTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌊((n+1:ℕ):ℝ)*(t:ℝ)⌋₊:ℝ≥0)/((n+1:ℕ):ℝ≥0)

lemma leftMeshTime_le (n : ℕ) (t : ℝ≥0) : leftMeshTime n t ≤ t := by
  apply NNReal.coe_le_coe.mp
  simp only [leftMeshTime,NNReal.coe_div,NNReal.coe_natCast]
  apply (div_le_iff₀ (show (0:ℝ)<((n+1:ℕ):ℝ) by positivity)).mpr
  have hh := Nat.floor_le (mul_nonneg (Nat.cast_nonneg (α := ℝ) (n+1)) t.coe_nonneg)
  nlinarith

lemma leftMeshTime_gt (n : ℕ) (t : ℝ≥0) : (t:ℝ)-1/((n+1:ℕ):ℝ) < leftMeshTime n t := by
  simp only [leftMeshTime,NNReal.coe_div,NNReal.coe_natCast]
  have hh := Nat.lt_floor_add_one (((n+1:ℕ):ℝ)*(t:ℝ))
  apply (lt_div_iff₀ (show (0:ℝ)<((n+1:ℕ):ℝ) by positivity)).mpr
  have he : ((t:ℝ)-1/((n+1:ℕ):ℝ))*((n+1:ℕ):ℝ) = ((n+1:ℕ):ℝ)*(t:ℝ)-1 := by
    field_simp
  rw [he]
  linarith

lemma leftMeshTime_tendsto (t : ℝ≥0) : Tendsto (fun n => leftMeshTime n t) atTop (𝓝 t) := by
  apply tendsto_subtype_rng.mpr
  have hl : Tendsto (fun n : ℕ => (t:ℝ)-1/((n+1:ℕ):ℝ)) atTop (𝓝 (t:ℝ)) := by
    simpa only [sub_zero,Nat.cast_add,Nat.cast_one] using
      tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (a := (t:ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (fun n => (leftMeshTime_gt n t).le) (fun n => leftMeshTime_le n t)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma leftMesh_progressive (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : Adapted ℱ B) (n : ℕ) : IsProgressive ℱ (fun t ξ => B (leftMeshTime n t) ξ) := by
  intro s
  have hm (k : ℕ) : Measurable[ℱ s] (B (min ((k:ℝ≥0)/((n+1:ℕ):ℝ≥0)) s)) :=
    (hB _).mono (ℱ.mono (min_le_right _ _)) le_rfl
  let : MeasurableSpace Ω := ℱ s
  have hprod : Measurable[(inferInstance : MeasurableSpace ℕ).prod (ℱ s)]
      (fun p : ℕ × Ω => B (min ((p.1:ℝ≥0)/((n+1:ℕ):ℝ≥0)) s) p.2) := by
    let : MeasurableSpace Ω := ℱ s
    exact measurable_from_prod_countable_right hm
  have ht : Measurable[(Subtype.instMeasurableSpace).prod (ℱ s)]
      (fun p : Set.Iic s × Ω => ((p.1:ℝ≥0):ℝ)) := by fun_prop
  have hi : Measurable[(Subtype.instMeasurableSpace).prod (ℱ s)]
      (fun p : Set.Iic s × Ω => ⌊((n+1:ℕ):ℝ)*((p.1:ℝ≥0):ℝ)⌋₊) :=
    (measurable_const.mul ht).nat_floor
  have hh := hprod.comp (hi.prodMk measurable_snd)
  have he : (fun p : Set.Iic s × Ω => B (leftMeshTime n p.1) p.2) =
      (fun p : ℕ × Ω => B (min ((p.1:ℝ≥0)/((n+1:ℕ):ℝ≥0)) s) p.2) ∘
        (fun p : Set.Iic s × Ω => (⌊((n+1:ℕ):ℝ)*((p.1:ℝ≥0):ℝ)⌋₊,p.2)) := by
    funext p
    have hle := (leftMeshTime_le n (p.1:ℝ≥0)).trans p.1.property
    dsimp only [leftMeshTime] at hle
    simp only [Function.comp_def,leftMeshTime,min_eq_left hle]
  rw [he]
  exact hh

def BrownianSystem.progressiveVersion (W : BrownianSystem Ω) (t : ℝ≥0) (ξ : Ω) : ℝ :=
  atTop.limUnder (fun n => W.B (leftMeshTime n t) ξ)

lemma BrownianSystem.progressiveVersion_progressive (W : BrownianSystem Ω) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      W.progressiveVersion := by
  intro s
  let ℱ := Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)
  have hn : Adapted ℱ W.B := fun t =>
    (Filtration.stronglyAdapted_natural (fun t => (W.measurable t).stronglyMeasurable) t).measurable
  let B : ℝ≥0 → Ω → ℝ := W.B
  have hm (n : ℕ) : StronglyMeasurable[(Subtype.instMeasurableSpace).prod (ℱ s)]
      (fun p : Set.Iic s × Ω => B (leftMeshTime n p.1) p.2) :=
    (leftMesh_progressive ℱ hn n s).stronglyMeasurable
  let : MeasurableSpace Ω := ℱ s
  exact (StronglyMeasurable.limUnder hm).measurable

lemma BrownianSystem.progressiveVersion_eq (W : BrownianSystem Ω) {ξ : Ω}
    (hc : Continuous (fun t => W.B t ξ)) (t : ℝ≥0) : W.progressiveVersion t ξ = W.B t ξ :=
  ((hc.tendsto t).comp (leftMeshTime_tendsto t)).limUnder_eq

lemma BrownianSystem.progressiveVersion_indistinguishable (W : BrownianSystem Ω) :
    ∀ᵐ ξ ∂W.law, ∀ t, W.progressiveVersion t ξ = W.B t ξ := by
  filter_upwards [W.brownian.cont] with ξ hξ
  exact W.progressiveVersion_eq hξ

def BrownianSystem.driver (W : BrownianSystem Ω) (t : ℝ≥0) (ξ : Ω) : ℝ :=
  W.progressiveVersion t ξ-W.progressiveVersion 0 ξ

lemma BrownianSystem.driver_progressive (W : BrownianSystem Ω) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)) W.driver := by
  intro s
  have hm := W.progressiveVersion_progressive.adapted 0
  have hm' := hm.mono ((Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)).mono
    (show (0:ℝ≥0) ≤ s by positivity)) le_rfl
  exact (W.progressiveVersion_progressive s).sub (hm'.comp measurable_snd)

lemma BrownianSystem.driver_zero (W : BrownianSystem Ω) (ξ : Ω) : W.driver 0 ξ = 0 := sub_self _

lemma BrownianSystem.driver_indistinguishable (W : BrownianSystem Ω) :
    ∀ᵐ ξ ∂W.law, ∀ t, W.driver t ξ = W.B t ξ := by
  filter_upwards [W.progressiveVersion_indistinguishable,W.brownian.eval_zero_ae_eq_zero] with ξ hh h₀ t
  simp only [BrownianSystem.driver,hh,h₀,sub_zero]

lemma BrownianSystem.driver_continuous (W : BrownianSystem Ω) :
    ∀ᵐ ξ ∂W.law, Continuous (fun t => W.driver t ξ) := by
  filter_upwards [W.driver_indistinguishable,W.brownian.cont] with ξ hh hc
  simpa only [hh] using hc

end ZeroTemperatureSK

end
end

end OAI
