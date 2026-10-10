import Mathlib
import OAI.Probability.Ballisticity.Estimates.ProductNormalJointPast

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def shrinkTime (n : ℕ) (t : unitInterval) : unitInterval :=
  ⟨((n:ℝ)+1)/((n:ℝ)+2)*(t:ℝ),by
    have hn : 0 ≤ ((n:ℝ)+1)/((n:ℝ)+2) := by positivity
    have hle : ((n:ℝ)+1)/((n:ℝ)+2) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    exact ⟨mul_nonneg hn t.property.1,(mul_le_mul_of_nonneg_left t.property.2 hn).trans (by simpa using hle)⟩⟩

lemma shrinkTime_lt_one (n : ℕ) (t : unitInterval) : (shrinkTime n t:ℝ) < 1 := by
  have hn : 0 ≤ ((n:ℝ)+1)/((n:ℝ)+2) := by positivity
  have hlt : ((n:ℝ)+1)/((n:ℝ)+2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_left t.property.2 hn).trans_lt (by simpa using hlt)

lemma shrinkTime_tendsto (t : unitInterval) : Tendsto (fun n => shrinkTime n t) atTop (𝓝 t) := by
  have hh : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  apply tendsto_subtype_rng.mpr
  have hc := ((tendsto_const_nhds (x := (1:ℝ))).sub hh).mul_const (t:ℝ)
  simp only [sub_zero,one_mul] at hc
  convert hc using 1
  funext n
  change ((n:ℝ)+1)/((n:ℝ)+2)*(t:ℝ)=(1-1/((n:ℝ)+2))*(t:ℝ)
  field_simp
  ring

lemma interior_pair_measure_ext (μ ν : Measure RealPathPair)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ I : Finset unitInterval, (∀ t ∈ I,(t:ℝ) < 1) →
      μ.map (pairRestricted I)=ν.map (pairRestricted I)) : μ=ν := by
  let e := TopologicalSpace.denseSeq unitInterval
  let f := fun j : ℕ × ℕ => shrinkTime j.2 (e j.1)
  let E := fun P : RealPathPair => fun j : ℕ × ℕ => (P.1 (f j),P.2 (f j))
  have hE : Continuous E := by fun_prop
  have hEinj : Function.Injective E := by
    intro P Q hPQ
    have hcoord (n : ℕ) : (P.1 (e n),P.2 (e n))=(Q.1 (e n),Q.2 (e n)) := by
      have hp : Tendsto (fun m => (P.1 (shrinkTime m (e n)),P.2 (shrinkTime m (e n)))) atTop
          (𝓝 (P.1 (e n),P.2 (e n))) :=
        ((P.1.continuous.prodMk P.2.continuous).tendsto (e n)).comp (shrinkTime_tendsto (e n))
      have hq : Tendsto (fun m => (Q.1 (shrinkTime m (e n)),Q.2 (shrinkTime m (e n)))) atTop
          (𝓝 (Q.1 (e n),Q.2 (e n))) :=
        ((Q.1.continuous.prodMk Q.2.continuous).tendsto (e n)).comp (shrinkTime_tendsto (e n))
      apply tendsto_nhds_unique hp
      apply hq.congr
      intro m
      exact (congrFun hPQ (n,m)).symm
    apply Prod.ext
    · apply ContinuousMap.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq unitInterval).equalizer P.1.continuous Q.1.continuous
        (funext fun n => congrArg Prod.fst (hcoord n))
    · apply ContinuousMap.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq unitInterval).equalizer P.2.continuous Q.2.continuous
        (funext fun n => congrArg Prod.snd (hcoord n))
  apply hE.measurableEmbedding hEinj |>.map_injective
  let P := fun J : Finset (ℕ × ℕ) => (μ.map E).map J.restrict
  have : ∀ J, IsFiniteMeasure (P J) := fun _ => inferInstance
  apply IsProjectiveLimit.unique (P := P) (fun _ => rfl)
  intro J
  let I := J.image f
  let g := fun z : I → ℝ × ℝ => fun j : J => z ⟨f j,Finset.mem_image_of_mem f j.property⟩
  have hg : Measurable g := by fun_prop
  have hm : Measurable (J.restrict : ((ℕ × ℕ) → ℝ × ℝ) → (J → ℝ × ℝ)) := by fun_prop
  change (ν.map E).map J.restrict=(μ.map E).map J.restrict
  rw [Measure.map_map hm hE.measurable,Measure.map_map hm hE.measurable]
  have he : J.restrict ∘ E=g ∘ pairRestricted I := rfl
  rw [he,← Measure.map_map hg (pairRestricted I).continuous.measurable,
    ← Measure.map_map hg (pairRestricted I).continuous.measurable,h I]
  intro t ht
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
  exact shrinkTime_lt_one j.2 (e j.1)

end DirectionalTransience

end

end

end OAI
