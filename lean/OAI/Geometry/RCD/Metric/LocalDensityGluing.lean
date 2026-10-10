import OAI.Geometry.RCD.Metric.MetricLimitAbsoluteContinuity
import Mathlib.Topology.LocallyConstant.Basic

namespace OAI

/-! # Gluing almost-everywhere local constants on a Euclidean ball -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem ae_constants_eq_on_open_overlap {n : ℕ} (f : Euclidean n → ℝ)
    {A B : Set (Euclidean n)} (hA : IsOpen A) (hB : IsOpen B) (hAB : (A ∩ B).Nonempty)
    {a b : ℝ} (ha : ∀ᵐ x ∂volume.restrict A, f x=a)
    (hb : ∀ᵐ x ∂volume.restrict B, f x=b) : a=b := by
  by_contra hne
  have hnull : ∀ᵐ x ∂(volume : Measure (Euclidean n)), x ∉ A ∩ B := by
    filter_upwards [(ae_restrict_iff' hA.measurableSet).mp ha,
      (ae_restrict_iff' hB.measurableSet).mp hb] with x hxa hxb hx
    exact hne ((hxa hx.1).symm.trans (hxb hx.2))
  have hz : volume (A ∩ B)=0 := by
    simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.mp hnull
  exact ((hA.inter hB).measure_pos volume hAB).ne' hz

theorem ae_constant_on_ball_of_locally_constant {n : ℕ} {S : ℝ} (hS : 0 < S)
    (f : Euclidean n → ℝ)
    (hlocal : ∀ z ∈ ball (0 : Euclidean n) S, ∃ R : ℝ, 0 < R ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∀ᵐ x ∂volume.restrict (ball z R), f x=c) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x ∂volume.restrict (ball (0 : Euclidean n) S), f x=c := by
  classical
  let Ω := ball (0 : Euclidean n) S
  have hl (z : Ω) := hlocal z z.2
  choose R hR c hc0 hc using hl
  have hg : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_exists_open c).mpr
    intro x
    refine ⟨Subtype.val ⁻¹' ball (x : Euclidean n) (R x),
      isOpen_ball.preimage continuous_subtype_val,mem_ball_self (hR x),?_⟩
    intro y hy
    exact ae_constants_eq_on_open_overlap f isOpen_ball isOpen_ball
      ⟨(y : Euclidean n),mem_ball_self (hR y),hy⟩ (hc y) (hc x)
  let : PreconnectedSpace Ω := Subtype.preconnectedSpace (convex_ball (0 : Euclidean n) S).isPreconnected
  let x0 : Ω := ⟨0,mem_ball_self hS⟩
  have hconst (x : Ω) : c x=c x0 := hg.apply_eq_of_preconnectedSpace x x0
  refine ⟨c x0,hc0 x0,?_⟩
  let O := fun x : Ω => ball (x : Euclidean n) (R x)
  let A := {y : Euclidean n | f y ≠ c x0}
  obtain ⟨T,hT,hcover⟩ := TopologicalSpace.isOpen_iUnion_countable O (fun _ => isOpen_ball)
  have hnull (x : Ω) : volume (A ∩ O x)=0 := by
    have he : ∀ᵐ y ∂volume.restrict (O x), f y=c x0 :=
      (hc x).mono (fun y hy => hy.trans (hconst x))
    have hh := ae_iff.mp he
    change (volume.restrict (O x)) A=0 at hh
    rwa [Measure.restrict_apply' measurableSet_ball] at hh
  have hsub : A ∩ Ω ⊆ ⋃ x ∈ T, A ∩ O x := by
    intro y hy
    have hyO : y ∈ ⋃ x ∈ T, O x := by
      rw [hcover]
      exact mem_iUnion_of_mem ⟨y,hy.2⟩ (mem_ball_self (hR ⟨y,hy.2⟩))
    obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp hyO
    exact mem_iUnion₂.mpr ⟨x,hx,hy.1,hyx⟩
  apply ae_iff.mpr
  change (volume.restrict Ω) A=0
  rw [Measure.restrict_apply' measurableSet_ball]
  exact measure_mono_null hsub ((measure_biUnion_null_iff hT).mpr (fun x _ => hnull x))

end RegularPointCoordinates

end

end OAI
