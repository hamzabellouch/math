import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Sequences

namespace OAI

/-! A completely metrizable subspace of a metrizable space is a G-delta.
The open sets below bound the diameter of their inverse images. A sequence
approaching a point in all these sets is Cauchy in the complete source metric. -/
open Set Function Filter Topology TopologicalSpace
noncomputable section
namespace CircleDomainRigidity

lemma isGDelta_range_embedding
    {A B : Type*} [TopologicalSpace A] [IsCompletelyMetrizableSpace A]
    [TopologicalSpace B] [MetrizableSpace B] {f : A → B} (hf : IsEmbedding f) :
    IsGδ (range f) := by
  let := upgradeIsCompletelyMetrizable A
  let : MetricSpace B := metrizableSpaceMetric B
  let U : ℕ → Set B := fun n => ⋃₀ {V : Set B | IsOpen V ∧
    ∀ a b : A, f a ∈ V → f b ∈ V → dist a b < 1 / (n + 1 : ℝ)}
  have hU : ∀ n, IsOpen (U n) := fun n => isOpen_sUnion fun V hV => hV.1
  have hsub : ∀ n, range f ⊆ U n := by
    intro n y hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨V, hVo, hV⟩ := hf.isInducing.isOpen_iff.mp
      (Metric.isOpen_ball (x := x) (ε := (1 / (n + 1 : ℝ)) / 2))
    refine mem_sUnion.mpr ⟨V, ⟨hVo, ?_⟩, ?_⟩
    · intro a b ha hb
      have ha' : dist a x < (1 / (n + 1 : ℝ)) / 2 := by
        have haa : a ∈ f ⁻¹' V := ha
        rw [hV] at haa
        exact haa
      have hb' : dist b x < (1 / (n + 1 : ℝ)) / 2 := by
        have hbb : b ∈ f ⁻¹' V := hb
        rw [hV] at hbb
        exact hbb
      linarith [dist_triangle_right a b x]
    · have hx : x ∈ Metric.ball x ((1 / (n + 1 : ℝ)) / 2) :=
        Metric.mem_ball_self (by positivity)
      rwa [← hV] at hx
  have heq : range f = closure (range f) ∩ ⋂ n, U n := by
    apply Subset.antisymm
    · exact fun y hy => ⟨subset_closure hy, mem_iInter.mpr (fun n => hsub n hy)⟩
    · intro y hy
      obtain ⟨ys, hys, hlim⟩ := mem_closure_iff_seq_limit.mp hy.1
      choose xs hxs using hys
      have hflim : Tendsto (fun n => f (xs n)) atTop (𝓝 y) := by
        simpa only [hxs] using hlim
      have hc : CauchySeq xs := Metric.cauchySeq_iff.mpr (by
        intro ε hε
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        obtain ⟨V, hV, hyV⟩ := mem_sUnion.mp (mem_iInter.mp hy.2 n)
        obtain ⟨N, hN⟩ := eventually_atTop.mp (hflim (hV.1.mem_nhds hyV))
        exact ⟨N, fun i hi j hj => (hV.2 _ _ (hN i hi) (hN j hj)).trans hn⟩)
      obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
      exact ⟨x, tendsto_nhds_unique (hf.continuous.tendsto x |>.comp hx) hflim⟩
  rw [heq]
  exact isClosed_closure.isGδ.inter (IsGδ.iInter_of_isOpen hU)

end CircleDomainRigidity

end

end OAI
