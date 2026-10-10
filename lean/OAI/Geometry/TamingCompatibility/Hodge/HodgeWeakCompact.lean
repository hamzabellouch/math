import Mathlib

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.WeakHeat
open Set Filter Topology
open scoped Topology RealInnerProductSpace
variable {H T I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [TopologicalSpace T]

lemma inner_continuousOn_of_dense (D : I → H) (hD : DenseRange D)
    (U : T → H) (S : Set T) {C : ℝ} (hC : 0 ≤ C) (hU : ∀ t ∈ S, ‖U t‖ ≤ C)
    (hweak : ∀ a, ContinuousOn (fun t => ⟪U t,D a⟫) S) (v : H) :
    ContinuousOn (fun t => ⟪U t,v⟫) S := by
  intro t ht
  apply Metric.continuousWithinAt_iff'.mpr
  intro ε hε
  have hp : 0 < C+1 := by linarith
  obtain ⟨a,ha⟩ := hD.exists_dist_lt v (div_pos hε (mul_pos (show (0:ℝ)<4 by norm_num) hp))
  have ha' : ‖v-D a‖ < ε/(4*(C+1)) := by simpa only [dist_eq_norm] using ha
  have herr : C*‖v-D a‖ < ε/4 := by
    calc
      _ ≤ (C+1)*‖v-D a‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C+1)*(ε/(4*(C+1))) := mul_lt_mul_of_pos_left ha' hp
      _ = _ := by field_simp
  have he (s : T) (hs : s ∈ S) : dist ⟪U s,v⟫ ⟪U s,D a⟫ < ε/4 := by
    rw [Real.dist_eq,← inner_sub_right]
    exact ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hU s hs) (norm_nonneg _))).trans_lt herr
  have hh := Metric.continuousWithinAt_iff'.mp (hweak a t ht) (ε/2) (by linarith)
  filter_upwards [hh,self_mem_nhdsWithin] with s hs hsS
  have hd := dist_triangle4 ⟪U s,v⟫ ⟪U s,D a⟫ ⟪U t,D a⟫ ⟪U t,v⟫
  have he₁ := he s hsS
  have he₂ := he t ht
  rw [dist_comm ⟪U t,D a⟫ ⟪U t,v⟫] at hd
  linarith

lemma continuousOn_of_weak_compact_range (U : T → H) (S : Set T)
    (K : Set H) (hK : IsCompact K) (hUK : ∀ t ∈ S, U t ∈ K)
    (hweak : ∀ v : H, ContinuousOn (fun t => ⟪U t,v⟫) S) : ContinuousOn U S := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : K → H → ℝ := fun x v => ⟪x.val,v⟫
  have hF : Continuous F := continuous_pi (fun _ => continuous_subtype_val.inner continuous_const)
  have hFi : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    apply ext_inner_right ℝ
    intro v
    exact congrFun h v
  have hFe := (hF.isClosedEmbedding hFi).isEmbedding
  let V : S → K := fun t => ⟨U t.val,hUK t.val t.property⟩
  have hV : Continuous V := hFe.continuous_iff.mpr (continuous_pi (fun v =>
    (continuousOn_iff_continuous_domRestrict.mp (hweak v))))
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hV)

lemma compact_symmetric_continuousOn (R : H →L[ℝ] H) (hR : IsCompactOperator R)
    (hRs : ∀ u v, ⟪R u,v⟫ = ⟪u,R v⟫)
    (D : I → H) (hD : DenseRange D) (U : T → H) (S : Set T)
    {C : ℝ} (hC : 0 ≤ C) (hU : ∀ t ∈ S, ‖U t‖ ≤ C)
    (hweak : ∀ a, ContinuousOn (fun t => ⟪U t,D a⟫) S) :
    ContinuousOn (fun t => R (U t)) S := by
  obtain ⟨K,hK,hRK⟩ := hR.image_closedBall_subset_compact C
  apply continuousOn_of_weak_compact_range _ S K hK
  · intro t ht
    exact hRK ⟨U t,by simpa only [Metric.mem_closedBall,dist_zero_right] using hU t ht,rfl⟩
  · intro v
    simp_rw [hRs]
    exact inner_continuousOn_of_dense D hD U S hC hU hweak (R v)

end TamingCompatibility.GeometricHilbert.WeakHeat

end
end

end

end OAI
