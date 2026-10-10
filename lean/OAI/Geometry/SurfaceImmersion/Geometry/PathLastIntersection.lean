import OAI.Geometry.SurfaceImmersion.Whitney.CompactArcLastIntersection
import OAI.Geometry.SurfaceImmersion.Geometry.InjectivePathConcatenation
import Mathlib.Topology.Subpath

namespace OAI

/-! Loop removal at the last intersection of two compact embedded arcs. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X] {x y z : X}

omit [T2Space X] in
lemma injective_subpath (γ : Path x y) (hi : Function.Injective γ)
    {s t : I} (hst : s ≠ t) : Function.Injective (γ.subpath s t) := by
  intro u v huv
  have h := congrArg (fun w : I => (w:ℝ)) (hi huv)
  change (1-(u:ℝ))*(s:ℝ)+(u:ℝ)*(t:ℝ) =
    (1-(v:ℝ))*(s:ℝ)+(v:ℝ)*(t:ℝ) at h
  have hst' : (s:ℝ) ≠ (t:ℝ) := fun he => hst (Subtype.ext he)
  apply Subtype.ext
  have hz : ((u:ℝ)-(v:ℝ))*((t:ℝ)-(s:ℝ)) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hz with huv0 | hts0
  · exact sub_eq_zero.mp huv0
  · exact False.elim (hst' (sub_eq_zero.mp hts0).symm)

lemma path_last_intersection (γ : Path x y) (δ : Path y z)
    (hend : z ∉ range γ) (hstart : x ∉ range δ) :
    ∃ s m : I, 0 < s ∧ m < 1 ∧ γ s = δ m ∧
      ∀ u v : I, u ≤ s → m < v → γ u ≠ δ v := by
  let K := δ ⁻¹' range γ
  have hK : IsCompact K :=
    ((isCompact_range γ.continuous).isClosed.preimage δ.continuous).isCompact
  have hne : K.Nonempty := ⟨0,by
    change δ 0 ∈ range γ
    exact ⟨1,by simp⟩⟩
  obtain ⟨m,hm,hmax⟩ := hK.exists_isGreatest hne
  obtain ⟨s,hsm⟩ := hm
  have hs : 0 < s := by
    refine lt_of_le_of_ne (unitInterval.nonneg s) ?_
    intro he
    apply hstart
    refine ⟨m,?_⟩
    simpa only [← he,Path.source] using hsm.symm
  have hm1 : m < 1 := by
    refine lt_of_le_of_ne (unitInterval.le_one m) ?_
    intro he
    apply hend
    exact ⟨s,by simpa only [he,Path.target] using hsm⟩
  refine ⟨s,m,hs,hm1,hsm,?_⟩
  intro u v _ hmv huv
  have hv : v ∈ K := ⟨u,huv⟩
  exact (not_le_of_gt hmv) (hmax hv)

theorem embedded_path_last_join (γ : Path x y) (δ : Path y z)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hend : z ∉ range γ) (hstart : x ∉ range δ) :
    ∃ s m : I, 0 < s ∧ m < 1 ∧ ∃ hsm : γ s = δ m,
      let P := ((γ.subpath 0 s).cast (show x = γ 0 from γ.source.symm) hsm.symm).trans
        ((δ.subpath m 1).cast rfl (show z = δ 1 from δ.target.symm))
      Function.Injective P ∧ range P ⊆ range γ ∪ range δ := by
  obtain ⟨s,m,hs,hm,hsm,hsep⟩ := path_last_intersection γ δ hend hstart
  refine ⟨s,m,hs,hm,hsm,?_,?_⟩
  · apply path_trans_injective
    · exact injective_subpath γ hγ (ne_of_lt hs)
    · exact injective_subpath δ hδ (ne_of_lt hm)
    · intro u v huv
      have hu : Icc.convexComb 0 s u ≤ s := by
        change (1-(u:ℝ)) * 0 + (u:ℝ)*(s:ℝ) ≤ (s:ℝ)
        nlinarith [unitInterval.le_one u,unitInterval.nonneg s]
      have hv : m ≤ Icc.convexComb m 1 v := by
        change (m:ℝ) ≤ (1-(v:ℝ))*(m:ℝ)+(v:ℝ)*1
        nlinarith [unitInterval.nonneg v,unitInterval.le_one m]
      have hev : Icc.convexComb m 1 v = m := by
        by_contra hn
        exact hsep _ _ hu (lt_of_le_of_ne hv (Ne.symm hn)) huv
      have he0 : v = 0 := by
        have he := congrArg (fun w : I => (w:ℝ)) hev
        change (1-(v:ℝ))*(m:ℝ)+(v:ℝ)*1 = (m:ℝ) at he
        apply Subtype.ext
        change (v:ℝ) = 0
        have hm' : (m:ℝ) < 1 := hm
        nlinarith
      have he1 : u = 1 := by
        have heγ : (γ.subpath 0 s) u = (γ.subpath 0 s) 1 := by
          have huv' : γ (Icc.convexComb 0 s u) = δ (Icc.convexComb m 1 v) := huv
          rw [he0,Icc.convexComb_zero] at huv'
          change γ (Icc.convexComb 0 s u) = γ (Icc.convexComb 0 s 1)
          rw [Icc.convexComb_one]
          exact huv'.trans hsm.symm
        exact injective_subpath γ hγ (ne_of_lt hs) heγ
      exact ⟨he1,he0⟩
  · rw [Path.trans_range]
    apply union_subset
    · intro w hw
      change w ∈ range (γ.subpath 0 s) at hw
      rw [Path.range_subpath] at hw
      exact Or.inl (image_subset_range _ _ hw)
    · intro w hw
      change w ∈ range (δ.subpath m 1) at hw
      rw [Path.range_subpath] at hw
      exact Or.inr (image_subset_range _ _ hw)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
