import OAI.Analysis.CircleDomains.Selection.RegularLevelFlow
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-! Complete tangent trajectories on a compact relatively clopen piece of
an actual regular scalar level. This includes a prescribed Jordan boundary
without requiring the other components of its defining level to be bounded. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

structure CompactRegularPieceFlow (f : ℂ → ℝ) (a : ℝ) (K : Set ℂ) where
  field : ℂ → ℂ
  lipschitzConstant : ℝ≥0
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field
  lipschitz : LipschitzWith lipschitzConstant field
  tangent : ∀ z, (fderiv ℝ f z) (field z) = 0
  in_level : K ⊆ {z | f z = a}
  trajectory : K → ℝ → ℂ
  initial : ∀ z, trajectory z 0 = z.val
  equation : ∀ z t, HasDerivAt (trajectory z) (field (trajectory z t)) t
  scalar : ∀ z t, f (trajectory z t) = a
  member : ∀ z t, trajectory z t ∈ K
  trajectory_smooth : ∀ z, ContDiff ℝ ∞ (trajectory z)
  regular : ∀ z t, deriv (trajectory z) t ≠ 0

lemma exists_compact_regular_piece_flow {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a : ℝ} (ha : IsPlanarRegularValue f a) {K : Set ℂ} (hc : IsCompact K)
    (hK : K ⊆ {z | f z = a}) (ho : IsOpen {z : {w // f w = a} | z.val ∈ K}) :
    Nonempty (CompactRegularPieceFlow f a K) := by
  obtain ⟨V,L,hV,hVc,hVL,ht,hne⟩ := exists_compact_level_tangent hf hc (fun z hz => ha z (hK hz))
  have he (z : K) : ∃ γ : ℝ → ℂ, γ 0 = z.val ∧ ∀ t, HasDerivAt γ (V (γ t)) t :=
    compact_vector_field_global_curve hV hVc z.val
  choose γ hγ0 hγ using he
  have hs (z : K) := smooth_integral_curve hV (hγ z)
  have hscalar (z : K) (t : ℝ) : f (γ z t) = a := by
    calc
      f (γ z t) = f (γ z 0) := integral_curve_preserves_scalar hf ht (hγ z) t 0
      _ = a := by rw [hγ0]; exact hK z.property
  have hm (z : K) (t : ℝ) : γ z t ∈ K := by
    let g : ℝ → {w // f w = a} := fun s => ⟨γ z s,hscalar z s⟩
    have hg : Continuous g := (hs z).continuous.subtype_mk _
    have hcl : IsClopen {w : {y // f y = a} | w.val ∈ K} :=
      ⟨hc.isClosed.preimage continuous_subtype_val,ho⟩
    have hz0 : g 0 ∈ {w : {y // f y = a} | w.val ∈ K} := by
      change γ z 0 ∈ K
      rw [hγ0]
      exact z.property
    exact (isPreconnected_range hg).subset_isClopen hcl ⟨g 0,mem_range_self 0,hz0⟩
      (mem_range_self t)
  refine ⟨⟨V,L,hV,hVc,hVL,ht,hK,γ,hγ0,hγ,hscalar,hm,hs,?_⟩⟩
  intro z t
  rw [(hγ z t).deriv]
  exact hne _ (hm z t)

end CircleDomainRigidity

end

end OAI
