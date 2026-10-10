import OAI.Analysis.CircleDomains.Topology.CompactVectorFieldFlow

namespace OAI

/-! Complete smooth nonstationary trajectories on compact regular levels
of the actual defining planar scalar function. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma smooth_integral_curve {V : ℂ → ℂ} (hV : ContDiff ℝ ∞ V)
    {γ : ℝ → ℂ} (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) : ContDiff ℝ ∞ γ := by
  have hd : Differentiable ℝ γ := fun t => (hγ t).differentiableAt
  have he : deriv γ = V ∘ γ := funext fun t => (hγ t).deriv
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
    refine ⟨hd,by simp,?_⟩
    rw [he]
    exact (hV.of_le (by simp)).comp ih

structure CompactRegularLevelFlow (f : ℂ → ℝ) (a : ℝ) where
  field : ℂ → ℂ
  lipschitzConstant : ℝ≥0
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field
  lipschitz : LipschitzWith lipschitzConstant field
  tangent : ∀ z, (fderiv ℝ f z) (field z) = 0
  trajectory : {z // f z = a} → ℝ → ℂ
  initial : ∀ z, trajectory z 0 = z.val
  equation : ∀ z t, HasDerivAt (trajectory z) (field (trajectory z t)) t
  scalar : ∀ z t, f (trajectory z t) = a
  trajectory_smooth : ∀ z, ContDiff ℝ ∞ (trajectory z)
  regular : ∀ z t, deriv (trajectory z) t ≠ 0

lemma exists_compact_regular_level_flow {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a : ℝ} (ha : IsPlanarRegularValue f a) (hc : IsCompact {z | f z = a}) :
    Nonempty (CompactRegularLevelFlow f a) := by
  obtain ⟨V,L,hV,hVc,hVL,ht,hne⟩ := exists_compact_level_tangent hf hc (fun z hz => ha z hz)
  have he (z : {z // f z = a}) : ∃ γ : ℝ → ℂ, γ 0 = z.val ∧ ∀ t, HasDerivAt γ (V (γ t)) t :=
    compact_vector_field_global_curve hV hVc z.val
  choose γ hγ0 hγ using he
  have hscalar (z : {z // f z = a}) (t : ℝ) : f (γ z t) = a := by
    calc
      f (γ z t) = f (γ z 0) := integral_curve_preserves_scalar hf ht (hγ z) t 0
      _ = a := by rw [hγ0]; exact z.property
  refine ⟨⟨V,L,hV,hVc,hVL,ht,γ,hγ0,hγ,hscalar,fun z => smooth_integral_curve hV (hγ z),?_⟩⟩
  intro z t
  rw [(hγ z t).deriv]
  exact hne _ (hscalar z t)

end CircleDomainRigidity

end

end OAI
