import OAI.Geometry.SurfaceImmersion.Geometry.InteriorDensityLocal
import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityPatching
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-! Smooth positive interior densities uniformly near a compact parameter set. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

/-- The full compact-parameter interior averaging construction. -/
theorem interior_positive_density_compact {A h : B → ℝ} {c : B → Plane}
    (hA : ContDiff ℝ ∞ A) (hh : ContDiff ℝ ∞ h) (hc : ContDiff ℝ ∞ c)
    {K : Set B} (hK : IsCompact K)
    (hmargin : ∀ b ∈ K, Real.pi + |h b| < A b)
    (hinside : ∀ b ∈ K, c b 0 ^ 2 + c b 1 ^ 2 < 1) :
    ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ σ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ σ (V ×ˢ univ) ∧
      (∀ b ∈ V, ∀ t, 0 < σ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => σ (b, t)) 1) ∧
      ∀ b ∈ V, (∫ t in 0..1, σ (b, t) • augment (interiorPath (A b) (h b) t)) = augment (c b) := by
  classical
  have hl (b : K) := interior_positive_density_near hA hh hc
    (hmargin b b.property) (hinside b b.property)
  choose U hU hb ρ hs hpos hper hmom using hl
  have hcover : K ⊆ ⋃ b : K, U b := by
    intro b hbk
    exact mem_iUnion.mpr ⟨⟨b, hbk⟩, hb ⟨b, hbk⟩⟩
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover U hU hcover
  have hcJ : K ⊆ ⋃ i : J, U i.val := by
    intro b hbk
    obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.mp (hJ hbk)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hbi⟩
  obtain ⟨ψ, hψsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, B))
    hK.isClosed (fun i : J => U i.val) (fun i => hU i.val) hcJ
  have hψ (i : J) : ContDiff ℝ ∞ (ψ i) := (ψ i).contMDiff.contDiff
  let S : B → ℝ := fun b => ∑ i : J, ψ i b
  have hS : ContDiff ℝ ∞ S := ContDiff.sum (fun i _ => hψ i)
  have hone (b : B) (hbk : b ∈ K) : S b = 1 := by
    simpa only [S, finsum_eq_sum_of_fintype] using ψ.sum_eq_one hbk
  let V : Set B := {b | 0 < S b}
  have hV : IsOpen V := isOpen_lt continuous_const hS.continuous
  have hKV : K ⊆ V := by
    intro b hbk
    change 0 < S b
    rw [hone b hbk]
    exact zero_lt_one
  obtain ⟨σ, hσ, hpσ, hperσ, hmσ, _⟩ := patch_densities (interiorPath_smooth hA hh)
    (fun i : J => U i.val) (fun i => hU i.val) (fun i => ρ i.val)
    (fun i => hs i.val) (fun i => hpos i.val) (fun i => hper i.val) (fun i => hmom i.val)
    (fun i b => ψ i b) hψ (fun i b => ψ.nonneg i b) hψsub
  exact ⟨V, hV, hKV, σ, hσ, hpσ, hperσ, hmσ⟩

end ClosedSurfaceR4.LoopDensity

end

end OAI
