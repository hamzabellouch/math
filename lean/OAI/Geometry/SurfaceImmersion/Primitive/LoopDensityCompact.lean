import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityPatching
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-! Compact patching, retaining every value on which the local densities agree. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem compact_patch_densities {ι : Type*} {p : B → ℝ → Plane} {c : B → Plane}
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (U : ι → Set B) (hU : ∀ i, IsOpen (U i))
    (ρ : ι → B × ℝ → ℝ)
    (hρ : ∀ i, ContDiffOn ℝ ∞ (ρ i) (U i ×ˢ univ))
    (hpos : ∀ i b, b ∈ U i → ∀ t, 0 < ρ i (b, t))
    (hper : ∀ i b, Function.Periodic (fun t => ρ i (b, t)) 1)
    (hmom : ∀ i b, b ∈ U i →
      (∫ t in 0..1, ρ i (b, t) • augment (p b t)) = augment (c b))
    {K : Set B} (hK : IsCompact K) (hcover : K ⊆ ⋃ i, U i) :
    ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ σ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ σ (V ×ˢ univ) ∧
      (∀ b ∈ V, ∀ t, 0 < σ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => σ (b, t)) 1) ∧
      (∀ b ∈ V, (∫ t in 0..1, σ (b, t) • augment (p b t)) = augment (c b)) ∧
      ∀ b ∈ V, ∀ t r, (∀ i, b ∈ U i → ρ i (b, t) = r) → σ (b, t) = r := by
  classical
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
  let V : Set B := {b | 0 < S b}
  have hV : IsOpen V := isOpen_lt continuous_const hS.continuous
  have hKV : K ⊆ V := by
    intro b hbk
    have hone : S b = 1 := by
      simpa only [S, finsum_eq_sum_of_fintype] using ψ.sum_eq_one hbk
    change 0 < S b
    rw [hone]
    exact zero_lt_one
  obtain ⟨σ, hσ, hpσ, hperσ, hmσ, hformula⟩ := patch_densities hp
    (fun i : J => U i.val) (fun i : J => hU i.val) (fun i : J => ρ i.val)
    (fun i : J => hρ i.val) (fun i : J => hpos i.val) (fun i : J => hper i.val)
    (fun i : J => hmom i.val) (fun (i : J) b => ψ i b) hψ
    (fun (i : J) b => ψ.nonneg i b) hψsub
  refine ⟨V, hV, hKV, σ, hσ, hpσ, hperσ, hmσ, ?_⟩
  intro b hb t r hr
  rw [hformula]
  change (∑ i : J, ψ i b * ρ i.val (b, t)) / S b = r
  have hsum : (∑ i : J, ψ i b * ρ i.val (b, t)) = S b * r := by
    dsimp only [S]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hz : ψ i b = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [hr i.val (hψsub i (subset_tsupport _ (Function.mem_support.mpr hz)))]
  rw [hsum]
  exact mul_div_cancel_left₀ r hb.ne'

end ClosedSurfaceR4.LoopDensity

end

end OAI
