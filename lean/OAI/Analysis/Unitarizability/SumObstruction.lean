import OAI.Analysis.Unitarizability.KernelObstruction
import OAI.Analysis.Unitarizability.HilbertSum
import OAI.Analysis.Unitarizability.Unitarizer
import Mathlib.Order.Filter.AtTopBot.Tendsto

namespace OAI

/-! The operator-theoretic direct-sum obstruction, constructed from stage operators
without any uniform bound on their norms. -/
noncomputable section
namespace Dixmier
namespace DirectSumObstruction
open Filter
open scoped Topology
variable {G : Type*} [Group G]

abbrev Stage (G : Type*) (k : ℕ → ℕ) (j : ℕ) : Type _ := KernelObstruction.Space G (Fin (k j))
abbrev Total (G : Type*) (k : ℕ → ℕ) : Type _ := HilbertSum.Space (Stage G k)
abbrev Carrier (G : Type*) (k : ℕ → ℕ) := Triangular.Double (Total G k)

theorem stage_unitary (k : ℕ → ℕ) (j : ℕ) (g : G) (x : Stage G k j) :
    ‖KernelObstruction.translation g x‖ = ‖x‖ :=
  KernelObstruction.reindex_norm (Equiv.mulLeft g⁻¹) x

/-- The direct-sum obstruction with its representation and bound.
The stage operators A_j and T_j need not be uniformly bounded. -/
theorem direct_sum_obstruction (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j-T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop) :
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + κ) ∧ ¬ SimilarToUnitary π := by
  let U : ∀ j, G →* (Stage G k j →L[ℂ] Stage G k j) := fun _ => KernelObstruction.translation
  have hU : ∀ j g x, ‖U j g x‖ = ‖x‖ := stage_unitary k
  let D : ∀ j, G → (Stage G k j →L[ℂ] Stage G k j) := fun j => coboundary (U j) (T j)
  have h1 : ∀ j, D j 1 = 0 := fun j => coboundary_one (U j) (T j)
  have hD : ∀ j g h, D j (g*h) = D j g + conjugate (U j) g (D j h) :=
    fun j => coboundary_cocycle (U j) (T j)
  let V := HilbertSum.representation U hU
  let δ := HilbertSum.cocycle D hκ hb
  have hδ1 : δ 1 = 0 := HilbertSum.cocycle_one D hκ hb h1
  have hδ : ∀ g h, δ (g*h) = δ g + conjugate V g (δ h) :=
    HilbertSum.cocycle_identity U hU D hκ hb hD
  let π := Triangular.representation V δ hδ1 hδ
  have hδb : ∀ g, ‖δ g‖ ≤ κ := fun g => HilbertSum.boundedSum_norm_le _ hκ _
  refine ⟨π, Triangular.representation_bound V δ hδ1 hδ
    (HilbertSum.representation_norm_map U hU) hδb, ?_⟩
  intro hπ
  rcases Triangular.implementer_of_similar V δ hδ1 hδ hπ with ⟨B, hB⟩
  have hbound (j : ℕ) : KernelObstruction.energy (A j) / k j ≤ 4 * (κ + ‖B‖)^2 := by
    let Bj := HilbertSum.compression B j
    have hBj (g : G) : D j g = coboundary (U j) Bj g :=
      HilbertSum.compression_implementer U hU D hκ hb B hB j g
    have hC : T j - Bj ∈ KernelObstruction.Commutant := by
      intro g
      exact ((equal_coboundaries_iff_commute_sub (U j) (T j) Bj g).mp (hBj g)).symm
    have henergy := KernelObstruction.kernel_obstruction (hA j) hκ (hr j) (hc j) hC
    simp only [Fintype.card_fin, sub_sub_cancel] at henergy
    have hnorm : ‖Bj‖ ≤ ‖B‖ := HilbertSum.compression_norm_le B j
    have hs : (κ + ‖Bj‖)^2 ≤ (κ + ‖B‖)^2 :=
      pow_le_pow_left₀ (add_nonneg hκ (norm_nonneg _)) (add_le_add (le_refl _) hnorm) 2
    have henergy' : KernelObstruction.energy (A j) ≤ 4 * (k j : ℝ) * (κ + ‖B‖)^2 :=
      henergy.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hk j))).mpr
    nlinarith [henergy']
  obtain ⟨j, hj⟩ := (he.eventually (eventually_gt_atTop (4 * (κ + ‖B‖)^2))).exists
  exact (not_lt_of_ge (hbound j)) hj

omit [Group G] in
/-- The concrete carrier is separable when the group is countable. -/
theorem carrier_separable [Countable G] (k : ℕ → ℕ) :
    TopologicalSpace.SeparableSpace (Carrier G k) := by
  have (j : ℕ) : TopologicalSpace.SeparableSpace (Stage G k j) := HilbertSum.separableSpace
  have : TopologicalSpace.SeparableSpace (Total G k) := HilbertSum.separableSpace
  infer_instance

/-- The direct-sum obstruction with all Hilbert-space structure and separability
explicit in the conclusion. -/
theorem separable_direct_sum_obstruction [Countable G] (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j-T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop) :
    TopologicalSpace.SeparableSpace (Carrier G k) ∧
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + κ) ∧ ¬ SimilarToUnitary π :=
  ⟨carrier_separable k, direct_sum_obstruction k hk A T hA hκ hr hc hb he⟩

end DirectSumObstruction
end Dixmier

end

end OAI
