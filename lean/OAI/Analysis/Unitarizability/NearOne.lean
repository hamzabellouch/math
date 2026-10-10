import Mathlib
import OAI.Analysis.Unitarizability.ScaledObstruction
import OAI.Analysis.Unitarizability.UniverseTransport

namespace OAI

noncomputable section
namespace Dixmier
universe u
open Filter
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem nonamenable_near_one (hG : ¬ Amenable G) (ε : ℝ) (hε : 0 < ε) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : G →* (H →L[ℂ] H)),
      (Countable G → TopologicalSpace.SeparableSpace H) ∧
      (∀ g, ‖π g‖ ≤ 1 + ε) ∧ ¬ SimilarToUnitary π := by
  classical
  obtain ⟨S, hS, hd, ρ, hρ, hρ1, hmask⟩ := sparse_splitting_of_nonamenable hG
  let d := S.card
  let k : ℕ → ℕ := fun j => fiberDimension d ρ (j+1)
  let r : ℕ → ℕ := fun j => endpointCapacity d ρ (j+1)
  let Labels : ℕ → Type u := fun j => Word S (j+1)
  let s : ∀ j, Labels j → G := fun j => wordProduct (fun x : S => (x : G)) (j+1)
  have hlabel (j : ℕ) : Fintype.card (Labels j) = d^(j+1) := by
    simp [Labels, word_card, d]
  have hn (j : ℕ) : 2 ≤ Fintype.card (Labels j) := by
    rw [hlabel]
    have hp : 1 ≤ d^j := one_le_pow₀ (by omega : 1 ≤ d)
    rw [pow_succ']
    dsimp [d] at *
    nlinarith
  have hr (j : ℕ) : 1 ≤ r j := endpointCapacity_pos hd hρ (j+1)
  have hk (j : ℕ) : 0 < k j := fiberDimension_pos hd hρ (j+1)
  have hdim (j : ℕ) : FrameParameters.dimension (Fintype.card (Labels j)) (r j) = k j := by
    simp [FrameParameters.dimension, hlabel, k, fiberDimension, r, Nat.cast_pow]
  have hframes (j : ℕ) : ∃ v : Labels j → EuclideanSpace ℂ (Fin (k j)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (min (2*r j) (Fintype.card (Labels j))) 10 := by
    have h := SignMatrix.frames_for_fintype (hn j) (hr j)
    rw [hdim j] at h
    exact h
  choose v hvunit hvframe using hframes
  have hmasks (j : ℕ) : ∃ a : G → Labels j → Bool,
      (∀ x, (rowOnes a x).card ≤ r j) ∧ ∀ y, (columnZeros a (s j) y).card ≤ r j :=
    hmask (j+1) (by omega)
  choose a har hac using hmasks
  let A : ∀ j, DirectSumObstruction.Stage G k j →L[ℂ] DirectSumObstruction.Stage G k j :=
    fun j => Masked.constant (v j) (s j)
  let T : ∀ j, DirectSumObstruction.Stage G k j →L[ℂ] DirectSumObstruction.Stage G k j :=
    fun j => Masked.oriented (v j) (s j) (a j)
  have hA (j : ℕ) : A j ∈ KernelObstruction.Commutant := Masked.constant_commutant _ _
  have hrow (j : ℕ) : ‖KernelObstruction.row (T j) 1‖ ≤ 100 := by
    have h := Masked.local_row_bound (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (har j) 1
    norm_num at h
    exact h
  have hcol (j : ℕ) : ‖KernelObstruction.col (A j-T j) 1‖ ≤ 100 := by
    have h := Masked.local_column_bound (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (hac j) 1
    norm_num at h
    exact h
  have hdiff (j : ℕ) (g : G) : ‖coboundary KernelObstruction.translation (T j) g‖ ≤ 100 := by
    have h := Masked.difference_norm_le (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (har j) (hac j) g
    norm_num at h
    exact h
  have henergy (j : ℕ) : (d : ℝ)^(j+1) ≤ KernelObstruction.energy (A j) := by
    have h := Masked.constant_energy_ge_card (v j) (hvunit j) (s j)
    rw [hlabel] at h
    simpa only [Nat.cast_pow] using h
  have hratio : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop := by
    have hbase := (reciprocal_dimension_ratio_tendsto hd hρ hρ1).comp (tendsto_add_atTop_nat 1)
    apply tendsto_atTop_mono _ hbase
    intro j
    exact div_le_div_of_nonneg_right (henergy j) (Nat.cast_nonneg _)
  obtain ⟨π, hπbound, hπnot⟩ := DirectSumObstruction.scaled_direct_sum_obstruction k hk A T hA
    (by norm_num : (0 : ℝ) ≤ 100) hrow hcol hdiff hratio
    (show 0 < ε / 100 by positivity)
  refine ⟨DirectSumObstruction.Carrier G k, inferInstance, inferInstance, inferInstance,
    π, ?_, ?_, hπnot⟩
  · intro hcount
    let := hcount
    exact DirectSumObstruction.carrier_separable k
  · intro g
    simpa only [div_mul_cancel₀ ε (by norm_num : (100 : ℝ) ≠ 0)] using hπbound g

universe v

theorem nonamenable_near_one_large (hG : ¬ Amenable G) (ε : ℝ) (hε : 0 < ε) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : G →* (H →L[ℂ] H)),
      (Countable G → TopologicalSpace.SeparableSpace H) ∧
      (∀ g, ‖π g‖ ≤ 1 + ε) ∧ ¬ SimilarToUnitary π := by
  let Q := ULift.{v} G
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  let e : G ≃* Q := MulEquiv.ulift.symm
  have hQ : ¬ Amenable Q := fun h => hG (amenable_of_mulEquiv e h)
  obtain ⟨H, hnorm, hinner, hcomplete, π, hsep, hb, hn⟩ := nonamenable_near_one hQ ε hε
  refine ⟨H, hnorm, hinner, hcomplete, π.comp e.toMonoidHom, ?_, fun g => hb (e g), ?_⟩
  · intro hcount
    let := hcount
    exact hsep (e.surjective.countable)
  · rintro ⟨S, hS⟩
    apply hn
    refine ⟨S, ?_⟩
    intro q x
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply]
      using hS (e.symm q) x

end Dixmier
end

end OAI
