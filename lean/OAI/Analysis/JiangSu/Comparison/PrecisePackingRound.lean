import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.PackingRounds

namespace OAI

noncomputable section
open Pureness
open scoped ComplexOrder

namespace DirectPacking
open CurrentMain

variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

lemma PackingStepBounds.mono_quality {p z y t : D} {c σ η δ : ℝ}
    {K : Finset (unitary D)} (H : PackingStepBounds p z y t c σ δ K)
    (hp : IsStarProjection p) (hy : IsStarProjection y) (hc : 0 ≤ c) (hση : σ ≤ η) :
    PackingStepBounds p z y t c η δ K := by
  refine { H with sampled_linear := ?_, sampled_energy := ?_ }
  · intro x hx τ
    exact (H.sampled_linear x hx τ).trans (by
      gcongr
      exact add_nonneg (τ.functional.map_nonneg hy.nonneg).1
        (mul_nonneg hc (τ.functional.map_nonneg hp.nonneg).1))
  · intro x hx τ
    exact (H.sampled_energy x hx τ).trans (by
      gcongr
      exact add_nonneg (τ.functional.map_nonneg hy.nonneg).1
        (mul_nonneg hc (τ.functional.map_nonneg hp.nonneg).1))

lemma exists_precise_packing_round (hcoef : CoefficientSupply (D := D)) (hinsert : InsertionSupply (D := D))
    {z₀ r : D} (hz₀ : IsStarProjection z₀) (F : WeightedBlockFamily r)
    (K : Finset (unitary D)) {η σ δ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hση : σ ≤ η) (hδ : 0 < δ)
    (happrox : ∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
      ‖F.range j*(x : D)*F.range j-(F.row j).matrix (F.base j) H‖ < σ) :
    ∃ R : SampledPackingRound F z₀ K η δ, ∀ a,
      PackingStepBounds (F.range a.1) (R.occupied a) (R.sampled a) (R.inserted a)
        (η*F.weight a.1/2) σ δ K := by
  classical
  let e := Fintype.equivFin (F.Index × Bool)
  let Q := fun (a : Fin (Fintype.card (F.Index × Bool))) (z y t : D) =>
    PackingStepBounds (F.range (e.symm a).1) z y t (η*F.weight (e.symm a).1/2) σ δ K
  have hc (a : F.Index × Bool) : η*F.weight a.1/2 ∈ Set.Icc (0 : ℝ) 1 := by
    have hw := F.weight_le_one a.1
    have hw0 := F.weight_pos a.1
    constructor
    · positivity
    · nlinarith
  have hstep (a : Fin (Fintype.card (F.Index × Bool))) (z : D) (hz : IsStarProjection z) :
      ∃ y t, IsStarProjection y ∧ IsStarProjection t ∧ t ≤ 1-z ∧ Q a z y t :=
    exists_packing_step (F.row (e.symm a).1) hcoef hinsert hz K (hc _) (hση.trans_lt hη1) hδ (happrox _)
  obtain ⟨S,hS⟩ := exists_projection_insertion _ hz₀ Q hstep
  let R : SampledPackingRound F z₀ K η δ := {
    final := S.occupied (Fin.last _)
    occupied := fun a => S.occupied (e a).castSucc
    sampled := fun a => S.sampled (e a)
    inserted := fun a => S.inserted (e a)
    final_projection := S.occupied_projection _
    occupied_projection := fun a => S.occupied_projection _
    sampled_projection := fun a => S.sampled_projection _
    inserted_projection := fun a => S.inserted_projection _
    occupied_le_final := fun a => S.monotone (Fin.le_last _)
    inserted_orthogonal := fun a b hab => S.orthogonal (e.injective.ne hab)
    initial_orthogonal := fun a => S.initial_orthogonal _
    final_eq := by rw [e.sum_comp S.inserted]; exact S.final_eq
    bounds := by
      intro a
      have h : PackingStepBounds (F.range a.1) (S.occupied (e a).castSucc)
          (S.sampled (e a)) (S.inserted (e a)) (η*F.weight a.1/2) σ δ K := by
        simpa only [Q,Equiv.symm_apply_apply] using hS (e a)
      exact h.mono_quality (F.range_projection a.1) (S.sampled_projection _) (hc a).1 hση }
  refine ⟨R,?_⟩
  intro a
  simpa only [Q,Equiv.symm_apply_apply] using hS (e a)

namespace SampledPackingRound
variable {z₀ r : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η σ δ : ℝ}
variable (R : SampledPackingRound F z₀ K η δ)

lemma precise_sampled_energy_sum
    (H : ∀ a, PackingStepBounds (F.range a.1) (R.occupied a) (R.sampled a) (R.inserted a)
      (η*F.weight a.1/2) σ δ K) (τ : RestrictedTracialState D) (x : unitary D) (hx : x ∈ K) :
    (∑ a, traceTwoNorm τ ((x : D)*R.sampled a-R.sampled a*(x : D))^2) ≤
      η*(∑ j, F.weight j*traceTwoNorm τ ((x : D)*F.range j-F.range j*(x : D))^2)+
        6*σ*(R.sampledMass τ+R.targetMass τ)+10*R.totalError := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (H a).sampled_energy x hx τ
  apply h.trans_eq
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sampledMass,targetMass,totalError]
  rw [signed_weighted_sum F η (fun j => traceTwoNorm τ ((x : D)*F.range j-F.range j*(x : D))^2),
    signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re)]

lemma inserted_row_energy (V : BistochasticTest D) (τ : RestrictedTracialState D) :
    (∑ a, V.energy τ (R.inserted a)) ≤
      2*(∑ a, V.energy τ (R.sampled a))+40*R.overlap τ := by
  have hd := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_distance τ
  have he := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => V.energy_perturb τ (R.inserted a) (R.sampled a)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hd he
  dsimp [overlap]
  linarith

end SampledPackingRound
end DirectPacking
end

noncomputable section
namespace DirectPacking
open CurrentMain

variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]
namespace OrthogonalProjectionPair

def zero : OrthogonalProjectionPair D where
  left := 0
  right := 0
  left_projection := IsStarProjection.zero D
  right_projection := IsStarProjection.zero D
  orthogonal := mul_zero 0

end OrthogonalProjectionPair

structure PackingBounds (ι : A →⋆ₐ[ℂ] D) (Q : OrthogonalProjectionPair D)
    (K : Finset (unitary A)) (η : ℝ) (n : ℕ) : Prop where
  energy : ∀ x ∈ K, ∀ τ : RestrictedTracialState D, Q.energy τ (ι (x : A)) ≤ packingEnergy η n
  remaining : ∀ τ : RestrictedTracialState D, Q.remaining τ ≤ packingRemainder η n
  balance : ∀ x ∈ K, ∀ τ : RestrictedTracialState D, Q.balance τ (ι (x : A)) ≤ packingBalance η n

end DirectPacking
end

end OAI
