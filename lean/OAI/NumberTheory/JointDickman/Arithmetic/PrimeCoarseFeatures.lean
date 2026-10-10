import OAI.NumberTheory.JointDickman.Amplification.LogMassBilinear

namespace OAI

/-! # Bounded coarse features of the actual prime-site distribution -/

namespace JointDickman
open Finset

noncomputable def primeGroupedTransition (m B : ℕ) (x : auxiliaryPrimes B → Bool)
    (a : Fin m × Fin (channelBlockCount m B)) : ℝ :=
  partialFairPrimeTransition (auxiliaryPrimes B)
    (logarithmicCell B (groupedLower m (channelBlockCount m B))
      (groupedUpper m (channelBlockCount m B))) x a

noncomputable def primeCoarseFeature (m B : ℕ) (d : Fin m)
    (x : auxiliaryPrimes B → Bool) : ℝ :=
  (∑ r : Fin (channelBlockCount m B), primeGroupedTransition m B x (d,r))/channelMesh m

theorem channelBlockCount_pos {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    0 < channelBlockCount m B := by
  have h := channelFineCount_pos hm hB
  rw [channelFineCount_eq] at h
  exact Nat.pos_of_ne_zero (by intro he; simp [he] at h)

theorem channelMesh_block_normalization {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    channelMesh (channelFineCount m B)*(channelBlockCount m B : ℝ) = channelMesh m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk0 : (channelBlockCount m B : ℝ) ≠ 0 := by
    exact_mod_cast (channelBlockCount_pos hm hB).ne'
  unfold channelMesh
  rw [channelFineCount_eq,Nat.cast_mul]
  field_simp

theorem primeCoarseFeature_bounds {m B : ℕ} (hm : 0 < m)
    (d : Fin m) (x : auxiliaryPrimes B → Bool) :
    0 ≤ primeCoarseFeature m B d x ∧ primeCoarseFeature m B d x ≤ 1/channelMesh m := by
  have hp (a : Fin m × Fin (channelBlockCount m B)) :
      0 ≤ primeGroupedTransition m B x a := partialFairPrimeTransition_nonneg _ _ _ _
  have hsum : (∑ r, primeGroupedTransition m B x (d,r)) ≤ 1 := by
    have hh := single_le_sum (s := univ) (f := fun e : Fin m =>
      ∑ r, primeGroupedTransition m B x (e,r))
      (fun e _ => sum_nonneg (fun r _ => hp (e,r))) (mem_univ d)
    have htotal : (∑ e : Fin m, ∑ r, primeGroupedTransition m B x (e,r)) ≤ 1 := by
      rw [← Fintype.sum_prod_type]
      exact partialFairPrimeTransition_sum_le _ _ _
    exact hh.trans htotal
  unfold primeCoarseFeature
  exact ⟨div_nonneg (sum_nonneg (fun r _ => hp (d,r))) (channelMesh_pos hm).le,
    div_le_div_of_nonneg_right hsum (channelMesh_pos hm).le⟩

theorem groupedManuscriptChannel_coarse_feature {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (g : (auxiliaryPrimes B → Bool) → ℝ)
    (a : Fin m × Fin (channelBlockCount m B)) :
    coarseGroupAverage (groupedManuscriptChannel m B g) a =
      ∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x*primeCoarseFeature m B a.1 x := by
  have hm0 := (channelMesh_pos hm).ne'
  have hδ0 := (channelMesh_pos (channelFineCount_pos hm hB)).ne'
  have hk0 : (channelBlockCount m B : ℝ) ≠ 0 := by
    exact_mod_cast (channelBlockCount_pos hm hB).ne'
  have he := channelMesh_block_normalization hm hB
  unfold coarseGroupAverage finiteResidueAverage groupedManuscriptChannel finiteChannel primeCoarseFeature
  simp only [Fintype.card_fin]
  change ((∑ r : Fin (channelBlockCount m B),
      (∑ x, fullPrimeMass (auxiliaryPrimes B) x*primeGroupedTransition m B x (a.1,r)*g x)/
        channelMesh (channelFineCount m B))/(channelBlockCount m B : ℝ)) = _
  simp only [sum_div,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro r _
  rw [← he]
  field_simp

theorem coarseLogMass_feature {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (i : Fin (channelFineCount m B)) :
    coarseLogMass m B g i = channelMesh (channelFineCount m B)*
      ∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x*
        primeCoarseFeature m B ((channelIndexEquiv m B).symm i).1 x := by
  unfold coarseLogMass
  rw [groupedManuscriptChannel_coarse_feature hm hB]

end JointDickman

end OAI
