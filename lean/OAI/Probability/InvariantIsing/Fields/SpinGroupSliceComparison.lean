import OAI.Probability.InvariantIsing.Fields.SpinGroupProjection
import OAI.Probability.InvariantIsing.Fields.SpinSliceComparison

namespace OAI

/-! Comparison of two attainable magnetization slices, with the precise
number of required spin flips summed over the field groups. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def spinGroupCountDistance {A : Type*} [Fintype A] (k l : A → ℕ) : ℕ :=
  ∑ a, ((k a - l a) + (l a - k a))

lemma spinGroupCountDistance_comm {A : Type*} [Fintype A] (k l : A → ℕ) :
    spinGroupCountDistance k l = spinGroupCountDistance l k := by
  unfold spinGroupCountDistance
  apply Finset.sum_congr rfl
  intro a _
  omega

lemma spinGroupProjection_from_slice {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k l : A → ℕ) (hl : ∀ a, l a ≤ spinGroupSize group a)
    {σ : Spin N} (hσ : σ ∈ spinGroupSlice group k) :
    hammingDist σ (spinGroupProjection group l hl σ) = spinGroupCountDistance k l := by
  have hcount := (Finset.mem_filter.mp hσ).2
  rw [spinGroupProjection_distance]
  simp only [hcount, spinGroupCountDistance]

theorem abs_restricted_group_slice_sub_le {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k l : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (hl : ∀ a, l a ≤ spinGroupSize group a)
    (eig c : Fin N → ℝ) (U : Rotation N) {K C t : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (heig : ∀ i, |eig i| ≤ K) (hc : ∀ i, |c i| ≤ C) :
    |restrictedSpinLog (spinGroupSlice group k) (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) -
      restrictedSpinLog (spinGroupSlice group l) (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)| ≤
      2 * K * Real.sqrt ((N : ℝ) * spinGroupCountDistance k l) +
      2 * C * spinGroupCountDistance k l + t * spinGroupCountDistance k l +
      N * Real.log (1 + Real.exp (-t)) := by
  apply abs_restricted_spin_pressure_sub_le _ _
    (spinGroupSlice_nonempty group k hk) (spinGroupSlice_nonempty group l hl)
    (spinGroupProjection group l hl) (spinGroupProjection group k hk)
    eig c U (spinGroupCountDistance k l) hK hC ht heig hc
  · exact fun σ _ => spinGroupProjection_mem group l hl σ
  · exact fun σ hσ => (spinGroupProjection_from_slice group k l hl hσ).le
  · exact fun σ _ => spinGroupProjection_mem group k hk σ
  · intro σ hσ
    rw [spinGroupProjection_from_slice group l k hk hσ, spinGroupCountDistance_comm]

end InvariantIsing

end

end OAI
