import OAI.Geometry.RCD.Transport.LengthComponentIntegral

namespace OAI

/-! # Finite uniform bins for bounded nonnegative transport lengths -/

open Set Filter MeasureTheory Function TopologicalSpace
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

def lengthBin (ε : ℝ) (i : ℕ) : Set ℝ := Ico ((i:ℝ)*ε) (((i:ℝ)+1)*ε)

theorem lengthBin_measurable (ε : ℝ) (i : ℕ) : MeasurableSet (lengthBin ε i) :=
  measurableSet_Ico

theorem lengthBin_pairwise {ε : ℝ} (hε : 0<ε) : Pairwise (Disjoint on lengthBin ε) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro d hi hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hn : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hij
    have hmul := mul_le_mul_of_nonneg_right hn hε.le
    exact (not_lt_of_ge (hmul.trans hj.1)) hi.2
  · have hn : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast hji
    have hmul := mul_le_mul_of_nonneg_right hn hε.le
    exact (not_lt_of_ge (hmul.trans hi.1)) hj.2

theorem mem_lengthBin_floor {ε d : ℝ} (hε : 0<ε) (hd : 0≤d) :
    d∈lengthBin ε ⌊d/ε⌋₊ := by
  have hp : 0≤d/ε := div_nonneg hd hε.le
  constructor
  · exact (le_div_iff₀ hε).mp (Nat.floor_le hp)
  · exact (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one (d/ε))

theorem lengthBin_finite_cover {ε D d : ℝ} (hε : 0<ε) (hd : 0≤d) (hD : d≤D) :
    ∃ i∈Finset.range (⌊D/ε⌋₊+1), d∈lengthBin ε i := by
  refine ⟨⌊d/ε⌋₊,Finset.mem_range.mpr ?_,mem_lengthBin_floor hε hd⟩
  exact Nat.lt_succ_of_le (Nat.floor_mono ((div_le_div_iff_of_pos_right hε).mpr hD))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem bounded_length_uniform_partition (π : Measure C(Time,X)) {D ε : ℝ}
    (hε : 0<ε) (hD : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D) :
    (∑ i∈Finset.range (⌊D/ε⌋₊+1), π.restrict {γ | dist (γ 0) (γ 1)∈lengthBin ε i})=π := by
  apply sum_length_restrictions π (lengthBin ε) _ (lengthBin_measurable ε)
    (fun _ _ _ _ hij => lengthBin_pairwise hε hij)
  exact hD.mono (fun γ hγ => lengthBin_finite_cover hε dist_nonneg hγ)

end RegularPointCoordinates

end

end OAI
