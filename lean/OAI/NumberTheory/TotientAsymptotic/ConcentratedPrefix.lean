import OAI.NumberTheory.TotientAsymptotic.HeadLimitedFamily

namespace OAI

/-! A simultaneous coordinate upper envelope, with a fixed terminal buffer. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

attribute [local instance] Classical.propDecidable

def prefixConcentrationIndices (N L : ℕ) : Finset (Fin (N+2)) :=
  Finset.univ.filter (fun i => i.val < N ∧ L ≤ N+2-(i.val+1))

def prefixConcentrationFailure (N L : ℕ) (B : ℝ) : Set (Fin (N+2) → ℝ) :=
  ⋃ i ∈ prefixConcentrationIndices N L,
    prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i

lemma concentration_index_sum {c : ℝ} (hc : 0 < c) (N L : ℕ) :
    (∑ i ∈ prefixConcentrationIndices N L,
      Real.exp (-c*((N+2-(i.val+1):ℕ):ℝ))) ≤
      Real.exp (-c*(L:ℝ))/(1-Real.exp (-c)) := by
  let q := Real.exp (-c)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hc])
  let K := (prefixConcentrationIndices N L).image (fun i => N+2-(i.val+1)-L)
  have hinj : Set.InjOn (fun i : Fin (N+2) => N+2-(i.val+1)-L)
      (↑(prefixConcentrationIndices N L)) := by
    intro i hi j hj he
    have hi := (Finset.mem_filter.mp hi).2
    have hj := (Finset.mem_filter.mp hj).2
    change N+2-(i.val+1)-L=N+2-(j.val+1)-L at he
    have hiLt := i.isLt
    have hjLt := j.isLt
    apply Fin.ext
    omega
  have he (i : Fin (N+2)) (hi : i ∈ prefixConcentrationIndices N L) :
      Real.exp (-c*((N+2-(i.val+1):ℕ):ℝ)) =
        Real.exp (-c*(L:ℝ))*q^(N+2-(i.val+1)-L) := by
    have hi := (Finset.mem_filter.mp hi).2.2
    have hnat : N+2-(i.val+1)=L+(N+2-(i.val+1)-L) := by omega
    conv_lhs => rw [hnat,Nat.cast_add]
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (-c*(L:ℝ))*∑ j ∈ K,q^j := by
      rw [Finset.mul_sum,Finset.sum_image hinj]
      exact Finset.sum_congr rfl he
    _ ≤ Real.exp (-c*(L:ℝ))*∑' j : ℕ,q^j :=
      mul_le_mul_of_nonneg_left
        ((summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _
          (fun _ _ => pow_nonneg hq0 _)) (Real.exp_pos _).le
    _ = _ := by rw [tsum_geometric_of_lt_one hq0 hq1,div_eq_mul_inv]

lemma prefix_concentration_failure_bound : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ N L : ℕ,∀ B : ℝ,0 < B →
      volume.real (prefixConcentrationFailure N L B) ≤
        (C*Real.exp (-c*(L:ℝ))/(1-Real.exp (-c)))*
          volume.real (prefixRegion (N+2) B 0 0) := by
  obtain ⟨C,c,hC,hc,hbound⟩ := prefix_coordinate_concentration_unconditional
  refine ⟨C,c,hC,hc,?_⟩
  intro N L B hB
  apply (measureReal_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ i ∈ prefixConcentrationIndices N L,
        C*Real.exp (-c*((N+2-(i.val+1):ℕ):ℝ))*
          volume.real (prefixRegion (N+2) B 0 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hbound N B hB i (Finset.mem_filter.mp hi).2.1
    _ = C*(∑ i ∈ prefixConcentrationIndices N L,
        Real.exp (-c*((N+2-(i.val+1):ℕ):ℝ)))*
          volume.real (prefixRegion (N+2) B 0 0) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (concentration_index_sum hc N L) hC.le
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_right hh (show 0 ≤ volume.real _ from ENNReal.toReal_nonneg)

end TotientAsymptotic

end

end OAI
