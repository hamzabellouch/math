import Mathlib
import OAI.Analysis.LaughlinFock.NullComponents
import OAI.Analysis.LaughlinFock.RelativeTransfer

namespace OAI

/-! Finite Comparison. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

 
def rowsEta {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow) : ℝ :=
  ∑ i, (rows i).ell ^ 2

 
def rowsThreeTrace {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow) (Q z : ℕ) : ℝ :=
  ∑ i, rowThreeTrace Q z (rows i).t.val (rows i).ell (rows i).alpha

 
def planarRowsThreeTrace {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow) (z : ℕ) : ℝ :=
  ∑ i, planarRowThreeTrace z (rows i).t.val (rows i).ell (rows i).alpha

theorem rowsThreeTrace_tendsto {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (z : ℕ) :
    Tendsto (fun Q => rowsThreeTrace rows Q z) atTop (𝓝 (planarRowsThreeTrace rows z)) :=
  tendsto_finsetSum Finset.univ (fun i _ =>
    rowThreeTrace_tendsto z (rows i).t.val (rows i).ell (rows i).alpha)

 
abbrev ComparedThreeBlock := {z : Fin 16 // z.val=2 ∨ 4 ≤ z.val}

 

theorem rowsThreeTrace_eventual_bound {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow)
    (hCertificate : ∀ z : ComparedThreeBlock,
      planarRowsThreeTrace rows z.val.val <
        (3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2) ^ z.val.val) :
    ∀ᶠ Q in atTop, ∀ z : ComparedThreeBlock,
      rowsThreeTrace rows Q z.val.val / spinRatio Q z.val.val < gramShift Q z.val.val := by
  apply eventually_all.mpr
  intro z
  have hlim : Tendsto (fun Q => spinRatio Q z.val.val * gramShift Q z.val.val)
      atTop (𝓝 ((3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2)^z.val.val)) := by
    simpa only [mul_assoc] using
      (spinRatio_tendsto z.val.val).mul (gramShift_tendsto z.val.val)
  have he := (rowsThreeTrace_tendsto rows z.val.val).eventually_lt hlim (hCertificate z)
  filter_upwards [he, eventually_ge_atTop 16] with Q hlt hQ
  have hn : (z.val.val : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : z.val.val ≤ Q)
  have hq : (16 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hp : 0 < spinRatio Q z.val.val := by
    unfold spinRatio
    apply div_pos <;> linarith
  rw [div_lt_iff₀ hp]
  simpa only [mul_comm] using hlt

 
def finiteThreeTarget (Q : ℕ) : FockMatrix Q :=
  exteriorLift Q 3 (threeWedgeMatrix Q *
    (∑ z ∈ Finset.range 16, (gramShift Q z : ℂ) • threeSpinProjection Q z) *
      (threeWedgeMatrix Q)ᴴ)

 
def fullThreeTarget (Q : ℕ) : FockMatrix Q :=
  exteriorLift Q 3 (threeWedgeMatrix Q *
    (∑ z ∈ Finset.range (Q+1), (gramShift Q z : ℂ) • threeSpinProjection Q z) *
      (threeWedgeMatrix Q)ᴴ)

 

def threeTraceForm {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow) (Q : ℕ) : FockMatrix Q :=
  exteriorLift Q 3 (threeWedgeMatrix Q *
    (∑ z ∈ Finset.range 16, (rowsThreeTrace rows Q z / spinRatio Q z : ℂ) •
      threeSpinProjection Q z) * (threeWedgeMatrix Q)ᴴ)

 
theorem threeWedgeMatrix_null_sandwich {Q z : ℕ} (hQ : 3 ≤ Q)
    (hz : z=0 ∨ z=1 ∨ z=3) (a : ℂ) :
    threeWedgeMatrix Q * (a • threeSpinProjection Q z) * (threeWedgeMatrix Q)ᴴ = 0 := by
  have hle : z ≤ Q := by rcases hz with rfl | rfl | rfl <;> omega
  rw [Matrix.mul_smul, threeWedgeMatrix_null_projection (by omega) hle hz,
    smul_zero, Matrix.zero_mul]

 

theorem threeTraceForm_le_finite_of_coefficients {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) {Q : ℕ} (hQ : 16 ≤ Q)
    (hbound : ∀ z : ComparedThreeBlock,
      rowsThreeTrace rows Q z.val.val / spinRatio Q z.val.val ≤ gramShift Q z.val.val) :
    (finiteThreeTarget Q - threeTraceForm rows Q).PosSemidef := by
  classical
  unfold finiteThreeTarget threeTraceForm
  rw [← exteriorLift_sub, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Finset.sum_sub_distrib]
  apply exteriorLift_posSemidef
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Matrix.posSemidef_sum
  intro z hz
  rw [← sub_smul, ← Complex.ofReal_div, ← Complex.ofReal_sub]
  by_cases hn : z=0 ∨ z=1 ∨ z=3
  · rw [threeWedgeMatrix_null_sandwich (by omega) hn]
    exact Matrix.PosSemidef.zero
  · have hzlt : z < 16 := Finset.mem_range.mp hz
    have hg : z=2 ∨ 4 ≤ z := by omega
    have h := hbound ⟨⟨z,hzlt⟩,hg⟩
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    exact (threeSpinProjection_posSemidef Q z).smul (by exact_mod_cast sub_nonneg.mpr h)

 

theorem threeTraceForm_eventual_bound {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow)
    (hCertificate : ∀ z : ComparedThreeBlock,
      planarRowsThreeTrace rows z.val.val <
        (3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2)^z.val.val) :
    ∀ᶠ Q in atTop, (finiteThreeTarget Q - threeTraceForm rows Q).PosSemidef := by
  filter_upwards [rowsThreeTrace_eventual_bound rows hCertificate, eventually_ge_atTop 16] with Q h hQ
  exact threeTraceForm_le_finite_of_coefficients rows hQ (fun z => (h z).le)

end LaughlinFock
end

end OAI
