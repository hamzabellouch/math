import OAI.Geometry.Convex.GeneralMahler.Update

namespace OAI
/-! Matrix trace order calculus for layer inequalities. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}
-- Use actual Borel measurable structure
instance mat_meas (m:ℕ) : MeasurableSpace (Mat m) := borel _
instance mat_borel (m:ℕ) : BorelSpace (Mat m) := ⟨rfl⟩
lemma trN_cyclic (A B:Mat m) : trN (A*B)=trN (B*A) :=
  congrArg (fun x=>(x:ℝ)/m) (Matrix.trace_mul_comm ..)
lemma trN_add (A B:Mat m) : trN (A+B)=trN A+trN B := by unfold trN; rw [trace_add,add_div]
lemma trN_sub (A B:Mat m) : trN (A-B)=trN A-trN B := by unfold trN; rw [trace_sub,sub_div]
lemma trN_smul (a:ℝ) (A:Mat m) : trN (a•A)=a*trN A := by
  unfold trN; rw [trace_smul]; simp; ring
lemma trN_mono {A B:Mat m} (h:A≤B) : trN A≤trN B := by
  have hi := Matrix.le_iff.mp h
  unfold trN
  have he := hi.trace_nonneg
  rw [trace_sub] at he
  gcongr; linarith
lemma sand_nonneg {A B:Mat m} (ha:0≤A) (hb:B.IsHermitian) : 0 ≤ B*A*B := by
  have he := ha.posSemidef.mul_mul_conjTranspose_same B
  rw [show Bᴴ=B from hb] at he; exact he.nonneg

lemma trN_mul_nonneg {A B : Mat m} (ha:0≤A) (hb:0≤B) : 0 ≤ trN (A*B) := by
  let S := CFC.sqrt B
  have hs : S.IsHermitian := (CFC.sqrt_nonneg B).posSemidef.1
  calc
    _ ≤ trN (S*A*S) := by
      simpa [trN] using trN_mono (sand_nonneg ha hs)
    _ = _ := by
      rw [mul_assoc,trN_cyclic S, mul_assoc,show S*S=B from CFC.sqrt_mul_sqrt_self B hb]
lemma trN_mul_mono {A B C:Mat m} (ha:A≤B) (hc:0≤C) : trN (A*C) ≤ trN (B*C) := by
  have h := trN_mul_nonneg (sub_nonneg.mpr ha) hc
  rwa [sub_mul,trN_sub,sub_nonneg] at h

lemma trN_j (A B:Mat m) : trN (jprod A B)=trN (A*B) := by
  rw [jprod,trN_smul,trN_add,trN_cyclic B]
  ring
lemma trN_one [NeZero m] : trN (1:Mat m)=1 := by simp [trN]
lemma trN_unit {A:Mat m} [NeZero m] (h:0≤A) (hh:A≤1) : 0≤trN A ∧ trN A≤1 := by
  have hi := trN_mono h; have he := trN_mono hh
  rw [show trN (0:Mat m)=0 from by simp [trN]] at hi; rw [trN_one] at he
  exact ⟨hi,he⟩
lemma trN_prod_unit {A B:Mat m} [NeZero m] (ha:0≤A) (ha':A≤1)
    (hb:0≤B) (hb':B≤1) : 0≤trN (A*B) ∧ trN (A*B)≤1 := by
  refine ⟨trN_mul_nonneg ha hb,?_⟩
  have h := trN_mul_mono ha' hb
  rw [one_mul] at h
  exact h.trans (trN_unit hb hb').2

lemma thresh_pd {A:Mat m} (h:0≤A) : (1+A).PosDef := Matrix.PosDef.one.add_posSemidef h.posSemidef

lemma inv_mul' {A:Mat m} (ha:A.PosDef) : A⁻¹*A=1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ha.det_pos.ne')
lemma mul_inv' {A:Mat m} (ha:A.PosDef) : A*A⁻¹=1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ha.det_pos.ne')

/-- Order reversal under inversion: prove by nonnegative remainder. -/
lemma inv_rev {A B:Mat m} (ha:A.PosDef) (hb:B.PosDef) (hh:A≤B) : B⁻¹≤A⁻¹ := by
  rw [← sub_nonneg]
  have hs : 0 ≤ (A⁻¹-B⁻¹)*A*(A⁻¹-B⁻¹) :=
    sand_nonneg ha.posSemidef.nonneg (ha.inv.1.sub hb.inv.1)
  have ht := sand_nonneg (sub_nonneg.mpr hh) hb.inv.1
  apply (add_nonneg hs ht).trans_eq
  calc
    _ = (A⁻¹*A)*A⁻¹ - B⁻¹*(A*A⁻¹) - (A⁻¹*A)*B⁻¹ + (B⁻¹*B)*B⁻¹ := by noncomm_ring
    _ = _ := by rw [inv_mul' ha, mul_inv' ha,inv_mul' hb]; simp

def thresh (A:Mat m) := 1-(1+A)⁻¹
lemma thresh_mono {A B:Mat m} (ha:0≤A) (hh:A≤B) : thresh A ≤ thresh B :=
  sub_le_sub_left (inv_rev (thresh_pd ha) (thresh_pd (ha.trans hh)) (by gcongr)) _
lemma thresh_unit {A:Mat m} (ha:0≤A) : 0≤thresh A ∧ thresh A≤1 := by
  constructor
  · have h := thresh_mono (A:= (0:Mat m)) le_rfl ha
    simpa [thresh] using h
  exact sub_le_self _ (thresh_pd ha).inv.posSemidef.nonneg
lemma thresh_eq {A:Mat m} (ha:0≤A) : thresh A=A*(1+A)⁻¹ := by
  have hh := mul_inv' (thresh_pd ha)
  rw [add_mul,one_mul] at hh
  unfold thresh; exact sub_eq_of_eq_add' hh.symm

-- b > 0 upper bound on I+A gives b⁻¹ A ≤ thresh A via eigenvectors or product of commuting
lemma mul_comm_nonneg {A B:Mat m} (ha:0≤A) (hb:0≤B) (hh:Commute A B) :
    0 ≤ A*B := by
  let S := CFC.sqrt B
  have he : Commute A S := by
    unfold S CFC.sqrt
    first | exact (hh.symm.cfc_nnreal _).symm | exact (hh.symm.cfcₙ_nnreal _).symm
  have hp : 0 ≤ S := CFC.sqrt_nonneg _
  calc
    _ ≤ S*A*S := sand_nonneg ha hp.posSemidef.1
    _ = _ := by rw [← he.eq,mul_assoc,show S*S=B from CFC.sqrt_mul_sqrt_self _ hb]

lemma thresh_low {A:Mat m} {b:ℝ} (ha:0≤A) (hb:0<b) (he:1+A ≤ scalar m b) :
    b⁻¹•A ≤ thresh A := by
  have hc : (scalar m b).PosDef :=
    form_posDef hb (show scalar m b∈specBox m b b from ⟨scalar_sym ..,le_rfl,le_rfl⟩)
  have hi := inv_rev (thresh_pd ha) hc he
  have heq : (scalar m b)⁻¹=scalar m b⁻¹ := by
    have hh := scalar_mul (m:=m) b⁻¹ b
    rw [inv_mul_cancel₀ hb.ne',show scalar m 1=1 from one_smul .. ] at hh
    exact ((left_inv_eq_left_inv (inv_mul' hc) hh))
  rw [heq] at hi
  have hb₁ := inv_mul' (thresh_pd ha)
  have hb₂ := mul_inv' (thresh_pd ha)
  have hp : Commute A ((1+A)⁻¹ - scalar m b⁻¹) := by
    have hh : Commute A (1+A)⁻¹ := by
      rw [mul_add,mul_one] at hb₁
      rw [add_mul,one_mul] at hb₂
      exact add_left_cancel (hb₂.trans hb₁.symm)
    exact hh.sub_right (by simp only [scalar_eq]; exact (Algebra.commutes _ _).symm)
  have hu := mul_comm_nonneg ha (sub_nonneg.mpr hi) hp
  rw [mul_sub,← thresh_eq ha] at hu
  rw [scalar,mul_smul_comm,mul_one,sub_nonneg] at hu
  exact hu
end GeneralMahler

end

end OAI
