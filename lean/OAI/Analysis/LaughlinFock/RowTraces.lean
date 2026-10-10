import Mathlib
import OAI.Analysis.LaughlinFock.HighestTails

namespace OAI

/-! Row Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

 

def rowThreePrewedge {β : Type*} [Fintype β] (Q : ℕ) (t : PairLabel Q) (ℓ : ℝ)
    (p : β → PairLabel Q) (i j : β → Orbital Q) (a : β → ℝ) :
    Matrix (PairLabel Q × Orbital Q) (PairLabel Q × Orbital Q) ℂ :=
  (∑ b, (ℓ*a b : ℂ) •
    (Matrix.single (t,i b) (p b,j b) 1 + Matrix.single (p b,j b) (t,i b) 1)) +
  ∑ b, ∑ c, (a b*a c : ℂ) •
    (if i b = i c then Matrix.single (p b,j b) (p c,j c) 1 else 0)

 

theorem exteriorLift_single_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q k : ℕ) (W : Matrix (SectorOccupation Q k) ι ℂ) (b c : ι) :
    exteriorLift Q k (W * Matrix.single b c (1 : ℂ) * Wᴴ) =
      (wedgeAnnihilator Q k (fun A => W A b))ᴴ *
        wedgeAnnihilator Q k (fun A => W A c) := by
  rw [exteriorLift_congruence]
  simp [Matrix.single_apply, ite_smul, ite_and]

 

theorem rowThreePrewedge_lift {β : Type*} [Fintype β]
    (Q : ℕ) (t : PairLabel Q) (ℓ : ℝ) (p : β → PairLabel Q)
    (i j : β → Orbital Q) (a : β → ℝ) :
    exteriorLift Q 3 (threeWedgeMatrix Q * rowThreePrewedge Q t ℓ p i j a *
      (threeWedgeMatrix Q)ᴴ) = rowThreeBody Q t.val ℓ (fun b => (p b).val) i j a := by
  classical
  have hs (c : ℂ) (M : Matrix (SectorOccupation Q 3) (SectorOccupation Q 3) ℂ) :
      exteriorLift Q 3 (c • M) = c • exteriorLift Q 3 M :=
    (exteriorLiftLinear Q 3).map_smul c M
  simp only [rowThreePrewedge, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, exteriorLift_add, exteriorLift_sum, hs]
  simp_rw [exteriorLift_single_congruence, threeWedgeMatrix_annihilator_column]
  unfold rowThreeBody
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro b _
    ext A B
    simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul, mul_add]
  · apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    split_ifs
    · rw [exteriorLift_single_congruence,
        threeWedgeMatrix_annihilator_column, threeWedgeMatrix_annihilator_column]
      ext A B
      simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul]
    · simp [exteriorLift]

 
theorem single_bilinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : ι) (x y : ι → ℂ) :
    star x ⬝ᵥ (Matrix.single b c 1 *ᵥ y) = star (x b) * y c := by
  simp [dotProduct, Matrix.mulVec, Matrix.single_apply, ite_mul, ite_and]

 

theorem rowThreePrewedge_bilinear {β : Type*} [Fintype β]
    (Q : ℕ) (t : PairLabel Q) (ℓ : ℝ) (p : β → PairLabel Q)
    (i j : β → Orbital Q) (a : β → ℝ) (x y : PairLabel Q × Orbital Q → ℝ) :
    star (fun b => (x b : ℂ)) ⬝ᵥ (rowThreePrewedge Q t ℓ p i j a *ᵥ
      fun b => (y b : ℂ)) =
      ((∑ b, ℓ*a b * (x (t,i b)*y (p b,j b) + x (p b,j b)*y (t,i b))) +
        ∑ b, ∑ c, if i b = i c then a b*a c*x (p b,j b)*y (p c,j c) else 0 : ℝ) := by
  classical
  simp only [rowThreePrewedge, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.sum_mulVec, dotProduct_add, dotProduct_sum, dotProduct_smul]
  simp_rw [single_bilinear, Complex.star_def, Complex.conj_ofReal]
  simp only [Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro b _
    ring
  · apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp [single_bilinear, Matrix.zero_mulVec, dotProduct_zero, mul_assoc]

 

abbrev RowEntry (t : ℕ) := { b : Fin 8 × Fin 9 // t ≤ b.1.val+b.2.val ∧ b.1.val+b.2.val ≤ t+8 }

def rowP {t : ℕ} (b : RowEntry t) : ℕ := b.val.1.val
def rowJ {t : ℕ} (b : RowEntry t) : ℕ := b.val.2.val
def rowI {t : ℕ} (b : RowEntry t) : ℕ := rowP b+rowJ b-t

theorem rowEntry_bounds {t : ℕ} (b : RowEntry t) :
    rowP b ≤ 7 ∧ rowJ b ≤ 8 ∧ rowI b ≤ 8 ∧ t+rowI b = rowP b+rowJ b := by
  have hp := b.val.1.isLt
  have hj := b.val.2.isLt
  have ht := b.property
  dsimp [rowP, rowJ, rowI]
  omega

theorem rowI_eq_iff {t : ℕ} (b c : RowEntry t) :
    rowI b = rowI c ↔ rowP b+rowJ b = rowP c+rowJ c := by
  have hb := (rowEntry_bounds b).2.2.2
  have hc := (rowEntry_bounds c).2.2.2
  omega

 
def rowFourLevel {t : ℕ} (b c : RowEntry t) : ℕ := rowP b+rowJ b+rowI c

theorem rowFourLevel_symm {t : ℕ} (b c : RowEntry t) :
    rowFourLevel b c = rowFourLevel c b := by
  have hb := (rowEntry_bounds b).2.2.2
  have hc := (rowEntry_bounds c).2.2.2
  dsimp [rowFourLevel]
  omega

theorem rowFourLevel_le {t : ℕ} (b c : RowEntry t) : rowFourLevel b c ≤ 23 := by
  have hb := rowEntry_bounds b
  have hc := rowEntry_bounds c
  dsimp [rowFourLevel]
  omega

 
def sphericalThreeCoefficient (Q z T p : ℕ) : ℝ :=
  if z ≤ T then coupledCoefficient (2*Q-2) Q z (T-z) p else 0

 
def planarThreeCoefficient (z T p : ℕ) : ℝ :=
  if z ≤ T then polynomialCouplingCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3))
    z (T-z) p else 0

theorem sphericalThreeCoefficient_tendsto (z T p : ℕ) :
    Tendsto (fun Q => sphericalThreeCoefficient Q z T p) atTop
      (𝓝 (planarThreeCoefficient z T p)) := by
  unfold sphericalThreeCoefficient planarThreeCoefficient
  split_ifs
  · exact threeCoupling_tendsto z (T-z) p
  · exact tendsto_const_nhds

 

def rowThreeTrace (Q z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ) : ℝ :=
  ∑ T ∈ Finset.range 16, if z ≤ T ∧ t ≤ T then
    let X := ∑ b : RowEntry t, if rowP b+rowJ b=T then
      a b*sphericalThreeCoefficient Q z T (rowP b) else 0
    2*ℓ*sphericalThreeCoefficient Q z T t*X + X^2
  else 0

 
def planarRowThreeTrace (z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ) : ℝ :=
  ∑ T ∈ Finset.range 16, if z ≤ T ∧ t ≤ T then
    let X := ∑ b : RowEntry t, if rowP b+rowJ b=T then
      a b*planarThreeCoefficient z T (rowP b) else 0
    2*ℓ*planarThreeCoefficient z T t*X + X^2
  else 0

 

theorem rowThreeTrace_tendsto (z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ) :
    Tendsto (fun Q => rowThreeTrace Q z t ℓ a) atTop (𝓝 (planarRowThreeTrace z t ℓ a)) := by
  unfold rowThreeTrace planarRowThreeTrace
  apply tendsto_finsetSum
  intro T _
  split_ifs
  · have hX : Tendsto (fun Q => ∑ b : RowEntry t, if rowP b+rowJ b=T then
        a b*sphericalThreeCoefficient Q z T (rowP b) else 0) atTop
        (𝓝 (∑ b : RowEntry t, if rowP b+rowJ b=T then
          a b*planarThreeCoefficient z T (rowP b) else 0)) := by
      apply tendsto_finsetSum
      intro b _
      split_ifs
      · exact (sphericalThreeCoefficient_tendsto z T (rowP b)).const_mul (a b)
      · exact tendsto_const_nhds
    exact (((sphericalThreeCoefficient_tendsto z T t).const_mul (2*ℓ)).mul hX).add (hX.pow 2)
  · exact tendsto_const_nhds

 

def rowFourTrace (Q D t : ℕ) (a : RowEntry t → ℝ) : Matrix (CopyLabel D) (CopyLabel D) ℝ :=
  fun r s => -(∑ b : RowEntry t, ∑ c : RowEntry t,
    a b*a c*sphericalCopyCoefficient Q D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      sphericalCopyCoefficient Q D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b))

 
def planarRowFourTrace (D t : ℕ) (a : RowEntry t → ℝ) : Matrix (CopyLabel D) (CopyLabel D) ℝ :=
  fun r s => -(∑ b : RowEntry t, ∑ c : RowEntry t,
    a b*a c*planarCopyCoefficient D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      planarCopyCoefficient D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b))

 

theorem rowFourTrace_tendsto (D t : ℕ) (a : RowEntry t → ℝ) (r s : CopyLabel D) :
    Tendsto (fun Q => rowFourTrace Q D t a r s) atTop (𝓝 (planarRowFourTrace D t a r s)) := by
  unfold rowFourTrace planarRowFourTrace
  apply Filter.Tendsto.neg
  apply tendsto_finsetSum
  intro b _
  apply tendsto_finsetSum
  intro c _
  exact ((sphericalCopyCoefficient_tendsto D (rowFourLevel b c) r.val.val
    (rowP b) (rowJ b) (rowI c)).const_mul (a b*a c)).mul
      (sphericalCopyCoefficient_tendsto D (rowFourLevel b c) s.val.val
        (rowP c) (rowJ c) (rowI b))

 

theorem rowFourTrace_symmetric (Q D t : ℕ) (a : RowEntry t → ℝ) :
    (rowFourTrace Q D t a).IsSymm := by
  ext r s
  change rowFourTrace Q D t a s r = rowFourTrace Q D t a r s
  unfold rowFourTrace
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [rowFourLevel_symm c b]
  ring

theorem planarRowFourTrace_symmetric (D t : ℕ) (a : RowEntry t → ℝ) :
    (planarRowFourTrace D t a).IsSymm := by
  ext r s
  change planarRowFourTrace D t a s r = planarRowFourTrace D t a r s
  unfold planarRowFourTrace
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [rowFourLevel_symm c b]
  ring

end LaughlinFock
end

end OAI
