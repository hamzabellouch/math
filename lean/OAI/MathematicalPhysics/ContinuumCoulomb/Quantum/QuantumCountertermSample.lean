import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAxisSample

namespace OAI

/-! The counterterms use only rational arithmetic and the fixed inverse-scale sample. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open scoped Classical

theorem factor_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCouplingFactor a b t = |t| *inverseScale a*inverseScale b := by
  have ha := inverseScale_mul a
  have hb := inverseScale_mul b
  have he : qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b = |t| :=
    qmaFourCouplingSize_square a b t
  calc
    _ = qmaFourCouplingFactor a b t*(inverseScale a*qmaFourAxisScale a)*
        (inverseScale b*qmaFourAxisScale b) := by rw [ha,hb]; ring
    _ = (qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b)*inverseScale a*inverseScale b := by ring
    _ = _ := by rw [he]

theorem counterA_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCounterA a b t = |t| *inverseScale b*qmaFourAxisShift b (qmaFourCouplingSign t) := by
  rw [qmaFourCounterA,factor_eq]
  calc
    _ = |t| *inverseScale b*(inverseScale a*qmaFourAxisScale a)*qmaFourAxisShift b (qmaFourCouplingSign t) := by ring
    _ = _ := by rw [inverseScale_mul]; ring

theorem counterB_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCounterB a b t = |t| *inverseScale a*qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisShift a true := by
  rw [qmaFourCounterB,factor_eq]
  calc
    _ = |t| *inverseScale a*qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisShift a true*
        (inverseScale b*qmaFourAxisScale b) := by ring
    _ = _ := by rw [inverseScale_mul]; ring

def shift (a : Fin 2) (p : Bool) : ℚ := if a = 0 then 400 else if p then 8/3 else 4/3
def polarity (t : ℚ) : ℚ := if t ≤ 0 then 1 else -1

theorem shift_cast (a : Fin 2) (p : Bool) : (shift a p:ℝ) = qmaFourAxisShift a p := by
  unfold shift qmaFourAxisShift
  split_ifs <;> norm_num

theorem polarity_cast (t : ℚ) : (polarity t:ℝ) = qmaFourAxisSign (qmaFourCouplingSign (t:ℝ)) := by
  by_cases ht : t ≤ 0
  · have htR : (t:ℝ) ≤ 0 := by exact_mod_cast ht
    simp [polarity,qmaFourAxisSign,qmaFourCouplingSign,ht,htR]
  · have htR : ¬(t:ℝ) ≤ 0 := by exact_mod_cast ht
    simp [polarity,qmaFourAxisSign,qmaFourCouplingSign,ht,htR]

theorem sign_cast (t : ℚ) : decide (t ≤ 0) = qmaFourCouplingSign (t:ℝ) := by
  unfold qmaFourCouplingSign
  congr 1
  exact propext (by exact_mod_cast (Iff.rfl : t ≤ 0 ↔ t ≤ 0))

def factor (k : ℕ) (a b : Fin 2) (t : ℚ) : ℚ := |t| *value k a*value k b
def counterA (k : ℕ) (_a b : Fin 2) (t : ℚ) : ℚ := |t| *value k b*shift b (decide (t ≤ 0))
def counterB (k : ℕ) (a _b : Fin 2) (t : ℚ) : ℚ := |t| *value k a*polarity t*shift a true

theorem factor_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(factor k a b t:ℝ)-qmaFourCouplingFactor a b (t:ℝ)| ≤ 2*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  rw [factor_eq]
  simp only [factor,Rat.cast_mul,Rat.cast_abs]
  calc
    _ = abs (|(t:ℝ)| *((value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b)) := by
      congr 1
      ring
    _ = |(t:ℝ)| *|(value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b| := by rw [abs_mul,abs_abs]
    _ ≤ |(t:ℝ)| *(2*(2:ℝ)⁻¹^k) := mul_le_mul_of_nonneg_left (product_error k a b) (abs_nonneg _)
    _ = _ := by ring

theorem counterA_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterA k a b t:ℝ)-qmaFourCounterA a b (t:ℝ)| ≤ 400*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  rw [counterA_eq]
  simp only [counterA,Rat.cast_mul,Rat.cast_abs,shift_cast,sign_cast]
  calc
    _ = abs (|(t:ℝ)| *((value k b:ℝ)-inverseScale b)*qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ))) := by
      congr 1
      ring
    _ = |(t:ℝ)| *|(value k b:ℝ)-inverseScale b| *|qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ))| := by
      rw [abs_mul,abs_mul,abs_abs]
    _ ≤ (|(t:ℝ)| *(2:ℝ)⁻¹^k)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_error k b) (abs_nonneg _))
      (qmaFourAxisShift_abs_bound b _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem counterB_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterB k a b t:ℝ)-qmaFourCounterB a b (t:ℝ)| ≤ 400*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  rw [counterB_eq]
  simp only [counterB,Rat.cast_mul,Rat.cast_abs,shift_cast,polarity_cast]
  calc
    _ = abs (|(t:ℝ)| *((value k a:ℝ)-inverseScale a)*qmaFourAxisSign (qmaFourCouplingSign (t:ℝ))*
        qmaFourAxisShift a true) := by
      congr 1
      ring
    _ = |(t:ℝ)| *|(value k a:ℝ)-inverseScale a| *|qmaFourAxisSign (qmaFourCouplingSign (t:ℝ))| *
        |qmaFourAxisShift a true| := by
      rw [abs_mul,abs_mul,abs_mul,abs_abs]
    _ = |(t:ℝ)| *|(value k a:ℝ)-inverseScale a| *|qmaFourAxisShift a true| := by
      rw [qmaFourAxisSign_abs,mul_one]
    _ ≤ (|(t:ℝ)| *(2:ℝ)⁻¹^k)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_error k a) (abs_nonneg _))
      (qmaFourAxisShift_abs_bound a true) (abs_nonneg _) (by positivity)
    _ = _ := by ring

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
