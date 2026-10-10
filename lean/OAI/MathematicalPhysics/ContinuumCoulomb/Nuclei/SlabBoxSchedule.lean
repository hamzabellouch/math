import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SlabOriginProgram

namespace OAI

/-! Rational slab dimensions with separate unary magnitude bounds. This
covers exactly the half-cell boundary of the odd centered grid. -/

noncomputable section
namespace ContinuumCoulomb.SlabBoxSchedule

abbrev Input := SlabOriginSchedule.Input × (ℚ×ℚ)

def input (rho : ℕ) (x : Input) : SlabOriginValue.Input :=
  (SlabOriginSchedule.count rho x.1,
    (((SlabOriginSchedule.count rho x.1,
      (SlabOriginSchedule.capDenominator rho x.1.1:ℚ)⁻¹),x.2),
      (-1,2/(SlabOriginSchedule.count rho x.1:ℚ))))

def value (rho : ℕ) (x : Input) : ℚ := SlabOriginValue.value (rho:ℚ) (input rho x)

def bound (rho Q N : ℕ) (H S : ℝ) : ℝ :=
  (rho:ℝ)*H^2*S*8*(3*((Q:ℝ)^2*(H+S))*(2/(N:ℝ))+
    (Q:ℝ)^2*(2:ℝ)⁻¹^N)+(rho:ℝ)*(2*Real.pi*((Q:ℝ)⁻¹)^2)

theorem bound_mono (rho Q N : ℕ) {H S A B : ℝ}
    (hH : 0 ≤ H) (hS : 0 ≤ S) (hHA : H ≤ A) (hSB : S ≤ B) :
    bound rho Q N H S ≤ bound rho Q N A B := by
  have hB : 0 ≤ B := hS.trans hSB
  unfold bound
  gcongr

theorem error (rho : ℕ) (x : Input)
    (hH : 0 ≤ x.2.1) (hS : 0 ≤ x.2.2)
    (hHcap : x.2.1 ≤ (x.1.2.1:ℚ)) (hScap : x.2.2 ≤ (x.1.2.2:ℚ)) :
    |(value rho x:ℝ)-slabPotential (rho:ℝ) (x.2.1:ℝ) (x.2.2:ℝ) 0| ≤
      1/(x.1.1+1:ℝ) := by
  have hN := SlabOriginSchedule.count_positive rho x.1
  have hQ := SlabOriginSchedule.capDenominator_positive rho x.1.1
  have hnq : (SlabOriginSchedule.count rho x.1:ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  have he := SlabOriginValue.error (rho:ℚ) (input rho x) (by positivity)
    (by dsimp [input]; positivity) hH hS
    (by dsimp [input]; positivity) rfl (by dsimp [input]; field_simp [hnq])
  apply he.trans
  calc
    _ = bound rho (SlabOriginSchedule.capDenominator rho x.1.1)
        (SlabOriginSchedule.count rho x.1) (x.2.1:ℝ) (x.2.2:ℝ) := by
      simp only [input,bound,Rat.cast_inv,Rat.cast_natCast,inv_inv,Rat.cast_div,
        Rat.cast_ofNat]
    _ ≤ bound rho (SlabOriginSchedule.capDenominator rho x.1.1)
        (SlabOriginSchedule.count rho x.1) (x.1.2.1:ℝ) (x.1.2.2:ℝ) :=
      bound_mono rho _ _ (by exact_mod_cast hH) (by exact_mod_cast hS)
        (by exact_mod_cast hHcap) (by exact_mod_cast hScap)
    _ ≤ _ := SlabOriginSchedule.numeric_budget rho x.1

/-- Exact half-width of the slab covered by centered indices from -q to q. -/
def centeredWidth (q N : ℕ) : ℚ := ((q:ℚ)+1/2)/N

theorem centeredWidth_nonnegative (q N : ℕ) : 0 ≤ centeredWidth q N := by
  unfold centeredWidth
  positivity

theorem centeredWidth_le (q N : ℕ) (hN : 0 < N) :
    centeredWidth q N ≤ (q+1:ℚ) := by
  have hn : (1:ℚ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  calc
    _ ≤ (q:ℚ)+1/2 := div_le_self (by positivity) hn
    _ ≤ _ := by linarith

theorem centeredWidth_real (q N : ℕ) :
    (centeredWidth q N:ℝ) = ((q:ℝ)+1/2)*(N:ℝ)⁻¹ := by
  simp [centeredWidth,div_eq_mul_inv]

theorem centeredWidth_product (W N : ℕ) (hN : 0 < N) :
    centeredWidth (W*N) N = (W:ℚ)+1/(2*(N:ℚ)) := by
  have hn : (N:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [centeredWidth,Nat.cast_mul]
  field_simp [hn]

theorem centeredWidth_product_bounds (W N : ℕ) (hW : 0 < W) (hN : 0 < N) :
    (W:ℚ) ≤ centeredWidth (W*N) N ∧ centeredWidth (W*N) N ≤ 2*(W:ℚ) := by
  rw [centeredWidth_product W N hN]
  have hn : (1:ℚ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hw : (1:ℚ) ≤ W := by exact_mod_cast (Nat.succ_le_iff.mpr hW)
  have he : 0 ≤ 1/(2*(N:ℚ)) := by positivity
  have he' : 1/(2*(N:ℚ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  constructor <;> linarith

def centered (P N H S : ℕ) : Input :=
  ((P,(H+1,S+1)),(centeredWidth H N,centeredWidth S N))

theorem centered_error (rho P N H S : ℕ) (hN : 0 < N) :
    |(value rho (centered P N H S):ℝ)-
      slabPotential (rho:ℝ) (((H:ℝ)+1/2)*(N:ℝ)⁻¹)
        (((S:ℝ)+1/2)*(N:ℝ)⁻¹) 0| ≤ 1/(P+1:ℝ) := by
  simpa only [centered,centeredWidth_real] using error rho (centered P N H S)
    (centeredWidth_nonnegative H N) (centeredWidth_nonnegative S N)
    (by simpa only [centered,Nat.cast_add,Nat.cast_one] using centeredWidth_le H N hN)
    (by simpa only [centered,Nat.cast_add,Nat.cast_one] using centeredWidth_le S N hN)

end ContinuumCoulomb.SlabBoxSchedule

end

end OAI
