import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabOriginValue
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ResolventSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ResolventNumericalBounds

namespace OAI

/-! Polynomial unary precision choices for the finite-slab scalar. -/

namespace ContinuumCoulomb.SlabOriginSchedule

abbrev Input := ℕ × (ℕ × ℕ)

def capDenominator (rho P : ℕ) : ℕ := 16*(rho+1)*(P+1)
def boxWeight (rho H S : ℕ) : ℕ := (rho+1)*(H+1)^2*(S+1)*(H+S+1)
def count (rho : ℕ) (x : Input) : ℕ :=
  128*boxWeight rho x.2.1 x.2.2*(x.1+1)*(capDenominator rho x.1)^2

def input (rho : ℕ) (x : Input) : SlabOriginValue.Input :=
  (count rho x, (((count rho x,(capDenominator rho x.1:ℚ)⁻¹),
    ((x.2.1:ℚ),(x.2.2:ℚ))),(-1,2/(count rho x:ℚ))))

def value (rho : ℕ) (x : Input) : ℚ := SlabOriginValue.value (rho:ℚ) (input rho x)

theorem capDenominator_positive (rho P : ℕ) : 0 < capDenominator rho P := by
  unfold capDenominator
  positivity

theorem boxWeight_positive (rho H S : ℕ) : 0 < boxWeight rho H S := by
  unfold boxWeight
  positivity

theorem count_positive (rho : ℕ) (x : Input) : 0 < count rho x := by
  unfold count
  exact mul_pos (mul_pos (mul_pos (by norm_num) (boxWeight_positive _ _ _))
    (Nat.succ_pos _)) (pow_pos (capDenominator_positive _ _) _)

theorem dyadic_error (n : ℕ) : (2:ℝ)⁻¹^n ≤ 1/(n+1:ℝ) := by
  have hn : n+1 ≤ 2^n := ResolventSchedule.succ_le_two_pow n
  have hr : (n+1:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hn
  rw [inv_pow,one_div]
  exact inv_anti₀ (by positivity) hr

theorem box_coefficient (rho H S : ℕ) :
    (rho:ℝ)*(H:ℝ)^2*(S:ℝ)*(6*((H:ℝ)+(S:ℝ))+1) ≤
      7*(boxWeight rho H S:ℝ) := by
  have hbase : (rho:ℝ)*(H:ℝ)^2*(S:ℝ)*((H:ℝ)+(S:ℝ)+1) ≤
      (boxWeight rho H S:ℝ) := by
    simp only [boxWeight,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
    gcongr <;> nlinarith
  have hA : 0 ≤ (rho:ℝ)*(H:ℝ)^2*(S:ℝ) := by positivity
  nlinarith [mul_nonneg hA (by positivity : 0 ≤ (H:ℝ)+(S:ℝ))]

theorem numeric_budget (rho : ℕ) (x : Input) :
    (rho:ℝ)*(x.2.1:ℝ)^2*(x.2.2:ℝ)*8*
      (3*((capDenominator rho x.1:ℝ)^2*((x.2.1:ℝ)+(x.2.2:ℝ)))*
        (2/(count rho x:ℝ))+(capDenominator rho x.1:ℝ)^2*(2:ℝ)⁻¹^(count rho x))+
      (rho:ℝ)*(2*Real.pi*((capDenominator rho x.1:ℝ)⁻¹)^2) ≤ 1/(x.1+1:ℝ) := by
  let Q : ℝ := capDenominator rho x.1
  let W : ℝ := boxWeight rho x.2.1 x.2.2
  let N : ℝ := count rho x
  let P : ℝ := x.1+1
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast capDenominator_positive rho x.1
  have hW : 0 < W := by dsimp [W]; exact_mod_cast boxWeight_positive rho x.2.1 x.2.2
  have hN : 0 < N := by dsimp [N]; exact_mod_cast count_positive rho x
  have hP : 0 < P := by dsimp [P]; positivity
  have hNdef : N=128*W*P*Q^2 := by simp [N,W,P,Q,count]
  have hQdef : Q=16*((rho:ℝ)+1)*P := by simp [Q,P,capDenominator]
  have hP1 : 1 ≤ P := by dsimp [P]; linarith [show (0:ℝ) ≤ (x.1:ℝ) from Nat.cast_nonneg _]
  have hQ1 : 1 ≤ Q := by nlinarith [show (0:ℝ) ≤ (rho:ℝ) from Nat.cast_nonneg _]
  have hQlarge : 16*(rho:ℝ)*P ≤ Q^2 := by
    have h1 : 16*(rho:ℝ)*P ≤ Q := by nlinarith
    exact h1.trans (by nlinarith)
  have hdyad : (2:ℝ)⁻¹^(count rho x) ≤ 1/N := by
    exact (dyadic_error _).trans (one_div_le_one_div_of_le hN (by dsimp [N]; norm_num))
  have hquad : (rho:ℝ)*(x.2.1:ℝ)^2*(x.2.2:ℝ)*8*
      (3*(Q^2*((x.2.1:ℝ)+(x.2.2:ℝ)))*(2/N)+Q^2*(2:ℝ)⁻¹^(count rho x)) ≤
      1/(2*P) := by
    calc
      _ ≤ 8*Q^2/N*((rho:ℝ)*(x.2.1:ℝ)^2*(x.2.2:ℝ)*
          (6*((x.2.1:ℝ)+(x.2.2:ℝ))+1)) := by
        have hm := mul_le_mul_of_nonneg_left hdyad
          (by positivity : 0 ≤ (rho:ℝ)*(x.2.1:ℝ)^2*(x.2.2:ℝ)*8*Q^2)
        calc
          _ = (rho:ℝ)*(x.2.1:ℝ)^2*(x.2.2:ℝ)*8*
              (3*(Q^2*((x.2.1:ℝ)+(x.2.2:ℝ)))*(2/N))+
            (rho:ℝ)*(x.2.1:ℝ)^2*(x.2.2:ℝ)*8*Q^2*(2:ℝ)⁻¹^(count rho x) := by ring
          _ ≤ (rho:ℝ)*(x.2.1:ℝ)^2*(x.2.2:ℝ)*8*
              (3*(Q^2*((x.2.1:ℝ)+(x.2.2:ℝ)))*(2/N))+
            (rho:ℝ)*(x.2.1:ℝ)^2*(x.2.2:ℝ)*8*Q^2*(1/N) := add_le_add le_rfl hm
          _ = _ := by ring
      _ ≤ 8*Q^2/N*(7*W) := mul_le_mul_of_nonneg_left
        (box_coefficient rho x.2.1 x.2.2) (by positivity)
      _ ≤ 1/(2*P) := by
        rw [hNdef]
        field_simp [hW.ne',hP.ne',hQ.ne']
        nlinarith [sq_pos_of_pos hQ]
  have hcap : (rho:ℝ)*(2*Real.pi*(Q⁻¹)^2) ≤ 1/(2*P) := by
    have hb : 16*(rho:ℝ)*P/Q^2 ≤ 1 := (div_le_one (sq_pos_of_pos hQ)).mpr hQlarge
    have hpi := Real.pi_lt_four
    have hr : (rho:ℝ)*8/Q^2 ≤ 1/(2*P) := by
      apply (le_div_iff₀ (by positivity : 0 < 2*P)).mpr
      convert hb using 1; ring
    calc
      _ = (2*(rho:ℝ)/Q^2)*Real.pi := by rw [inv_pow]; ring
      _ ≤ (2*(rho:ℝ)/Q^2)*4 :=
        mul_le_mul_of_nonneg_left hpi.le (by positivity)
      _ = (rho:ℝ)*8/Q^2 := by ring
      _ ≤ _ := hr
  change _ ≤ 1/P
  have hsum : 1/(2*P)+1/(2*P)=1/P := by
    field_simp [hP.ne']
    ring
  exact (add_le_add hquad hcap).trans_eq hsum

theorem error (rho : ℕ) (x : Input) :
    |(value rho x:ℝ)-slabPotential (rho:ℝ) (x.2.1:ℝ) (x.2.2:ℝ) 0| ≤
      1/(x.1+1:ℝ) := by
  have hN := count_positive rho x
  have hQ := capDenominator_positive rho x.1
  have hnq : (count rho x:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have he := SlabOriginValue.error (rho:ℚ) (input rho x) (by positivity)
    (by dsimp [input]; positivity)
    (by change (0:ℚ) ≤ x.2.1; positivity) (by change (0:ℚ) ≤ x.2.2; positivity)
    (by dsimp [input]; positivity) rfl (by dsimp [input]; field_simp [hnq])
  apply he.trans
  simpa only [input,Rat.cast_inv,Rat.cast_natCast,inv_inv,Rat.cast_div,Rat.cast_ofNat,
    one_div] using numeric_budget rho x

end ContinuumCoulomb.SlabOriginSchedule

end OAI
