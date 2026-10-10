import Mathlib
import OAI.Analysis.FreeWords.DyadicGrid

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance dyadicPhasesPartialOrder (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance dyadicPhasesPreorder (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance dyadicPhasesLE (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance dyadicPhasesStarOrderedRing (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

end

end KKProjectionSupport

namespace KKProjectionSupport

noncomputable section

def dyadicRoot (n : ℕ) : ℂ := Complex.exp (2*Real.pi*Complex.I/(2:ℂ)^n)

@[simp] theorem dyadicRoot_zero : dyadicRoot 0=1 := by
  simp only [dyadicRoot,pow_zero,div_one,Complex.exp_two_pi_mul_I]

theorem dyadicRoot_norm (n : ℕ) : ‖dyadicRoot n‖=1 := by
  have he : 2*Real.pi*Complex.I/(2:ℂ)^n=Complex.I*((2*Real.pi/(2:ℝ)^n:ℝ):ℂ) := by push_cast; ring
  rw [dyadicRoot,he,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_self,Real.exp_zero]

theorem dyadicRoot_square (n : ℕ) : dyadicRoot (n+1)^2=dyadicRoot n := by
  rw [dyadicRoot,dyadicRoot,← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

theorem dyadicRoot_sub_one (n : ℕ) : ‖dyadicRoot n-1‖ ≤ 2*Real.pi/(2:ℝ)^n := by
  have he : 2*Real.pi*Complex.I/(2:ℂ)^n=Complex.I*((2*Real.pi/(2:ℝ)^n:ℝ):ℂ) := by push_cast; ring
  rw [dyadicRoot,he]
  exact (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)])

theorem dyadicRoot_pow_ne_one (n k : ℕ) (hk : 0 < k) (hkn : k < 2^n) :
    dyadicRoot n^k≠1 := by
  rw [dyadicRoot,← Complex.exp_nat_mul]
  have he : (k:ℂ)*(2*Real.pi*Complex.I/(2:ℂ)^n)=2*Real.pi*Complex.I*k/(2^n:ℕ) := by push_cast; ring
  rw [he,ne_eq,Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (by positivity)]
  exact Nat.not_dvd_of_pos_of_lt hk hkn

def dyadicPhase : (n : ℕ) → BitWords n → ℂ
  | 0, _ => 1
  | n+1, w => dyadicPhase n w.1 * if w.2 then dyadicRoot (n+1) else 1

theorem dyadicPhase_norm (n : ℕ) (w : BitWords n) : ‖dyadicPhase n w‖=1 := by
  induction n with
  | zero => simp [dyadicPhase]
  | succ n ih =>
    rcases w with ⟨w,b⟩; cases b <;> simp only [dyadicPhase,Bool.false_eq_true,ite_false,
      ite_true,mul_one,norm_mul,ih,dyadicRoot_norm]

def phaseMoment (n k : ℕ) : ℂ := (1/2:ℂ)^n * ∑ w, dyadicPhase n w^k

@[simp] theorem phaseMoment_zero (k : ℕ) : phaseMoment 0 k=1 := by
  change (1/2:ℂ)^0 * ∑ _ : Unit, (1:ℂ)^k=1
  simp

theorem phaseMoment_succ (n k : ℕ) :
    phaseMoment (n+1) k=(1+dyadicRoot (n+1)^k)/2*phaseMoment n k := by
  change (1/2:ℂ)^(n+1) * (∑ w : BitWords n × Bool, dyadicPhase (n+1) w ^ k)=_
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,dyadicPhase,Bool.false_eq_true,ite_true,ite_false,
    mul_pow,mul_one,one_pow]
  simp only [Finset.sum_add_distrib,← Finset.sum_mul,phaseMoment,pow_succ]
  ring

theorem phaseMoment_annihilation (n k : ℕ) :
    (1-dyadicRoot n^k)*phaseMoment n k=0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [phaseMoment_succ]
    have hs : (dyadicRoot (n+1)^k)^2=dyadicRoot n^k := by
      rw [← pow_mul,mul_comm k 2,pow_mul,dyadicRoot_square]
    calc
      (1-dyadicRoot (n+1)^k)*((1+dyadicRoot (n+1)^k)/2*phaseMoment n k) =
          (1-(dyadicRoot (n+1)^k)^2)*phaseMoment n k/2 := by ring
      _ = 0 := by rw [hs,ih,zero_div]

theorem phaseMoment_eq_zero (n k : ℕ) (hk : 0 < k) (hkn : k < 2^n) :
    phaseMoment n k=0 :=
  (mul_eq_zero.mp (phaseMoment_annihilation n k)).resolve_left
    (sub_ne_zero.mpr (Ne.symm (dyadicRoot_pow_ne_one n k hk hkn)))

end

end KKProjectionSupport
end

end OAI
