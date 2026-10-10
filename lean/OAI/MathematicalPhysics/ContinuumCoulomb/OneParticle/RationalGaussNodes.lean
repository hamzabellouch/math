import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedNodes
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalSquareRoot
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.EulerGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ResolventNumericalBounds

namespace OAI

/-! Rational initial nodes for the tensor Gauss rule on mesh `1/N`.
The only irrational constant is evaluated by the existing dyadic square-root
program; the error bound is uniform over the entire integer lattice. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.RationalGaussNodes
open CappedKernelProgram (Triple position)
open EulerRegisters (Registers)

abbrev Signs := Bool×(Bool×Bool)

def abscissa (P : ℕ) : ℚ := RationalSquareRoot.value (2*(P+1),(1/3:ℚ))
def signed (P : ℕ) (b : Bool) : ℚ := if b then abscissa P else -abscissa P
def index (k : Registers) (b : Signs) : GaussLatticeIndex :=
  (![k.1,k.2.1,k.2.2],![if b.1 then 1 else 0,if b.2.1 then 1 else 0,if b.2.2 then 1 else 0])
def value (P N : ℕ) (k : Registers) (b : Signs) : Triple :=
  (((k.1:ℚ)+signed P b.1/2)/N,
    (((k.2.1:ℚ)+signed P b.2.1/2)/N,((k.2.2:ℚ)+signed P b.2.2/2)/N))

theorem abscissa_error (P : ℕ) :
    |(abscissa P:ℝ)-gaussAbscissa| ≤ (2*((P:ℝ)+1))⁻¹ := by
  have he := RationalSquareRoot.value_error (2*(P+1)) (q := (1/3:ℚ)) (by norm_num)
  have hs : Real.sqrt ((1/3:ℚ):ℝ) = gaussAbscissa := by
    norm_num [gaussAbscissa,Real.sqrt_inv]
  rw [hs] at he
  apply he.trans
  have hn : 2*(P+1) ≤ 2^(2*(P+1)) := (ResolventSchedule.succ_le_two_pow _).trans' (by omega)
  have hr : 2*((P:ℝ)+1) ≤ (2:ℝ)^(2*(P+1)) := by exact_mod_cast hn
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hr

theorem signed_error (P : ℕ) (b : Bool) :
    |(signed P b:ℝ)-gaussNode (if b then 1 else 0)| ≤ (2*((P:ℝ)+1))⁻¹ := by
  cases b
  · change |((-abscissa P:ℚ):ℝ)-(-gaussAbscissa)| ≤ _
    rw [Rat.cast_neg,neg_sub_neg,abs_sub_comm]
    exact abscissa_error P
  · change |(abscissa P:ℝ)-gaussAbscissa| ≤ _
    exact abscissa_error P

private theorem coordinate_error (P : ℕ) {N : ℕ} (hN : 0 < N) (k : ℤ) (b : Bool) :
    |((((k:ℚ)+signed P b/2)/N:ℚ):ℝ)-
      (N:ℝ)⁻¹*((k:ℝ)+gaussNode (if b then 1 else 0)/2)| ≤
      (1/(2*(N:ℝ)))*(2*((P:ℝ)+1))⁻¹ := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hid : ((((k:ℚ)+signed P b/2)/N:ℚ):ℝ)-
      (N:ℝ)⁻¹*((k:ℝ)+gaussNode (if b then 1 else 0)/2) =
      (1/(2*(N:ℝ)))*((signed P b:ℝ)-gaussNode (if b then 1 else 0)) := by
    push_cast
    ring
  rw [hid,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(2*(N:ℝ)))]
  exact mul_le_mul_of_nonneg_left (signed_error P b) (by positivity)

theorem approximation_error (P : ℕ) {N : ℕ} (hN : 0 < N) (k : Registers) (b : Signs) :
    ‖position (value P N k b)-gaussLatticePoint (N:ℝ)⁻¹ (index k b)‖ ≤ ((P:ℝ)+1)⁻¹ := by
  let d : ℝ := (1/(2*(N:ℝ)))*(2*((P:ℝ)+1))⁻¹
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hc (a : Fin 3) :
      |(position (value P N k b)-gaussLatticePoint (N:ℝ)⁻¹ (index k b)) a| ≤ |(0:Position) a|+d := by
    fin_cases a
    · simpa [value,position,gaussLatticePoint,index,d] using coordinate_error P hN k.1 b.1
    · simpa [value,position,gaussLatticePoint,index,d] using coordinate_error P hN k.2.1 b.2.1
    · simpa [value,position,gaussLatticePoint,index,d] using coordinate_error P hN k.2.2 b.2.2
  have he := EulerRegisters.norm_of_coordinate_error hd hc
  simp only [norm_zero,zero_add] at he
  apply he.trans
  have hn : (1:ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hp : 0 < (P:ℝ)+1 := by positivity
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hid : 3*d = (3/(4*(N:ℝ)))/((P:ℝ)+1) := by
    dsimp [d]
    field_simp [hNp.ne',hp.ne']
    ring
  rw [hid,← one_div]
  apply div_le_div_of_nonneg_right _ hp.le
  apply (div_le_one (by positivity : (0:ℝ) < 4*(N:ℝ))).mpr
  nlinarith

/-- The initial-node error and the rational ODE solver error add after
transport by the actual common Lipschitz map. -/
theorem transported_error (G : Position → Position) {K : ℝ≥0} (hG : LipschitzWith K G)
    (P : ℕ) {N : ℕ} (hN : 0 < N) (k : Registers) (b : Signs)
    (out : Triple) {δ : ℝ}
    (he : ‖position out-G (position (value P N k b))‖ ≤ δ) :
    ‖position out-G (gaussLatticePoint (N:ℝ)⁻¹ (index k b))‖ ≤
      δ+(K:ℝ)*((P:ℝ)+1)⁻¹ := by
  have ht := hG.dist_le_mul (position (value P N k b))
    (gaussLatticePoint (N:ℝ)⁻¹ (index k b))
  rw [dist_eq_norm,dist_eq_norm] at ht
  have hh := ht.trans (mul_le_mul_of_nonneg_left (approximation_error P hN k b) K.coe_nonneg)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (G (position (value P N k b))) _).trans (add_le_add he hh)

end ContinuumCoulomb.RationalGaussNodes

end

end OAI
