import OAI.Probability.ClassicalON.BondExpansion

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def spinBondParameter (left right : E → V) (b : E → ℝ) (s : V → Spin 3) (e : E) : ℝ :=
  1-Real.exp (-2*b e*max ((s (left e)).val 0*(s (right e)).val 0) 0)

def spinBondWeight (left right : E → V) (b : E → ℝ) (s : V → Spin 3) (η : E → Bool) : ℝ :=
  ∏ e,if η e then spinBondParameter left right b s e else 1-spinBondParameter left right b s e

omit [Fintype V] [Fintype E] in
theorem continuous_spinBondParameter (left right : E → V) (b : E → ℝ) (e : E) :
    Continuous (fun s => spinBondParameter left right b s e) := by
  unfold spinBondParameter
  fun_prop

omit [Fintype V] in
theorem continuous_spinBondWeight (left right : E → V) (b : E → ℝ) (η : E → Bool) :
    Continuous (fun s => spinBondWeight left right b s η) := by
  unfold spinBondWeight
  apply continuous_finsetProd
  intro e _
  split <;> [exact continuous_spinBondParameter _ _ _ _;exact continuous_const.sub (continuous_spinBondParameter _ _ _ _)]

omit [Fintype V] [Fintype E] in
theorem spinBondParameter_bounds (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (s : V → Spin 3) (e : E) : 0 ≤ spinBondParameter left right b s e ∧ spinBondParameter left right b s e≤1 := by
  have hn : -2*b e*max ((s (left e)).val 0*(s (right e)).val 0) 0≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hb e)) (le_max_right _ _)
  have h := Real.exp_le_one_iff.mpr hn
  have hp := Real.exp_pos (-2*b e*max ((s (left e)).val 0*(s (right e)).val 0) 0)
  constructor <;> unfold spinBondParameter <;> linarith

omit [Fintype V] in
theorem spinBondWeight_nonneg (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (s : V → Spin 3) (η : E → Bool) : 0 ≤ spinBondWeight left right b s η := by
  apply Finset.prod_nonneg
  intro e _
  split
  · exact (spinBondParameter_bounds _ _ _ hb s e).1
  · exact sub_nonneg.mpr (spinBondParameter_bounds _ _ _ hb s e).2

omit [Fintype V] in
theorem spinBondWeight_sum (left right : E → V) (b : E → ℝ) (s : V → Spin 3) :
    (∑ η,spinBondWeight left right b s η)=1 := by
  unfold spinBondWeight
  change (∑ η : E → Bool, ∏ e, (fun (e : E) (z : Bool) => if z then spinBondParameter left right b s e else 1-spinBondParameter left right b s e) e (η e)) = 1
  rw [← Fintype.prod_sum (fun (e : E) (z : Bool) => if z then spinBondParameter left right b s e else 1-spinBondParameter left right b s e)]
  simp

omit [Fintype V] [Fintype E] in
theorem spinBondParameter_cylinder (left right : E → V) (b : E → ℝ)
    (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) (e : E) :
    spinBondParameter left right b (cylindricalConfiguration r τ θ) e=
      if τ (left e)=τ (right e) then 1-Real.exp (-2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e) else 0 := by
  have hp : 0≤(r (left e):ℝ)*(r (right e):ℝ) := mul_nonneg (r (left e)).property.1 (r (right e)).property.1
  unfold spinBondParameter cylindricalConfiguration cylindricalSpin
  simp only [Fin.isValue,Matrix.cons_val_zero]
  have hmul : (r (left e):ℝ)*signValue (τ (left e))*((r (right e):ℝ)*signValue (τ (right e)))=
      (r (left e):ℝ)*(r (right e):ℝ)*(signValue (τ (left e))*signValue (τ (right e))) := by ring
  rw [hmul]
  cases τ (left e) <;> cases τ (right e) <;> simp only [signValue,Bool.false_eq_true,ite_false,ite_true,
    mul_neg,neg_mul,mul_one,neg_neg]
  all_goals simp only [max_eq_left hp,max_eq_right (neg_nonpos.mpr hp),mul_zero,neg_zero,Real.exp_zero,sub_self]
  all_goals (congr 2 <;> (unfold amplitudeCoupling; ring))

omit [Fintype V] in
theorem cylindrical_ising_bond_weight (left right : E → V) (K : E → ℝ) (τ : V → Bool) (η : E → Bool) :
    Real.exp (edgeHamiltonian (isingEnergy left right) K τ)*
      (∏ e,if η e then (if τ (left e)=τ (right e) then 1-Real.exp (-2*K e) else 0)
        else 1-(if τ (left e)=τ (right e) then 1-Real.exp (-2*K e) else 0))=
      Real.exp (-∑ e,K e)*bondSignProduct left right (fun e => Real.exp (2*K e)-1) η τ := by
  have he (k : ℝ) (a d z : Bool) :
      Real.exp (k*(signValue a*signValue d))*(if z then (if a=d then 1-Real.exp (-2*k) else 0)
        else 1-(if a=d then 1-Real.exp (-2*k) else 0))=
      Real.exp (-k)*(if z then (if a=d then Real.exp (2*k)-1 else 0) else 1) := by
    have h1 : Real.exp k*Real.exp (-(2*k))=Real.exp (-k) := by rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-k)*Real.exp (2*k)=Real.exp k := by rw [← Real.exp_add]; congr 1; ring
    cases a <;> cases d <;> cases z <;> simp [signValue,mul_sub,h1,h2]
  unfold edgeHamiltonian isingEnergy
  rw [Real.exp_sum,← Finset.prod_mul_distrib]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_neg_distrib]
  rfl

omit [Fintype V] in
theorem cylindrical_spin_bond_weight (left right : E → V) (b : E → ℝ)
    (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) (η : E → Bool) :
    Real.exp (freeSpinEnergy 3 left right b (cylindricalConfiguration r τ θ))*
      spinBondWeight left right b (cylindricalConfiguration r τ θ) η=
      Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
        bondSignProduct left right (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1) η τ*
        Real.exp (edgeHamiltonian (planarEnergy left right)
          (amplitudeCoupling left right b (fun v => transverseAmplitude (r v))) θ) := by
  rw [cylindricalConfiguration_energy,Real.exp_add]
  unfold spinBondWeight
  simp_rw [spinBondParameter_cylinder]
  rw [mul_right_comm, cylindrical_ising_bond_weight]

end ClassicalON

end

end OAI
