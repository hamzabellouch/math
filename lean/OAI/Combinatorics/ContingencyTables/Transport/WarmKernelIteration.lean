import OAI.Combinatorics.ContingencyTables.Transport.RealKernelApproximation

namespace OAI

/-! # Repeating an implementation bound averaged under the exact warm law -/

namespace ContingencyTables.WarmKernelIteration

open CommonBasesFPRAS RealKernelApproximation
open scoped BigOperators Classical

noncomputable section
variable {X : Type*} [Fintype X]

/-- At every replacement step the reference distribution remains warm.
No warmness assumption is imposed on the implemented distribution. -/
theorem power_distance (C : FiniteChain X) (K : FiniteKernel X X)
    (nu : X → ℝ) (hnu : ∀ x,0≤nu x) (hmass : ∑ x,nu x≤1)
    (U e : ℝ) (hwarm : ∀ x,nu x≤U*C.π x)
    (hstep : ∀ rho : X → ℝ,(∀ x,0≤rho x) → (∑ x,rho x≤1) →
      (∀ x,rho x≤U*C.π x) → distance (K.push rho) (C.kernel.push rho)≤e)
    (n : ℕ) :
    distance ((K.power n).push nu) ((C.kernel.power n).push nu)≤n*e := by
  induction n with
  | zero => simp [FiniteKernel.power,FiniteKernel.push_identity,distance]
  | succ n ih =>
    let p := (K.power n).push nu
    let q := (C.kernel.power n).push nu
    have hq0 : ∀ x,0≤q x := (C.kernel.power n).push_nonneg nu hnu
    have hq1 : ∑ x,q x≤1 := by
      dsimp only [q]
      rw [C.power_push_mass]
      exact hmass
    have hqwarm : ∀ x,q x≤U*C.π x := C.power_warm n nu U hwarm
    have ht := distance_triangle (K.push p) (K.push q) (C.kernel.push q)
    have hc := distance_push K p q
    have hs := hstep q hq0 hq1 hqwarm
    rw [FiniteKernel.power_push_succ,FiniteKernel.power_push_succ]
    change distance (K.push p) (C.kernel.push q)≤_
    have hh : distance (K.push p) (C.kernel.push q)≤distance p q+e := by linarith
    exact hh.trans (by dsimp only [p,q]; push_cast; linarith)

/-- A uniform relative row estimate gives the corresponding total
variation estimate for every normalized incoming distribution. -/
theorem mixing_distance (C : FiniteChain X) (nu : X → ℝ)
    (hnu : ∀ x,0≤nu x) (hmass : ∑ x,nu x=1) (n : ℕ) (e : ℝ)
    (hmix : ∀ x y,|((C.kernel.power n).P x y)/C.π y-1|≤e) :
    distance ((C.kernel.power n).push nu) C.π≤e/2 := by
  have hpoint (x y : X) : |(C.kernel.power n).P x y-C.π y|≤e*C.π y := by
    have he : (((C.kernel.power n).P x y)/C.π y-1)*C.π y=
        (C.kernel.power n).P x y-C.π y := by
      field_simp [(C.positive y).ne']
    rw [←he,abs_mul,abs_of_pos (C.positive y)]
    exact mul_le_mul_of_nonneg_right (hmix x y) (C.positive y).le
  have hmixpoint (y : X) : |(C.kernel.power n).push nu y-C.π y|≤e*C.π y := by
    have he : (C.kernel.power n).push nu y-C.π y=
        ∑ x,nu x*((C.kernel.power n).P x y-C.π y) := by
      simp only [FiniteKernel.push,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hmass,one_mul]
    rw [he]
    calc
      _ ≤ ∑ x,|nu x*((C.kernel.power n).P x y-C.π y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x,nu x*(e*C.π y) := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul,abs_of_nonneg (hnu x)]
        exact mul_le_mul_of_nonneg_left (hpoint x y) (hnu x)
      _ = _ := by rw [←Finset.sum_mul,hmass,one_mul]
  unfold distance
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ y,e*C.π y := Finset.sum_le_sum (fun y _ => hmixpoint y)
    _ = e := by rw [←Finset.mul_sum,C.normalized,mul_one]

end
end ContingencyTables.WarmKernelIteration

end OAI
