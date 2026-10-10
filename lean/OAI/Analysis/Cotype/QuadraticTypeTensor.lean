import OAI.Analysis.Cotype.FixedTypeImprovement
import OAI.Analysis.Cotype.WalshCoordinates
import OAI.Analysis.Cotype.NoiseHypercontractivity

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def QuadraticTypeBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) (A : ℝ) : Prop :=
  ∀ x : Fin n → X, cubeL2 X (rademacherSum X x)^2 ≤ A*∑ i, ‖x i‖^2

def signCubeTwist {n : ℕ} (σ : Cube n) : Cube n ≃ Cube n where
  toFun ε i := xor (σ i) (ε i)
  invFun ε i := xor (σ i) (ε i)
  left_inv ε := by
    funext i
    change xor (σ i) (xor (σ i) (ε i)) = ε i
    cases σ i <;> cases ε i <;> rfl
  right_inv ε := by
    funext i
    change xor (σ i) (xor (σ i) (ε i)) = ε i
    cases σ i <;> cases ε i <;> rfl

@[simp] theorem sign_mul_of_xor (a b : Bool) : sign (xor a b) = sign a*sign b := by
  cases a <;> cases b <;> norm_num

theorem average_rademacher_twist {n : ℕ} (x : Fin n → X) (σ : Cube n) :
    average (fun ε : Cube n => ‖∑ i, (sign (σ i)*sign (ε i)) • x i‖^2) =
      cubeL2 X (rademacherSum X x)^2 := by
  rw [cubeL2_sq]
  simpa only [signCubeTwist,rademacherSum,Equiv.coe_fn_mk,sign_mul_of_xor] using
    average_equiv (signCubeTwist σ) (fun ε => ‖rademacherSum X x ε‖^2)

theorem average_const_value {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp [average,smul_eq_mul]

theorem quadraticTypeBound_chaos {n m : ℕ} {A B : ℝ} (hA : 0 ≤ A)
    (hn : QuadraticTypeBound X n A) (hm : QuadraticTypeBound X m B)
    (x : Fin n → Fin m → X) :
    average (fun ε : Cube n => average (fun η : Cube m =>
      ‖∑ i, ∑ j, (sign (ε i)*sign (η j)) • x i j‖^2)) ≤
        A*B*∑ i, ∑ j, ‖x i j‖^2 := by
  classical
  rw [average_comm]
  have hin (η : Cube m) : average (fun ε : Cube n =>
      ‖∑ i, ∑ j, (sign (ε i)*sign (η j)) • x i j‖^2) ≤
        A*∑ i, ‖rademacherSum X (x i) η‖^2 := by
    have hh := hn (fun i => rademacherSum X (x i) η)
    simpa only [cubeL2_sq,rademacherSum,Finset.smul_sum,smul_smul] using hh
  have hb := average_mono hin
  have he : average (fun η : Cube m => A*∑ i, ‖rademacherSum X (x i) η‖^2) =
      A*∑ i, cubeL2 X (rademacherSum X (x i))^2 := by
    simp only [cubeL2_sq,average,smul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro η _
    ring
  rw [he] at hb
  calc
    _ ≤ A*∑ i, cubeL2 X (rademacherSum X (x i))^2 := hb
    _ ≤ A*∑ i, B*∑ j, ‖x i j‖^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hm (x i))) hA
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem quadraticTypeBound_mul {n m : ℕ} {A B : ℝ} (hA : 0 ≤ A)
    (hn : QuadraticTypeBound X n A) (hm : QuadraticTypeBound X m B) :
    QuadraticTypeBound X (n*m) (A*B) := by
  classical
  intro x
  let e : Fin n × Fin m ≃ Fin (n*m) := finProdFinEquiv
  let f : Cube (n*m) → Cube n → Cube m → ℝ := fun ζ ε η =>
    ‖∑ i, ∑ j, (sign (ε i)*sign (η j)) • (sign (ζ (e (i,j))) • x (e (i,j)))‖^2
  have hbound ζ : average (fun ε => average (f ζ ε)) ≤ A*B*∑ i, ‖x i‖^2 := by
    have hh := quadraticTypeBound_chaos hA hn hm (fun i j => sign (ζ (e (i,j))) • x (e (i,j)))
    have hs : (∑ i, ∑ j, ‖sign (ζ (e (i,j))) • x (e (i,j))‖^2) = ∑ i, ‖x i‖^2 := by
      have hnorm i j : ‖sign (ζ (e (i,j))) • x (e (i,j))‖ = ‖x (e (i,j))‖ := by
        cases ζ (e (i,j)) <;> simp
      simp only [hnorm]
      simpa only [Fintype.sum_prod_type] using e.sum_comp (fun u => ‖x u‖^2)
    simpa only [hs] using hh
  have havg (ε : Cube n) (η : Cube m) : average (fun ζ => f ζ ε η) =
      cubeL2 X (rademacherSum X x)^2 := by
    let σ : Cube (n*m) := fun u => xor (ε (e.symm u).1) (η (e.symm u).2)
    have he : (fun ζ => f ζ ε η) = fun ζ : Cube (n*m) =>
        ‖∑ u, (sign (σ u)*sign (ζ u)) • x u‖^2 := by
      funext ζ
      simp only [f,smul_smul]
      congr 2
      rw [← e.sum_comp]
      simp only [Fintype.sum_prod_type,σ,e.symm_apply_apply,sign_mul_of_xor]
    rw [he]
    exact average_rademacher_twist x σ
  have hall := average_mono hbound
  have he : average (fun ζ => average (fun ε => average (f ζ ε))) =
      cubeL2 X (rademacherSum X x)^2 := by
    rw [average_comm]
    simp_rw [average_comm (fun ζ η => f ζ _ η),havg,average_const_value]
  rw [he,average_const_value] at hall
  exact hall

theorem quadraticTypeBound_one : QuadraticTypeBound X 1 1 := by
  intro x
  have hn (ε : Cube 1) : ‖rademacherSum X x ε‖^2 = ‖x 0‖^2 := by
    simp only [rademacherSum,Fin.sum_univ_one]
    cases ε 0 <;> simp
  simp only [cubeL2_sq,hn,average_const_value,Fin.sum_univ_one,one_mul,le_refl]

theorem quadraticTypeBound_pow {n : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (h : QuadraticTypeBound X n A) (k : ℕ) :
    QuadraticTypeBound X (n^k) (A^k) := by
  induction k with
  | zero => simpa using (quadraticTypeBound_one (X := X))
  | succ k ih => simpa [pow_succ'] using quadraticTypeBound_mul hA h ih

theorem quadraticType_powers_of_bConvex (h : BConvex X) :
    ∃ n : ℕ, 0 < n ∧ ∃ A : ℝ, 0 ≤ A ∧ A < n ∧
      ∀ k : ℕ, QuadraticTypeBound X (n^k) (A^k) := by
  obtain ⟨n,hn,A,hA,hAn,h⟩ := fixed_quadratic_improvement_of_bConvex h
  exact ⟨n,hn,A,hA,hAn,quadraticTypeBound_pow hA h⟩

end Cotype

end

end OAI
