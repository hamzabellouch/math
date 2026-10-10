import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

noncomputable section

namespace UniformKServer.FiniteProbability

section
attribute [local instance] Classical.propDecidable

structure Law (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def Law.expect (P : Law Ω) (f : Ω → ℝ) : ℝ := ∑ ω, P.weight ω*f ω

theorem Law.expect_nonneg (P : Law Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ P.expect f := Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hf ω)

theorem Law.expect_mono (P : Law Ω) (f g : Ω → ℝ) (hfg : ∀ ω, f ω ≤ g ω) :
    P.expect f ≤ P.expect g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (P.nonneg ω)

@[simp] theorem Law.expect_const (P : Law Ω) (c : ℝ) : P.expect (fun _ => c) = c := by
  simp [expect,←Finset.sum_mul,P.total]

theorem Law.expect_add (P : Law Ω) (f g : Ω → ℝ) :
    P.expect (fun ω => f ω+g ω) = P.expect f+P.expect g := by
  simp [expect,mul_add,Finset.sum_add_distrib]

theorem Law.expect_sub (P : Law Ω) (f g : Ω → ℝ) :
    P.expect (fun ω => f ω-g ω) = P.expect f-P.expect g := by
  simp [expect,mul_sub,Finset.sum_sub_distrib]

theorem Law.expect_mul (P : Law Ω) (c : ℝ) (f : Ω → ℝ) :
    P.expect (fun ω => c*f ω) = c*P.expect f := by
  simp only [expect,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

def Law.prod (P : Law Ω) (Q : Law Γ) : Law (Ω × Γ) where
  weight ω := P.weight ω.1*Q.weight ω.2
  nonneg ω := mul_nonneg (P.nonneg ω.1) (Q.nonneg ω.2)
  total := by simp [Fintype.sum_prod_type,←Finset.mul_sum,Q.total,P.total]

theorem Law.expect_prod (P : Law Ω) (Q : Law Γ) (f : Ω → Γ → ℝ) :
    (P.prod Q).expect (fun ω => f ω.1 ω.2) = P.expect (fun ω => Q.expect (f ω)) := by
  simp only [expect,prod,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

omit [Fintype Γ] in
theorem Law.expect_indicator_le (P : Law Ω) (A B : Ω → Prop)
    (h : ∀ ω, A ω → B ω) :
    P.expect (fun ω => if A ω then 1 else 0) ≤ P.expect (fun ω => if B ω then 1 else 0) := by
  apply P.expect_mono
  intro ω
  by_cases ha : A ω
  · simp [ha,h ω ha]
  · simp only [ite_eq_right ha]
    split_ifs <;> norm_num

variable {I : Type*} [Fintype I]

def bernoulli (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

theorem bernoulli_total (p : ℝ) : ∑ b : Bool, bernoulli p b = 1 := by
  simp [bernoulli]

def coins (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) : Law (I → Bool) where
  weight ω := ∏ i, bernoulli (p i) (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => by
    unfold bernoulli
    split_ifs
    · exact (hp i).1
    · linarith [(hp i).2]
  total := by
    classical
    rw [←Fintype.prod_sum]
    simp only [bernoulli_total,Finset.prod_const_one]

theorem coins_expect_coordinate (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (i : I) (f : Bool → ℝ) :
    (coins p hp).expect (fun ω => f (ω i)) = (1-p i)*f false+p i*f true := by
  classical
  have hpoint (ω : I → Bool) : (∏ j, bernoulli (p j) (ω j))*f (ω i) =
      ∏ j, bernoulli (p j) (ω j)*(if j=i then f (ω j) else 1) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    symm
    simpa only [ite_true] using (Finset.prod_eq_single (s := Finset.univ)
      (f := fun j : I => if j=i then f (ω j) else 1) i
      (by intro j _ hj; simp [hj]) (by simp))
  unfold Law.expect coins
  simp only [hpoint]
  rw [←Fintype.prod_sum (fun (j : I) (b : Bool) =>
    bernoulli (p j) b*(if j=i then f b else 1))]
  have hexcept (j : I) (hj : j ≠ i) :
      (∑ b : Bool, bernoulli (p j) b*(if j=i then f b else 1)) = 1 := by
    simpa [hj] using bernoulli_total (p j)
  rw [Finset.prod_eq_single i (fun j _ hj => hexcept j hj) (by simp)]
  simp [bernoulli,add_comm]

@[simp] theorem coins_true (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (i : I) :
    (coins p hp).expect (fun ω => if ω i then 1 else 0) = p i := by
  rw [coins_expect_coordinate p hp i (fun b => if b then 1 else 0)]
  simp

@[simp] theorem coins_false (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (i : I) :
    (coins p hp).expect (fun ω => if ω i then 0 else 1) = 1-p i := by
  rw [coins_expect_coordinate p hp i (fun b => if b then 0 else 1)]
  simp

end
variable {Ω I : Type*} [Fintype Ω]

theorem Law.expect_congr (P : Law Ω) (f g : Ω → ℝ) (h : ∀ ω, f ω = g ω) :
    P.expect f = P.expect g := by
  unfold expect
  exact Finset.sum_congr rfl (fun ω _ => by rw [h ω])

theorem Law.expect_finset_sum (P : Law Ω) (S : Finset I) (f : I → Ω → ℝ) :
    P.expect (fun ω => ∑ i ∈ S, f i ω) = ∑ i ∈ S, P.expect (f i) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

theorem Law.expect_close (P : Law Ω) (f g : Ω → ℝ) (d : ℝ)
    (h : ∀ ω, |f ω-g ω| ≤ d) : |P.expect f-P.expect g| ≤ d := by
  apply abs_le.mpr
  have hlo := P.expect_mono (fun _ => -d) (fun ω => f ω-g ω) (fun ω => (abs_le.mp (h ω)).1)
  have hhi := P.expect_mono (fun ω => f ω-g ω) (fun _ => d) (fun ω => (abs_le.mp (h ω)).2)
  rw [P.expect_const,P.expect_sub] at hlo
  rw [P.expect_const,P.expect_sub] at hhi
  exact ⟨hlo,hhi⟩

end UniformKServer.FiniteProbability

end

end OAI
