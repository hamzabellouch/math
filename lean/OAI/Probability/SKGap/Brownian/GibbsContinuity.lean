import Mathlib
import OAI.Probability.SKGap.Terminal.TerminalMatrixTransfer

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set
open scoped BigOperators
variable {n : ℕ}

lemma continuous_weight (g : Disorder n) (x : Spin n) : Continuous (fun h : Fin n→ℝ=>weight g h x) := by
  unfold weight hamiltonian
  fun_prop

lemma continuous_partition (g : Disorder n) : Continuous (partition g) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _=>continuous_weight g x)

lemma continuous_mass (g : Disorder n) (x : Spin n) : Continuous (fun h : Fin n→ℝ=>mass g h x) :=
  (continuous_weight g x).div (continuous_partition g) (fun h=>(partition_pos g h).ne')

lemma continuous_expectation (g : Disorder n) (f : Spin n→ℝ) : Continuous (fun h : Fin n→ℝ=>expectation g h f) := by
  unfold expectation
  exact continuous_finsetSum _ (fun x _=>(continuous_mass g x).mul continuous_const)

lemma continuous_conditionalExpectation (g : Disorder n) (i : Fin n) (f : Spin n→ℝ) (x : Spin n) :
    Continuous (fun h : Fin n→ℝ=>conditionalExpectation g h i f x) := by
  unfold conditionalExpectation
  exact ((continuous_weight g x).mul continuous_const |>.add
    ((continuous_weight g (flip i x)).mul continuous_const)).div
    ((continuous_weight g x).add (continuous_weight g (flip i x)))
    (fun h=>(add_pos (weight_pos g h x) (weight_pos g h (flip i x))).ne')

lemma continuous_variance (g : Disorder n) (f : Spin n→ℝ) : Continuous (fun h : Fin n→ℝ=>variance g h f) := by
  unfold variance expectation
  apply continuous_finsetSum
  intro x _
  exact (continuous_mass g x).mul ((continuous_const.sub (continuous_expectation g f)).pow 2)

lemma continuous_dirichlet (g : Disorder n) (f : Spin n→ℝ) : Continuous (fun h : Fin n→ℝ=>dirichlet g h f) := by
  unfold dirichlet expectation
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro x _
  exact (continuous_mass g x).mul ((continuous_const.sub (continuous_conditionalExpectation g i f x)).pow 2)

lemma terminal_goodSet_closed (g : Disorder n) (C : ℝ) :
    IsClosed {h : Fin n→ℝ | ∀ f : Spin n→ℝ,variance g h f ≤ C*dirichlet g h f} := by
  have he : {h : Fin n→ℝ | ∀ f : Spin n→ℝ,variance g h f ≤ C*dirichlet g h f}=
      ⋂ f : Spin n→ℝ,{h | variance g h f ≤ C*dirichlet g h f} := by ext h;simp
  rw [he]
  exact isClosed_iInter (fun f=>isClosed_le (continuous_variance g f) (continuous_const.mul (continuous_dirichlet g f)))

lemma mass_le_one (g : Disorder n) (h : Fin n→ℝ) (x : Spin n) : mass g h x ≤ 1 := by
  rw [← sum_mass g h]
  exact Finset.single_le_sum (fun y _=>mass_nonneg g h y) (Finset.mem_univ x)

lemma expectation_abs_le (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) {C : ℝ}
    (hf : ∀ x,|f x| ≤ C) : |expectation g h f| ≤ C := by
  calc
    _ ≤ ∑ x,|mass g h x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x,mass g h x*|f x| := by simp only [abs_mul,abs_of_nonneg (mass_nonneg g h _)]
    _ ≤ ∑ x,mass g h x*C := Finset.sum_le_sum (fun x _=>mul_le_mul_of_nonneg_left (hf x) (mass_nonneg g h x))
    _ = C := by rw [← Finset.sum_mul,sum_mass,one_mul]

lemma conditionalExpectation_abs_le (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (f : Spin n→ℝ)
    {C : ℝ} (hf : ∀ x,|f x| ≤ C) (x : Spin n) : |conditionalExpectation g h i f x| ≤ C := by
  have hd := add_pos (weight_pos g h x) (weight_pos g h (flip i x))
  rw [conditionalExpectation,abs_div,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_pos (weight_pos g h x),abs_of_pos (weight_pos g h (flip i x))]
  nlinarith only [mul_le_mul_of_nonneg_left (hf x) (weight_pos g h x).le,
    mul_le_mul_of_nonneg_left (hf (flip i x)) (weight_pos g h (flip i x)).le]

lemma conditionalExpectation_invariant (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (k : Spin n→ℝ) (hk : ∀ x,k (flip i x)=k x) : conditionalExpectation g h i k=k := by
  funext x
  unfold conditionalExpectation
  rw [hk]
  apply (div_eq_iff (add_pos (weight_pos g h x) (weight_pos g h (flip i x))).ne').mpr
  ring

lemma conditionalExpectation_minimal (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) (hk : ∀ x,k (flip i x)=k x) :
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2) ≤
      expectation g h (fun x=>(f x-k x)^2) := by
  let p := conditionalExpectation g h i f
  have hpp := conditionalExpectation_adjoint g h i f p
  have hpk := conditionalExpectation_adjoint g h i f k
  have hp' : conditionalExpectation g h i p=p := funext (conditionalExpectation_idem g h i f)
  rw [hp'] at hpp
  rw [conditionalExpectation_invariant g h i k hk] at hpk
  have he (x : Spin n) : (f x-k x)^2=(f x-p x)^2+(p x-k x)^2+
      2*(f x*p x-p x*p x)-2*(f x*k x-p x*k x) := by ring
  simp_rw [he]
  rw [expectation_sub,expectation_add,expectation_add,expectation_const_mul,expectation_const_mul,
    expectation_sub,expectation_sub,← hpp,← hpk]
  have hn := expectation_nonneg g h (fun x=>sq_nonneg (p x-k x))
  change expectation g h (fun x=>(f x-p x)^2) ≤ _
  linarith only [hn]
end SKGap

end
end

end OAI
