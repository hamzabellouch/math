import OAI.Probability.DilutedSpin.InsertionPoissonAlgebra
import OAI.Probability.DilutedSpin.PoissonCountThinning
import OAI.Probability.DilutedSpin.ProductComparison
import OAI.Probability.DilutedSpin.RootProductLaw

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

lemma successCount_le {p k : ℕ} [NeZero p] (a : Fin k → Fin p) : successCount a ≤ k := by
  unfold successCount
  apply (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin k))) =>
    show (if a i=0 then 1 else 0)≤1 by split_ifs <;> omega)).trans_eq
  simp

lemma successCount_cons {p k : ℕ} [NeZero p] (a : Fin p) (x : Fin k → Fin p) :
    successCount (Fin.cons a x)=(if a=0 then 1 else 0)+successCount x := by
  simp only [successCount,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma uniform_indicator_expect (p : ℕ) [NeZero p] (f : ℕ → ℝ) (n : ℕ) :
    (FiniteLaw.uniform : FiniteLaw (Fin p)).expect (fun a => f (n+if a=0 then 1 else 0)) =
      (f (n+1)+((p-1:ℕ):ℝ)*f n)/p := by
  classical
  rw [FiniteLaw.uniform_expect,Fintype.card_fin]
  congr 1
  have he (a : Fin p) : f (n+if a=0 then 1 else 0)=
      (if a=0 then f (n+1)-f n else 0)+f n := by split_ifs <;> simp
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]
  ring

/-- Finite independent replacement of real-or-null interactions by cavity
interactions. The error has its exact extensive coefficient. -/
lemma finite_count_replacement (p : ℕ) [NeZero p] (f : ℕ → ℕ → ℝ) (c : ℝ)
    (h : ∀ n l,f (n+1) l+((p-1:ℕ):ℝ)*f n l ≤ (p:ℝ)*(f n (l+1)-c))
    (k n l : ℕ) :
    (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
      (fun a => f (n+successCount a) l) ≤ f n (l+k)-(k:ℝ)*c := by
  induction k generalizing l with
  | zero => simp [FiniteLaw.expect,FiniteLaw.pi,successCount]
  | succ k ih =>
      rw [FiniteLaw.expect_pi_cons]
      simp only [successCount_cons]
      rw [FiniteLaw.expect_comm]
      calc
        _ ≤ (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
            (fun a => f (n+successCount a) (l+1)-c) := by
          apply FiniteLaw.expect_mono
          intro a
          have hn : ∀ b : Fin p,n+((if b=0 then 1 else 0)+successCount a)=
              (n+successCount a)+(if b=0 then 1 else 0) := by intro b; omega
          simp_rw [hn]
          rw [uniform_indicator_expect p (fun k => f k l)]
          exact (div_le_iff₀ (by exact_mod_cast NeZero.pos p)).mpr (by
            simpa only [mul_comm (p:ℝ)] using h (n+successCount a) l)
        _ ≤ f n ((l+1)+k)-(k:ℝ)*c-c := by
          rw [FiniteLaw.expect_sub,FiniteLaw.expect_const]
          exact sub_le_sub_right (ih (l+1)) c
        _ = _ := by rw [show (l+1)+k=l+(k+1) by omega,Nat.cast_add,Nat.cast_one]; ring

lemma integral_poisson_thinning (r : ℝ≥0) (p : ℕ) [NeZero p]
    (f : ℕ → ℝ) {B D : ℝ} (hD : 0≤D) (hf : ∀ n,|f n|≤B+D*n) :
    (∫ k,(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
      (fun a => f (successCount a)) ∂poissonMeasure r) =
    ∫ n,f n ∂poissonMeasure (r/p) := by
  let ν := fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin p))
  have hi : Integrable (fun z : (k : ℕ) × (Fin k → Fin p) => f (successCount z.2))
      (familyLaw (poissonMeasure r) ν) := by
    apply familyLaw_integrable_bound (poissonMeasure r) ν
      (fun k (a : Fin k → Fin p) => f (successCount a)) (fun _ => measurable_of_countable _)
      ((integrable_const B).add ((poisson_integrable_count r).const_mul D))
    intro k a
    exact (hf _).trans (add_le_add_right (mul_le_mul_of_nonneg_left
      (show (successCount a:ℝ)≤k by exact_mod_cast successCount_le a) hD) B)
  rw [← map_poisson_successCount r p]
  rw [integral_map (measurable_sigmaUncurry (fun k => measurable_of_countable (fun a : Fin k → Fin p => successCount a))).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  rw [integral_familyLaw (poissonMeasure r) ν (fun k (a : Fin k → Fin p) => f (successCount a))
    (fun _ => measurable_of_countable _) hi]
  apply integral_congr_ae
  filter_upwards [] with k
  dsimp only [ν]
  rw [finiteUniform_pi,integral_finiteUniform]
  have hh : FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p))) =
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p)) := by
    apply FiniteLaw.ext
    intro a
    simp [FiniteLaw.pi,FiniteLaw.uniform]
  rw [hh,FiniteLaw.uniform_expect]
  simp [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- Uniformized Poisson interpolation endpoint. The sole local input is the
conditional cavity replacement inequality, at ALL old real/cavity counts. -/
lemma poisson_count_replacement (r : ℝ≥0) (p : ℕ) [NeZero p]
    (f : ℕ → ℕ → ℝ) (c : ℝ) {B D : ℝ} (hD : 0≤D)
    (hf : ∀ n l,|f n l|≤B+D*(n+l))
    (h : ∀ n l,f (n+1) l+((p-1:ℕ):ℝ)*f n l ≤ (p:ℝ)*(f n (l+1)-c)) :
    (∫ n,f n 0 ∂poissonMeasure (r/p))+(r:ℝ)*c ≤ ∫ l,f 0 l ∂poissonMeasure r := by
  rw [← integral_poisson_thinning r p (fun n => f n 0) hD (by simpa using fun n => hf n 0)]
  have hb (k : ℕ) : |(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
      (fun a => f (successCount a) 0)|≤B+D*k := by
    apply FiniteLaw.abs_expect_le
    intro a
    exact (hf _ 0).trans (by simpa only [Nat.cast_zero,add_zero] using (add_le_add_right (mul_le_mul_of_nonneg_left (show (successCount a:ℝ)≤k by exact_mod_cast successCount_le a) hD) B))
  have hi := poisson_average_integrable r _ hb
  have hj := poisson_average_integrable r (fun k => f 0 k) (by simpa using fun k => hf 0 k)
  have hh := integral_mono hi (hj.sub ((poisson_integrable_count r).mul_const c))
    (fun k => by simpa only [zero_add,Pi.sub_apply] using finite_count_replacement p f c h k 0 0)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hj ((poisson_integrable_count r).mul_const c),integral_mul_const,poisson_mean] at hh
  linarith

end DilutedSpinGlass

end

end OAI
