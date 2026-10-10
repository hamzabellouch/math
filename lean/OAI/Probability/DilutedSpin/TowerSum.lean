import OAI.Probability.DilutedSpin.TowerPadding

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
namespace FiniteLaw
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i,Fintype (A i)]
lemma logMean_pi_sum (Q : (i : ι) → FiniteLaw (A i)) (m : ℝ)
    (f : (i : ι) → A i → ℝ) :
    (pi Q).logMean m (fun x => ∑ i,f i (x i))=∑ i,(Q i).logMean m (f i) := by
  classical
  unfold logMean expMoment
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [expect_pi_product Q (fun i x => Real.exp (m*f i x)),Real.log_prod]
  · simp only [Finset.sum_div]
  · intro i _
    exact (expMoment_pos (Q i) m (f i)).ne'
end FiniteLaw

namespace KernelTower
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [Fintype A]
lemma backwardLog_pi_sum (n : ℕ) (T : (i : ι) → KernelTower A n)
    (m : Fin n → ℝ) (f : (i : ι) → FinitePath A n → ℝ) :
    backwardLog n (pi n T) m (fun y => ∑ i,f i (FinitePath.proj n y i))=
      ∑ i,backwardLog n (T i) m (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ι → FiniteLaw A × (A → KernelTower A n) at T
    change ι → A × FinitePath A n → ℝ at f
    change (FiniteLaw.pi (fun i => (T i).1)).logMean (m 0)
      (fun x => backwardLog n (pi n (fun i => (T i).2 (x i))) (fun j => m j.succ)
        (fun y => ∑ i,f i (x i,FinitePath.proj n y i))) =
      ∑ i,(T i).1.logMean (m 0) (fun a => backwardLog n ((T i).2 a) (fun j => m j.succ) (fun y => f i (a,y)))
    have he : (fun x : ι → A => backwardLog n (pi n (fun i => (T i).2 (x i))) (fun j => m j.succ)
        (fun y => ∑ i,f i (x i,FinitePath.proj n y i))) =
      (fun x => ∑ i,backwardLog n ((T i).2 (x i)) (fun j => m j.succ) (fun y => f i (x i,y))) := by
      funext x
      exact ih (fun i => (T i).2 (x i)) (fun j => m j.succ) (fun i y => f i (x i,y))
    rw [he]
    exact FiniteLaw.logMean_pi_sum (fun i => (T i).1) (m 0)
      (fun i x => backwardLog n ((T i).2 x) (fun j => m j.succ) (fun y => f i (x,y)))
end KernelTower
end DilutedSpinGlass

end

end OAI
