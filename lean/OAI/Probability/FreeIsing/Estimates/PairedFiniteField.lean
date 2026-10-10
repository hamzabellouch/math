import OAI.Probability.FreeIsing.Estimates.FiniteCavity
import OAI.Probability.FreeIsing.Posterior.FinitePosterior
import OAI.Probability.FreeIsing.Spins.Kernel

namespace OAI

noncomputable section

namespace Problem367

variable {I : Type*} [Fintype I] [Nonempty I]

theorem log_sum_exp_le_of_le_add (E F : I → ℝ) (C : ℝ)
    (h : ∀ i, E i ≤ F i + C) :
    Real.log (∑ i, Real.exp (E i)) ≤ Real.log (∑ i, Real.exp (F i)) + C := by
  have hF : 0 < ∑ i, Real.exp (F i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hE : 0 < ∑ i, Real.exp (E i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hsum : (∑ i, Real.exp (E i)) ≤ (∑ i, Real.exp (F i)) * Real.exp C := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (h i))
  have hlog := Real.log_le_log hE hsum
  rwa [Real.log_mul hF.ne' (Real.exp_pos C).ne', Real.log_exp] at hlog

theorem abs_log_sum_exp_sub_le (E F : I → ℝ) (C : ℝ)
    (h : ∀ i, |E i - F i| ≤ C) :
    |Real.log (∑ i, Real.exp (E i)) - Real.log (∑ i, Real.exp (F i))| ≤ C := by
  have hEF := log_sum_exp_le_of_le_add E F C (fun i => by
    have hi := (abs_le.mp (h i)).2
    linarith)
  have hFE := log_sum_exp_le_of_le_add F E C (fun i => by
    have hi := (abs_le.mp (h i)).1
    linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def pairedFieldWeight (E : I → ℝ) (x : ℝ) : ℝ :=
  Real.exp x * ∑ i, Real.exp (E i)

theorem pairedFieldWeight_pos (E : I → ℝ) (x : ℝ) : 0 < pairedFieldWeight E x := by
  exact mul_pos (Real.exp_pos x)
    (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty)

theorem paired_field_eq (E F : I → ℝ) (x : ℝ) :
    Real.artanh ((pairedFieldWeight E x - pairedFieldWeight F (-x)) /
      (pairedFieldWeight E x + pairedFieldWeight F (-x))) =
      x + (Real.log (∑ i, Real.exp (E i)) - Real.log (∑ i, Real.exp (F i))) / 2 := by
  rw [binary_mean_eq_tanh_half_log (pairedFieldWeight_pos E x)
    (pairedFieldWeight_pos F (-x)), Real.artanh_tanh]
  have hE : (∑ i, Real.exp (E i)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty)
  have hF : (∑ i, Real.exp (F i)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty)
  rw [pairedFieldWeight, pairedFieldWeight,
    Real.log_mul (Real.exp_pos x).ne' hE, Real.log_mul (Real.exp_pos (-x)).ne' hF,
    Real.log_exp, Real.log_exp]
  ring

theorem paired_field_difference_bound (E F : I → ℝ) (x K : ℝ)
    (h : ∀ i, |E i - F i| ≤ 2 * K) :
    |Real.artanh ((pairedFieldWeight E x - pairedFieldWeight F (-x)) /
      (pairedFieldWeight E x + pairedFieldWeight F (-x))) - x| ≤ K := by
  rw [paired_field_eq, add_sub_cancel_left, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
    simpa only [mul_comm K 2] using abs_log_sum_exp_sub_le E F (2 * K) h)

end Problem367

namespace Problem367

variable {I J : Type*} [Fintype I] [Nonempty I]

theorem paired_interaction_field_bound (D : Finset J) (residual : I → ℝ)
    (spin : I → J → ℝ) {beta : ℝ} (hbeta : 0 ≤ beta) (x : ℝ)
    (hspin : ∀ i j, j ∈ D → |spin i j| ≤ 1) :
    |Real.artanh ((pairedFieldWeight (fun i => residual i + beta * ∑ j ∈ D, spin i j) x -
        pairedFieldWeight (fun i => residual i - beta * ∑ j ∈ D, spin i j) (-x)) /
      (pairedFieldWeight (fun i => residual i + beta * ∑ j ∈ D, spin i j) x +
        pairedFieldWeight (fun i => residual i - beta * ∑ j ∈ D, spin i j) (-x))) - x| ≤
      (D.card : ℝ) * beta := by
  apply paired_field_difference_bound
  intro i
  have hs : |∑ j ∈ D, spin i j| ≤ (D.card : ℝ) := by
    calc
      |∑ j ∈ D, spin i j| ≤ ∑ j ∈ D, |spin i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ D, (1 : ℝ) := Finset.sum_le_sum (fun j hj => hspin i j hj)
      _ = (D.card : ℝ) := by simp
  have heq : residual i + beta * ∑ j ∈ D, spin i j -
      (residual i - beta * ∑ j ∈ D, spin i j) =
      (2 * beta) * ∑ j ∈ D, spin i j := by ring
  rw [heq, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hbeta)]
  nlinarith

end Problem367

namespace Problem367

variable {I : Type*} [Fintype I] [Nonempty I]

def pairedEnergy (E F : I → ℝ) (s : IsingSpin × I) : ℝ :=
  match s.1 with
  | .neg => F s.2
  | .pos => E s.2

omit [Nonempty I] in

theorem paired_posterior_mean (E F : I → ℝ) (x : ℝ) :
    FinitePosterior.mean (pairedEnergy E F) (fun s => spinSign s.1)
      (fun s => spinSign s.1) x =
      (pairedFieldWeight E x - pairedFieldWeight F (-x)) /
        (pairedFieldWeight E x + pairedFieldWeight F (-x)) := by
  simp only [FinitePosterior.mean, FinitePosterior.partition, FinitePosterior.weight,
    Fintype.sum_prod_type, sum_isingSpin, pairedEnergy, spinSign_neg, spinSign_pos,
    mul_neg_one, mul_one, neg_one_mul, one_mul, Real.exp_add, Finset.sum_neg_distrib,
    ← Finset.sum_mul, pairedFieldWeight]
  ring

theorem paired_posterior_field_bound (E F : I → ℝ) (x K : ℝ)
    (h : ∀ i, |E i - F i| ≤ 2 * K) :
    |Real.artanh (FinitePosterior.mean (pairedEnergy E F) (fun s => spinSign s.1)
      (fun s => spinSign s.1) x) - x| ≤ K := by
  rw [paired_posterior_mean]
  exact paired_field_difference_bound E F x K h

end Problem367

namespace Problem367

theorem finitePosterior_mean_equiv {S R : Type*} [Fintype S] [Fintype R]
    (e : S ≃ R) (energy signal observable : R → ℝ) (x : ℝ) :
    FinitePosterior.mean (energy ∘ e) (signal ∘ e) (observable ∘ e) x =
      FinitePosterior.mean energy signal observable x := by
  unfold FinitePosterior.mean FinitePosterior.partition FinitePosterior.weight
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun s => observable s * Real.exp (energy s + x * signal s)),
    e.sum_comp (fun s => Real.exp (energy s + x * signal s))]

theorem paired_posterior_field_bound_equiv {S I : Type*} [Fintype S] [Fintype I]
    [Nonempty I] (e : S ≃ IsingSpin × I) (energy : S → ℝ) (x K : ℝ)
    (h : ∀ i, |energy (e.symm (.pos, i)) - energy (e.symm (.neg, i))| ≤ 2 * K) :
    |Real.artanh (FinitePosterior.mean energy (fun s => spinSign (e s).1)
      (fun s => spinSign (e s).1) x) - x| ≤ K := by
  have hm := finitePosterior_mean_equiv e.symm energy
    (fun s => spinSign (e s).1) (fun s => spinSign (e s).1) x
  simp only [Function.comp_def, e.apply_symm_apply] at hm
  rw [← hm]
  have he : (fun s => energy (e.symm s)) =
      pairedEnergy (fun i => energy (e.symm (.pos, i)))
        (fun i => energy (e.symm (.neg, i))) := by
    funext s
    rcases s with ⟨s, i⟩
    cases s <;> rfl
  rw [he]
  exact paired_posterior_field_bound _ _ x K h

theorem finite_site_posterior_field_bound {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (energy : (V → IsingSpin) → ℝ) (x K : ℝ)
    (h : ∀ r : {w : V // w ≠ v} → IsingSpin,
      |energy ((Equiv.funSplitAt v IsingSpin).symm (.pos, r)) -
        energy ((Equiv.funSplitAt v IsingSpin).symm (.neg, r))| ≤ 2 * K) :
    |Real.artanh (FinitePosterior.mean energy (fun s => spinSign (s v))
      (fun s => spinSign (s v)) x) - x| ≤ K := by
  let : Nonempty IsingSpin := ⟨.neg⟩
  exact paired_posterior_field_bound_equiv (Equiv.funSplitAt v IsingSpin) energy x K h

end Problem367

end

end OAI
