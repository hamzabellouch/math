import OAI.Probability.InvariantIsing.Gaussian.GaussianComparisonSign

namespace OAI

/-! Finite Gaussian maxima and their log-sum-exp approximation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {X : Type*} [Fintype X] [Nonempty X]

def finiteGaussianMaximum {d : ℕ} (C : X → Fin d → ℝ) (g : Fin d → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => linearGaussian C g x)

lemma finiteGaussianMaximum_integrable {d : ℕ} (C : X → Fin d → ℝ) :
    Integrable (finiteGaussianMaximum C) (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  have hm : Measurable (finiteGaussianMaximum C) := by
    have hc := Finset.measurable_sup' (s := (Finset.univ : Finset X)) Finset.univ_nonempty
      (fun x _ => show Measurable (fun g => linearGaussian C g x) from by unfold linearGaussian; fun_prop)
    convert hc using 1
    funext g
    rw [Finset.sup'_apply]
    rfl
  apply (integrable_finsetSum Finset.univ (fun x _ => (integrable_linearGaussian C x).abs)).mono'
    hm.aestronglyMeasurable
  apply ae_of_all
  intro g
  obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun x => linearGaussian C g x)
  change ‖Finset.univ.sup' Finset.univ_nonempty _‖ ≤ _
  rw [he,Real.norm_eq_abs]
  exact Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian C g y)) hx

lemma finiteGaussianMaximum_log_bounds {d : ℕ} (C : X → Fin d → ℝ)
    (g : Fin d → ℝ) (β : ℝ) (hβ : 0 < β) :
    β * finiteGaussianMaximum C g ≤
        Real.log (finitePartition (fun _ : X => 1) (fun x => β*linearGaussian C g x)) ∧
    Real.log (finitePartition (fun _ : X => 1) (fun x => β*linearGaussian C g x)) ≤
      β * finiteGaussianMaximum C g + Real.log (Fintype.card X) := by
  have hw : GibbsReference (fun _ : X => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one,⟨Classical.choice ‹Nonempty X›,zero_lt_one⟩⟩
  constructor
  · obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun x => linearGaussian C g x)
    have hs : Real.exp (β * finiteGaussianMaximum C g) ≤
        finitePartition (fun _ : X => 1) (fun x => β*linearGaussian C g x) := by
      unfold finiteGaussianMaximum
      rw [he]
      simpa only [finitePartition,one_mul] using
        Finset.single_le_sum (fun y _ => (Real.exp_pos (β*linearGaussian C g y)).le) hx
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hs
  · have hb (x : X) : β*linearGaussian C g x ≤ 0+β*finiteGaussianMaximum C g := by
      simpa only [zero_add,finiteGaussianMaximum] using mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun x => linearGaussian C g x) (Finset.mem_univ x)) hβ.le
    have he := log_finitePartition_le_add hw hb
    simpa only [finitePartition,Real.exp_zero,mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      mul_one,add_comm] using he

end InvariantIsing

end

end OAI
