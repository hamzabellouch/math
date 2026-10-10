import OAI.Probability.InvariantIsing.Gaussian.GordonValueBound

namespace OAI

/-! Finite minimum--maximum values and their two-level log-sum-exp bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

def finiteRowMax (H : U × V → ℝ) (v : V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun u => H (u,v))

def finiteMinmax (H : U × V → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (finiteRowMax H)

lemma finiteMinmax_le_row (H : U × V → ℝ) (v : V) : finiteMinmax H ≤ finiteRowMax H v :=
  Finset.inf'_le _ (Finset.mem_univ v)

lemma finite_log_sum_exp_bounds {X : Type*} [Fintype X] [Nonempty X] (H : X → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty H ≤ Real.log (finitePartition (fun _ => 1) H) ∧
    Real.log (finitePartition (fun _ => 1) H) ≤
      Finset.univ.sup' Finset.univ_nonempty H+Real.log (Fintype.card X) := by
  constructor
  · obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty H
    rw [he]
    have hs : Real.exp (H x) ≤ finitePartition (fun _ => 1) H := by
      simpa only [finitePartition,one_mul] using
        Finset.single_le_sum (fun y _ => (Real.exp_pos (H y)).le) hx
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hs
  · have he := log_finitePartition_le_add (gordon_reference (X := X))
      (fun x => show H x ≤ 0+Finset.univ.sup' Finset.univ_nonempty H by
        simpa only [zero_add] using Finset.le_sup' H (Finset.mem_univ x))
    simpa only [finitePartition,Real.exp_zero,mul_one,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one,add_comm] using he

lemma gordonValue_finiteMinmax_bounds (H : U × V → ℝ) (β : ℝ) (hβ : 0 < β) :
    β*finiteMinmax H-Real.log (Fintype.card V) ≤ gordonValue (fun x => β*H x) ∧
    gordonValue (fun x => β*H x) ≤ β*finiteMinmax H+Real.log (Fintype.card U) := by
  have hr (v : V) : β*finiteRowMax H v ≤ gordonRow (fun x => β*H x) v ∧
      gordonRow (fun x => β*H x) v ≤ β*finiteRowMax H v+Real.log (Fintype.card U) := by
    have hs : Finset.univ.sup' Finset.univ_nonempty (fun u => β*H (u,v)) =
        β*finiteRowMax H v := by
      obtain ⟨u,hu,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun u => H (u,v))
      apply le_antisymm
      · apply Finset.sup'_le
        intro a _
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun u => H (u,v)) (Finset.mem_univ a)) hβ.le
      · change β*(Finset.univ.sup' Finset.univ_nonempty (fun u => H (u,v))) ≤ _
        rw [he]
        exact Finset.le_sup' (fun u => β*H (u,v)) hu
    simpa only [hs,gordonRow] using finite_log_sum_exp_bounds (fun u => β*H (u,v))
  constructor
  · have hb (v : V) : -gordonRow (fun x => β*H x) v ≤ 0+(-β*finiteMinmax H) := by
      have hm := mul_le_mul_of_nonneg_left (finiteMinmax_le_row H v) hβ.le
      linarith [(hr v).1]
    have he := log_finitePartition_le_add (gordon_reference (X := V)) hb
    have hz : finitePartition (fun _ : V => (1 : ℝ)) (fun _ => 0) = Fintype.card V := by
      simp [finitePartition]
    rw [hz] at he
    change β*finiteMinmax H-Real.log (Fintype.card V) ≤ -Real.log _
    linarith
  · obtain ⟨v,hv,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (finiteRowMax H)
    have hl : -gordonRow (fun x => β*H x) v ≤ Real.log
        (finitePartition (fun _ : V => 1) (fun v => -gordonRow (fun x => β*H x) v)) := by
      exact (Finset.le_sup' (fun v => -gordonRow (fun x => β*H x) v) hv).trans
        (finite_log_sum_exp_bounds _).1
    have hmin : finiteMinmax H = finiteRowMax H v := he
    have hh := (hr v).2
    rw [← hmin] at hh
    change -Real.log _ ≤ _
    linarith

lemma finiteMinmax_linear_integrable {d : ℕ} (C : U × V → Fin d → ℝ) :
    Integrable (fun g => finiteMinmax (fun x => linearGaussian C g x))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  have hm : Measurable (fun g => finiteMinmax (fun x => linearGaussian C g x)) := by
    have hr (v : V) : Continuous (fun g => finiteRowMax (fun x => linearGaussian C g x) v) :=
      Continuous.finset_sup'_apply Finset.univ_nonempty (fun u _ => by
        unfold linearGaussian; fun_prop)
    exact (Continuous.finset_inf'_apply Finset.univ_nonempty (fun v _ => hr v)).measurable
  apply (integrable_finsetSum Finset.univ (fun x _ => (integrable_linearGaussian C x).abs)).mono'
    hm.aestronglyMeasurable
  apply ae_of_all
  intro g
  obtain ⟨v,_,hv⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (finiteRowMax (fun x => linearGaussian C g x))
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun u => linearGaussian C g (u,v))
  change ‖Finset.univ.inf' Finset.univ_nonempty _‖ ≤ _
  rw [hv]
  change ‖Finset.univ.sup' Finset.univ_nonempty _‖ ≤ _
  rw [hu,Real.norm_eq_abs]
  exact Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian C g y)) (Finset.mem_univ (u,v))

end InvariantIsing

end

end OAI
