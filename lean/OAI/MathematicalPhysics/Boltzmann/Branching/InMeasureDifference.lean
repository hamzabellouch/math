import OAI.MathematicalPhysics.Boltzmann.Branching.AverageMajorant
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

section

/-! # Convergence in measure through a measure-preserving chart -/
noncomputable section
open MeasureTheory Filter
namespace BoltzmannNonuniqueness.Compactness

theorem inMeasure_comp_measurePreserving
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {φ : X → Y} (hφ : MeasurePreserving φ μ ν)
    {f : ℕ → Y → ℝ} {g : Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (h : TendstoInMeasure ν f atTop g) :
    TendstoInMeasure μ (fun n => f n ∘ φ) atTop (g ∘ φ) := by
  rw [tendstoInMeasure_iff_norm] at h ⊢
  intro ε hε
  have he n : μ {x | ε ≤ ‖f n (φ x)-g (φ x)‖} = ν {y | ε ≤ ‖f n y-g y‖} :=
    hφ.measure_preimage (measurableSet_le measurable_const ((hfm n).sub hgm).norm).nullMeasurableSet
  simpa only [Function.comp_def,he] using h ε hε

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Difference and domination rules for local convergence in measure -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem tendstoInMeasure_zero_of_abs_le {f g : ℕ → X → ℝ}
    (hg : TendstoInMeasure μ g atTop (fun _ => 0))
    (hb : ∀ n x, |f n x| ≤ |g n x|) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hg ⊢
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε) (fun _ => zero_le)
  intro n
  apply measure_mono
  intro x hx
  change ε ≤ ‖f n x-0‖ at hx
  change ε ≤ ‖g n x-0‖
  simp only [sub_zero,Real.norm_eq_abs] at hx ⊢
  exact hx.trans (hb n x)

variable [IsFiniteMeasure μ]

theorem tendstoInMeasure_sub {f g : ℕ → X → ℝ} {a b : X → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hgm : ∀ n, AEStronglyMeasurable (g n) μ)
    (hf : TendstoInMeasure μ f atTop a) (hg : TendstoInMeasure μ g atTop b) :
    TendstoInMeasure μ (fun n x => f n x-g n x) atTop (fun x => a x-b x) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => (hfm n).sub (hgm n))).mpr
  intro ns hns
  obtain ⟨i,hi,hfi⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨j,hj,hgj⟩ := (hg.comp (hns.comp hi).tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨i ∘ j,hi.comp hj,?_⟩
  filter_upwards [hfi,hgj] with x hfx hgx
  exact (hfx.comp hj.tendsto_atTop).sub hgx

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
