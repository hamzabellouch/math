import Mathlib
import OAI.Analysis.Commutator.L2FiniteSum

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem exists_finite_test_subsequence (f : ℕ → ι → Lp H 2 μ) (g : ι → Lp H 2 μ)
    (h : ∀ i,Tendsto (fun n => f n i) atTop (𝓝 (g i))) :
    ∃ k : ℕ → ℕ,StrictMono k ∧
      ∀ᵐ a ∂μ,∀ i,Tendsto (fun n => f (k n) i a) atTop (𝓝 (g i a)) := by
  let F : ℕ → PiLp 2 (fun _ : ι => Lp H 2 μ) := fun n => WithLp.toLp 2 (f n)
  let G : PiLp 2 (fun _ : ι => Lp H 2 μ) := WithLp.toLp 2 g
  have hFG : Tendsto F atTop (𝓝 G) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp H 2 μ)).symm.continuous.tendsto g |>.comp
      (tendsto_pi_nhds.mpr h)
  have hL : Tendsto (fun n => assemble μ (F n)) atTop (𝓝 (assemble μ G)) :=
    (assembleIsometry μ).continuous.tendsto G |>.comp hFG
  obtain ⟨k,hk,hka⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  refine ⟨k,hk,?_⟩
  filter_upwards [hka,assemble_ae μ G,ae_all_iff.mpr (fun n => assemble_ae μ (F n))]
    with a hka hG hF
  intro i
  have he (n : ℕ) : assemble μ (F (k n)) a=WithLp.toLp 2 (fun i => f (k n) i a) := hF (k n)
  simp only [he] at hka
  rw [hG] at hka
  exact (PiLp.proj 2 (fun _ : ι => H) i : PiLp 2 (fun _ : ι => H) →L[ℂ] H).continuous.tendsto _ |>.comp hka

end Kadison.Decomposable

end

end
end

end OAI
