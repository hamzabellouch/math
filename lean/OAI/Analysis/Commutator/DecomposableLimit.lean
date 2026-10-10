import Mathlib
import OAI.Analysis.Commutator.DenseFieldClosure
import OAI.Analysis.Commutator.FiniteVectorLpConvergence

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem mem_ae_of_bounded_strong_limit (Q : Ω → VonNeumannAlgebra H)
    (T : Ω → H →L[ℂ] H) (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {c : ℝ} (hc : ∀ᵐ a ∂μ,‖T a‖≤c)
    (S : ℕ → Ω → H →L[ℂ] H)
    (hS : ∀ n ξ,AEStronglyMeasurable (fun a => S n a ξ) μ)
    {b : ℝ} (hb : 0≤b) (hSb : ∀ n,∀ᵐ a ∂μ,‖S n a‖≤b)
    (hmem : ∀ n,∀ᵐ a ∂μ,S n a∈Q a)
    (hlim : ∀ f,Tendsto (fun n => operator μ (S n) (hS n) (hSb n) f) atTop
      (𝓝 (operator μ T hT hc f))) : ∀ᵐ a ∂μ,T a∈Q a := by
  let v : ℕ → H := TopologicalSpace.denseSeq H
  let V : ℕ → Lp H 2 μ := fun j => Lp.constL 2 μ ℂ (v j)
  have hconst (j : ℕ) : V j =ᵐ[μ] fun _ => v j := Lp.coeFn_const 2 μ (v j)
  have hfinite (m : ℕ) : ∀ᵐ a ∂μ,∃ k : ℕ → ℕ,∀ j : Fin m,
      Tendsto (fun n => S (k n) a (v j)) atTop (𝓝 (T a (v j))) := by
    obtain ⟨k,hk,hka⟩ := exists_finite_test_subsequence μ
      (fun n (j : Fin m) => operator μ (S n) (hS n) (hSb n) (V j))
      (fun (j : Fin m) => operator μ T hT hc (V j)) (fun j => hlim (V j))
    filter_upwards [hka,ae_all_iff.mpr hconst,
      ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun j : ℕ =>
        operator_ae μ (S n) (hS n) (hSb n) (V j))),
      ae_all_iff.mpr (fun j : ℕ => operator_ae μ T hT hc (V j))]
      with a hka hv hs ht
    refine ⟨k,fun j => ?_⟩
    have he (n : ℕ) : operator μ (S (k n)) (hS (k n)) (hSb (k n)) (V j) a=
        S (k n) a (v j) := by rw [hs,hv]
    have he' : operator μ T hT hc (V j) a=T a (v j) := by rw [ht,hv]
    simpa only [he,he'] using hka j
  filter_upwards [ae_all_iff.mpr hfinite,ae_all_iff.mpr hSb,ae_all_iff.mpr hmem]
    with a hf hba hma
  apply mem_vonNeumann_of_dense_finite_tests (Q a) v
    (TopologicalSpace.denseRange_denseSeq H) (T a) b hb
  intro m
  obtain ⟨k,hk⟩ := hf m
  have hevent : ∀ᶠ n in atTop,∀ j : Fin m,
      ‖S (k n) a (v j)-T a (v j)‖<1/((m:ℝ)+1) := by
    apply eventually_all.mpr
    intro j
    exact (tendsto_iff_norm_sub_tendsto_zero.mp (hk j)).eventually
      (gt_mem_nhds (by positivity : (0:ℝ)<1/((m:ℝ)+1)))
  obtain ⟨n,hn⟩ := hevent.exists
  exact ⟨S (k n) a,hma (k n),hba (k n),fun j => (hn j).le⟩

end Kadison.Decomposable

end

end
end

end OAI
