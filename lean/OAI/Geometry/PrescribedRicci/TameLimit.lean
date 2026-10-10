import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevReconstruction
import OAI.Geometry.PrescribedRicci.TameApproximation

namespace OAI

/-! Tame Limit. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical ComplexOrder MatrixOrder
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma coefficientBCF_tendsto (k : ℝ) (hk : (Module.finrank ℝ E : ℝ) < 2*k)
    (a : ℕ → SmoothCoefficients ι E) (b : ι → ι → L2 E)
    (ha : ∀ i j, Tendsto (fun l => schwartzCoord k (a l i j)) atTop (nhds (b i j))) :
    Tendsto (fun l => coefficientBCF (a l)) atTop
      (nhds (fun i j => strongEmbedding k hk (b i j))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hh := ((strongEmbedding k hk).continuous.tendsto (b i j)).comp (ha i j)
  simpa only [Function.comp_def,strongEmbedding_schwartz,coefficientBCF] using hh

end SobolevChart
namespace FrozenPoisson.ParameterRegularity
open SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

lemma tame_limit_equation (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : (Module.finrank ℝ (EC n):ℝ) < 2*(k:ℝ)) (M θ : ℝ)
    (x : ℕ → TameData H t v k M θ (ellipticBound H hH))
    (a : ι → ι → L2 (EC n)) (f u : L2 (EC n))
    (ha : ∀ i j, Tendsto (fun l => schwartzCoord (k:ℝ) ((x l).a i j)) atTop (nhds (a i j)))
    (hf : Tendsto (fun l => schwartzCoord (k:ℝ) (x l).f) atTop (nhds f))
    (hu : Tendsto (fun l => schwartzCoord ((k:ℝ)+2) (x l).u) atTop (nhds u)) :
    lowerCoord ((k:ℝ)+2) 2 (by simp) u = parameterHilbert H hH t ht
      (lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) f +
        perturbation v (fun i j => strongEmbedding (k:ℝ) hk (a i j))
          (lowerCoord ((k:ℝ)+2) 2 (by simp) u)) := by
  have hf0 := ((lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k)).continuous.tendsto f).comp hf
  have hu2 := ((lowerCoord ((k:ℝ)+2) 2 (by simp)).continuous.tendsto u).comp hu
  simp only [Function.comp_def,lowerCoord_schwartz] at hf0 hu2
  have ha0 := coefficientBCF_tendsto (k:ℝ) hk (fun l => (x l).a) a ha
  have hp := ((continuous_perturbation v).tendsto
    ((fun i j => strongEmbedding (k:ℝ) hk (a i j)),
      lowerCoord ((k:ℝ)+2) 2 (by simp) u)).comp (ha0.prodMk_nhds hu2)
  have hr := ((parameterHilbert H hH t ht).continuous.tendsto _).comp (hf0.add hp)
  have he l := tame_data_low_equation H hH t ht v k M θ (x l)
  simp only [Function.comp_def,← he] at hr
  exact tendsto_nhds_unique hu2 hr

 

theorem tame_limit_representation (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : Module.finrank ℝ (EC n)+1 < k)
    (hs : (Module.finrank ℝ (EC n):ℝ) < 2*(k:ℝ))
    (M : ℝ) (hM : 0 ≤ M) (θ : ℝ) (hθ : θ < 1)
    (x : ℕ → TameData H t v k M θ (ellipticBound H hH))
    (a : ι → ι → L2 (EC n)) (f : L2 (EC n))
    (ha : ∀ i j, Tendsto (fun l => schwartzCoord (k:ℝ) ((x l).a i j)) atTop (nhds (a i j)))
    (hf : Tendsto (fun l => schwartzCoord (k:ℝ) (x l).f) atTop (nhds f))
    (hsmall : perturbationBound v (fun i j => strongEmbedding (k:ℝ) hs (a i j))*ellipticBound H hH < 1) :
    MemSobolev ((k:ℝ)+2) 2 (realize 2 (parameterLocal H hH t ht v
      (fun i j => strongEmbedding (k:ℝ) hs (a i j)) hsmall (lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) f))) := by
  have hc := tame_high_cauchy H hH t ht v k hk M hM θ hθ x hf.cauchySeq
    (fun i j => (ha i j).cauchySeq)
  obtain ⟨u,hu⟩ := cauchySeq_tendsto_of_complete hc
  have he := tame_limit_equation H hH t ht v k hs M θ x a f u ha hf hu
  have he' := fixed_unique H hH t ht v _ hsmall _ _ _ he
    (parameterLocal_fixed H hH t ht v _ hsmall _)
  rw [← he',realize_lowerCoord]
  exact realize_memSobolev _ _

end FrozenPoisson.ParameterRegularity

end
end

end OAI
