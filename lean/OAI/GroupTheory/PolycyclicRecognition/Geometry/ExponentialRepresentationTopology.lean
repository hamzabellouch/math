import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialLocalSeparation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Algebra

namespace OAI

/-! # Recovering the source topology from a faithful exponential representation -/

noncomputable section
namespace PolycyclicRecognition

open Filter Topology

variable {L G A : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [FiniteDimensional ℝ L] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

omit [FiniteDimensional ℝ L] [CompleteSpace A] in
theorem inducing_of_exponential_chart_and_local_logarithm
    (S : Subalgebra ℝ A) [IsTopologicalRing S] (chart : L ≃ₜ G) (hzero : chart 0 = 1)
    (j : L →ₗ[ℝ] S) (hj : Function.Injective j)
    (ρ : G →* Aˣ) (hρ : Continuous ρ)
    (hexp : ∀ x, (ρ (chart x) : A) = (NormedSpace.exp (j x) : S))
    (hker : ∀ a : S, NormedSpace.exp a = 1 → a = 0) :
    Topology.IsInducing ρ := by
  obtain ⟨q, hq⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  obtain ⟨P, hP⟩ := S.val.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hqj (x : L) : q (j x) = x := DFunLike.congr_fun hq x
  have hPi (x : S) : P (x : A) = x := DFunLike.congr_fun hP x
  obtain ⟨log, hlog, hlog1, huniq⟩ := exists_unique_local_logarithm hker
  let r : Aˣ → S := fun u => P (u : A)
  have hr : Continuous r := P.continuous_of_finiteDimensional.comp Units.continuous_val
  have hr1 : r 1 = 1 := hPi 1
  let inv : Aˣ → G := fun u => chart (q (log (r u)))
  have hinv1 : inv 1 = 1 := by simp only [inv, hr1, hlog1, map_zero, hzero]
  have hcinv : ContinuousAt inv 1 := by
    exact chart.continuous.continuousAt.comp
      (q.continuous_of_finiteDimensional.continuousAt.comp
        (hlog.comp_of_eq hr.continuousAt hr1))
  have hevent : ∀ᶠ u in 𝓝 (1 : Aˣ),
      ∀ x : L, ρ (chart x) = u → inv u = chart x := by
    have ht := (hr.continuousAt.tendsto.mono_right (le_of_eq (congrArg nhds hr1))) huniq
    filter_upwards [ht] with u hu x hx
    have hxexp : NormedSpace.exp (j x) = r u := by
      have he := congrArg P (hexp x)
      rw [hPi] at he
      simpa only [r, hx] using he.symm
    have hjx := hu.2 (j x) hxexp
    change chart (q (log (r u))) = chart x
    rw [← hjx, hqj]
  have hleft : ∀ᶠ g in Filter.comap ρ (𝓝 (1 : Aˣ)), inv (ρ g) = g := by
    filter_upwards [Filter.tendsto_comap hevent] with g hg
    have h := hg (chart.symm g) (by rw [chart.apply_symm_apply])
    simpa only [chart.apply_symm_apply] using h
  have ht : Tendsto (fun g => inv (ρ g)) (Filter.comap ρ (𝓝 (1 : Aˣ))) (𝓝 (1 : G)) := by
    rw [← hinv1]
    exact hcinv.tendsto.comp Filter.tendsto_comap
  have hle : Filter.comap ρ (𝓝 (1 : Aˣ)) ≤ 𝓝 (1 : G) := by
    have ht' : Tendsto (id : G → G) (Filter.comap ρ (𝓝 (1 : Aˣ))) (𝓝 (1 : G)) :=
      ht.congr' hleft
    simpa only [Filter.tendsto_id'] using ht'
  apply (IsTopologicalGroup.isInducing_iff_nhds_one (f := ρ)).mpr
  apply le_antisymm
  · exact (hρ.continuousAt.tendsto.mono_right
      (le_of_eq (congrArg nhds (ρ.map_one)))).le_comap
  · exact hle

end PolycyclicRecognition

end

end OAI
