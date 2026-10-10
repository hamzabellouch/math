import Mathlib.Geometry.Manifold.PartitionOfUnity
import OAI.Geometry.NodalSets.Charts.SeedChartScalarExtension
import OAI.Geometry.NodalSets.Spectral.SphereSmoothResolventBridge

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff
noncomputable section
local instance sphereL2InfiniteMeasurable : MeasurableSpace Base := borel Base
local instance sphereL2InfiniteBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_finite_distinct_points (N : ℕ) :
    ∃ p : Fin N → Base, Function.Injective p := by
  refine ⟨fun i ↦ seedSphereFromCoord (fun _ ↦ (i.val : ℝ)),?_⟩
  intro i j hij
  have h := congrArg seedSphereToCoord hij
  simp only [seedSphereToCoord_from] at h
  have hv := congrFun h (0 : Fin 4)
  apply Fin.ext
  exact_mod_cast hv

theorem sphere_smooth_finite_interpolation (d : SphereEnergyData) {N : ℕ}
    (p : Fin N → Base) (hp : Function.Injective p) :
    ∃ f : Fin N → SphereEnergySmooth d,
      ∀ i j, (SphereEnergySmooth.toSmooth d (f i) : Base → ℝ) (p j) =
        if i = j then 1 else 0 := by
  classical
  have hex (i : Fin N) : ∃ u : SphereEnergySmooth d,
      ∀ j, (SphereEnergySmooth.toSmooth d u : Base → ℝ) (p j) =
        if i = j then 1 else 0 := by
    let s : Set Base := p '' {j | j ≠ i}
    have hs : IsClosed s := ((Set.toFinite {j : Fin N | j ≠ i}).image p).isClosed
    have hd : Disjoint s {p i} := by
      apply disjoint_singleton_right.mpr
      rintro ⟨j,hj,hji⟩
      exact hj (hp hji)
    obtain ⟨g,hg0,hg1,-⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := ⊤)
      (𝓡 4) hs isClosed_singleton hd
    refine ⟨(⟨g,g.contMDiff⟩ : sphereSmoothFunctions),?_⟩
    intro j
    change g (p j) = _
    by_cases hij : i = j
    · subst j
      simpa using hg1 (mem_singleton (p i))
    · have hj : p j ∈ s := ⟨j,Ne.symm hij,rfl⟩
      simpa [hij] using hg0 hj
  choose f hf using hex
  exact ⟨f,hf⟩

theorem sphere_smooth_arbitrary_independent (d : SphereEnergyData) (N : ℕ) :
    ∃ f : Fin N → SphereEnergySmooth d, LinearIndependent ℝ f := by
  classical
  obtain ⟨p,hp⟩ := sphere_finite_distinct_points N
  obtain ⟨f,hf⟩ := sphere_smooth_finite_interpolation d p hp
  refine ⟨f,Fintype.linearIndependent_iff.mpr ?_⟩
  intro c hc j
  let ev : SphereEnergySmooth d →ₗ[ℝ] ℝ :=
    (LinearMap.proj (p j)).comp sphereSmoothFunctions.subtype
  have h := congrArg ev hc
  simp only [map_sum,map_smul,map_zero] at h
  change (∑ i, c i * (SphereEnergySmooth.toSmooth d (f i) : Base → ℝ) (p j)) = 0 at h
  simpa [hf] using h

theorem sphereWeightedL2_infiniteDimensional (d : SphereEnergyData) :
    ¬FiniteDimensional ℝ (SphereWeightedL2 d) := by
  intro hdim
  let := hdim
  have hinj : Function.Injective (sphereEnergyL2Linear d) := by
    apply (sphereEnergyL2Linear d).ker_eq_bot.mp
    exact LinearMap.ker_eq_bot'.mpr (fun u hu ↦ (sphereEnergyL2Linear_eq_zero_iff d u).mp hu)
  obtain ⟨f,hf⟩ := sphere_smooth_arbitrary_independent d
    (Module.finrank ℝ (SphereWeightedL2 d)+1)
  have hli := hf.map' (sphereEnergyL2Linear d) ((sphereEnergyL2Linear d).ker_eq_bot.mpr hinj)
  have hc := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hc
  omega

end
end Yau.Target

end OAI
