import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Fourier.MinimalMask

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ENNReal
variable {d n : ℕ}
namespace PositiveDistanceState

lemma uniform_minimalMask_nested_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ],
      N₀≤e.N → e.sig=sig → e.J=J → 0<e.q → e.t≤e.N →
      ∀ v≤e.t, ∀ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d), z.1≠z.2 →
        e.minimalMask z≠0 → z∈({e with t:=v,i:=e.i+1} : PositiveDistanceState d).good := by
  obtain ⟨N₀,h₀⟩ := uniform_actualEndpointMask_support (d:=d) hsig hJ
  refine ⟨N₀,?_⟩
  intro e he hN hsig' hJ' hq ht v hv z hz hm b hb
  have hb' := policyDescriptorList_mono (adjustedProfile (d:=d) e.mass e.N) (le_refl e.a) hv hb
  have hp := Finset.prod_ne_zero_iff.mp hm b hb'
  have hvalid := policyDescriptor_valid _ hq ht hb'
  have hmask (x : EuclideanSpace ℝ (Fin d))
      (hx : actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J e.i b x (radialVector z.1 z.2)≠0) :
      (x,radialVector z.1 z.2)∈endpointGood e.ρ e.mass e.N e.sig e.C e.J (e.i+1) b := by
    have h := h₀ e.N hN e.ρ he e.mass e.C e.i b hvalid 0 x (radialVector z.1 z.2)
      (norm_radialVector hz)
    rw [← hsig',← hJ'] at h
    apply h
    apply subset_tsupport
    rw [Function.mem_support,← norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
    exact hx
  exact ⟨hmask z.1 (mul_ne_zero_iff.mp hp).1,hmask z.2 (mul_ne_zero_iff.mp hp).2⟩

lemma weightedDistance_le_nested (e : PositiveDistanceState (n+1)) [IsFiniteMeasure e.ρ]
    {K : ℝ} (hK : 32*(n+2:ℝ)≤K) (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)))
    (v : ℕ) (hg : ∀ᵐ z ∂e.cellPair, e.spatialWeight z≠0 →
      z∈({e with t:=v,i:=e.i+1} : PositiveDistanceState (n+1)).good) :
    e.weightedDistance≤ENNReal.ofReal (e.levelMass^(-2:ℤ)) •
      ({e with t:=v,i:=e.i+1} : PositiveDistanceState (n+1)).distance := by
  let f : PositiveDistanceState (n+1) := {e with t:=v,i:=e.i+1}
  have hp : e.weightedPair≤ENNReal.ofReal (e.levelMass^(-2:ℤ)) • f.pair := by
    change e.weightedPair≤ENNReal.ofReal (e.levelMass^(-2:ℤ)) • e.cellPair.restrict f.good
    rw [← withDensity_const,← withDensity_indicator f.measurable_good]
    apply withDensity_mono
    filter_upwards [e.spatialWeight_bounds hK hX hY hs,hg] with z hz hg
    by_cases hw : e.spatialWeight z=0
    · simp only [hw,mul_zero,ENNReal.ofReal_zero]
      exact zero_le
    · rw [Set.indicator_of_mem (hg hw)]
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (by positivity) hz.1.2)
  have h := Measure.map_mono hp (continuous_fst.dist continuous_snd).measurable
  rw [Measure.map_smul _ (continuous_fst.dist continuous_snd).measurable.aemeasurable] at h
  simpa only [weightedDistance,distance] using h

lemma uniform_weightedDistance_nested_domination {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ (e : PositiveDistanceState (n+1)) [IsFiniteMeasure e.ρ],
      N₀≤e.N → e.sig=sig → e.J=J → 0<e.q → e.t≤e.N →
      ∀ K : ℝ, 32*(n+2:ℝ)≤K → e.X.length=e.a → e.Y.length=e.a →
      farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)) →
      ∀ v≤e.t, e.weightedDistance≤ENNReal.ofReal (e.levelMass^(-2:ℤ)) •
        ({e with t:=v,i:=e.i+1} : PositiveDistanceState (n+1)).distance := by
  obtain ⟨N₀,h₀⟩ := uniform_minimalMask_nested_support (d:=n+1) hsig hJ
  refine ⟨N₀,?_⟩
  intro e he hN hsig' hJ' hq ht K hK hX hY hs v hv
  apply e.weightedDistance_le_nested hK hX hY hs v
  filter_upwards [e.ae_cellPair_mem] with z hz
  intro hw
  have hne : z.1≠z.2 := by
    have hh := (e.separated_distance_ratio hK hX hY hs hz.1 hz.2).1
    intro he
    simp only [he,dist_self,zero_mul] at hh
    norm_num at hh
  have hm : e.minimalMask z≠0 := by
    intro h
    exact hw (by simp only [spatialWeight,h,mul_zero])
  exact h₀ e hN hsig' hJ' hq ht v hv z hne hm

end PositiveDistanceState
end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
