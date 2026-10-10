import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincSpectralIdentity
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Measures.CharFunSqIntervalIntegrable
import OAI.MeasureTheory.FalconerCompletion.Shells.WeightedDistanceCollisionLower
import OAI.MeasureTheory.FalconerCompletion.Shells.WidthKernel

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

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
variable (e : PositiveDistanceState d)

noncomputable def prefixShell (j : ℕ) : ℝ :=
  (2:ℝ)^(-(e.a:ℝ))*(∫ r in Icc ((2:ℝ)^j) ((2:ℝ)^(j+1)), ‖charFun e.weightedDistance r‖^2)

noncomputable def prefixLowIndices : Finset ℕ := by
  classical
  exact (Finset.Ico e.a e.t).filter (fun j => e.sig*e.N≤(e.t:ℝ)-(j+1:ℕ))

noncomputable def prefixHighIndices : Finset ℕ := by
  classical
  exact (Finset.Ico e.a e.t).filter (fun j => ¬e.sig*e.N≤(e.t:ℝ)-(j+1:ℕ))

lemma prefixShell_nonneg (j : ℕ) : 0≤e.prefixShell j :=
  mul_nonneg (by positivity) (integral_nonneg (fun r => sq_nonneg ‖charFun e.weightedDistance r‖))

lemma prefixShell_le_band [IsFiniteMeasure e.weightedDistance] (j : ℕ) :
    e.prefixShell j≤(2:ℝ)^(-(e.a:ℝ))*
      (∫ r in Icc (-((2:ℝ)^(j+1))) ((2:ℝ)^(j+1)), ‖charFun e.weightedDistance r‖^2) := by
  have hsub : Icc ((2:ℝ)^j) ((2:ℝ)^(j+1))⊆Icc (-((2:ℝ)^(j+1))) ((2:ℝ)^(j+1)) := by
    intro r hr
    refine ⟨?_,hr.2⟩
    have h₁ : 0<(2:ℝ)^j := by positivity
    have h₂ : 0<(2:ℝ)^(j+1) := by positivity
    linarith [hr.1]
  have hi : Integrable (fun r => ‖charFun e.weightedDistance r‖^2)
      (volume.restrict (Icc (-((2:ℝ)^(j+1))) ((2:ℝ)^(j+1)))) := by
    simpa only [one_mul] using charFun_sq_integrable_finite e.weightedDistance
      (volume.restrict (Icc (-((2:ℝ)^(j+1))) ((2:ℝ)^(j+1)))) 1
  exact mul_le_mul_of_nonneg_left
    (integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun e.weightedDistance r‖)) hi) (by positivity)

lemma prefix_frequency_decomposition [IsFiniteMeasure e.weightedDistance] (hat : e.a≤e.t) :
    (2:ℝ)^(-(e.a:ℝ))*(∫ r in Icc (-((2:ℝ)^e.t)) ((2:ℝ)^e.t), ‖charFun e.weightedDistance r‖^2)=
      (2:ℝ)^(-(e.a:ℝ))*(∫ r in Icc (-((2:ℝ)^e.a)) ((2:ℝ)^e.a), ‖charFun e.weightedDistance r‖^2)+
      2*∑ j∈e.prefixLowIndices, e.prefixShell j + 2*∑ j∈e.prefixHighIndices, e.prefixShell j := by
  classical
  have hp := Finset.sum_filter_add_sum_filter_not (Finset.Ico e.a e.t)
    (fun j => e.sig*e.N≤(e.t:ℝ)-(j+1:ℕ)) e.prefixShell
  change (∑ j∈e.prefixLowIndices, e.prefixShell j)+(∑ j∈e.prefixHighIndices, e.prefixShell j)=_ at hp
  rw [add_assoc,← mul_add,hp,distance_dyadic_band_decomposition e.weightedDistance hat]
  simp only [prefixShell,← Finset.mul_sum]
  ring

end PositiveDistanceState

theorem uniform_actual_prefix_decomposition {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J)
    {K : ℝ} (hK : 32*(n+2:ℝ)≤K) :
    ∃ H : ℝ, 0<H ∧ ∃ N₀ : ℕ, ∀ (e : PositiveDistanceState (n+1)),
      N₀≤e.N → e.sig=sig → e.J=J → 0<e.q → e.a≤e.t → e.t≤e.N →
      e.X.length=e.a → e.Y.length=e.a →
      farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)) →
      ∀ (B : ℕ) (s lam : ℝ), RegularizedProfileData e.ρ e.N B s lam e.mass →
      e.coincidence.toReal≤H*(2*((2:ℝ)^e.N)^(4*(n+2:ℝ)*lam)+
        2*(32*binKernelConstant.toReal)*
          (∑ j∈e.prefixLowIndices, ({e with t:=j+1,i:=e.i+1} : PositiveDistanceState (n+1)).coincidence.toReal)+
        2*∑ j∈e.prefixHighIndices, e.prefixShell j) := by
  classical
  obtain ⟨H,hH,hpass⟩ := actual_prefix_lowpass hK
  obtain ⟨N₀,hband⟩ := uniform_actual_prefix_low_band (n:=n) hsig hJ
  refine ⟨H,hH,N₀,?_⟩
  intro e hN hsig' hJ' hq hat ht hX hY hs B s lam hd
  let := hd.probability
  let := e.weightedDistance_isFinite hK hX hY hs
  have hpass' := hpass e hX hY hs
  rw [mul_assoc,e.prefix_frequency_decomposition hat] at hpass'
  apply hpass'.trans
  apply mul_le_mul_of_nonneg_left _ hH.le
  have hlow : (∑ j∈e.prefixLowIndices, e.prefixShell j)≤(32*binKernelConstant.toReal)*
      (∑ j∈e.prefixLowIndices, ({e with t:=j+1,i:=e.i+1} : PositiveDistanceState (n+1)).coincidence.toReal) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjt : j+1≤e.t := Nat.succ_le_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2
    exact (e.prefixShell_le_band j).trans
      (hband e hN hsig' hJ' hq ht K hK hX hY hs (j+1) hjt)
  have hstop := e.prefix_low_frequency_stopping hK hd (hat.trans ht) hX hY hs
  nlinarith

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
