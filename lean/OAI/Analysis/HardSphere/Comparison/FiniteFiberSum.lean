import Mathlib
import OAI.Analysis.HardSphere.Geometry.CenteredCircleLift

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma finite_fiber_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι→ι) (a : ι→ℝ) (C : ℕ) (ha : ∀ i, 0≤a i)
    (hc : ∀ k, (Finset.univ.filter (fun i ↦ f i=k)).card≤C) :
    (∑ i, a (f i))≤(C:ℝ)*∑ i, a i := by
  rw [←Finset.sum_fiberwise Finset.univ f (fun i ↦ a (f i)),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  calc
    _ = ∑ i∈Finset.univ.filter (fun i ↦ f i=k), a k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = ((Finset.univ.filter (fun i ↦ f i=k)).card:ℝ)*a k := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc k) (ha k)

theorem nearestParticleDistance_sum_sq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (L : Length) (X Y : ι→Torus L) (hX : Function.Injective X) (hY : Function.Injective Y) :
    (∑ i, (nearestParticleDistance L Y i-nearestParticleDistance L X i)^2)≤
      502*∑ i, torusDistance L (X i) (Y i)^2 := by
  let δ : ι→ℝ := fun i ↦ torusDistance L (X i) (Y i)
  have hδ (i : ι) : 0≤δ i := Real.sqrt_nonneg _
  have hpoint (i : ι) : (nearestParticleDistance L Y i-nearestParticleDistance L X i)^2≤
      2*(δ i)^2+2*(δ (nearestLabel L X i))^2+2*(δ (nearestLabel L Y i))^2 := by
    have hp := nearestParticleDistance_sub_le L X Y i
    have hm := nearestParticleDistance_sub_le L Y X i
    have hs (j : ι) : torusDistance L (Y j) (X j)=δ j := by simp only [δ,torusDistance,dist_comm]
    change nearestParticleDistance L Y i-nearestParticleDistance L X i≤δ i+δ (nearestLabel L X i) at hp
    simp only [hs] at hm
    by_cases h : 0≤nearestParticleDistance L Y i-nearestParticleDistance L X i
    · have hsq := (sq_le_sq₀ h (add_nonneg (hδ i) (hδ _))).mpr hp
      nlinarith only [hsq,sq_nonneg (δ i-δ (nearestLabel L X i)),sq_nonneg (δ (nearestLabel L Y i))]
    · have h' : 0≤nearestParticleDistance L X i-nearestParticleDistance L Y i := by linarith only [h]
      have hsq := (sq_le_sq₀ h' (add_nonneg (hδ i) (hδ _))).mpr hm
      nlinarith only [hsq,sq_nonneg (δ i-δ (nearestLabel L Y i)),sq_nonneg (δ (nearestLabel L X i))]
  have hSX := finite_fiber_sum_le (nearestLabel L X) (fun i ↦ (δ i)^2) 125
    (fun _ ↦ sq_nonneg _) (nearestLabel_fiber_card L X hX)
  have hSY := finite_fiber_sum_le (nearestLabel L Y) (fun i ↦ (δ i)^2) 125
    (fun _ ↦ sq_nonneg _) (nearestLabel_fiber_card L Y hY)
  calc
    _ ≤ ∑ i, (2*(δ i)^2+2*(δ (nearestLabel L X i))^2+2*(δ (nearestLabel L Y i))^2) :=
      Finset.sum_le_sum (fun i _ ↦ hpoint i)
    _ = 2*(∑ i, (δ i)^2)+2*(∑ i, (δ (nearestLabel L X i))^2)+2*(∑ i, (δ (nearestLabel L Y i))^2) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ 502*∑ i, (δ i)^2 := by norm_num at hSX hSY; linarith only [hSX,hSY]

end HardSphere

end

end OAI
