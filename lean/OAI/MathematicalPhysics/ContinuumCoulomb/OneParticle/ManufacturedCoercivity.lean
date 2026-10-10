import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedTensorGap
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoreOrbitalProjection

namespace OAI

/-! The positive tensor-complement gap retains kinetic coercivity. The
potential lower bound is uniform in the growing slab dimensions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem gap_kinetic_coercivity {F K M C g : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hg : 0 < g)
    (hgap : g*M ≤ F) (hkin : K-C*M ≤ F) :
    (g/(2*(C+g+1)))*(M+2*K) ≤ F := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 2*(C+g+1))).2
  have h₁ := mul_le_mul_of_nonneg_left hkin (by positivity : 0 ≤ 2*g)
  have h₂ := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2*(C+1))
  nlinarith only [h₁,h₂,mul_nonneg hg.le hM]

theorem planarWellSum_uniform_lower {m : ℕ} (u : Fin m → PlanarPosition)
    (x : PlanarPosition) : -(m:ℝ)*PlanarSobolev.wellBound ≤ planarWellSum u x := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (abs_le.mp (by simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (x-u i))).1)
  simpa only [planarWellSum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_neg,neg_mul] using h

theorem manufacturedSlab_uniform_lower {rho H S freq scale η : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H) (hscale : 0 ≤ scale)
    (hrelation : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) (x : Position) :
    -(((m:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho) ≤
      manufacturedSlabPotential rho H S freq scale u x := by
  have h := manufacturedSlabPotential_lower hrho hH hS.le hscale hrelation u hsep hη hcoeff x
  have hp := planarWellSum_uniform_lower u (positionSplitCoordinates x).1
  have hv : 0 ≤ verticalCapPotential freq S (positionSplitCoordinates x).2 := by
    unfold verticalCapPotential
    positivity
  have hratio : 6*Real.pi*rho*S^3/H ≤ 6*Real.pi*rho := by
    apply (div_le_iff₀ hH).2
    exact mul_le_mul_of_nonneg_left hSH (by positivity)
  linarith

theorem boundedPotentialForm_kinetic_lower {n : ℕ}
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (C : ℝ) (hC : ∀ x, -C ≤ V x) (u : Coulomb.H1Vector n) :
    Coulomb.kinetic u-C*Coulomb.mass u ≤ boundedPotentialForm V u := by
  have hp (s : SpinConfiguration n) := integral_mono
    ((u.value_L2 s).norm.integrable_sq.const_mul (-C))
    (bounded_state_potential_integrable u V hV B hB s)
    (fun x => mul_le_mul_of_nonneg_right (hC x) (sq_nonneg ‖u.value s x‖))
  have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hp s)
  simp only [integral_const_mul,← Finset.mul_sum] at h
  change (-C)*Coulomb.mass u ≤ Coulomb.potentialForm V u at h
  change Coulomb.kinetic u-C*Coulomb.mass u ≤ Coulomb.kinetic u+Coulomb.potentialForm V u
  linarith

theorem manufacturedSlab_manyElectron_kinetic_lower {rho H S freq scale η : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H) (hscale : 0 ≤ scale)
    (hrelation : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) {n : ℕ} (v : Coulomb.H1Vector n) :
    Coulomb.kinetic v-(n:ℝ)*(((m:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho)*Coulomb.mass v ≤
      boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) v := by
  let V (x : Configuration n) := ∑ i, manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
  have hV : Continuous V := continuous_finsetSum _ (fun i _ =>
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u).comp
      (Coulomb.positionCLM i).continuous)
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hb (x : Configuration n) : |V x| ≤ (n:ℝ)*B := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hB (Coulomb.position x i)))
  apply boundedPotentialForm_kinetic_lower V hV _ hb
  intro x
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    manufacturedSlab_uniform_lower hrho hH hS hSH hscale hrelation u hsep hη hcoeff (Coulomb.position x i))
  simpa only [V,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_neg] using h

theorem manufacturedSlab_coercive_of_gap {rho H S freq scale η E g : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H) (hscale : 0 ≤ scale)
    (hrelation : freq^2 = 4*Real.pi*rho) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) {n : ℕ} (v : Coulomb.H1Vector n)
    (hE : 0 ≤ E) (hg : 0 < g)
    (hgap : ((n:ℝ)*E+g)*Coulomb.mass v ≤
      boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) v) :
    (g/(2*((n:ℝ)*(((m:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+E)+g+1)))*
      (Coulomb.mass v+2*Coulomb.kinetic v) ≤
    boundedPotentialForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
      (Coulomb.position x i)) v-(n:ℝ)*E*Coulomb.mass v := by
  have hk := manufacturedSlab_manyElectron_kinetic_lower hrho hH hS hSH hscale
    hrelation u hsep hη hcoeff v
  have hC : 0 ≤ (n:ℝ)*(((m:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+E) := by
    have hw := PlanarSobolev.wellBound_nonnegative
    positivity
  apply gap_kinetic_coercivity (Coulomb.mass_nonneg v) hC hg
  · nlinarith only [hgap]
  · nlinarith only [hk]

end ContinuumCoulomb

end

end OAI
