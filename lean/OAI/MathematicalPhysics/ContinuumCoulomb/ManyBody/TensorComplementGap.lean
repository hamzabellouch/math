import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoreTensorFiber
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoreOrbitalCongruence
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.FullTensorComplement

namespace OAI

/-! The tensor-complement occupation deficit gives a full many-electron
gap once the proved one-body finite-rank estimate is supplied. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorRemainder_totalOccupation {m n : ℕ} {ι : Type*} [Fintype ι]
    (v : Fin m → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0)
    (f : ι → Position → ℝ) (hf : ∀ i, MemLp (f i) 2)
    (e : Fin m ≃ ι × Fin 2) (he : ∀ a, v a = realSpinOrbital (f (e a).1) (e a).2)
    (u : Coulomb.H1Vector (n+1)) (hu : Coulomb.Antisymmetric u) :
    let q := finiteTensorRemainder v hv hL2 hpartial u
    totalOrbitalMass q (fun i => oneElectronOrbitalLp (f i) (hf i)) ≤ (n:ℝ)*Coulomb.mass q := by
  let q := finiteTensorRemainder v hv hL2 hpartial u
  have hq : Coulomb.Antisymmetric q := finiteTensorRemainder_antisymmetric v hv hL2 hpartial u hu
  have h := finiteTensorRemainder_flat_occupation v hv hL2 hpartial ho u hu
  change (n+1:ℕ)*(∑ a, ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
    (Coulomb.flatSpinOrbital (v a)) (Coulomb.firstFiber (Coulomb.cubeState q)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) ≤ (n:ℝ)*Coulomb.mass q at h
  have hs : (∑ a, ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
    (Coulomb.flatSpinOrbital (v a)) (Coulomb.firstFiber (Coulomb.cubeState q)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) =
      coreOrbitalMass q (fun i => oneElectronOrbitalLp (f i) (hf i)) := by
    rw [coreOrbitalMass_first_occupation q hq f hf]
    simp_rw [he]
    let F (a : ι × Fin 2) : ℝ := ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital (f a.1) a.2))
      (Coulomb.firstFiber (Coulomb.cubeState q)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)
    exact (e.sum_comp F).trans (Fintype.sum_prod_type F)
  rw [hs,← totalOrbitalMass_antisymmetric q hq] at h
  exact h

theorem tensorComplement_energy_gap {n : ℕ} {ι : Type*} [Fintype ι]
    (q : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1)))
    (E τ b Q : ℝ) (hτ : 0 ≤ τ) (hb : 0 ≤ b)
    (hocc : totalOrbitalMass q φ ≤ (n:ℝ)*Coulomb.mass q)
    (hform : (n+1:ℕ)*(E+τ)*Coulomb.mass q -
      (τ+b)*totalOrbitalMass q φ ≤ Q)
    (herr : (n:ℝ)*b ≤ τ/2) :
    ((n+1:ℕ)*E+τ/2)*Coulomb.mass q ≤ Q := by
  have hm : 0 ≤ Coulomb.mass q := Coulomb.mass_nonneg q
  have hprod := mul_le_mul_of_nonneg_left hocc (add_nonneg hτ hb)
  have he := mul_le_mul_of_nonneg_right herr hm
  push_cast at hform ⊢
  nlinarith

theorem tensorComplement_residual_budget {n : ℕ} {γ ε : ℝ}
    (hγ : 0 < γ) (hε : 0 ≤ ε) (he : ε ≤ γ/(16*(n+1:ℕ))) :
    (n:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hden : (0:ℝ) < 16*(n+1:ℕ) := by positivity
  have hb := (le_div_iff₀ hden).mp he
  push_cast at hb
  have hεγ : ε ≤ γ/16 := by nlinarith [mul_nonneg hn hε]
  have hq : ε^2/(γ/4) ≤ ε/4 := by
    apply (div_le_iff₀ (by positivity : 0 < γ/4)).2
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hεγ)]
  have hh := mul_le_mul_of_nonneg_left hq hn
  nlinarith

end ContinuumCoulomb

end

end OAI
