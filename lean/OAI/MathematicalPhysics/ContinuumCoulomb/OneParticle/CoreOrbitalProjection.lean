import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.H1FiniteProjection
import OAI.Analysis.CoulombRadii.FormDomain.CoreKinetic

namespace OAI

/-! Integrating the one-particle projection estimate over the other electron
coordinates. Slices belong to the full weak-H1 domain almost everywhere. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem h1_inner_orbital {n : ℕ} (u : Coulomb.H1Vector n)
    (s : SpinConfiguration n) (φ : Lp ℂ 2 (volume : Measure (Configuration n))) :
    inner ℂ φ (h1Coordinates u (Sum.inl s)) =
      ∫ x, star (φ x)*u.value s x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u (Sum.inl s)).coeFn_toLp] with x hx
  change h1Coordinates u (Sum.inl s) x = u.value s x at hx
  rw [hx,RCLike.inner_apply]
  exact mul_comm _ _

def coreOrbitalCoefficient {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (φ : Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) (t : SpinConfiguration 1) (x : Configuration n) : ℂ :=
  ∫ y, star (φ y)*u.value (Fin.append s t) (Coulomb.joinConfiguration n 1 (x,y))

theorem coreOrbitalCoefficient_memLp {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (φ : Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) (t : SpinConfiguration 1) :
    MemLp (coreOrbitalCoefficient u φ s t) 2 :=
  Coulomb.fiberContract_memLp (Lp.memLp φ)
    ((u.value_L2 (Fin.append s t)).comp_measurePreserving
      (Coulomb.joinConfiguration_measurePreserving n 1))

theorem core_graphOrbitalMass_ae {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) :
    (fun x => graphOrbitalMass φ (h1Coordinates (u.coreSlice s x))) =ᵐ[volume]
      fun x => ∑ t, ∑ i, ‖coreOrbitalCoefficient u (φ i) s t x‖^2 := by
  filter_upwards [u.coreSliceRegular_ae s] with x hx
  simp only [graphOrbitalMass,h1_inner_orbital,u.coreSlice_value s hx,
    coreOrbitalCoefficient]

theorem core_graphOrbitalMass_integrable {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) :
    Integrable (fun x => graphOrbitalMass φ (h1Coordinates (u.coreSlice s x))) := by
  apply Integrable.congr _ (core_graphOrbitalMass_ae u φ s).symm
  exact integrable_finsetSum _ (fun t _ => integrable_finsetSum _
    (fun i _ => (coreOrbitalCoefficient_memLp u (φ i) s t).norm.integrable_sq))

def coreOrbitalMass {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) : ℝ :=
  ∑ s, ∫ x, graphOrbitalMass φ (h1Coordinates (u.coreSlice s x))

theorem coreOrbitalMass_eq_coefficients {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) :
    coreOrbitalMass u φ = ∑ s, ∑ t, ∑ i, ∫ x, ‖coreOrbitalCoefficient u (φ i) s t x‖^2 := by
  unfold coreOrbitalMass
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_congr_ae (core_graphOrbitalMass_ae u φ s),
    integral_finsetSum _ (fun t _ => integrable_finsetSum _
      (fun i _ => (coreOrbitalCoefficient_memLp u (φ i) s t).norm.integrable_sq))]
  apply Finset.sum_congr rfl
  intro t _
  exact integral_finsetSum _
    (fun i _ => (coreOrbitalCoefficient_memLp u (φ i) s t).norm.integrable_sq)

theorem bounded_state_potential_integrable {n : ℕ} (u : Coulomb.H1Vector n)
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ)
    (hB : ∀ x, |V x| ≤ B) (s : SpinConfiguration n) :
    Integrable (fun x => V x*‖u.value s x‖^2) := by
  apply ((u.value_L2 s).norm.integrable_sq.const_mul B).mono'
    (hV.aestronglyMeasurable.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2))
  filter_upwards [] with x
  change ‖V x*‖u.value s x‖^2‖ ≤ B*‖u.value s x‖^2
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u.value s x‖)]
  exact mul_le_mul_of_nonneg_right (hB x) (sq_nonneg _)

theorem coreOneBody_projection_lower {n : ℕ} {ι : Type*} [Fintype ι]
    (V : Configuration 1 → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) (E κ : ℝ)
    (hbound : ∀ v : Coulomb.H1Vector 1,
      E*Coulomb.mass v-κ*graphOrbitalMass φ (h1Coordinates v) ≤ boundedPotentialForm V v)
    (u : Coulomb.H1Vector (n+1)) :
    E*Coulomb.mass u-κ*coreOrbitalMass u φ ≤ Coulomb.coreKinetic u+
      Coulomb.potentialForm (fun z => V ((Coulomb.joinConfiguration n 1).symm z).2) u := by
  have hip (st : SpinConfiguration (n+1)) : Integrable
      (fun z => V ((Coulomb.joinConfiguration n 1).symm z).2*‖u.value st z‖^2) :=
    bounded_state_potential_integrable u _
      (hV.comp ((Coulomb.joinConfiguration n 1).symm.continuous.snd)) B (fun z => hB _) st
  have hp (s : SpinConfiguration n) :=
    Coulomb.potentialForm_coreSlice_parameter_integrable u s (fun _ y => V y)
      (fun t => hip (Fin.append s t))
  have hs (s : SpinConfiguration n) := integral_mono
    (((Coulomb.mass_coreSlice_integrable u s).const_mul E).sub
      ((core_graphOrbitalMass_integrable u φ s).const_mul κ))
    ((Coulomb.kinetic_coreSlice_integrable u s).add (hp s))
    (fun x => hbound (u.coreSlice s x))
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hs s)
  simp only [Pi.sub_apply,Pi.add_apply] at hh
  simp_rw [integral_sub ((Coulomb.mass_coreSlice_integrable u _).const_mul E)
    ((core_graphOrbitalMass_integrable u φ _).const_mul κ),integral_const_mul,
    integral_add (Coulomb.kinetic_coreSlice_integrable u _) (hp _)] at hh
  have hpot := Coulomb.integral_potentialForm_coreSlice_parameter u (fun _ y => V y) hip
  simp only [Coulomb.potentialForm] at hpot
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Coulomb.integral_mass_coreSlice,Coulomb.integral_kinetic_coreSlice,
    coreOrbitalMass,Coulomb.coreKinetic,Coulomb.potentialForm,hpot] using hh

end ContinuumCoulomb

end

end OAI
