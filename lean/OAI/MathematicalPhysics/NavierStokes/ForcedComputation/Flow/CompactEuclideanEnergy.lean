import OAI.MathematicalPhysics.AlternatingFlow.EnergyUniqueness
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.CompactRapidCoordinates

namespace OAI

/-! Energy regularity of compact smooth fields, transferred to the Euclidean
coordinate convention. Pressure uniqueness is stated modulo time-dependent
spatial constants, as in the balanced-box application. -/

noncomputable section
namespace ForcedComputation.CompactEuclidean
open Set
open RapidForcing.CompactEmbedding
open scoped ContDiff

def velocity (V : ShearFlows.Velocity) : AlternatingNS.Velocity :=
  fun t x => piCoordinates.symm (V (t, piCoordinates x))

theorem velocity_smooth {V : ShearFlows.Velocity} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (velocity V)) :=
  piCoordinates.symm.contDiff.comp
    (hV.comp (contDiff_fst.prodMk (piCoordinates.contDiff.comp contDiff_snd)))

theorem piField_velocity (V : ShearFlows.Velocity) :
    piField (velocity V) = V := by
  funext y
  simp only [piField, velocity, ContinuousLinearEquiv.apply_symm_apply]

theorem velocity_divergence (V : ShearFlows.Velocity) (t : ℝ) (x : AlternatingNS.Space) :
    AlternatingNS.div (velocity V) t x =
      ShearFlows.divergence (fun y => V (t,y)) (piCoordinates x) := by
  have h := piField_divergence (velocity V) t (piCoordinates x)
  rw [piField_velocity] at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply, AlternatingNS.div,
    AlternatingNS.dx, AlternatingNS.e, RapidForcing.divergence,
    RapidForcing.spatialD, RapidForcing.basis] using h.symm

theorem velocity_support {V : ShearFlows.Velocity} {K : Set ShearFlows.Space}
    (hs : ∀ t, Function.support (fun x => V (t,x)) ⊆ K) (t : ℝ) :
    Function.support (velocity V t) ⊆ piCoordinates.symm '' K := by
  intro x hx
  have hv : V (t, piCoordinates x) ≠ 0 := by
    intro hz
    exact hx (by simp only [velocity, hz, map_zero])
  exact ⟨piCoordinates x, hs t hv, piCoordinates.symm_apply_apply x⟩

theorem velocity_energyClass {V : ShearFlows.Velocity} (hV : ContDiff ℝ ∞ V)
    {K : Set ShearFlows.Space} (hK : IsCompact K)
    (hs : ∀ t, Function.support (fun x => V (t,x)) ⊆ K) :
    AlternatingNS.EnergyClass (velocity V) (fun _ _ => 0) :=
  AlternatingNS.Analytic.smooth_energyClass (velocity V) (velocity_smooth hV)
    (piCoordinates.symm '' K) (hK.image piCoordinates.symm.continuous) (velocity_support hs)

theorem velocity_global_material_flow {V : ShearFlows.Velocity} (hV : ContDiff ℝ ∞ V)
    {K : Set ShearFlows.Space} (hK : IsCompact K)
    (hs : ∀ t, Function.support (fun x => V (t,x)) ⊆ K) :
    ∃ X : AlternatingNS.Space → ℝ → AlternatingNS.Space,
      (∀ a, AlternatingNS.IsTrajectory (velocity V) a (X a)) ∧
      (∀ a γ, AlternatingNS.IsTrajectory (velocity V) a γ →
        ∀ t, 0 ≤ t → γ t = X a t) :=
  AlternatingNS.Analytic.global_material_flow (velocity V) (velocity_smooth hV)
    (piCoordinates.symm '' K) (hK.image piCoordinates.symm.continuous) (velocity_support hs)

/-- A pressure class has an energy-regular representative satisfying the
equations. Its spatially constant gauge may depend on time. -/
def IsEnergySolutionModuloConstants (ν : ℝ) (f u : AlternatingNS.Velocity)
    (p : AlternatingNS.Pressure) : Prop :=
  ∃ c : ℝ → ℝ,
    AlternatingNS.NavierStokes ν f u (fun t x => p t x - c t) ∧
    AlternatingNS.CompetitorEnergyClass u (fun t x => p t x - c t)

theorem energy_unique_modulo_constants {ν : ℝ} (hν : 0 ≤ ν)
    {f U v : AlternatingNS.Velocity} {p : AlternatingNS.Pressure}
    (hU : AlternatingNS.NavierStokes ν f U (fun _ _ => 0))
    (hUE : AlternatingNS.EnergyClass U (fun _ _ => 0))
    (hv : IsEnergySolutionModuloConstants ν f v p) :
    ∃ c : ℝ → ℝ, ∀ t, 0 ≤ t → ∀ x, v t x = U t x ∧ p t x = c t := by
  obtain ⟨c, hvc, hvE⟩ := hv
  have he := AlternatingNS.Analytic.energy_unique ν hν f U v (fun t x => p t x - c t)
    hU hvc hUE hvE
  exact ⟨c, fun t ht x => ⟨(he t ht x).1, sub_eq_zero.mp (he t ht x).2⟩⟩

theorem compact_velocity_solution {ν : ℝ} (hν : 0 < ν)
    {V : ShearFlows.Velocity} (hV : ContDiff ℝ ∞ V)
    {K : Set ShearFlows.Space} (hK : IsCompact K)
    (hs : ∀ t, Function.support (fun x => V (t,x)) ⊆ K)
    (h0 : ∀ x, V (0,x) = 0) (hd : ShearFlows.Solenoidal V) :
    let U := velocity V
    AlternatingNS.NavierStokes ν (AlternatingNS.residual ν U) U (fun _ _ => 0) ∧
    AlternatingNS.EnergyClass U (fun _ _ => 0) ∧
    ∀ v p, IsEnergySolutionModuloConstants ν (AlternatingNS.residual ν U) v p →
      ∃ c : ℝ → ℝ, ∀ t, 0 ≤ t → ∀ x, v t x = U t x ∧ p t x = c t := by
  dsimp only
  have hsol := AlternatingNS.Analytic.residual_navierStokes ν (velocity V) (velocity_smooth hV)
    (fun x => by simp only [velocity, h0, map_zero])
    (fun t _ x => by rw [velocity_divergence]; exact hd t (piCoordinates x))
  have hE := velocity_energyClass hV hK hs
  exact ⟨hsol, hE, fun v p hv => energy_unique_modulo_constants hν.le hsol hE hv⟩

end ForcedComputation.CompactEuclidean

end

end OAI
