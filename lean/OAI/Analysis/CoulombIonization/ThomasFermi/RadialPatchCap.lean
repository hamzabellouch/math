import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialPatchGeometry
import OAI.Analysis.CoulombIonization.ThomasFermi.TFNonradialOscillation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAtom
open CoulombAnalysis

theorem radialPatchMinimizer_nonradial_cap {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hbt : 4*b < t) (hy : t ≤ ‖y‖) (Z lam : ℝ) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := orderedCutForm p hp ψ c
    ∀ᵐ u, ∀ x : Space, ‖x‖ ≤ 3*(t-4*b)/4 →
      let f := tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos
        (conditionalPatchField χ s Z lam y (t-4*b) u)
      normalizedCoreField Z lam (coreSlice χ s u) (y+x)-tfBallPotential (t-4*b) f x ≤
        tfPatchCapConstant/(t-4*b)^4 := by
  dsimp only
  filter_upwards [(orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ c).ae_coreSlice s] with u hu
  intro x hx
  apply conditionalPatchMinimizer_nonradial_cap _ s u hu (radialPatchCore y t) _ y
    (by linarith) hb hb (radialPatch_nuclear_distance hb hy)
    (radialPatch_core_distance y hb) Z lam x hx
  intro x i hi
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists x u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

theorem radialPatchMinimizer_density_cap {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hbt : 4*b < t) (hy : t ≤ ‖y‖) (Z lam : ℝ) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := orderedCutForm p hp ψ c
    ∀ᵐ u,
      let f := tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos
        (conditionalPatchField χ s Z lam y (t-4*b) u)
      ∀ᵐ x ∂ballMeasure (t-4*b), ‖x‖ ≤ 3*(t-4*b)/4 →
        f x ≤ (tfPatchCapConstant/(t-4*b)^4/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) := by
  dsimp only
  filter_upwards [(orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ c).ae_coreSlice s] with u hu
  apply conditionalPatchMinimizer_density_cap _ s u hu (radialPatchCore y t) _ y
    (by linarith) hb hb (radialPatch_nuclear_distance hb hy)
    (radialPatch_core_distance y hb) Z lam
  intro x i hi
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists x u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

end CoulombAtom

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

def tfPatchOscillationConstant : ℝ :=
  Classical.choose (exists_weak_tf_oscillation_constant tfReactionCoefficient_pos)

lemma tfPatchOscillationConstant_pos : 0 < tfPatchOscillationConstant :=
  (Classical.choose_spec (exists_weak_tf_oscillation_constant tfReactionCoefficient_pos)).1

lemma tfPatchOscillationConstant_bound {u : Space → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (closedBall 0 R))
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R →
      (∫ x, u x*Δ g x) = ∫ x, tfReactionCoefficient*(max (u x) 0)^(3/2:ℝ)*g x)
    (x : Space) (hx : ‖x‖ ≤ R/12) :
    |u x-u 0| ≤ tfPatchOscillationConstant/R*‖x‖*(R⁻¹^4+max (-u 0) 0) :=
  (Classical.choose_spec (exists_weak_tf_oscillation_constant tfReactionCoefficient_pos)).2 u R hR hu hw x hx

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

theorem conditionalPatchMinimizer_nonradial_oscillation {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (Z lam : ℝ) (x : Space) (hx : ‖x‖ ≤ R/12) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    let W := fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-tfBallPotential R f z
    |W x-W 0| ≤ tfPatchOscillationConstant/R*‖x‖*(R⁻¹^4+max (-W 0) 0) := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  apply tfPatchOscillationConstant_bound hR
    (actualPatchField_continuousOn hu A hcore y R hd hr hnuc hsep Z lam f) _ x hx
  intro g hg hcg hs
  apply tf_weak_pde_volume _ hg hcg hs
  intro g hg hcg hs
  exact conditionalPatchMinimizer_weak_pde ψ t u hu A hcore y R hd hr hnuc hsep Z lam hg hcg hs

theorem radialPatchMinimizer_nonradial_oscillation {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hbt : 4*b < t) (hy : t ≤ ‖y‖) (Z lam : ℝ) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := orderedCutForm p hp ψ c
    ∀ᵐ u, ∀ x : Space, ‖x‖ ≤ (t-4*b)/12 →
      let f := tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos
        (conditionalPatchField χ s Z lam y (t-4*b) u)
      let W := fun z => normalizedCoreField Z lam (coreSlice χ s u) (y+z)-tfBallPotential (t-4*b) f z
      |W x-W 0| ≤ tfPatchOscillationConstant/(t-4*b)*‖x‖*((t-4*b)⁻¹^4+max (-W 0) 0) := by
  dsimp only
  filter_upwards [(orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ c).ae_coreSlice s] with u hu
  intro x hx
  apply conditionalPatchMinimizer_nonradial_oscillation _ s u hu (radialPatchCore y t) _ y
    (by linarith) hb hb (radialPatch_nuclear_distance hb hy)
    (radialPatch_core_distance y hb) Z lam x hx
  intro x i hi
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists x u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

end CoulombAtom

end

end OAI
