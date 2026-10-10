import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.dInverseLocalTF

namespace OAI

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local instance] physicalObservationLaw_probability

 theorem exists_actual_annular_TF_cap_constant {B c ε : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c) (hcL : c < (10*(100000:ℝ))⁻¹) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        ∃ G : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] G ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real Gᶜ ≤ C*u^25 ∧
          ∀ q ∈ G, ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
            (‖y‖^4*originalQueryField (F i) (Z i) (lam i) (r₀ i) j c (r₀ i) (s i) q y ≤ actualInverseCap) ∧
            |originalQueryDensity (F i) (r₀ i) j c (r₀ i) (s i) q y -
              tfDensityCoefficient*(max
                (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c (r₀ i) (s i) q y) 0)^(3/2:ℝ)|
              < ε/‖y‖^6 := by
  have hcap : 0 ≤ actualInverseCap := by
    have hh := tfPatchCapConstant_pos
    unfold actualInverseCap
    positivity
  obtain ⟨lo,xi,hlo,hxi,hsmall,hlh,hgap,hTF⟩ :=
    exists_inverse_local_tf_admissible_parameters tfDensityCoefficient_pos hcap
      (hi := actualInverseCap+2) (by linarith) hε
  obtain ⟨C,hC,hresult⟩ := exists_actual_fullAnnulus_good_constant hB hc hcL hlh.le hxi hsmall
  refine ⟨C,hC,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs hr hF
  have hgood := hresult hδ hs hr hF
  filter_upwards [hgood,hr] with i hi hri
  intro j hjs
  obtain ⟨G,hG,hprob,hcomp⟩ := hi j hjs
  refine ⟨G,hG,hprob,?_⟩
  intro q hq y hyl hyh
  have hy : 0 < ‖y‖ := (mul_pos (pow_pos (by norm_num) _) hri).trans_le hyl
  exact ⟨(hcomp q hq y hyl hyh).1,
    hTF hy (jointMasterPosterior_nonneg _ _ _ _ _ _ _ _ _) (hcomp q hq y hyl hyh)⟩

end CoulombAtom

end

end OAI
