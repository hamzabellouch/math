import OAI.Analysis.KadisonKastler.BilateralBlockWords
import OAI.Analysis.KadisonKastler.BilateralL2Transport
import OAI.Analysis.KadisonKastler.UnitaryCoordinateFunctions

namespace OAI

/-! Measurability and independence of the two transported finite blocks. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory Set

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

def bilateralBlockA (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) : Lp K 2 (bilateralWalkLaw G) :=
  countableUnitaryL2 σ (bilateralLeftWord_measurable G m) g

def bilateralBlockB (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) : Lp K 2 (bilateralWalkLaw G) :=
  countableUnitaryL2 (fun h => (σ h)⁻¹) (bilateralRightWord_measurable G m)
    (bilateralTranslateL2 (2 * m + 2) g)

theorem bilateralBlockA_coordinate (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | j ≤ m}]
      (bilateralBlockA σ m g) (bilateralWalkLaw G) := by
  apply countableUnitaryL2_sigma
  · exact bilateralIncrementProduct_coordinate_measurable (m + 1) (by intro j hj; change (j : ℤ) ≤ m; omega)
  · exact hg.mono (cylinderEvents_mono (by intro j hj; exact hj.2))

theorem bilateralBlockB_coordinate (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | (m : ℤ) + 2 ≤ j}]
      (bilateralBlockB σ m g) (bilateralWalkLaw G) := by
  apply countableUnitaryL2_sigma
  · exact bilateralIncrementProduct_shift_coordinate_measurable (m + 2) m
      (by intro j hj; change (m : ℤ) + 2 ≤ (j : ℤ) + (m + 2); omega)
  · have ht := bilateralTranslate_coordinate_aestronglyMeasurable (2 * m + 2 : ℤ)
      (show ∀ j ∈ bilateralSymmetricWindow m, j + (2 * m + 2 : ℤ) ∈ {j : ℤ | (m : ℤ) + 2 ≤ j} from by
        intro j hj
        change -(m : ℤ) ≤ j ∧ j ≤ m at hj
        change (m : ℤ) + 2 ≤ j + (2 * m + 2 : ℤ)
        omega) hg
    exact ht.congr (bilateralTranslateL2_ae (2 * m + 2) g).symm

variable [MeasurableSpace K] [BorelSpace K]

theorem bilateralBlock_independent_left (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    IndepFun (bilateralBlockA σ m g)
      (fun ω => (bilateralMiddleWord G m ω, bilateralBlockB σ m g ω)) (bilateralWalkLaw G) := by
  have ha := bilateralBlockA_coordinate σ m g hg
  have hb := (bilateralBlockB_coordinate σ m g hg).mono
    (cylinderEvents_mono (show {j : ℤ | (m : ℤ) + 2 ≤ j} ⊆ {j : ℤ | (m : ℤ) < j} from by
      intro j hj; change (m : ℤ) + 2 ≤ j at hj; change (m : ℤ) < j; omega))
  have hp : Measurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | (m : ℤ) < j}]
      (bilateralMiddleWord G m) :=
    (measurable_of_countable (Inv.inv : G → G)).comp (measurable_cylinderEvent_apply (by
      change (m : ℤ) < ((m + 1 : ℕ) : ℤ); omega))
  have hd : Disjoint {j : ℤ | j ≤ m} {j : ℤ | (m : ℤ) < j} := by
    apply Set.disjoint_left.mpr
    intro j hj hk
    change j ≤ (m : ℤ) at hj
    change (m : ℤ) < j at hk
    omega
  refine bilateralCoordinate_indepFun hd ha.stronglyMeasurable_mk.measurable
    (hp.prodMk hb.stronglyMeasurable_mk.measurable) ha.ae_eq_mk ?_
  exact hb.ae_eq_mk.mono (fun ω hω => Prod.ext rfl hω)

theorem bilateralBlock_independent_right (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    IndepFun (bilateralBlockB σ m g)
      (fun ω => (bilateralMiddleWord G m ω, bilateralBlockA σ m g ω)) (bilateralWalkLaw G) := by
  have hb := bilateralBlockB_coordinate σ m g hg
  have ha := (bilateralBlockA_coordinate σ m g hg).mono
    (cylinderEvents_mono (show {j : ℤ | j ≤ m} ⊆ {j : ℤ | j ≤ (m : ℤ) + 1} from by
      intro j hj; change j ≤ (m : ℤ) at hj; change j ≤ (m : ℤ) + 1; omega))
  have hp : Measurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | j ≤ (m : ℤ) + 1}]
      (bilateralMiddleWord G m) :=
    (measurable_of_countable (Inv.inv : G → G)).comp (measurable_cylinderEvent_apply (by
      change ((m + 1 : ℕ) : ℤ) ≤ (m : ℤ) + 1; omega))
  have hd : Disjoint {j : ℤ | (m : ℤ) + 2 ≤ j} {j : ℤ | j ≤ (m : ℤ) + 1} := by
    apply Set.disjoint_left.mpr
    intro j hj hk
    change (m : ℤ) + 2 ≤ j at hj
    change j ≤ (m : ℤ) + 1 at hk
    omega
  refine bilateralCoordinate_indepFun hd hb.stronglyMeasurable_mk.measurable
    (hp.prodMk ha.stronglyMeasurable_mk.measurable) hb.ae_eq_mk ?_
  exact ha.ae_eq_mk.mono (fun ω hω => Prod.ext rfl hω)

end

end KadisonKastler

end OAI
