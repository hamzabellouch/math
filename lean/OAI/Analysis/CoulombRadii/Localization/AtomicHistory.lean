import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.EnsembleCoveredCost

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def atomicIMS {n : ℕ} (ψ : H1Vector n) (y : Space) : ℝ :=
  3*(radialCutCoefficient/(40*atomicCellScale y))^2*
    expectedPopulation ψ (Metric.closedBall y (80*atomicCellScale y))

def atomicPatchRegion {j : ℕ} (y : Fin j → Space) : Set Space :=
  ⋃ i, Metric.closedBall (y i) (80*atomicCellScale (y i))

lemma atomicPatchRegion_snoc {j : ℕ} (y : Fin j → Space) (z : Space) :
    atomicPatchRegion (Fin.snoc y z)=atomicPatchRegion y∪Metric.closedBall z (80*atomicCellScale z) := by
  unfold atomicPatchRegion
  rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]
  simp only [Function.comp_def,Fin.snoc_castSucc,Fin.snoc_last]

structure AtomicCutHistory {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (j : ℕ) where
  ensemble : RecordedEnsemble n
  target : Fin j → Space
  nonzero : ∀ i, target i≠0
  law : ensemble.Conserves ψ
  fermionic : ensemble.CoreFermionic
  support : ensemble.OutSupported (atomicPatchRegion target)
  mass_eq : ensemble.totalMass=mass ψ
  energy : ensemble.totalForm S≤form S ψ+∑ i, atomicIMS ψ (target i)

namespace AtomicCutHistory
variable {J n j : ℕ} {S : Nuclei J} {ψ : H1Vector n}

def initial (S : Nuclei J) (ψ : H1Vector n) (hψ : Antisymmetric ψ) : AtomicCutHistory S ψ 0 where
  ensemble := RecordedEnsemble.initial ψ
  target := Fin.elim0
  nonzero := fun i => Fin.elim0 i
  law := RecordedEnsemble.initial_conserves ψ
  fermionic := RecordedEnsemble.initial_fermionic ψ hψ
  support := by simpa only [atomicPatchRegion,Set.iUnion_of_empty] using RecordedEnsemble.initial_supported ψ
  mass_eq := RecordedEnsemble.initial_mass ψ
  energy := by simp only [RecordedEnsemble.initial_form,Finset.univ_eq_empty,Finset.sum_empty,add_zero,le_refl]

def center (T : AtomicCutHistory S ψ j) (c : Fin j × {z : Space // z∈atomicPatchMesh}) : Space :=
  atomicMeshCenter (T.target c.1) c.2.val

lemma center_nonzero (T : AtomicCutHistory S ψ j) (c) : T.center c≠0 :=
  atomicCellScale_near_nonzero (T.nonzero c.1) (by
    change ‖atomicMeshCenter (T.target c.1) c.2.val-T.target c.1‖≤_
    have H := atomicMeshCenter_distance (T.target c.1) c.2.val c.2.property
    nlinarith [atomicCellScale_nonneg (T.target c.1)])

theorem append (hatom : ∀ i, S.position i=0) (T : AtomicCutHistory S ψ j)
    (hmass : mass ψ=1) {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S)
    (hstate : form S ψ≤E+δ) {y : Space} (hy : y≠0) :
    ∃ U : AtomicCutHistory S ψ (j+1),
      U.target=Fin.snoc T.target y ∧
      (∀ H : ℝ,
        (∀ c v, ‖v-U.center c‖≤2*atomicCellScale (U.center c) →
          U.ensemble.rawSquare S v (atomicCellScale v)≤H) →
        atomicCellScale y/(16*ballTrialCoefficient)*T.ensemble.rawSquare S y (atomicCellScale y)≤
          δ+(∑ i, atomicIMS ψ (U.target i))+4*ballTrialCoefficient*(screenBaseMass (atomicCellScale y))^2/atomicCellScale y+
          ∑ c, (Real.sqrt (localCountSecondMoment ψ (Metric.closedBall (U.center c) (atomicCellScale (U.center c)))*(8*H))+
            (((Fintype.card (Fin (j+1) × {z : Space // z∈atomicPatchMesh})):ℝ)*
              (∑ d, localCountSecondMoment ψ (Metric.closedBall (U.center d) (atomicCellScale (U.center d)))))/
              (3*atomicCellScale (U.center c)))) := by
  have ha := atomicCellScale_pos hy
  have hnuc (i) : 3*atomicCellScale y≤‖S.position i-y‖ := by
    rw [hatom i]
    have H := atomicCellScale_nucleus_far y
    linarith [atomicCellScale_nonneg y]
  obtain ⟨V,hV,hanti,hsupp,hm,hform,hgain⟩ := T.ensemble.append_radial S ψ T.law T.fermionic
    (atomicPatchRegion T.target) T.support ha y hnuc hE
  have hag : ∑ i : Fin (j+1), atomicIMS ψ (Fin.snoc (α := fun _ => Space) T.target y i)=(∑ i, atomicIMS ψ (T.target i))+atomicIMS ψ y := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
  let U : AtomicCutHistory S ψ (j+1) := {
    ensemble := V
    target := Fin.snoc T.target y
    nonzero := by
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using hy
      · simpa only [Fin.snoc_castSucc] using T.nonzero i
    law := hV
    fermionic := hanti
    support := by rwa [atomicPatchRegion_snoc]
    mass_eq := hm.trans T.mass_eq
    energy := by
      rw [hag]
      have HG := T.energy
      change V.totalForm S≤_
      change V.totalForm S≤T.ensemble.totalForm S+atomicIMS ψ y at hform
      linarith }
  refine ⟨U,rfl,?_⟩
  intro H hraw
  have hcost := RecordedEnsemble.atomic_cost_lower S hatom ψ U.ensemble U.law U.center U.center_nonzero
    (RecordedEnsemble.patches_cover U.ensemble U.target U.nonzero U.support) hraw
  have hm1 : T.ensemble.totalMass=1 := T.mass_eq.trans hmass
  rw [hm1,mul_one,mul_one] at hgain
  have HG := T.energy
  have hs : ∑ i, atomicIMS ψ (U.target i)=(∑ i, atomicIMS ψ (T.target i))+atomicIMS ψ y := hag
  rw [hs]
  change _≤_+atomicIMS ψ y-_ -E+_ at hgain
  linarith

end AtomicCutHistory
end Coulomb
end

end
end

end OAI
