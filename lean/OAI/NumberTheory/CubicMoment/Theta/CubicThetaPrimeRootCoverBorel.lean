import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCoverDegree
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

/-! A measurable section of the actual root cover, constructed from
a countable disjoint refinement of its injective covering charts. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaPrimeRootCoverChart {p : Eisenstein} (hp : primaryPrime p) (x : CubicThetaPoint) :
    OpenPartialHomeomorph CubicThetaPoint (CubicThetaPrimeRootCover hp) :=
  Classical.choose ((cubicThetaPrimeRootCover_covering hp).isCoveringMap.isLocalHomeomorph x)

lemma cubicThetaPrimeRootCoverChart_source {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) : x∈(cubicThetaPrimeRootCoverChart hp x).source :=
  (Classical.choose_spec ((cubicThetaPrimeRootCover_covering hp).isCoveringMap.isLocalHomeomorph x)).1

lemma cubicThetaPrimeRootCoverChart_coe {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    (cubicThetaPrimeRootCoverChart hp x : CubicThetaPoint → CubicThetaPrimeRootCover hp)=
      cubicThetaPrimeRootCoverMap hp :=
  (Classical.choose_spec ((cubicThetaPrimeRootCover_covering hp).isCoveringMap.isLocalHomeomorph x)).2.symm

lemma cubicThetaPrimeRootCover_countable_charts {p : Eisenstein} (hp : primaryPrime p) :
    ∃ c : ℕ → CubicThetaPoint,
      ∀ q : CubicThetaPrimeRootCover hp, ∃ n, q∈(cubicThetaPrimeRootCoverChart hp (c n)).target := by
  obtain ⟨S,hSc,hS⟩ := isLindelof_univ.elim_countable_subcover
    (fun x : CubicThetaPoint => (cubicThetaPrimeRootCoverChart hp x).target)
    (fun x => (cubicThetaPrimeRootCoverChart hp x).open_target) (by
      intro q _
      obtain ⟨x,rfl⟩ := Quotient.mk_surjective q
      apply mem_iUnion.mpr
      refine ⟨x,?_⟩
      change cubicThetaPrimeRootCoverMap hp x∈(cubicThetaPrimeRootCoverChart hp x).target
      rw [←cubicThetaPrimeRootCoverChart_coe hp x]
      exact (cubicThetaPrimeRootCoverChart hp x).map_source (cubicThetaPrimeRootCoverChart_source hp x))
  have hSne : S.Nonempty := by
    let x : CubicThetaPoint := ⟨(0,1),by norm_num⟩
    obtain ⟨y,hy,_⟩ := mem_iUnion₂.mp (hS (mem_univ (cubicThetaPrimeRootCoverMap hp x)))
    exact ⟨y,hy⟩
  obtain ⟨c,hc⟩ := hSc.exists_eq_range hSne
  refine ⟨c,fun q => ?_⟩
  obtain ⟨x,hx,hqx⟩ := mem_iUnion₂.mp (hS (mem_univ q))
  rw [hc] at hx
  obtain ⟨n,rfl⟩ := hx
  exact ⟨n,hqx⟩

def cubicThetaPrimeRootCoverCenter {p : Eisenstein} (hp : primaryPrime p) : ℕ → CubicThetaPoint :=
  Classical.choose (cubicThetaPrimeRootCover_countable_charts hp)

def cubicThetaPrimeRootCoverOpen {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    Set (CubicThetaPrimeRootCover hp) :=
  (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).target

def cubicThetaPrimeRootCoverPiece {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    Set (CubicThetaPrimeRootCover hp) := disjointed (cubicThetaPrimeRootCoverOpen hp) n

lemma cubicThetaPrimeRootCoverPiece_measurable {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    MeasurableSet (cubicThetaPrimeRootCoverPiece hp n) :=
  MeasurableSet.disjointed
    (fun n => (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).open_target.measurableSet) n

lemma cubicThetaPrimeRootCoverPiece_cover {p : Eisenstein} (hp : primaryPrime p) :
    ⋃ n, cubicThetaPrimeRootCoverPiece hp n=univ := by
  change (⋃ n, disjointed (cubicThetaPrimeRootCoverOpen hp) n)=univ
  rw [iUnion_disjointed]
  apply eq_univ_of_forall
  intro q
  exact mem_iUnion.mpr (Classical.choose_spec (cubicThetaPrimeRootCover_countable_charts hp) q)

def cubicThetaPrimeRootCoverLocalLift {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    CubicThetaPrimeRootCover hp → CubicThetaPoint :=
  (cubicThetaPrimeRootCoverOpen hp n).piecewise
    (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).symm
    (fun _ => cubicThetaPrimeRootCoverCenter hp n)

lemma cubicThetaPrimeRootCoverLocalLift_measurable {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    Measurable (cubicThetaPrimeRootCoverLocalLift hp n) := by
  apply ContinuousOn.measurable_piecewise
  · exact (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).symm.continuousOn
  · exact continuous_const.continuousOn
  · exact (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).open_target.measurableSet

lemma cubicThetaPrimeRootCoverLocalLift_rightInverse {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) {q : CubicThetaPrimeRootCover hp} (hq : q∈cubicThetaPrimeRootCoverPiece hp n) :
    cubicThetaPrimeRootCoverMap hp (cubicThetaPrimeRootCoverLocalLift hp n q)=q := by
  have hu := disjointed_subset (cubicThetaPrimeRootCoverOpen hp) n hq
  rw [cubicThetaPrimeRootCoverLocalLift,piecewise_eq_of_mem _ _ _ hu]
  rw [←cubicThetaPrimeRootCoverChart_coe hp (cubicThetaPrimeRootCoverCenter hp n)]
  exact (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).right_inv hu

theorem cubicThetaPrimeRootCover_measurable_section_exists {p : Eisenstein} (hp : primaryPrime p) :
    ∃ s : CubicThetaPrimeRootCover hp → CubicThetaPoint,
      Measurable s ∧ Function.RightInverse s (cubicThetaPrimeRootCoverMap hp) := by
  obtain ⟨s,hs,hse⟩ := exists_measurable_piecewise (cubicThetaPrimeRootCoverPiece hp)
    (cubicThetaPrimeRootCoverPiece_measurable hp) (cubicThetaPrimeRootCoverLocalLift hp)
    (cubicThetaPrimeRootCoverLocalLift_measurable hp) (by
      intro i j hij q hq
      exact False.elim (Set.disjoint_left.mp
        (disjoint_disjointed (cubicThetaPrimeRootCoverOpen hp) hij) hq.1 hq.2))
  refine ⟨s,hs,fun q => ?_⟩
  obtain ⟨n,hn⟩ := mem_iUnion.mp ((cubicThetaPrimeRootCoverPiece_cover hp).symm ▸ mem_univ q)
  rw [hse n hn]
  exact cubicThetaPrimeRootCoverLocalLift_rightInverse hp n hn

def cubicThetaPrimeRootBorelSection {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeRootCover hp → CubicThetaPoint :=
  Classical.choose (cubicThetaPrimeRootCover_measurable_section_exists hp)

lemma cubicThetaPrimeRootBorelSection_measurable {p : Eisenstein} (hp : primaryPrime p) :
    Measurable (cubicThetaPrimeRootBorelSection hp) :=
  (Classical.choose_spec (cubicThetaPrimeRootCover_measurable_section_exists hp)).1

lemma cubicThetaPrimeRootBorelSection_rightInverse {p : Eisenstein} (hp : primaryPrime p) :
    Function.RightInverse (cubicThetaPrimeRootBorelSection hp) (cubicThetaPrimeRootCoverMap hp) :=
  (Classical.choose_spec (cubicThetaPrimeRootCover_measurable_section_exists hp)).2

end CubicFirstMoment

end

end OAI
