import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverDegree
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

/-! A measurable section of the actual finite cover, constructed from
a countable disjoint refinement of its injective covering charts. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaPrimeCoverChart {p : Eisenstein} (hp : primaryPrime p) (x : CubicThetaPoint) :
    OpenPartialHomeomorph CubicThetaPoint (CubicThetaPrimeCover hp) :=
  Classical.choose ((cubicThetaPrimeCover_covering hp).isCoveringMap.isLocalHomeomorph x)

lemma cubicThetaPrimeCoverChart_source {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) : x∈(cubicThetaPrimeCoverChart hp x).source :=
  (Classical.choose_spec ((cubicThetaPrimeCover_covering hp).isCoveringMap.isLocalHomeomorph x)).1

lemma cubicThetaPrimeCoverChart_coe {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    (cubicThetaPrimeCoverChart hp x : CubicThetaPoint → CubicThetaPrimeCover hp)=
      cubicThetaPrimeCoverMap hp :=
  (Classical.choose_spec ((cubicThetaPrimeCover_covering hp).isCoveringMap.isLocalHomeomorph x)).2.symm

lemma cubicThetaPrimeCover_countable_charts {p : Eisenstein} (hp : primaryPrime p) :
    ∃ c : ℕ → CubicThetaPoint,
      ∀ q : CubicThetaPrimeCover hp, ∃ n, q∈(cubicThetaPrimeCoverChart hp (c n)).target := by
  obtain ⟨S,hSc,hS⟩ := isLindelof_univ.elim_countable_subcover
    (fun x : CubicThetaPoint => (cubicThetaPrimeCoverChart hp x).target)
    (fun x => (cubicThetaPrimeCoverChart hp x).open_target) (by
      intro q _
      obtain ⟨x,rfl⟩ := Quotient.mk_surjective q
      apply mem_iUnion.mpr
      refine ⟨x,?_⟩
      change cubicThetaPrimeCoverMap hp x∈(cubicThetaPrimeCoverChart hp x).target
      rw [←cubicThetaPrimeCoverChart_coe hp x]
      exact (cubicThetaPrimeCoverChart hp x).map_source (cubicThetaPrimeCoverChart_source hp x))
  have hSne : S.Nonempty := by
    let x : CubicThetaPoint := ⟨(0,1),by norm_num⟩
    obtain ⟨y,hy,_⟩ := mem_iUnion₂.mp (hS (mem_univ (cubicThetaPrimeCoverMap hp x)))
    exact ⟨y,hy⟩
  obtain ⟨c,hc⟩ := hSc.exists_eq_range hSne
  refine ⟨c,fun q => ?_⟩
  obtain ⟨x,hx,hqx⟩ := mem_iUnion₂.mp (hS (mem_univ q))
  rw [hc] at hx
  obtain ⟨n,rfl⟩ := hx
  exact ⟨n,hqx⟩

def cubicThetaPrimeCoverCenter {p : Eisenstein} (hp : primaryPrime p) : ℕ → CubicThetaPoint :=
  Classical.choose (cubicThetaPrimeCover_countable_charts hp)

def cubicThetaPrimeCoverOpen {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    Set (CubicThetaPrimeCover hp) :=
  (cubicThetaPrimeCoverChart hp (cubicThetaPrimeCoverCenter hp n)).target

def cubicThetaPrimeCoverPiece {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    Set (CubicThetaPrimeCover hp) := disjointed (cubicThetaPrimeCoverOpen hp) n

lemma cubicThetaPrimeCoverPiece_measurable {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    MeasurableSet (cubicThetaPrimeCoverPiece hp n) :=
  MeasurableSet.disjointed
    (fun n => (cubicThetaPrimeCoverChart hp (cubicThetaPrimeCoverCenter hp n)).open_target.measurableSet) n

lemma cubicThetaPrimeCoverPiece_cover {p : Eisenstein} (hp : primaryPrime p) :
    ⋃ n, cubicThetaPrimeCoverPiece hp n=univ := by
  change (⋃ n, disjointed (cubicThetaPrimeCoverOpen hp) n)=univ
  rw [iUnion_disjointed]
  apply eq_univ_of_forall
  intro q
  exact mem_iUnion.mpr (Classical.choose_spec (cubicThetaPrimeCover_countable_charts hp) q)

def cubicThetaPrimeCoverLocalLift {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    CubicThetaPrimeCover hp → CubicThetaPoint :=
  (cubicThetaPrimeCoverOpen hp n).piecewise
    (cubicThetaPrimeCoverChart hp (cubicThetaPrimeCoverCenter hp n)).symm
    (fun _ => cubicThetaPrimeCoverCenter hp n)

lemma cubicThetaPrimeCoverLocalLift_measurable {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    Measurable (cubicThetaPrimeCoverLocalLift hp n) := by
  apply ContinuousOn.measurable_piecewise
  · exact (cubicThetaPrimeCoverChart hp (cubicThetaPrimeCoverCenter hp n)).symm.continuousOn
  · exact continuous_const.continuousOn
  · exact (cubicThetaPrimeCoverChart hp (cubicThetaPrimeCoverCenter hp n)).open_target.measurableSet

lemma cubicThetaPrimeCoverLocalLift_rightInverse {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) {q : CubicThetaPrimeCover hp} (hq : q∈cubicThetaPrimeCoverPiece hp n) :
    cubicThetaPrimeCoverMap hp (cubicThetaPrimeCoverLocalLift hp n q)=q := by
  have hu := disjointed_subset (cubicThetaPrimeCoverOpen hp) n hq
  rw [cubicThetaPrimeCoverLocalLift,piecewise_eq_of_mem _ _ _ hu]
  rw [←cubicThetaPrimeCoverChart_coe hp (cubicThetaPrimeCoverCenter hp n)]
  exact (cubicThetaPrimeCoverChart hp (cubicThetaPrimeCoverCenter hp n)).right_inv hu

theorem cubicThetaPrimeCover_measurable_section_exists {p : Eisenstein} (hp : primaryPrime p) :
    ∃ s : CubicThetaPrimeCover hp → CubicThetaPoint,
      Measurable s ∧ Function.RightInverse s (cubicThetaPrimeCoverMap hp) := by
  obtain ⟨s,hs,hse⟩ := exists_measurable_piecewise (cubicThetaPrimeCoverPiece hp)
    (cubicThetaPrimeCoverPiece_measurable hp) (cubicThetaPrimeCoverLocalLift hp)
    (cubicThetaPrimeCoverLocalLift_measurable hp) (by
      intro i j hij q hq
      exact False.elim (Set.disjoint_left.mp
        (disjoint_disjointed (cubicThetaPrimeCoverOpen hp) hij) hq.1 hq.2))
  refine ⟨s,hs,fun q => ?_⟩
  obtain ⟨n,hn⟩ := mem_iUnion.mp ((cubicThetaPrimeCoverPiece_cover hp).symm ▸ mem_univ q)
  rw [hse n hn]
  exact cubicThetaPrimeCoverLocalLift_rightInverse hp n hn

def cubicThetaPrimeBorelSection {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeCover hp → CubicThetaPoint :=
  Classical.choose (cubicThetaPrimeCover_measurable_section_exists hp)

lemma cubicThetaPrimeBorelSection_measurable {p : Eisenstein} (hp : primaryPrime p) :
    Measurable (cubicThetaPrimeBorelSection hp) :=
  (Classical.choose_spec (cubicThetaPrimeCover_measurable_section_exists hp)).1

lemma cubicThetaPrimeBorelSection_rightInverse {p : Eisenstein} (hp : primaryPrime p) :
    Function.RightInverse (cubicThetaPrimeBorelSection hp) (cubicThetaPrimeCoverMap hp) :=
  (Classical.choose_spec (cubicThetaPrimeCover_measurable_section_exists hp)).2

end CubicFirstMoment

end

end OAI
