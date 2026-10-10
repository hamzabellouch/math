import Mathlib
import OAI.Analysis.Conductivity.Branching.RegularMomentTransport

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma CompactSmoothPair.sum {ι : Type*} (s : Finset ι) (r : ι → PhysicalSourcePair)
    (hr : ∀ i∈s,CompactSmoothPair (r i)) : CompactSmoothPair (∑ i∈s,r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CompactSmoothPair.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hr a (Finset.mem_insert_self a s)).add (ih fun i hi => hr i (Finset.mem_insert_of_mem hi))

lemma PairSupported.sum {ι : Type*} (s : Finset ι) (r : ι → PhysicalSourcePair)
    {U : Set Coord3} (hr : ∀ i∈s,PairSupported (r i) U) : PairSupported (∑ i∈s,r i) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PairSupported.zero (U := U)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hr a (Finset.mem_insert_self a s)).add (ih fun i hi => hr i (Finset.mem_insert_of_mem hi))

lemma physicalSourceMoment_sum {ι : Type*} (s : Finset ι) (r : ι → PhysicalSourcePair)
    {u : Coord3 → Fin 2 → ℝ} (hu : Continuous u)
    (hr : ∀ i∈s,CompactSmoothPair (r i)) :
    physicalSourceMoment u (∑ i∈s,r i)=∑ i∈s,physicalSourceMoment u (r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using physicalSourceMoment_zero u
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha,physicalSourceMoment_add hu
      (hr a (Finset.mem_insert_self a s))
      (CompactSmoothPair.sum s r (fun i hi => hr i (Finset.mem_insert_of_mem hi)))]
    rw [ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))]

lemma PhysicallyCorrectable.sum {ι : Type*} (s : Finset ι) (r : ι → PhysicalSourcePair)
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {U : Set Coord3} (hr : ∀ i∈s,PhysicallyCorrectable u U (r i)) :
    PhysicallyCorrectable u U (∑ i∈s,r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PhysicallyCorrectable.zero (u := u) (U := U)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hr a (Finset.mem_insert_self a s)).add hu (ih fun i hi => hr i (Finset.mem_insert_of_mem hi))

theorem physical_source_finite_split
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (hU : IsOpen U) (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p))
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : PairSupported r U) :
    ∃ (s : Finset (RegularCorrectionBox u U)) (p : s → PhysicalSourcePair),
      (∀ i,CompactSmoothPair (p i)) ∧
      (∀ i,PairSupported (p i) i.val.region) ∧ (∑ i,p i)=r := by
  classical
  let K := tsupport (r 0) ∪ tsupport (r 1)
  have hK : IsCompact K := (hr 0).2.union (hr 1).2
  have hKU : K⊆U := union_subset (hs 0) (hs 1)
  have hcov : K⊆⋃ B : RegularCorrectionBox u U,B.region := by
    rwa [regular_correction_boxes_cover hu hU hD]
  obtain ⟨s,hsc⟩ := hK.elim_finite_subcover (fun B : RegularCorrectionBox u U => B.region)
    (fun B => B.region_open) hcov
  have hsc' : K⊆⋃ B : s,B.val.region := by
    intro x hx
    obtain ⟨B,hB,hxB⟩ := mem_iUnion₂.mp (hsc hx)
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hxB⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ Coord3) hK.isClosed (fun B : s => B.val.region)
    (fun B => B.val.region_open) hsc'
  let p : s → PhysicalSourcePair := fun i j x => ρ i x*r j x
  refine ⟨s,p,fun i j => ⟨(ρ i).contMDiff.contDiff.mul (hr j).1,(hr j).2.mul_left⟩,
    fun i j => tsupport_mul_subset_left.trans (hρ i),?_⟩
  funext j x
  simp only [Finset.sum_apply,p]
  change (∑ i : s,ρ i x*r j x)=r j x
  rw [←Finset.sum_mul]
  by_cases hx : x∈K
  · have he := ρ.sum_eq_one hx
    rw [finsum_eq_sum_of_fintype] at he
    rw [he,one_mul]
  · have hz : r j x=0 := by
      apply Function.notMem_support.mp
      intro h
      apply hx
      fin_cases j
      · exact Or.inl (subset_tsupport (r 0) h)
      · exact Or.inr (subset_tsupport (r 1) h)
    simp [hz]

theorem global_regular_symmetric_correction
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p))
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : PairSupported r U)
    (hm : physicalSourceMoment u r=0) : PhysicallyCorrectable u U r := by
  classical
  by_cases hne : U.Nonempty
  · obtain ⟨x,hx⟩ := hne
    obtain ⟨B,_⟩ := exists_regular_correction_box hu hU hx (hD x hx)
    obtain ⟨s,p,hp,hps,hpe⟩ := physical_source_finite_split hu hU hD hr hs
    choose q hq hqs hqm hqc using fun i : s =>
      regular_source_transport hu hU hUc hD i.val B (hp i) (hps i)
    have hQ : CompactSmoothPair (∑ i,q i) := CompactSmoothPair.sum _ q (fun i _ => hq i)
    have hQs : PairSupported (∑ i,q i) B.region := PairSupported.sum _ q (fun i _ => hqs i)
    have hQm : physicalSourceMoment u (∑ i,q i)=0 := by
      rw [physicalSourceMoment_sum _ q hu.continuous (fun i _ => hq i)]
      simp_rw [hqm]
      rw [←physicalSourceMoment_sum _ p hu.continuous (fun i _ => hp i),hpe,hm]
    have hbase := B.correct hu hQ hQs hQm
    have hall := (PhysicallyCorrectable.sum Finset.univ (fun i => p i-q i) hu
      (fun i _ => hqc i)).add hu hbase
    rw [Finset.sum_sub_distrib,sub_add_cancel,hpe] at hall
    exact hall
  · have he : r=0 := by
      funext j x
      exact Function.notMem_support.mp (fun h => hne ⟨x,hs j (subset_tsupport (r j) h)⟩)
    rw [he]
    exact PhysicallyCorrectable.zero

end ScalarConductivity

end
end

end OAI
