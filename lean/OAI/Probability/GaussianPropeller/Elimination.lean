import OAI.Probability.GaussianPropeller.Configuration

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction.Configuration
variable {d k:ℕ}

lemma impossible_five_or_more (D:Configuration d k) (hk:5≤k) : False := by
  classical
  let r:ℕ→ℝ := fun i=>if hi:i<k then ‖D.z ⟨i,hi⟩‖ else 0
  let P:ℕ→ℝ := fun i=>if hi:i<k then D.P ⟨i,hi⟩ else 0
  have hr:∀ i:Fin k,r i=‖D.z i‖ := by intro i; simp [r,i.isLt]
  have hp:∀ i:Fin k,P i=D.P i := by intro i; simp [P,i.isLt]
  have hnorm:∑ i∈Finset.range k,r i^2=1 := by
    rw [Finset.sum_range]
    simpa only [hr] using D.norm
  have hprob:∑ i∈Finset.range k,P i=1 := by
    rw [Finset.sum_range]
    simpa only [hp] using D.probability
  let i:Fin k:=⟨k-1,by omega⟩
  let j:Fin k:=⟨0,by omega⟩
  let l:Fin k:=⟨1,by omega⟩
  let q:Fin k:=⟨2,by omega⟩
  have hdet:=configuration_determinants D.z D.zero D.obtuse i (D.pos i)
    (j:=j) (l:=l) (q:=q) (by dsimp [i,j]; intro h; have:=congrArg Fin.val h; simp at this; omega)
    (by dsimp [i,l]; intro h; have:=congrArg Fin.val h; simp at this; omega)
    (by dsimp [i,q]; intro h; have:=congrArg Fin.val h; simp at this; omega)
    (by simp [j,l,Fin.ext_iff]) (by simp [j,q,Fin.ext_iff]) (by simp [l,q,Fin.ext_iff])
    (D.order (by simp [j,q])) (D.order (by simp [l,q]))
    (D.order (by change 2≤k-1; omega)) (D.pair i)
  apply Scalar.scalar_incompatibility hk r P
  · intro a ha
    simp only [r,dite_eq_left ha]
    exact norm_pos_iff.mpr (D.pos _)
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    simp only [r,dite_eq_left ha,dite_eq_left hb]
    exact D.order (show (⟨a,ha⟩:Fin k)≤⟨b,hb⟩ from hab)
  · intro a ha
    simpa only [r,dite_eq_left ha] using D.cap ⟨a,ha⟩
  · exact hnorm
  · exact hprob
  · intro a ha
    simpa only [r,P,dite_eq_left ha] using D.quadratic ⟨a,ha⟩
  · intro a ha
    simpa only [r,P,dite_eq_left ha] using D.linear ⟨a,ha⟩
  · simpa only [r,dite_eq_left (show 0<k by omega),dite_eq_left (show 1<k by omega),
      dite_eq_left (show 2<k by omega),dite_eq_left (show k-1<k by omega),i,j,l,q] using hdet.1
  · simpa only [r,dite_eq_left (show 2<k by omega),dite_eq_left (show k-1<k by omega),i,q] using hdet.2

lemma impossible_four (D:Configuration d 4) : False :=
  four_incompatibility D.z D.P D.zero D.norm D.pos D.order D.obtuse D.cap
    D.probability D.half (D.cap3 rfl) D.linear (D.loss4 rfl) D.pair

end GaussianPropeller.Reduction.Configuration

namespace GaussianPropeller.Reduction
variable {d k:ℕ}

lemma remove_null_partition {A:Fin (k+1)→Set (Space d)} (hA:IsPartition A)
    (i:Fin (k+1)) (hi:gaussian d (A i)=0) :
    IsPartition (fun j:Fin k=>A (i.succAbove j)) := by
  constructor
  · intro j; exact hA.1 _
  have hn:∀ᵐ x∂gaussian d,x∉A i := by
    exact (ae_iff.mpr (by simpa using hi))
  filter_upwards [hA.2,hn] with x hx hxi
  obtain ⟨j,hj,huniq⟩:=hx
  have hji:j≠i := by intro hh; subst j; contradiction
  obtain ⟨a,ha⟩:=Fin.exists_succAbove_eq hji
  refine ⟨a,?_,?_⟩
  · simpa only [ha] using hj
  · intro b hb
    apply Fin.succAbove_right_injective
    exact (huniq _ hb).trans ha.symm

lemma remove_null_value {A:Fin (k+1)→Set (Space d)} (i:Fin (k+1))
    (hi:gaussian d (A i)=0) : value (fun j:Fin k=>A (i.succAbove j))=value A := by
  unfold value
  rw [Fin.sum_univ_succAbove (fun j=>‖centroid (A j)‖^2) i,centroid_eq_zero_of_null hi]
  simp

lemma partition_bound_small {A:Fin k→Set (Space d)} (hk:k≤3) (hA:IsPartition A) :
    value A≤9/(8*Real.pi) := by
  have he:∃ B:Fin 3→Set (Space d), IsPartition B ∧ value B=value A := by
    have hc:∀ m, k ≤ m → ∃ B:Fin m→Set (Space d), IsPartition B ∧ value B=value A := by
      intro m hm
      induction m,hm using Nat.le_induction with
      | base => exact ⟨A,hA,rfl⟩
      | succ m hm ih =>
        obtain ⟨B,hB,hv⟩:=ih
        let B' : Fin (m+1) → Set (Space d) := Fin.lastCases ∅ B
        have hp : IsPartition B' := append_empty_partition (A := B) hB
        have he : value B' = value B := append_empty_value B
        exact ⟨B',hp,he.trans hv⟩
    exact hc 3 hk
  obtain ⟨B,hB,hv⟩:=he
  rw [←hv]
  exact three_partition_bound hB

end GaussianPropeller.Reduction

end OAI
