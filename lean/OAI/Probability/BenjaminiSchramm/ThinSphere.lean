import OAI.Probability.BenjaminiSchramm.IntrinsicSphere

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_thin_intrinsicSphere (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (r k : ℕ) (hf : (cluster G ω x).Finite)
    (hsmall : (cluster G ω x).ncard < (r+1)*(k+1)) :
    ∃ j ∈ Finset.Icc r (2*r), (intrinsicSphere G ω x j).ncard ≤ k := by
  by_contra hnot
  push Not at hnot
  let F : ℕ → Finset V := fun j => (intrinsicSphere_finite G hloc ω x j).toFinset
  have hdisj : (↑(Finset.Icc r (2*r)) : Set ℕ).PairwiseDisjoint F := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro y hi hj
    exact Set.disjoint_left.mp (intrinsicSphere_disjoint G ω x hij)
      ((intrinsicSphere_finite G hloc ω x i).mem_toFinset.mp hi)
      ((intrinsicSphere_finite G hloc ω x j).mem_toFinset.mp hj)
  have hsub : (Finset.Icc r (2*r)).biUnion F ⊆ hf.toFinset := by
    intro y hy
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hy
    exact hf.mem_toFinset.mpr ((intrinsicSphere_finite G hloc ω x j).mem_toFinset.mp hj).1
  have hcards := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcards
  have hlo : (r+1)*(k+1) ≤ ∑ j ∈ Finset.Icc r (2*r), (F j).card := by
    calc
      _ = ∑ j ∈ Finset.Icc r (2*r), (k+1) := by
        rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.card_Icc]
        have he : 2*r+1-r = r+1 := by omega
        rw [he]
      _ ≤ _ := Finset.sum_le_sum (fun j hj => by
        have h := hnot j hj
        change k < (intrinsicSphere G ω x j).ncard at h
        rw [Set.ncard_eq_toFinset_card _ (intrinsicSphere_finite G hloc ω x j)] at h
        exact h)
  have he : hf.toFinset.card = (cluster G ω x).ncard := (Set.ncard_eq_toFinset_card _ hf).symm
  rw [he] at hcards
  omega

def thinSphereCell (G : BondGraph V E) (S : Set E) (x : V) (r k j : ℕ)
    (U W : Finset V) : Set (Set E) :=
  {ω | r ≤ j ∧ j ≤ 2*r ∧ intrinsicBall G (ω ∩ S) x (j-1) = U ∧
    intrinsicBall G (ω ∩ S) x j = W ∧
    (intrinsicSphere G (ω ∩ S) x j).ncard ≤ k ∧
    ∀ i, r ≤ i → i < j → k < (intrinsicSphere G (ω ∩ S) x i).ncard}

theorem thinSphereCell_pairwise (G : BondGraph V E) (S : Set E) (x : V) (r k : ℕ) :
    Pairwise (fun a b : ℕ × Finset V × Finset V =>
      Disjoint (thinSphereCell G S x r k a.1 a.2.1 a.2.2)
        (thinSphereCell G S x r k b.1 b.2.1 b.2.2)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro ω ha hb
  have hj : a.1 = b.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (not_lt_of_ge ha.2.2.2.2.1) (hb.2.2.2.2.2 a.1 ha.1 h)
    · exact (not_lt_of_ge hb.2.2.2.2.1) (ha.2.2.2.2.2 b.1 hb.1 h)
  have hU : a.2.1 = b.2.1 := by
    apply Finset.coe_injective
    have haU : intrinsicBall G (ω ∩ S) x (b.1-1) = (a.2.1 : Set V) := by
      simpa only [hj] using ha.2.2.1
    exact haU.symm.trans hb.2.2.1
  have hW : a.2.2 = b.2.2 := by
    apply Finset.coe_injective
    have haW : intrinsicBall G (ω ∩ S) x b.1 = (a.2.2 : Set V) := by
      simpa only [hj] using ha.2.2.2.1
    exact haW.symm.trans hb.2.2.2.1
  exact hab (Prod.ext hj (Prod.ext hU hW))

end Percolation.BenjaminiSchramm

end OAI
