import OAI.MeasureTheory.Falconer.Angular.InverseAngularSymbol
import OAI.MeasureTheory.Falconer.Geometry.SeededSeparation
import OAI.MeasureTheory.Falconer.Angular.FactorizedAngularState

namespace OAI

/-! # The actual inverse step on factorized descriptor symbols

An endpoint is labelled by one angular multiplier and its original finite
set of descriptors. The seed retains every old jet order. A new inverse
adds at most `2*j` to each endpoint's descriptor budget.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

abbrev DescriptorInverseLabel (F : Finset PolicyDescriptor) := Unit ⊕ {b // b ∈ F}

noncomputable def descriptorInverseSeed {m KL KR L : ℕ} {F G : Finset PolicyDescriptor}
    {D : ℝ} (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) :
    DescriptorInverseLabel F ⊕ DescriptorInverseLabel G → MaskJetIndex (m+3) :=
  Sum.elim (Sum.elim (fun _ => MaskJetIndex.zero (m+3)) (fun b => f.jet b))
    (Sum.elim (fun _ => MaskJetIndex.zero (m+3)) (fun b => g.jet b))

namespace MaskJetExpansion
variable {ι τ : Type} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem seed_inverse_single_order (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (a : ((seed k).inverse m j).index) (i : ι) :
    ((((seed k).inverse m j).term a).jet i).order ≤ (k i).order+2*j := by
  have hbase := (seed_ordersExtend k).inverse j a i
  have hsingle : ((((seed k).inverse m j).term a).jet i).order-(k i).order ≤
      ∑ t, (((((seed k).inverse m j).term a).jet t).order-(k t).order) :=
    Finset.single_le_sum
      (f := fun t => ((((seed k).inverse m j).term a).jet t).order-(k t).order)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have htotal := seed_inverse_added_order m j k a
  omega

theorem seed_inverse_left_order (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (a : ((seed k).inverse m j).index) :
    (∑ i, ((((seed k).inverse m j).term a).jet (.inl i)).order) ≤
      (∑ i, (k (.inl i)).order)+2*j := by
  have htotal := seededJetSeparation_added_order m j k a
  change
    (∑ i, (((((seed k).inverse m j).term a).jet (.inl i)).order-(k (.inl i)).order)) +
      (∑ i, (((((seed k).inverse m j).term a).jet (.inr i)).order-(k (.inr i)).order)) ≤ 2*j
    at htotal
  have hsum :
      (∑ i, (((((seed k).inverse m j).term a).jet (.inl i)).order-(k (.inl i)).order)) +
        (∑ i, (k (.inl i)).order) =
        ∑ i, ((((seed k).inverse m j).term a).jet (.inl i)).order := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel ((seed_ordersExtend k).inverse j a (.inl i))
  omega

end MaskJetExpansion

namespace DescriptorJetSymbol
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

noncomputable def inverseLeftJets (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) :
    PolicyDescriptor → MaskJetIndex (m+3) :=
  fun b => if hb : b ∈ F then
    (((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
      (.inl (.inr ⟨b,hb⟩)) else MaskJetIndex.zero (m+3)

theorem inverseLeftJets_order (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) :
    (∑ b ∈ F, (f.inverseLeftJets g j a b).order) ≤ KL+2*j := by
  let k := descriptorInverseSeed f g
  let T := (MaskJetExpansion.seed k).inverse m j
  have hleft := MaskJetExpansion.seed_inverse_left_order m j k a
  have hinitial : (∑ i : DescriptorInverseLabel F, (k (.inl i)).order) =
      ∑ b ∈ F, (f.jet b).order := by
    rw [Fintype.sum_sum_type]
    simp only [k,descriptorInverseSeed,Sum.elim_inl,Sum.elim_inr,MaskJetIndex.zero,
      Fintype.sum_unique,zero_add]
    exact Finset.sum_coe_sort F (fun b => (f.jet b).order)
  have hout : (∑ b ∈ F, (f.inverseLeftJets g j a b).order) =
      ∑ b : {b // b ∈ F}, ((T.term a).jet (.inl (.inr b))).order := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    simp only [inverseLeftJets,dite_eq_left b.property]
    rfl
  rw [hinitial] at hleft
  rw [hout]
  have hpartial : (∑ b : {b // b ∈ F}, ((T.term a).jet (.inl (.inr b))).order) ≤
      ∑ i : DescriptorInverseLabel F, ((T.term a).jet (.inl i)).order := by
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_unique]
    omega
  exact hpartial.trans (hleft.trans (Nat.add_le_add_right f.order_le (2*j)))

end DescriptorJetSymbol
end Falconer

end OAI
