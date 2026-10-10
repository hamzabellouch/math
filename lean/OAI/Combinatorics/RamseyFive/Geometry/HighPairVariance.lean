import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.SubsetMixture
import OAI.Combinatorics.RamseyFive.Marking.State
import OAI.Combinatorics.RamseyFive.Entropy.WeightedLowHits

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma relationMass_good_incident (p : Law (ℙ K V)) (r : Law (ℙ K (Dual K V)))
    (G : Finset (ℙ K V)) (H : Finset (ℙ K (Dual K V))) :
    relationMass (fun a b=>a∈G ∧ b∈H ∧ Incident a b) p r =
      ∑ b∈H,r b*weightOnHyperplane (fun a=>if a∈G then p a else 0) b := by
  rw [relationMass_by_target]
  have he : (∑ b∈H,r b*weightOnHyperplane (fun a=>if a∈G then p a else 0) b)=
      ∑ b,if b∈H then r b*weightOnHyperplane (fun a=>if a∈G then p a else 0) b else 0 := by
    simp only [Finset.sum_ite_mem,Finset.univ_inter]
  rw [he]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_filter]
  by_cases hb : b∈H
  · simp only [hb,true_and,ite_true,weightOnHyperplane,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a∈G <;> by_cases hi : Incident a b <;>
      simp only [ha,hi,incidenceEntry,ite_true,ite_false,and_true,and_false,
        one_mul,zero_mul,mul_zero]
  · simp only [hb,and_false,false_and,ite_false,Finset.sum_const_zero,mul_zero]

theorem high_pair_incident_lower (hdim : finrank K V=5)
    (p : Law (ℙ K V)) (r : Law (ℙ K (Dual K V)))
    (G : Finset (ℙ K V)) (H : Finset (ℙ K (Dual K V))) (A B : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hp : ∀ a∈G,p a≤A) (hr : ∀ b∈H,r b≤B)
    (hG : (3:ℝ)/4≤eventMass p G) (hH : (3:ℝ)/4≤eventMass r H)
    (hsmall : 64*(Nat.card K:ℝ)^5*A*B≤(1:ℝ)/4) :
    1/(8*(Nat.card K:ℝ))≤relationMass (fun a b=>a∈G ∧ b∈H ∧ Incident a b) p r := by
  let w : ℙ K V→ℝ:=fun a=>if a∈G then p a else 0
  have hw : ∀ a,0≤w a ∧ w a≤A := by
    intro a
    dsimp [w]
    split_ifs with ha
    · exact ⟨p.nonneg a,hp a ha⟩
    · exact ⟨le_rfl,hA⟩
  have hm : (∑ a,w a)=eventMass p G := by simp [w,eventMass,Finset.sum_ite_mem]
  have hlow := lowHits_mass hdim w r H A B hA hB hw (hm ▸ hG)
    (hm ▸ eventMass_le_one p G) hr
  have hpart : eventMass r (H\lowHits w)+eventMass r (H∩lowHits w)=eventMass r H := by
    unfold eventMass
    exact by
      rw [←Finset.sum_union (Finset.disjoint_sdiff_inter H (lowHits w)),
        Finset.sdiff_union_inter]
  have hmass : (1:ℝ)/2≤eventMass r (H\lowHits w) := by linarith
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hn : ∀ b,0≤weightOnHyperplane w b := by
    intro b
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (by unfold incidenceEntry;split_ifs <;> norm_num) (hw a).1
  rw [relationMass_good_incident]
  calc
    _ = ((1:ℝ)/2)*(1/(4*(Nat.card K:ℝ))) := by ring
    _ ≤ eventMass r (H\lowHits w)*(1/(4*(Nat.card K:ℝ))) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = ∑ b∈H\lowHits w,r b*(1/(4*(Nat.card K:ℝ))) := by unfold eventMass; rw [Finset.sum_mul]
    _ ≤ ∑ b∈H\lowHits w,r b*weightOnHyperplane w b := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_left _ (r.nonneg b)
      have hh := (Finset.mem_sdiff.mp hb).2
      have he : ¬weightOnHyperplane w b<1/(4*(Nat.card K:ℝ)) := by
        intro he
        exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
      exact le_of_not_gt he
    _ ≤ ∑ b∈H,r b*weightOnHyperplane w b :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun b _ _=>mul_nonneg (r.nonneg b) (hn b))
end
end SharpRamseyFive.ProjectiveIncidence

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev SampleFlag := ℙ K V × ℙ K (Dual K V)

def growSpan {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) : Submodule K (Dual K V) :=
  W ⊔ Marking.state (fun i=>(x i).1) (fun i=>(x i).2) Finset.univ y

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma le_growSpan {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) : W≤growSpan y W x := le_sup_left

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma hit_le_growSpan {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) (i : Fin n) (hi : Incident (x i).1 y) :
    (x i).2.submodule≤growSpan y W x := by
  apply le_trans _ le_sup_right
  unfold Marking.state
  exact le_iSup_of_le i (le_iSup_of_le (Finset.mem_univ i) (by rw [ite_eq_left hi]))

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma rank_growSpan_mono {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) : finrank K W≤finrank K (growSpan y W x) :=
  Submodule.finrank_mono (le_growSpan y W x)

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma growSpan_eq_of_rank_le {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) (hr : finrank K (growSpan y W x)≤finrank K W) :
    growSpan y W x=W := by
  exact (Submodule.eq_of_le_of_finrank_eq (le_growSpan y W x)
    (Nat.le_antisymm (rank_growSpan_mono y W x) hr)).symm

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma small_subspace_card (W : Submodule K (Dual K V)) (hr : finrank K W<4) :
    ((Finset.univ.filter fun b : ℙ K (Dual K V)=>b.submodule≤W).card:ℝ)≤
      2*(Nat.card K:ℝ)^2 := by
  rw [Marking.subspace_finset_card,Nat.cast_sum]
  simp only [Nat.cast_pow]
  have hle : (∑ i∈Finset.range (finrank K W),(Nat.card K:ℝ)^i)≤
      ∑ i∈Finset.range 3,(Nat.card K:ℝ)^i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro i _ _
    positivity
  apply hle.trans
  have hq : 2≤(Nat.card K:ℝ) := by exact_mod_cast Finite.one_lt_card (α:=K)
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,zero_add]
  nlinarith

def newHits (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V)) :
    Finset (SampleFlag (K:=K) (V:=V)) :=
  Finset.univ.filter fun z=>Incident z.1 y ∧ ¬z.2.submodule≤W

omit [Finite K] [FiniteDimensional K V] in
lemma first_incident_mass (p : Law (SampleFlag (K:=K) (V:=V))) (y : ℙ K (Dual K V)) :
    eventMass p (Finset.univ.filter fun z=>Incident z.1 y)=weightOnHyperplane (first p) y := by
  simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,
    weightOnHyperplane,incidenceEntry,first]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · simp only [one_mul]
  · simp only [Finset.sum_const_zero,zero_mul]

omit [FiniteDimensional K V] in
lemma second_subspace_mass (p : Law (SampleFlag (K:=K) (V:=V)))
    (W : Submodule K (Dual K V)) (B : ℝ) (hr : finrank K W<4) (hB : 0≤B)
    (hp : ∀ b,second p b≤B) :
    eventMass p (Finset.univ.filter fun z=>z.2.submodule≤W)≤2*(Nat.card K:ℝ)^2*B := by
  have he : eventMass p (Finset.univ.filter fun z=>z.2.submodule≤W)=
      ∑ b∈Finset.univ.filter (fun b=>b.submodule≤W),second p b := by
    simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,second]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp only [Finset.sum_const_zero]
  rw [he]
  calc
    _ ≤ ∑ _b∈Finset.univ.filter (fun b : ℙ K (Dual K V)=>b.submodule≤W),B :=
      Finset.sum_le_sum fun b _=>hp b
    _ = ((Finset.univ.filter fun b : ℙ K (Dual K V)=>b.submodule≤W).card:ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (small_subspace_card W hr) hB

omit [FiniteDimensional K V] in
theorem newHits_mass (p : Law (SampleFlag (K:=K) (V:=V)))
    (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V)) (B : ℝ)
    (hr : finrank K W<4) (hB : 0≤B) (hp : ∀ b,second p b≤B)
    (hy : y∉lowHits (first p)) (hsmall : 2*(Nat.card K:ℝ)^2*B≤1/(20*(Nat.card K:ℝ))) :
    1/(5*(Nat.card K:ℝ))≤eventMass p (newHits y W) := by
  have hhit : 1/(4*(Nat.card K:ℝ))≤weightOnHyperplane (first p) y := by
    exact le_of_not_gt fun h=>hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hsub := second_subspace_mass p W B hr hB hp
  have hpart : eventMass p (Finset.univ.filter fun z=>Incident z.1 y)≤
      eventMass p (newHits y W)+eventMass p (Finset.univ.filter fun z=>z.2.submodule≤W) := by
    simp only [eventMass,newHits,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    by_cases hh : Incident z.1 y <;> by_cases hw : z.2.submodule≤W <;>
      simp only [hh,hw,not_true_eq_false,not_false_eq_true,and_self,and_false,
        and_true,ite_true,ite_false,zero_add,add_zero,le_refl]
    exact p.nonneg z
  rw [first_incident_mass] at hpart
  have he : 1/(4*(Nat.card K:ℝ))-1/(20*(Nat.card K:ℝ))=1/(5*(Nat.card K:ℝ)) := by ring
  linarith
end
end SharpRamseyFive.HighSamples

end OAI
