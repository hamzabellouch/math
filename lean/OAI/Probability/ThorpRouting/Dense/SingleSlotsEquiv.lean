import Mathlib
import OAI.Probability.ThorpRouting.Dense.PalindromeFamilyCost

namespace OAI

namespace ThorpNine.Dense

open scoped BigOperators
namespace Thorp.RoutingNetwork
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def singleSlotsEquiv (p : Equiv.Perm α) (S : Finset α) (r : ℕ) :
    CycleSlots p S (fun _ : Fin 1 => r) ≃
      {C : SelectedCycle p S // C.val.card = r+1} :=
  (cycleSlotsEquivAssignments p S (fun _ : Fin 1 => r)).trans
  { toFun := fun a => ⟨a.val 0, a.property.2 0⟩
    invFun := fun C => ⟨fun _ => C.val, Function.injective_of_subsingleton _, fun _ => C.property⟩
    left_inv := fun a => by
      apply Subtype.ext
      funext i
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      rfl
    right_inv := fun C => rfl }

noncomputable def cycleCount (p : Equiv.Perm α) (S : Finset α) (r : ℕ) : ℝ :=
  Fintype.card {C : SelectedCycle p S // C.val.card = r+1}

lemma cycleCount_eq_sum (p : Equiv.Perm α) (S : Finset α) (r : ℕ) :
    cycleCount p S r = ∑ C : SelectedCycle p S, if C.val.card=r+1 then (1:ℝ) else 0 := by
  classical
  simp only [cycleCount, Fintype.card_subtype, Finset.sum_boole]

lemma hasSum_cycleCount_weight (p : Equiv.Perm α) (S : Finset α) (f : ℕ → ℝ) :
    HasSum (fun l => cycleCount p S l * f (l+1))
      (∑ C : SelectedCycle p S, f C.val.card) := by
  classical
  have h (C : SelectedCycle p S) :
      HasSum (fun l : ℕ => if C.val.card=l+1 then f C.val.card else 0) (f C.val.card) := by
    have hc : 1 ≤ C.val.card := C.nonempty.card_pos
    have hs := hasSum_single (C.val.card-1)
      (f := fun l : ℕ => if C.val.card=l+1 then f C.val.card else 0)
      (fun l hl => ite_eq_right (by omega))
    simpa only [Nat.sub_add_cancel hc, ↓reduceIte] using hs
  convert hasSum_sum (s := Finset.univ) (fun C _ => h C) using 1
  funext l
  rw [cycleCount_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro C _
  split_ifs with hc
  · simp only [one_mul, hc]
  · simp

end Thorp.RoutingNetwork

namespace Thorp
open scoped BigOperators
lemma hasSum_finiteMean {Ω : Type*} [Fintype Ω] {f : Ω → ℕ → ℝ} {a : Ω → ℝ}
    (hf : ∀ ω, HasSum (f ω) (a ω)) :
    HasSum (fun l => finiteMean (fun ω => f ω l)) (finiteMean a) :=
  (hasSum_sum (s := Finset.univ) (fun ω _ => hf ω)).div_const (Fintype.card Ω : ℝ)
end Thorp

namespace Thorp.RoutingNetwork
open scoped BigOperators
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {d : ℕ} (R : RoutingNetwork α ι d)

lemma selected_cycle_mean_le_h (S : Finset α) :
    finiteMean (fun ω : ι → Bool => (Fintype.card (SelectedCycle (R.perm ω) S) : ℝ)) ≤
      (S.card : ℝ) * DenseTruncation.h (d+1) := by
  classical
  by_cases hS : S.Nonempty
  · have hpos : (0:ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
    let w : ℕ → ℝ := fun l => finiteMean (fun ω : ι → Bool => cycleCount (R.perm ω) S l)
    have hw : ∀ l, 0 ≤ w l := fun _ => finiteMean_nonneg (fun _ => Nat.cast_nonneg _)
    have hc (l : ℕ) : w l ≤ (S.card : ℝ) / (2:ℝ)^d := by
      apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^d)).mpr
      have he (ω : ι → Bool) : cycleCount (R.perm ω) S l =
          (Fintype.card (CycleSlots (R.perm ω) S (fun _ : Fin 1 => l)) : ℝ) := by
        rw [cycleCount, Fintype.card_congr (singleSlotsEquiv (R.perm ω) S l)]
      simpa only [w,he] using single_cycleSlots_weighted_moment R S l
    have hmass := hasSum_finiteMean (fun ω : ι → Bool =>
      hasSum_cycleCount_weight (R.perm ω) S (fun n => (n:ℝ)))
    have hm : HasSum (fun l => ((l+1 : ℕ) : ℝ) * w l)
        (finiteMean (fun ω : ι → Bool => (cycleMass (R.perm ω) S : ℝ))) := by
      simp only [finiteMean_mul_const] at hmass
      simpa only [w, mul_comm, cycleMass,Nat.cast_sum] using hmass
    have hmt : finiteMean (fun ω : ι → Bool => (cycleMass (R.perm ω) S : ℝ)) ≤ S.card := by
      calc
        _ ≤ finiteMean (fun _ : ι → Bool => (S.card : ℝ)) :=
          finiteMean_mono (fun ω => by exact_mod_cast cycleMass_le (R.perm ω) S)
        _ = _ := finiteMean_const _
    let q : ℕ → ℝ := fun l => ((l+1 : ℕ) : ℝ) * w l / S.card
    have hq : ∀ l, 0 ≤ q l := fun l => div_nonneg (mul_nonneg (by positivity) (hw l)) hpos.le
    have hqs : Summable q := (hm.div_const (S.card : ℝ)).summable
    have hqt : (∑' l, q l) ≤ 1 := by
      rw [(hm.div_const (S.card : ℝ)).tsum_eq]
      exact (div_le_one hpos).mpr hmt
    have hqc (l : ℕ) : q l ≤ ((l+1 : ℕ) : ℝ) / (2:ℝ)^((d+1)-1) := by
      simp only [Nat.add_sub_cancel]
      dsimp [q]
      calc
        _ ≤ (((l+1 : ℕ) : ℝ) * ((S.card : ℝ) / (2:ℝ)^d)) / S.card := by
          gcongr
          exact hc l
        _ = _ := by field_simp
    have hh := DenseTruncation.subprob_reciprocal_le_h hq hqs hqt hqc
    have hcount := hasSum_finiteMean (fun ω : ι → Bool =>
      hasSum_cycleCount_weight (R.perm ω) S (fun _ => (1:ℝ)))
    have hwc : HasSum w (finiteMean (fun ω : ι → Bool =>
        (Fintype.card (SelectedCycle (R.perm ω) S) : ℝ))) := by
      simpa only [mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using hcount
    have he (l : ℕ) : q l / ((l+1 : ℕ) : ℝ) = w l / S.card := by
      have hl : ((l+1 : ℕ) : ℝ) ≠ 0 := by positivity
      dsimp [q]
      field_simp
    simp only [he, (hwc.div_const (S.card : ℝ)).tsum_eq] at hh
    simpa only [mul_comm] using (div_le_iff₀ hpos).mp hh
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    have hz (ω : ι → Bool) : Fintype.card (SelectedCycle (R.perm ω) ∅) = 0 := by
      let : IsEmpty (SelectedCycle (R.perm ω) ∅) :=
        ⟨fun C => C.nonempty.ne_empty (Finset.subset_empty.mp C.property.2)⟩
      exact Fintype.card_eq_zero
    simp only [hz,Nat.cast_zero,finiteMean_const,Finset.card_empty,zero_mul,le_refl]

end Thorp.RoutingNetwork

namespace Thorp.DenseTruncation
open scoped BigOperators

lemma reciprocal_values_nonempty (j : ℕ) :
    {z : ℝ | ∃ p : ℕ → ℝ, AdmissibleCycleLaw j p ∧
      z = ∑' l : ℕ, p l / ((l+1 : ℕ) : ℝ)}.Nonempty := by
  let t := 2^(j-1)-1
  have ht : t+1 = 2^(j-1) := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))
  let p : ℕ → ℝ := fun l => if l=t then 1 else 0
  have hp : AdmissibleCycleLaw j p := by
    refine ⟨fun l => by dsimp [p]; split_ifs <;> norm_num, hasSum_ite_eq t 1, ?_⟩
    intro l
    by_cases hl : l=t
    · subst l
      have he : ((t+1 : ℕ) : ℝ) = (2:ℝ)^(j-1) := by rw [ht]; norm_cast
      simp only [p,↓reduceIte,he,div_self (by positivity : (2:ℝ)^(j-1) ≠ 0),le_refl]
    · simp only [p,ite_eq_right hl]
      positivity
  exact ⟨_,p,hp,rfl⟩

lemma h_nonneg (j : ℕ) : 0 ≤ h j := by
  obtain ⟨z,p,hp,rfl⟩ := reciprocal_values_nonempty j
  exact (law_reciprocal_nonneg hp).trans (reciprocal_le_h hp)

lemma h_le_one (j : ℕ) : h j ≤ 1 :=
  csSup_le (reciprocal_values_nonempty j) (fun _ ⟨_,hp,hz⟩ => hz ▸ law_reciprocal_le_one hp)

lemma law_reciprocal_cutoff {j : ℕ} {p : ℕ → ℝ} (hp : AdmissibleCycleLaw j p)
    (L : ℕ) (hL : 0 < L) :
    (∑' l, p l / ((l+1 : ℕ) : ℝ)) ≤ (L : ℝ)/(2:ℝ)^(j-1) + 1/L := by
  let a : ℕ → ℝ := fun l => if l<L then 1/(2:ℝ)^(j-1) else 0
  have ha : HasSum a ((L : ℝ)/(2:ℝ)^(j-1)) := by
    have hs : HasSum a (∑ l ∈ Finset.range L, a l) :=
      hasSum_sum_of_ne_finset_zero (s := Finset.range L) (f := a)
      (fun l hl => by simpa only [a,Finset.mem_range] using ite_eq_right (show ¬l<L from fun hh => hl (Finset.mem_range.mpr hh)))
    simpa only [a,Finset.sum_ite_of_true (fun l hl => Finset.mem_range.mp hl),
      Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one_div] using hs
  have hb := hp.2.1.div_const (L:ℝ)
  have he (l : ℕ) : p l / ((l+1 : ℕ) : ℝ) ≤ a l + p l/L := by
    by_cases hl : l<L
    · have hc : p l / ((l+1 : ℕ) : ℝ) ≤ 1/(2:ℝ)^(j-1) := by
        have hp1 := hp.2.2 l
        have hlpos : (0:ℝ) < (l+1 : ℕ) := by positivity
        apply (div_le_iff₀ hlpos).mpr
        simpa only [one_div, div_eq_mul_inv,mul_comm,one_mul] using hp1
      dsimp [a]
      rw [ite_eq_left hl]
      exact hc.trans (le_add_of_nonneg_right (div_nonneg (hp.1 l) (by positivity)))
    · dsimp [a]
      rw [ite_eq_right hl,zero_add]
      exact div_le_div_of_nonneg_left (hp.1 l) (by exact_mod_cast hL)
        (by exact_mod_cast (show L ≤ l+1 by omega))
  have hh := Summable.tsum_le_tsum he (law_reciprocal_summable hp) (ha.add hb).summable
  rwa [(ha.add hb).tsum_eq] at hh

lemma h_cutoff (j L : ℕ) (hL : 0 < L) :
    h j ≤ (L : ℝ)/(2:ℝ)^(j-1) + 1/L :=
  csSup_le (reciprocal_values_nonempty j)
    (fun _ ⟨_,hp,hz⟩ => hz ▸ law_reciprocal_cutoff hp L hL)

lemma h_dyadic_bound (j : ℕ) : h (j+1) ≤ 2/(2:ℝ)^(j/2) := by
  have h := h_cutoff (j+1) (2^(j/2)) (by positivity)
  simp only [Nat.add_sub_cancel,Nat.cast_pow,Nat.cast_ofNat] at h
  have hpow : ((2:ℝ)^(j/2))^2 ≤ (2:ℝ)^j := by
    rw [←pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hp : (0:ℝ) < (2:ℝ)^(j/2) := by positivity
  have hq : (0:ℝ) < (2:ℝ)^j := by positivity
  have hr : (2:ℝ)^(j/2)/(2:ℝ)^j ≤ 1/(2:ℝ)^(j/2) := by
    apply (div_le_div_iff₀ hq hp).mpr
    nlinarith
  calc
    _ ≤ 1/(2:ℝ)^(j/2) + 1/(2:ℝ)^(j/2) := h.trans (by linarith)
    _ = _ := by ring

lemma summable_half_dyadic : Summable (fun j : ℕ => 2/(2:ℝ)^(j/2)) := by
  apply ((Nat.divModEquiv 2).symm.summable_iff).mp
  have he (p : ℕ × Fin 2) : 2/(2:ℝ)^(((Nat.divModEquiv 2).symm p)/2) =
      2*(1/2:ℝ)^p.1 := by
    rw [Nat.divModEquiv_symm_apply]
    have hi : (p.1*2+p.2.val)/2 = p.1 := by omega
    rw [hi,div_pow,one_pow]
    ring
  simp only [Function.comp_def,he]
  apply (summable_prod_of_nonneg (fun p => by positivity)).mpr
  constructor
  · intro n
    exact (hasSum_fintype _).summable
  · simpa only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_ofNat,←mul_assoc,show (2:ℝ)*2=4 from by norm_num] using summable_geometric_two.mul_left 4

lemma h_summable : Summable (fun j => h (j+1)) :=
  Summable.of_nonneg_of_le (fun j => h_nonneg (j+1)) h_dyadic_bound summable_half_dyadic

lemma allocation_value_summable {ρ : ℝ} {x : ℕ → ℝ} (hx : AdmissibleAllocation ρ x) :
    Summable (fun j => h (j+1)*x j) :=
  Summable.of_nonneg_of_le (fun j => mul_nonneg (h_nonneg _) (hx.1 j).1)
    (fun j => mul_le_of_le_one_right (h_nonneg _) (hx.1 j).2) h_summable

lemma H_values_bdd (ρ : ℝ) : BddAbove {z : ℝ | ∃ x : ℕ → ℝ,
    AdmissibleAllocation ρ x ∧ z = (1/2:ℝ)*∑' j, h (j+1)*x j} := by
  refine ⟨(1/2:ℝ)*∑' j, h (j+1), ?_⟩
  rintro z ⟨x,hx,rfl⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Summable.tsum_le_tsum (fun j => mul_le_of_le_one_right (h_nonneg _) (hx.1 j).2)
    (allocation_value_summable hx) h_summable

lemma allocation_le_H {ρ : ℝ} {x : ℕ → ℝ} (hx : AdmissibleAllocation ρ x) :
    (1/2:ℝ)*∑' j, h (j+1)*x j ≤ H ρ :=
  le_csSup (H_values_bdd ρ) ⟨x,hx,rfl⟩

end Thorp.DenseTruncation

namespace Thorp
open scoped BigOperators

def unitCardEquiv (d : ℕ) : Card d ≃ Unit × Card d where
  toFun x := ((),x)
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by cases x with | mk u x => cases u; rfl

def unitBitsEquiv (d : ℕ) : (Unit × SwitchIndex d → Bool) ≃ (SwitchIndex d → Bool) where
  toFun ω i := ω ((),i)
  invFun ω i := ω i.2
  left_inv ω := by funext i; rcases i with ⟨u,i⟩; cases u; rfl
  right_inv _ := rfl

lemma relabeled_single_cycle_mean (d : ℕ) (pre post : Equiv.Perm (Card d))
    (S : Finset (Card d)) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      (Fintype.card (RoutingNetwork.SelectedCycle
        (post * butterflyPerm d (decodeButterfly d ω) * pre) S) : ℝ)) ≤
      (S.card : ℝ)*DenseTruncation.h (d+1) := by
  have hh := RoutingNetwork.selected_cycle_mean_le_h
    (parallelNetwork (pre.trans (unitCardEquiv d)) ((unitCardEquiv d).symm.trans post)) S
  rw [finiteMean_equiv (unitBitsEquiv d)] at hh
  exact hh

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def projectSharedCycle (p : Equiv.Perm α) (A B : Finset α)
    (C : RoutingNetwork.SelectedCycle (alternatingPerm p) (childJoin A B)) :
    RoutingNetwork.SelectedCycle p (A ∩ B) := by
  refine ⟨(projectCycle p A B C).val, (projectCycle p A B C).property.1, ?_⟩
  intro x hx
  apply Finset.mem_inter.mpr
  refine ⟨(projectCycle p A B C).property.2 hx, ?_⟩
  have he := selected_alternating_eq p A B C
  have hc : (true,x) ∈ C.val := by
    rw [he]
    exact (mem_childJoin _ _ true x).mpr hx
  exact (mem_childJoin A B true x).mp (C.property.2 hc)

lemma projectSharedCycle_injective (p : Equiv.Perm α) (A B : Finset α) :
    Function.Injective (projectSharedCycle p A B) := by
  intro C D h
  apply projectCycle_injective p A B
  apply Subtype.ext
  change (projectSharedCycle p A B C).val = (projectSharedCycle p A B D).val
  exact congrArg Subtype.val h

lemma card_alternating_cycles_le_shared (p : Equiv.Perm α) (A B : Finset α) :
    Fintype.card (RoutingNetwork.SelectedCycle (alternatingPerm p) (childJoin A B)) ≤
      Fintype.card (RoutingNetwork.SelectedCycle p (A ∩ B)) :=
  Fintype.card_le_of_injective _ (projectSharedCycle_injective p A B)

end CycleColoring

namespace PairRouting
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable def sharedPairs (e : ι ↪ Bool × α) : Finset α :=
  boolFiber (labelSet e) false ∩ boolFiber (labelSet e) true

lemma alternatingCycles_le_sharedSelected (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    alternatingCycles e p ≤
      Fintype.card (RoutingNetwork.SelectedCycle (alternatingProjection p) (sharedPairs e)) := by
  unfold alternatingCycles sharedPairs
  conv_lhs => rw [←childJoin_boolFiber (labelSet e)]
  exact CycleColoring.card_alternating_cycles_le_shared _ _ _

omit [Fintype α] in
lemma sharedPairs_card_twice_le (e : ι ↪ Bool × α) :
    2*(sharedPairs e).card ≤ Fintype.card ι := by
  have he := card_childJoin (boolFiber (labelSet e) false) (boolFiber (labelSet e) true)
  rw [childJoin_boolFiber,card_labelSet] at he
  have h₀ := Finset.card_le_card (Finset.inter_subset_left : sharedPairs e ⊆ boolFiber (labelSet e) false)
  have h₁ := Finset.card_le_card (Finset.inter_subset_right : sharedPairs e ⊆ boolFiber (labelSet e) true)
  simp only [sharedPairs] at *
  omega

omit [Fintype α] in
lemma labelSet_switched (e : ι ↪ Bool × α) (ξ : α → Bool) :
    labelSet (switchedEmbedding e ξ) = (labelSet e).image (pairLayer ξ) := by
  classical
  simp only [labelSet,Finset.image_image,switchedEmbedding]
  rfl

omit [Fintype α] in
lemma sharedPairs_switched (e : ι ↪ Bool × α) (ξ : α → Bool) :
    sharedPairs (switchedEmbedding e ξ) = sharedPairs e := by
  classical
  ext x
  simp only [sharedPairs,Finset.mem_inter,mem_boolFiber,labelSet_switched,mem_image_perm_iff]
  change (Bool.xor false (ξ x),x) ∈ labelSet e ∧
      (Bool.xor true (ξ x),x) ∈ labelSet e ↔
      (false,x) ∈ labelSet e ∧ (true,x) ∈ labelSet e
  cases ξ x <;> simp only [Bool.xor_false,Bool.xor_true,Bool.not_false,Bool.not_true,and_comm]

lemma node_cycle_mean (d : ℕ) (e : ι ↪ Bool × Card d) :
    finiteMean (fun c : BenesCoins d × BenesCoins d =>
      (alternatingCycles e (fun b => palindromePerm d (if b then c.2 else c.1)) : ℝ)) ≤
        (sharedPairs e).card * DenseTruncation.h (d+1) := by
  classical
  rw [finiteMean_prod]
  have hone (c₀ : BenesCoins d) :
      finiteMean (fun c₁ : BenesCoins d =>
        (alternatingCycles e (fun b => palindromePerm d (if b then c₁ else c₀)) : ℝ)) ≤
          (sharedPairs e).card * DenseTruncation.h (d+1) := by
    rw [finiteMean_prod,finiteMean_comm]
    have hf (X : SwitchIndex d → Bool) :
        finiteMean (fun Y : SwitchIndex d → Bool =>
          (alternatingCycles e (fun b => palindromePerm d (if b then (Y,X) else c₀)) : ℝ)) ≤
          (sharedPairs e).card * DenseTruncation.h (d+1) := by
      calc
        _ ≤ finiteMean (fun Y : SwitchIndex d → Bool =>
            (Fintype.card (RoutingNetwork.SelectedCycle
              ((palindromePerm d c₀).symm * butterflyPerm d (decodeButterfly d Y) *
                (butterflyPerm d (decodeButterfly d X)).symm) (sharedPairs e)) : ℝ)) := by
          apply finiteMean_mono
          intro Y
          have hh := alternatingCycles_le_sharedSelected e
            (fun b => palindromePerm d (if b then (Y,X) else c₀))
          simpa only [alternatingProjection,Bool.false_eq_true,↓reduceIte,palindromePerm,mul_assoc] using
            (Nat.cast_le.mpr hh : (alternatingCycles e _ : ℝ) ≤ _)
        _ ≤ _ := relabeled_single_cycle_mean d _ _ _
    calc
      _ ≤ finiteMean (fun _ : SwitchIndex d → Bool =>
          (sharedPairs e).card * DenseTruncation.h (d+1)) := finiteMean_mono hf
      _ = _ := finiteMean_const _
  calc
    _ ≤ finiteMean (fun _ : BenesCoins d => (sharedPairs e).card * DenseTruncation.h (d+1)) :=
      finiteMean_mono hone
    _ = _ := finiteMean_const _

end PairRouting
end Thorp

namespace Thorp

lemma exp_secant {M x t : ℝ} (hM : 0 < M) (hx : 0 ≤ x) (hxM : x ≤ M) :
    Real.exp (t*x) ≤ 1 + x*((Real.exp (t*M)-1)/M) := by
  have hb : 0 ≤ x/M := div_nonneg hx hM.le
  have ha : 0 ≤ 1-x/M := sub_nonneg.mpr ((div_le_one hM).mpr hxM)
  have hh := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (t*M)) ha hb
    (show (1-x/M)+(x/M)=1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hh
  have he : x/M*(t*M) = t*x := by field_simp
  rw [he] at hh
  calc
    _ ≤ 1-x/M+(x/M)*Real.exp (t*M) := hh
    _ = _ := by ring

lemma finiteMean_exp_bounded {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) (M t μ : ℝ) (hM : 0 < M) (ht : 0 ≤ t)
    (hZ : ∀ ω, 0 ≤ Z ω ∧ Z ω ≤ M) (hmean : finiteMean Z ≤ μ) :
    finiteMean (fun ω => Real.exp (t*Z ω)) ≤
      Real.exp (μ*((Real.exp (t*M)-1)/M)) := by
  have hz : 0 ≤ (Real.exp (t*M)-1)/M :=
    div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg ht hM.le))) hM.le
  calc
    _ ≤ finiteMean (fun ω => 1 + Z ω*((Real.exp (t*M)-1)/M)) :=
      finiteMean_mono (fun ω => exp_secant hM (hZ ω).1 (hZ ω).2)
    _ = 1 + finiteMean Z*((Real.exp (t*M)-1)/M) := by
      rw [finiteMean_add,finiteMean_const,finiteMean_mul_const]
    _ ≤ 1 + μ*((Real.exp (t*M)-1)/M) := by gcongr
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (μ*((Real.exp (t*M)-1)/M))

namespace PairRouting
variable {ι : Type*} [Fintype ι]

lemma node_cycle_mgf (d : ℕ) (e : ι ↪ Bool × Card d) (t : ℝ) (ht : 0 ≤ t) :
    finiteMean (fun c : BenesCoins d × BenesCoins d =>
      Real.exp (t * alternatingCycles e
        (fun b => palindromePerm d (if b then c.2 else c.1)))) ≤
      Real.exp ((sharedPairs e).card * DenseTruncation.h (d+1) *
        ((Real.exp (t*(2:ℝ)^d)-1)/(2:ℝ)^d)) := by
  apply finiteMean_exp_bounded _ _ _ _ (by positivity) ht _ (node_cycle_mean d e)
  intro c
  constructor
  · exact Nat.cast_nonneg _
  · have h₀ := alternatingCycles_double e
      (fun b => palindromePerm d (if b then c.2 else c.1))
    have h₁ := Fintype.card_le_of_injective e e.injective
    simp only [Fintype.card_prod,Fintype.card_bool,card_positions] at h₁
    have h₂ : alternatingCycles e (fun b => palindromePerm d (if b then c.2 else c.1)) ≤ 2^d := by omega
    exact_mod_cast h₂

end PairRouting

open scoped BigOperators

lemma shared_pair_mgf {β Ω : Type*} [Fintype β] [DecidableEq β]
    [Fintype Ω] (F : Ω → Finset (Bool × β)) (p : Bool × β → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hc : CylinderBound (inclusionMoment F) p)
    (z : ℝ) (hz : 0 ≤ z) :
    finiteMean (fun ω => Real.exp (z * (boolFiber (F ω) false ∩ boolFiber (F ω) true).card)) ≤
      Real.exp ((Real.exp z - 1) * ∑ b, p (false,b)*p (true,b)) := by
  classical
  let T : β → Bool → Finset (Bool × β) := fun b q =>
    if q then {(false,b),(true,b)} else ∅
  let c : β → Bool → ℝ := fun _ q => if q then Real.exp z - 1 else 1
  have hcz : 0 ≤ Real.exp z - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hz)
  have hdis : ∀ b b', b ≠ b' → ∀ q q', Disjoint (T b q) (T b' q') := by
    intro b b' h q q'
    cases q <;> cases q' <;> simp [T,Finset.disjoint_left,h]
  have hh := cylinder_block_polynomial (fun _ : β => Bool) F p hc T c
    (fun b q => by cases q <;> simp only [c,↓reduceIte] <;> positivity) hdis
  have hsum (A : Finset (Bool × β)) (b : β) :
      (∑ q, c b q * if T b q ⊆ A then 1 else 0) =
        Real.exp (z * if (false,b) ∈ A ∧ (true,b) ∈ A then 1 else 0) := by
    simp only [Fintype.sum_bool,c,T,Bool.false_eq_true,↓reduceIte,Finset.empty_subset,
      mul_one,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    split_ifs <;> simp
  have hcard (A : Finset (Bool × β)) :
      (∑ b : β, if (false,b) ∈ A ∧ (true,b) ∈ A then (1:ℝ) else 0) =
        (boolFiber A false ∩ boolFiber A true).card := by
    rw [Finset.sum_boole]
    congr 2
    ext b
    simp [mem_boolFiber]
  have hleft (ω : Ω) :
      (∏ b, ∑ q, c b q * if T b q ⊆ F ω then 1 else 0) =
        Real.exp (z*(boolFiber (F ω) false ∩ boolFiber (F ω) true).card) := by
    simp_rw [hsum]
    rw [←Real.exp_sum,←Finset.mul_sum,hcard]
  have hright (b : β) :
      (∑ q, c b q * ∏ x ∈ T b q, p x) =
        1+(Real.exp z-1)*(p (false,b)*p (true,b)) := by
    simp [c,T,add_comm]
  simp_rw [hleft,hright] at hh
  refine hh.trans ?_
  rw [Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro b _
    exact add_nonneg (by norm_num) (mul_nonneg hcz (mul_nonneg (hp _) (hp _)))
  · intro b _
    simpa only [add_comm] using Real.add_one_le_exp ((Real.exp z-1)*(p (false,b)*p (true,b)))

end Thorp

namespace Thorp
variable {B : Type*} [Fintype B] [DecidableEq B]

lemma prod_blockMarks (d : ℕ) (S : Finset (B × Card d)) (f : B × Card d → ℝ) :
    (∏ x ∈ S, f x) = ∏ b, ∏ x ∈ blockMarks (Equiv.refl _) S b, f (b,x) := by
  classical
  have hb (b : B) : (∏ x ∈ blockMarks (Equiv.refl _) S b, f (b,x)) =
      ∏ x, if (b,x) ∈ S then f (b,x) else 1 := by
    exact Finset.prod_filter (fun x => (b,x) ∈ S) (fun x => f (b,x))
  simp_rw [hb]
  rw [←Fintype.prod_prod_type (fun x : B × Card d => if x ∈ S then f x else 1)]
  symm
  calc
    _ = ∏ x ∈ Finset.univ.filter (fun x : B × Card d => x ∈ S), f x :=
      (Finset.prod_filter _ _).symm
    _ = _ := by simp

omit [Fintype B] in
lemma subset_parallel_inverse (d : ℕ) (A S : Finset (B × Card d))
    (ω : B × SwitchIndex d → Bool) :
    S ⊆ A.image (parallelPerm ω).symm ↔
      ∀ b, blockMarks (Equiv.refl _) S b ⊆
        inverseButterflyMarks d (blockMarks (Equiv.refl _) A b) (fun i => ω (b,i)) := by
  classical
  constructor
  · intro h b x hx
    have hh := h ((mem_blockMarks (Equiv.refl _) S b x).mp hx)
    rw [mem_image_perm_iff] at hh
    rw [inverseButterflyMarks,mem_image_perm_iff]
    exact (mem_blockMarks (Equiv.refl _) A b _).mpr hh
  · intro h ⟨b,x⟩ hx
    have hh := h b ((mem_blockMarks (Equiv.refl _) S b x).mpr hx)
    rw [inverseButterflyMarks,mem_image_perm_iff] at hh
    rw [mem_image_perm_iff]
    exact (mem_blockMarks (Equiv.refl _) A b _).mp hh

lemma parallel_inverse_cylinder (d : ℕ) (A : Finset (B × Card d)) :
    CylinderBound (inclusionMoment (fun ω : B × SwitchIndex d → Bool =>
      A.image (parallelPerm ω).symm))
      (fun x => (blockMarks (Equiv.refl _) A x.1).card / (2:ℝ)^d) := by
  classical
  intro S
  rw [inclusionMoment_eq,finiteMean_equiv (Equiv.curry B (SwitchIndex d) Bool)]
  have hi (ω : B → SwitchIndex d → Bool) :
      (if S ⊆ A.image (parallelPerm ((Equiv.curry B (SwitchIndex d) Bool).symm ω)).symm
        then (1:ℝ) else 0) =
      ∏ b, if blockMarks (Equiv.refl _) S b ⊆ inverseButterflyMarks d
        (blockMarks (Equiv.refl _) A b) (ω b) then 1 else 0 := by
    simp only [subset_parallel_inverse]
    change (if ∀ b, blockMarks (Equiv.refl _) S b ⊆ inverseButterflyMarks d
      (blockMarks (Equiv.refl _) A b) (ω b) then (1:ℝ) else 0) = _
    by_cases h : ∀ b, blockMarks (Equiv.refl _) S b ⊆
        inverseButterflyMarks d (blockMarks (Equiv.refl _) A b) (ω b)
    · simp [h]
    · rw [ite_eq_right h]
      obtain ⟨b,hb⟩ := not_forall.mp h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      exact ite_eq_right hb
  simp_rw [hi]
  rw [finiteMean_pi_prod (fun b ω => if blockMarks (Equiv.refl _) S b ⊆
    inverseButterflyMarks d (blockMarks (Equiv.refl _) A b) ω then 1 else 0),prod_blockMarks]
  apply Finset.prod_le_prod₀
  · intro b _
    exact finiteMean_nonneg (fun ω => by split_ifs <;> norm_num)
  · intro b _
    simpa only [←inclusionMoment_eq,Finset.prod_const] using
      inverseButterflyMarks_inclusion d (blockMarks (Equiv.refl _) A b)
        (blockMarks (Equiv.refl _) S b)

end Thorp

namespace Thorp
namespace PairRouting
variable {ι : Type*} [Fintype ι]

lemma node_cycle_mean_one_fresh (d : ℕ) (e : ι ↪ Bool × Card d)
    (c₀ : BenesCoins d) (X : SwitchIndex d → Bool) :
    finiteMean (fun Y : SwitchIndex d → Bool =>
      (alternatingCycles e (fun b => palindromePerm d (if b then (Y,X) else c₀)) : ℝ)) ≤
        (sharedPairs e).card * DenseTruncation.h (d+1) := by
  classical
  calc
    _ ≤ finiteMean (fun Y : SwitchIndex d → Bool =>
        (Fintype.card (RoutingNetwork.SelectedCycle
          ((palindromePerm d c₀).symm * butterflyPerm d (decodeButterfly d Y) *
            (butterflyPerm d (decodeButterfly d X)).symm) (sharedPairs e)) : ℝ)) := by
      apply finiteMean_mono
      intro Y
      have hh := alternatingCycles_le_sharedSelected e
        (fun b => palindromePerm d (if b then (Y,X) else c₀))
      simpa only [alternatingProjection,Bool.false_eq_true,↓reduceIte,palindromePerm,mul_assoc] using
        (Nat.cast_le.mpr hh : (alternatingCycles e _ : ℝ) ≤ _)
    _ ≤ _ := relabeled_single_cycle_mean d _ _ _

lemma node_cycle_mgf_fixed_input (d : ℕ) (e : ι ↪ Bool × Card d)
    (X : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (t : ℝ) (ht : 0 ≤ t) :
    finiteMean (fun Y : (SwitchIndex d → Bool) × (SwitchIndex d → Bool) =>
      Real.exp (t * alternatingCycles e
        (fun b => palindromePerm d (if b then (Y.2,X.2) else (Y.1,X.1))))) ≤
      Real.exp ((sharedPairs e).card * DenseTruncation.h (d+1) *
        ((Real.exp (t*(2:ℝ)^d)-1)/(2:ℝ)^d)) := by
  apply finiteMean_exp_bounded _ _ _ _ (by positivity) ht
  · intro Y
    constructor
    · exact Nat.cast_nonneg _
    · have h₀ := alternatingCycles_double e
        (fun b => palindromePerm d (if b then (Y.2,X.2) else (Y.1,X.1)))
      have h₁ := Fintype.card_le_of_injective e e.injective
      simp only [Fintype.card_prod,Fintype.card_bool,card_positions] at h₁
      exact_mod_cast (show alternatingCycles e _ ≤ 2^d by omega)
  · rw [finiteMean_prod]
    calc
      _ ≤ finiteMean (fun _ : SwitchIndex d → Bool =>
          (sharedPairs e).card * DenseTruncation.h (d+1)) :=
        finiteMean_mono (fun Y => node_cycle_mean_one_fresh d e (Y,X.1) X.2)
      _ = _ := finiteMean_const _

end PairRouting

noncomputable def sharedLevel (t : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → (SwitchIndex d → Bool) → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, X =>
      let χ := coinStepEquiv d X
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x χ.2
      let hc := PairRouting.colors_compatible x χ.2
      if t = d+1 then (PairRouting.sharedPairs x).card else
        sharedLevel t d (PairRouting.childEmbedding x c hc false) χ.1.1 +
          sharedLevel t d (PairRouting.childEmbedding x c hc true) χ.1.2

noncomputable def denseLevelCoefficient (j : ℕ) (t : ℝ) : ℝ :=
  DenseTruncation.h (j+1) * ((Real.exp (t*(2:ℝ)^j)-1)/(2:ℝ)^j)

lemma denseLevelCoefficient_nonneg (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ denseLevelCoefficient j t := by
  apply mul_nonneg (DenseTruncation.h_nonneg _)
  apply div_nonneg _ (by positivity)
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg ht (by positivity)))

lemma palindrome_level_dense_conditional (j d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (t : ℝ) (ht : 0 ≤ t) :
    finiteMean (fun Y : SwitchIndex d → Bool =>
      Real.exp (t * palindromeLevelCost (j+1) d e (Y,X))) ≤
        Real.exp (denseLevelCoefficient j t * sharedLevel (j+1) d e X) := by
  classical
  induction d generalizing ι with
  | zero => simp only [palindromeLevelCost,sharedLevel,Nat.cast_zero,mul_zero,
      Real.exp_zero,finiteMean_const,le_refl]
  | succ d ih =>
    let χ := coinStepEquiv d X
    let x := e.trans (headTailEquiv d).toEmbedding
    let c := PairRouting.colors x χ.2
    let hc := PairRouting.colors_compatible x χ.2
    let e₀ := PairRouting.childEmbedding x c hc false
    let e₁ := PairRouting.childEmbedding x c hc true
    have hs (Y : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (η : Card d → Bool) :
        palindromeLevelCost (j+1) (d+1) e ((coinStepEquiv d).symm (Y,η),X) =
          if j+1 = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x χ.2)
            (fun b => palindromePerm d (if b then (Y.2,χ.1.2) else (Y.1,χ.1.1))) else
            palindromeLevelCost (j+1) d e₀ (Y.1,χ.1.1) +
              palindromeLevelCost (j+1) d e₁ (Y.2,χ.1.2) := by
      conv_lhs => rw [←(coinStepEquiv d).symm_apply_apply X]
      rw [palindromeLevelCost_step]
    rw [finiteMean_equiv (coinStepEquiv d),finiteMean_prod]
    simp_rw [hs,finiteMean_const]
    change _ ≤ Real.exp (denseLevelCoefficient j t *
      (if j+1 = d+1 then (PairRouting.sharedPairs x).card else
        sharedLevel (j+1) d e₀ χ.1.1 + sharedLevel (j+1) d e₁ χ.1.2))
    by_cases hj : j = d
    · subst j
      simp only [ite_true]
      have hh := PairRouting.node_cycle_mgf_fixed_input d
        (PairRouting.switchedEmbedding x χ.2) χ.1 t ht
      rw [PairRouting.sharedPairs_switched] at hh
      simpa only [denseLevelCoefficient,mul_left_comm,mul_assoc,mul_comm] using hh
    · have hne : j+1 ≠ d+1 := by omega
      simp only [ite_eq_right hne,Nat.cast_add,mul_add,Real.exp_add]
      rw [finiteMean_prod_mul
        (fun Y : SwitchIndex d → Bool => Real.exp (t * palindromeLevelCost (j+1) d e₀ (Y,χ.1.1)))
        (fun Y : SwitchIndex d → Bool => Real.exp (t * palindromeLevelCost (j+1) d e₁ (Y,χ.1.2)))]
      exact mul_le_mul (ih e₀ χ.1.1) (ih e₁ χ.1.2)
        (finiteMean_nonneg (fun _ => (Real.exp_pos _).le)) (Real.exp_pos _).le


def pairCoords (r s : ℕ) : Card ((s+1)+r) ≃ Bool × (Card r × Card s) :=
  (cardSplit r (s+1)).trans
    { toFun := fun x => ((x.2) 0,(x.1,Fin.tail x.2))
      invFun := fun x => (x.2.1,Fin.cons x.1 x.2.2)
      left_inv := by intro x; simp only [Fin.cons_self_tail]
      right_inv := by intro x; simp only [Fin.cons_zero,Fin.tail_cons] }

noncomputable def gridPairs (r s : ℕ) (A : Finset (Card ((s+1)+r))) : Finset (Card r × Card s) :=
  Finset.univ.filter (fun x => (pairCoords r s).symm (false,x) ∈ A ∧
    (pairCoords r s).symm (true,x) ∈ A)

noncomputable def gridShared (r s : ℕ) (A : Finset (Card ((s+1)+r))) : ℕ :=
  (gridPairs r s A).card

lemma gridPairs_eq (r s : ℕ) (A : Finset (Card ((s+1)+r))) :
    gridPairs r s A = boolFiber (A.image (pairCoords r s)) false ∩
      boolFiber (A.image (pairCoords r s)) true := by
  classical
  ext x
  have hm (b : Bool) : (b,x) ∈ A.image (pairCoords r s) ↔
      (pairCoords r s).symm (b,x) ∈ A := by
    constructor
    · rintro h
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
      rw [←he,Equiv.symm_apply_apply]
      exact ha
    · intro h
      exact Finset.mem_image.mpr ⟨_,h,(pairCoords r s).apply_symm_apply _⟩
  simp only [gridPairs,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter,
    mem_boolFiber,hm]

lemma gridShared_zero (s : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+1)) :
    gridShared 0 s (Finset.univ.image e) =
      (PairRouting.sharedPairs (e.trans (headTailEquiv s).toEmbedding)).card := by
  classical
  let z : Card 0 := fun i => Fin.elim0 i
  have he : gridPairs 0 s (Finset.univ.image e) =
      (PairRouting.sharedPairs (e.trans (headTailEquiv s).toEmbedding)).image (fun y => (z,y)) := by
    ext ⟨b,y⟩
    have hb : b = z := Subsingleton.elim _ _
    subst b
    simp only [gridPairs,Finset.mem_filter,Finset.mem_univ,true_and,
      PairRouting.sharedPairs,Finset.mem_inter,mem_boolFiber,PairRouting.labelSet,
      Finset.mem_image,Prod.mk.injEq,true_and]
    change ((∃ i, e i = Fin.cons false y) ∧ ∃ i, e i = Fin.cons true y) ↔ _
    simp only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
      headTailEquiv]
    constructor
    · rintro ⟨⟨i,hi⟩,⟨i',hi'⟩⟩
      refine ⟨y,⟨?_,?_⟩,rfl⟩
      · exact ⟨i,by change (e i 0,Fin.tail (e i)) = (false,y); rw [hi]; rfl⟩
      · exact ⟨i',by change (e i' 0,Fin.tail (e i')) = (true,y); rw [hi']; rfl⟩
    · rintro ⟨y',⟨⟨i,hi⟩,⟨i',hi'⟩⟩,rfl⟩
      constructor
      · exact ⟨i,(headTailEquiv s).injective hi⟩
      · exact ⟨i',(headTailEquiv s).injective hi'⟩
  rw [gridShared,he,Finset.card_image_of_injective]
  intro y y' h
  exact congrArg Prod.snd h

lemma gridShared_step (r s : ℕ) (A : Finset (Card ((s+1)+(r+1)))) :
    gridShared (r+1) s A = gridShared r s (childMarks A false) +
      gridShared r s (childMarks A true) := by
  classical
  have hsum (r : ℕ) (A : Finset (Card ((s+1)+r))) : gridShared r s A =
      ∑ b : Card r, ∑ y : Card s,
        if (pairCoords r s).symm (false,(b,y)) ∈ A ∧
          (pairCoords r s).symm (true,(b,y)) ∈ A then (1:ℕ) else 0 := by
    rw [gridShared,gridPairs,Finset.card_filter,Fintype.sum_prod_type]
  rw [hsum,hsum,hsum,←Equiv.sum_comp (headTailEquiv r).symm,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hc (b : Bool) (x : Card r) (y : Card s) (ε : Bool) :
      (pairCoords (r+1) s).symm (ε,((headTailEquiv r).symm (b,x),y)) =
        Fin.cons b ((pairCoords r s).symm (ε,(x,y))) := rfl
  simp only [hc,mem_childMarks]
  exact add_comm _ _

lemma butterfly_false (d : ℕ) :
    butterflyPerm d (decodeButterfly d (fun _ => false)) = 1 := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    have he : (fun _ : SwitchIndex (d+1) => false) = (coinStepEquiv d).symm
        (((fun _ => false),(fun _ => false)),fun _ => false) := by
      funext i
      rcases i with y | ⟨b,i⟩
      · rfl
      · cases b <;> rfl
    rw [he,butterflyPerm_step]
    ext x i
    simp [ih,Equiv.Perm.mul_apply,childLift]
    change Fin.cons (Bool.xor (x 0) false) (Fin.tail x) i = x i
    simp

lemma inverseButterflyMarks_false (d : ℕ) (A : Finset (Card d)) :
    inverseButterflyMarks d A (fun _ => false) = A := by
  rw [inverseButterflyMarks,butterfly_false]
  change Finset.image id A = A
  exact Finset.image_id


lemma sharedLevel_partial_marks (r s : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card ((s+1)+r))
    (lo : Card r × SwitchIndex (s+1) → Bool)
    (hi : Card (s+1) × SwitchIndex r → Bool) :
    sharedLevel (s+1) ((s+1)+r) e (assembleBits r (s+1) lo hi) =
      gridShared r s (inverseButterflyMarks ((s+1)+r) (Finset.univ.image e)
        (assembleBits r (s+1) (fun _ => false) hi)) := by
  classical
  induction r generalizing ι with
  | zero =>
    rw [show assembleBits 0 (s+1) (fun _ => false) hi = (fun _ => false) from rfl,
      inverseButterflyMarks_false,gridShared_zero]
    simp only [sharedLevel,ite_true]
  | succ r ih =>
    obtain ⟨c,rfl⟩ := (highStepEquiv r (s+1)).symm.surjective hi
    simp only [Nat.add_succ] at *
    rw [assembleBits_step,sharedLevel]
    simp only [Equiv.apply_symm_apply]
    rw [ite_eq_right (by omega : s+1 ≠ s+1+r+1)]
    rw [ih,ih,assembleBits_step,gridShared_step,
      inverseButterflyMarks_child,inverseButterflyMarks_child]
    rfl

lemma partial_input_parallel (r s : ℕ) (hi : Card s × SwitchIndex r → Bool)
    (x : Card (s+r)) :
    ((cardSplit r s).trans (Equiv.prodComm _ _))
      ((butterflyPerm (s+r) (decodeButterfly (s+r)
        (assembleBits r s (fun _ => false) hi))).symm x) =
      (parallelPerm hi).symm (((cardSplit r s).trans (Equiv.prodComm _ _)) x) := by
  let y := (butterflyPerm (s+r) (decodeButterfly (s+r)
    (assembleBits r s (fun _ => false) hi))).symm x
  have hh := butterfly_split r s (fun _ => false) hi y
  dsimp only [y] at hh
  simp only [butterfly_false,Equiv.Perm.one_apply,Equiv.apply_symm_apply] at hh
  change cardSplit r s x =
    (butterflyPerm r (decodeButterfly r (fun i => hi ((cardSplit r s y).2,i)))
      (cardSplit r s y).1,(cardSplit r s y).2) at hh
  have hs := congrArg Prod.snd hh
  have hf := congrArg Prod.fst hh
  dsimp only at hs hf
  change ((cardSplit r s y).2,(cardSplit r s y).1) =
    ((cardSplit r s x).2,(butterflyPerm r
      (decodeButterfly r (fun i => hi ((cardSplit r s x).2,i)))).symm (cardSplit r s x).1)
  rw [hs,hf,Equiv.symm_apply_apply]

lemma partial_marks_parallel (r s : ℕ) (A : Finset (Card (s+r)))
    (hi : Card s × SwitchIndex r → Bool) :
    (inverseButterflyMarks (s+r) A (assembleBits r s (fun _ => false) hi)).image
      ((cardSplit r s).trans (Equiv.prodComm _ _)) =
        (A.image ((cardSplit r s).trans (Equiv.prodComm _ _))).image (parallelPerm hi).symm := by
  classical
  simp only [inverseButterflyMarks,Finset.image_image]
  congr 1
  funext x
  exact partial_input_parallel r s hi x

lemma cylinder_image_equiv_bound {α β Ω : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype Ω] (e : α ≃ β) (F : Ω → Finset α) (p : α → ℝ)
    (h : CylinderBound (inclusionMoment F) p) :
    CylinderBound (inclusionMoment (fun ω => (F ω).image e)) (fun x => p (e.symm x)) := by
  intro S
  rw [inclusionMoment_image_equiv]
  have hh := h (S.image e.symm)
  simpa only [Finset.prod_image e.symm.injective.injOn] using hh


noncomputable def suffixMarks (r s : ℕ) (A : Finset (Card (s+r))) (y : Card s) : Finset (Card r) :=
  blockMarks ((cardSplit r s).trans (Equiv.prodComm _ _)) A y

noncomputable def sharedPartnerMean (r s : ℕ) (A : Finset (Card ((s+1)+r))) : ℝ :=
  (∑ y : Card s, ((suffixMarks r (s+1) A (Fin.cons false y)).card : ℝ) *
    (suffixMarks r (s+1) A (Fin.cons true y)).card) / (2:ℝ)^r

lemma blockMarks_image_equiv {α B : Type*} [Fintype α] [DecidableEq α]
    [Fintype B] [DecidableEq B] (r : ℕ) (E : α ≃ B × Card r)
    (A : Finset α) (b : B) :
    blockMarks (Equiv.refl _) (A.image E) b = blockMarks E A b := by
  classical
  ext y
  simp only [mem_blockMarks,Equiv.refl_symm,Equiv.refl_apply,Finset.mem_image]
  constructor
  · rintro ⟨x,hx,he⟩
    rw [←he,Equiv.symm_apply_apply]
    exact hx
  · intro h
    exact ⟨_,h,E.apply_symm_apply _⟩

def pairReorder (r s : ℕ) : Card (s+1) × Card r ≃ Bool × (Card r × Card s) where
  toFun x := (x.1 0,(x.2,Fin.tail x.1))
  invFun x := (Fin.cons x.1 x.2.2,x.2.1)
  left_inv x := by simp only [Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero,Fin.tail_cons]

lemma pairCoords_reorder (r s : ℕ) :
    pairCoords r s = ((cardSplit r (s+1)).trans (Equiv.prodComm _ _)).trans (pairReorder r s) := rfl

lemma partial_grid_mgf (r s : ℕ) (A : Finset (Card ((s+1)+r)))
    (z : ℝ) (hz : 0 ≤ z) :
    finiteMean (fun hi : Card (s+1) × SwitchIndex r → Bool =>
      Real.exp (z * gridShared r s (inverseButterflyMarks ((s+1)+r) A
        (assembleBits r (s+1) (fun _ => false) hi)))) ≤
      Real.exp ((Real.exp z-1)*sharedPartnerMean r s A) := by
  classical
  let E := (cardSplit r (s+1)).trans (Equiv.prodComm _ _)
  let F (hi : Card (s+1) × SwitchIndex r → Bool) := (A.image E).image (parallelPerm hi).symm
  let p (x : Card (s+1) × Card r) : ℝ :=
    (suffixMarks r (s+1) A x.1).card / (2:ℝ)^r
  have hc : CylinderBound (inclusionMoment F) p := by
    have hh := parallel_inverse_cylinder r (A.image E)
    simp only [blockMarks_image_equiv] at hh
    exact hh
  have hp : ∀ x, 0 ≤ p x := by intro x; exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hh := shared_pair_mgf (fun hi => (F hi).image (pairReorder r s))
    (fun x => p ((pairReorder r s).symm x)) (fun x => hp _)
    (cylinder_image_equiv_bound (pairReorder r s) F p hc) z hz
  have he (hi : Card (s+1) × SwitchIndex r → Bool) :
      (F hi).image (pairReorder r s) =
        (inverseButterflyMarks ((s+1)+r) A
          (assembleBits r (s+1) (fun _ => false) hi)).image (pairCoords r s) := by
    rw [pairCoords_reorder]
    change (F hi).image (pairReorder r s) =
      (inverseButterflyMarks ((s+1)+r) A
        (assembleBits r (s+1) (fun _ => false) hi)).image ((pairReorder r s) ∘ E)
    rw [←Finset.image_image,partial_marks_parallel]
  have hm : (∑ b : Card r × Card s,
      p ((pairReorder r s).symm (false,b))*p ((pairReorder r s).symm (true,b))) =
        sharedPartnerMean r s A := by
    simp only [p,pairReorder,Equiv.coe_fn_symm_mk,Fintype.sum_prod_type]
    rw [Finset.sum_const,Finset.card_univ,card_positions,nsmul_eq_mul]
    simp only [sharedPartnerMean, div_mul_div_comm, ←Finset.sum_div]
    rw [show (↑(2^r) : ℝ) = (2:ℝ)^r by rfl]
    have hpow : (2:ℝ)^r ≠ 0 := by positivity
    generalize (∑ y : Card s, (suffixMarks r (s+1) A (Fin.cons false y)).card *
      (suffixMarks r (s+1) A (Fin.cons true y)).card : ℝ) = v
    field_simp
    ; push_cast
    ; ring
  simp_rw [he,←gridPairs_eq] at hh
  rw [hm] at hh
  exact hh

end Thorp

end ThorpNine.Dense

end OAI
