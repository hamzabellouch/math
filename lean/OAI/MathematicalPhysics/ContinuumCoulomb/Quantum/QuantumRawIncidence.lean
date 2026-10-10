import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryIncidence
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedRawBlock
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelPacking
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListDegree

namespace OAI

/-! The literal four-spin exchange list preserves a uniform incidence bound.
All bonds are counted, including bonds with zero weight. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawIncidence
open QuantumForkList QuantumOrderedIncidence QuantumRawExchange MediatorListProgram
open scoped BigOperators Classical

theorem degree_le_length (bs : List Bond) (v : ℕ) : degree bs v ≤ bs.length := by
  induction bs with
  | nil => simp [degree]
  | cons b bs ih =>
    simp only [degree,List.map_cons,List.sum_cons,List.length_cons,incident] at ih ⊢
    split_ifs <;> omega

theorem degree_zero (bs : List Bond) (v : ℕ)
    (h : ∀ b ∈ bs, b.1 ≠ v ∧ b.2.1 ≠ v) : degree bs v = 0 := by
  unfold degree
  apply List.sum_eq_zero
  intro k hk
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hk
  simp [incident,(h b hb).1,(h b hb).2]

theorem degree_flatten (bss : List (List Bond)) (v : ℕ) :
    degree bss.flatten v = (bss.map (fun bs => degree bs v)).sum := by
  simp only [degree,List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def]

def sites {n : ℕ} : QMAXZTerm n → List (Fin n)
  | .scalar => []
  | .field i _ => [i]
  | .pair i j _ _ _ => [i,j]

theorem slot_div (i : ℕ) (j : Fin 4) : (4*i+j.val)/4=i := by omega

theorem field_origin (k i : ℕ) (a : Fin 2) (J : ℚ) (b : Bond)
    (hb : b ∈ field k i a J) (v : ℕ) (hv : b.1=v ∨ b.2.1=v) : v/4=i := by
  obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
  rcases hv with hv | hv
  · change 4*i=v at hv
    omega
  · change 4*i+(qmaFieldEdgeRight e).val=v at hv
    rw [← hv]
    exact slot_div i _

theorem cross_origin (k : ℕ) (r : ℚ) (i j : ℕ) (a b : Fin 2) (J : ℚ)
    (e : Bond) (he : e ∈ cross k r i j a b J) (v : ℕ)
    (hv : e.1=v ∨ e.2.1=v) : v/4=i ∨ v/4=j := by
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp he
  rcases hv with hv | hv
  · left
    change 4*i+((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm p).1.val=v at hv
    rw [← hv]
    exact slot_div i _
  · right
    change 4*j+((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm p).2.val=v at hv
    rw [← hv]
    exact slot_div j _

theorem packed_origin {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ)
    (b : Bond) (hb : b ∈ bonds ((k,r),pack t J)) (v : ℕ)
    (hv : b.1=v ∨ b.2.1=v) : ∃ i ∈ sites t, i.val=v/4 := by
  cases t with
  | scalar => simp [bonds,pack] at hb
  | field i a =>
    have hi := field_origin k i.val (axis (decide (a=0))) J b hb v hv
    exact ⟨i,by simp [sites],hi.symm⟩
  | pair i j hij a b' =>
    change b ∈ cross k r i.val j.val _ _ J ++ field k i.val _ _ ++ field k j.val _ _ at hb
    simp only [List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · rcases cross_origin k r i.val j.val _ _ J b hb v hv with hi | hj
      · exact ⟨i,by simp [sites],hi.symm⟩
      · exact ⟨j,by simp [sites],hj.symm⟩
    · exact ⟨i,by simp [sites],(field_origin _ _ _ _ b hb v hv).symm⟩
    · exact ⟨j,by simp [sites],(field_origin _ _ _ _ b hb v hv).symm⟩

theorem ofSites_subset {n : ℕ} (xs : List (Fin n)) (w : Fin n → Fin 4) :
    ∀ i ∈ sites (QuantumOrderedXZTerm.ofSites xs w), i ∈ xs := by
  cases xs with
  | nil => simp [QuantumOrderedXZTerm.ofSites,sites]
  | cons i xs =>
    cases xs with
    | nil =>
      by_cases h : w i=0 <;>
        simp [QuantumOrderedXZTerm.ofSites,QuantumOrderedXZTerm.field,sites,h]
    | cons j xs =>
      by_cases hij : i=j <;> by_cases hi : w i=0 <;> by_cases hj : w j=0 <;>
        simp [QuantumOrderedXZTerm.ofSites,QuantumOrderedXZTerm.field,sites,hij,hi,hj]

theorem term_degree {n : ℕ} (k : ℕ) (r : ℚ) (xs : List (Fin n))
    (w : Fin n → Fin 4) (J : ℚ) (v : ℕ) (q : Fin n) (hq : q.val=v/4) :
    degree (bonds ((k,r),pack (QuantumOrderedXZTerm.ofSites xs w) J)) v ≤
      22*(if q ∈ xs then 1 else 0) := by
  by_cases h : q ∈ xs
  · simpa only [h,ite_true,Nat.mul_one] using
      (degree_le_length _ v).trans (bonds_length _)
  · have hz : degree (bonds ((k,r),pack (QuantumOrderedXZTerm.ofSites xs w) J)) v=0 := by
      apply degree_zero
      intro b hb
      have hn : ¬(b.1=v ∨ b.2.1=v) := by
        intro hv
        obtain ⟨i,hi,he⟩ := packed_origin k r _ J b hb v hv
        have hiq : i=q := Fin.ext (he.trans hq.symm)
        exact h (hiq ▸ ofSites_subset xs w i hi)
      exact not_or.mp hn
    simp only [h,ite_false,Nat.mul_zero,hz,le_refl]

theorem penalty_degree (n : ℕ) (r : ℚ) (v : ℕ) : degree (penalty n r) v ≤ 6 := by
  have hb (i : ℕ) : degree (penaltyBlock r i) v ≤ 6*(if v/4=i then 1 else 0) := by
    by_cases hi : v/4=i
    · simpa only [hi,ite_true,Nat.mul_one,penaltyBlock,List.length_ofFn] using
        degree_le_length (penaltyBlock r i) v
    · have hz : degree (penaltyBlock r i) v=0 := by
        apply degree_zero
        intro b hb
        obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
        have hl : 4*i+(qmaFourEdgeLeft e).val ≠ v := by
          intro he
          exact hi (by rw [← he]; exact slot_div i _)
        have hr : 4*i+(qmaFourEdgeRight e).val ≠ v := by
          intro he
          exact hi (by rw [← he]; exact slot_div i _)
        exact ⟨hl,hr⟩
      simp [hz,hi]
  unfold penalty
  rw [degree_flatten,List.map_map,range_sum]
  calc
    _ ≤ ∑ i : Fin n, 6*(if v/4=i.val then 1 else 0) :=
      Finset.sum_le_sum (fun i _ => hb i.val)
    _ = 6*∑ i : Fin n, if v/4=i.val then 1 else 0 := (Finset.mul_sum _ _ _).symm
    _ ≤ 6*1 := by
      apply Nat.mul_le_mul_left
      simpa only [eq_comm] using qmaCount_eq_le_one Fin.val Fin.val_injective (v/4)
    _ = 6 := by omega

theorem raw_degree {n m : ℕ} (N : ℕ) (xs : Fin m → List (Fin n))
    (w : Fin m → Fin n → Fin 4) (J : Fin m → ℚ) {D : ℕ}
    (hx : Bounded xs D) (v : ℕ) (hv : v<n*4) :
    degree (QuantumOrderedRawBlock.output N xs w J).1 v ≤ 6+22*D := by
  let q : Fin n := ⟨v/4,by omega⟩
  let env : Environment :=
    (bits (n,N,packed (QuantumOrderedRawBlock.terms xs w) J),
      scale N (packed (QuantumOrderedRawBlock.terms xs w) J))
  change degree (penalty n env.2 ++ termBondsList (env,
    packed (QuantumOrderedRawBlock.terms xs w) J)) v ≤ _
  rw [degree_append]
  have hp := penalty_degree n env.2 v
  have ht : degree (termBondsList (env,packed (QuantumOrderedRawBlock.terms xs w) J)) v ≤
      22*D := by
    unfold termBondsList packed
    rw [degree_flatten,List.map_map,List.map_ofFn,List.sum_ofFn]
    calc
      _ ≤ ∑ e : Fin m, 22*(if q ∈ xs e then 1 else 0) := by
        apply Finset.sum_le_sum
        intro e _
        exact term_degree env.1 env.2 (xs e) (w e) (J e) v q rfl
      _ = 22*count xs q := by
        rw [count,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : q ∈ xs e <;> simp only [h,ite_true,ite_false]
      _ ≤ 22*D := Nat.mul_le_mul_left 22 (hx q)
  omega

theorem numbered_bound {ι κ : Type} [Fintype κ] {n m D : ℕ}
    (q : Fin n ≃ ι) (e : Fin m ≃ κ) (xs : κ → List ι) (hx : Bounded xs D) :
    Bounded (QuantumOrderedLabelTable.numberedSites q e xs) D := by
  intro i
  have hm (a : Fin m) :
      i ∈ QuantumOrderedLabelTable.numberedSites q e xs a ↔ q i ∈ xs (e a) := by
    simp only [QuantumOrderedLabelTable.numberedSites,List.mem_map]
    constructor
    · rintro ⟨j,hj,hji⟩
      have hj' : j=q i := by simpa using congrArg q hji
      simpa only [hj'] using hj
    · intro hi
      exact ⟨q i,hi,q.symm_apply_apply i⟩
  calc
    count (QuantumOrderedLabelTable.numberedSites q e xs) i =
        ∑ a : Fin m, if q i ∈ xs (e a) then 1 else 0 := by simp only [count,hm]
    _ = count xs (q i) := by
      rw [count]
      exact e.sum_comp (fun a => if q i ∈ xs a then (1:ℕ) else 0)
    _ ≤ D := hx (q i)

end ContinuumCoulomb.QuantumRawIncidence

end

end OAI
