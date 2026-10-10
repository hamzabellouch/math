import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.State
import OAI.Combinatorics.RamseyFive.Bounds.UpperSet

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (ℙ K (Dual K V))]

lemma card_upper (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) :
    (upperSet W r).card=∑ l∈Finset.range (r+1),(levelSet W l).card := by
  have hh:=Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (ℙ K (Dual K V)))
    (Finset.range (r+1)) (fun y => finrank K (W y))
  simpa only [levelSet,upperSet,Finset.mem_range,Nat.lt_succ_iff] using hh.symm

lemma exists_level (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) :
    ∃ l,l≤r ∧ (∀ j,j≤r → (levelSet W j).card≤(levelSet W l).card) ∧
      (upperSet W r).card≤(r+1)*(levelSet W l).card := by
  obtain ⟨l,hl,hh⟩:=Finset.exists_max_image (Finset.range (r+1))
    (fun l => (levelSet W l).card) (by simp)
  refine ⟨l,Nat.le_of_lt_succ (Finset.mem_range.mp hl),?_,?_⟩
  · intro j hj
    exact hh j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  · rw [card_upper]
    calc
      _ ≤∑ j∈Finset.range (r+1),(levelSet W l).card := Finset.sum_le_sum hh
      _ = _ := by simp

noncomputable def chooseLevel (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) : ℕ :=
  (exists_level W r).choose

lemma chooseLevel_le (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) :
    chooseLevel W r≤r := (exists_level W r).choose_spec.1

lemma chooseLevel_large (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) :
    (upperSet W r).card≤(r+1)*(levelSet W (chooseLevel W r)).card :=
  (exists_level W r).choose_spec.2.2

lemma chooseLevel_nonempty (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (b : ℙ K (Dual K V)) :
    (levelSet W (chooseLevel W (finrank K (W b)))).Nonempty := by
  have hb : b∈upperSet W (finrank K (W b)) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_rfl⟩
  have hc := chooseLevel_large W (finrank K (W b))
  have hn := Finset.card_pos.mpr ⟨b,hb⟩
  apply Finset.card_pos.mp
  by_contra h
  have hh : (levelSet W (chooseLevel W (finrank K (W b)))).card=0 := by omega
  rw [hh,mul_zero] at hc
  omega

lemma chooseLevel_sublevel (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ)
    (hr : r≤4) :
    (upperSet W (chooseLevel W r)).card≤5*(levelSet W (chooseLevel W r)).card := by
  have hm : upperSet W (chooseLevel W r)⊆upperSet W r := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hy).2.trans (chooseLevel_le W r)⟩
  exact (Finset.card_le_card hm).trans ((chooseLevel_large W r).trans (Nat.mul_le_mul_right _ (by omega)))

end

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Fintype (ℙ K (Dual K V))] in
lemma coannihilator_card_bound (hdim : finrank K V=5)
    (W : Submodule K (Dual K V)) (r : ℕ) (hr : finrank K W=r) (hr4 : r≤4) :
    ((Finset.univ.filter fun a : ℙ K V => a.submodule≤W.dualCoannihilator).card:ℝ)≤
      2*(Nat.card K:ℝ)^(4-r) := by
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hr,hdim] at hd
  have hdc : finrank K W.dualCoannihilator=5-r := by omega
  have hcard : ((Finset.univ.filter fun a : ℙ K V => a.submodule≤W.dualCoannihilator).card:ℝ)=
      ∑ i∈Finset.range (5-r),(Nat.card K:ℝ)^i := by
    rw [subspace_finset_card,hdc]
    push_cast
    rfl
  rw [hcard]
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast Finite.one_lt_card (α := K)
  have hh:=q_mul_geometric_bound (Nat.card K:ℝ) hq (5-r)
  have he : 5-r=(4-r)+1 := by omega
  rw [he,pow_succ] at hh
  rw [he]
  nlinarith

theorem popular_joint_count (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r l : ℕ) (hlr : l≤r) (hr : r≤4) (hZ : (levelSet W l).Nonempty)
    (B : Finset (ℙ K (Dual K V)))
    (hB : ∀ b∈B,finrank K (W b)=r ∧
      ((levelSet W l).card:ℝ)/(16*Nat.card K)≤ memberships W (levelSet W l) b) :
    (((Finset.univ ×ˢ B).filter fun ab : ℙ K V × ℙ K (Dual K V) =>
      ab.1.submodule≤(W ab.2).dualCoannihilator).card:ℝ)≤64*(Nat.card K:ℝ)^4 := by
  have hcard := popular_count W (levelSet W l) hZ l (fun y hy => (Finset.mem_filter.mp hy).2)
  have hsub : B⊆Finset.univ.filter fun b : ℙ K (Dual K V) =>
      ((levelSet W l).card:ℝ)/(16*Nat.card K)≤ memberships W (levelSet W l) b := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hB b hb).2⟩
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hbcard : (B.card:ℝ)≤32*(Nat.card K:ℝ)^r := by
    have hb : (B.card:ℝ)≤(Finset.univ.filter fun b : ℙ K (Dual K V) =>
      ((levelSet W l).card:ℝ)/(16*Nat.card K)≤ memberships W (levelSet W l) b).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hb.trans (hcard.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hlr) (by norm_num)))
  rw [←Finset.sum_boole,Finset.sum_product,Finset.sum_comm]
  calc
    _ ≤ ∑ b∈B,2*(Nat.card K:ℝ)^(4-r) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [Finset.sum_boole]
      exact coannihilator_card_bound hdim (W b) r (hB b hb).1 hr
    _ = (B.card:ℝ)*(2*(Nat.card K:ℝ)^(4-r)) := by simp
    _ ≤ (32*(Nat.card K:ℝ)^r)*(2*(Nat.card K:ℝ)^(4-r)) :=
      mul_le_mul_of_nonneg_right hbcard (by positivity)
    _ = _ := by
      have hp : (Nat.card K:ℝ)^r*(Nat.card K:ℝ)^(4-r)=(Nat.card K:ℝ)^4 := by
        rw [←pow_add,Nat.add_sub_of_le hr]
      nlinarith [hp]

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

def Expensive (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b : ℙ K (Dual K V)) (q : ℝ) : Prop :=
  let Z:=levelSet W (chooseLevel W (finrank K (W b)))
  ((Z.filter fun y => b.submodule≤W y).card:ℝ)<(Z.card:ℝ)/(16*q) ∧
  (Z.card:ℝ)/(8*q)<((Z.filter fun y => Incident a y).card:ℝ)

noncomputable def scanSet (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) : ℕ → Finset ℕ
  | 0 => ∅
  | n+1 => if Expensive (state a b (scanSet a b q n)) (a n) (b n) q
      then insert n (scanSet a b q n) else scanSet a b q n

noncomputable def scanState (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) : ℙ K (Dual K V) → Submodule K (Dual K V) := state a b (scanSet a b q n)

omit [FiniteDimensional K V] in
lemma scanSet_subset (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (n : ℕ) :
    scanSet a b q n⊆Finset.range n := by
  induction n with
  | zero => simp [scanSet]
  | succ n ih =>
    rw [scanSet]
    split_ifs
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (ih hi)))
    · exact Finset.Subset.trans ih (Finset.range_mono (Nat.le_succ n))

omit [FiniteDimensional K V] in
lemma scanSet_mono (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (n : ℕ) :
    scanSet a b q n⊆scanSet a b q (n+1) := by
  rw [scanSet]
  split_ifs
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

omit [FiniteDimensional K V] in
lemma scanState_mono (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) (y : ℙ K (Dual K V)) :
    scanState a b q n y≤ scanState a b q (n+1) y :=
  state_mono a b (scanSet_mono a b q n) y

omit [FiniteDimensional K V] in
lemma scanState_update (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) (he : Expensive (scanState a b q n) (a n) (b n) q) :
    scanState a b q (n+1)=nextState (scanState a b q n) (a n) (b n) := by
  funext y
  change state a b (scanSet a b q (n+1)) y=_
  change Expensive (state a b (scanSet a b q n)) (a n) (b n) q at he
  rw [scanSet,ite_eq_left he,state_insert]
  unfold nextState
  split_ifs
  · rfl
  · exact bot_sup_eq _

lemma scan_rank (hdim : finrank K V=5) (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (N : ℕ)
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N) : finrank K (scanState a b q n (b n))≤4 := by
  have hle : scanState a b q n (b n)≤(a n).submodule.dualAnnihilator := by
    apply iSup₂_le
    intro i hi
    split_ifs with hab
    · exact (incident_iff_dualAnnihilator _ _).mp
        (hF i n (Finset.mem_range.mp (scanSet_subset a b q n hi)) hn hab)
    · exact bot_le
  have hr:=Submodule.finrank_mono hle
  have hd:=Subspace.finrank_add_finrank_dualAnnihilator_eq (a n).submodule
  rw [(a n).finrank_submodule,hdim] at hd
  omega

omit [FiniteDimensional K V] in
lemma scan_count (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ) :
    (scanSet a b q N).card=((Finset.range N).filter fun n =>
      Expensive (state a b (scanSet a b q n)) (a n) (b n) q).card := by
  induction N with
  | zero => simp [scanSet]
  | succ N ih =>
    have hn : N∉scanSet a b q N := fun h => (Nat.lt_irrefl N) (Finset.mem_range.mp (scanSet_subset a b q N h))
    rw [scanSet,Finset.range_add_one,Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem hn,Finset.card_insert_of_notMem (by simp),ih]
    · exact ih

end SharpRamseyFive.Marking

end OAI
