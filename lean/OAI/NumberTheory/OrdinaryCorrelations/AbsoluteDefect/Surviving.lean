import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryFrequencyChain
open Finset
attribute [local instance] Classical.propDecidable

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

def surviving (R : Finset α) (good : ℕ → α → Prop) (j : ℕ) : Finset α := by
  classical
  exact R.filter (fun t => ∀ i<j, ¬good i t)

def firstGood (R : Finset α) (good : ℕ → α → Prop) (j : ℕ) : Finset α := by
  classical
  exact (surviving R good j).filter (good j)

omit [DecidableEq α] in
lemma surviving_zero [DecidableEq α] (R : Finset α) (good : ℕ → α → Prop) :
    surviving R good 0=R := by
  classical
  ext t
  simp [surviving]

omit [DecidableEq α] in
lemma surviving_succ [DecidableEq α] (R : Finset α) (good : ℕ → α → Prop) (j : ℕ) :
    surviving R good (j+1)=(surviving R good j).filter (fun t => ¬good j t) := by
  classical
  ext t
  simp only [surviving,mem_filter]
  constructor
  · rintro ⟨ht,hg⟩
    exact ⟨⟨ht,fun i hi => hg i (by omega)⟩,hg j (by omega)⟩
  · rintro ⟨⟨ht,hg⟩,hj⟩
    refine ⟨ht,fun i hi => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hii|rfl
    · exact hg i hii
    · exact hj

lemma sum_partition (R : Finset α) (good : ℕ → α → Prop) (J : ℕ) (w : α → ℝ) :
    (∑t∈R,w t)=(∑j∈range J,∑t∈firstGood R good j,w t)+∑t∈surviving R good J,w t := by
  classical
  induction J with
  | zero => simp [surviving_zero]
  | succ J ih =>
    rw [ih,sum_range_succ,add_assoc]
    congr 1
    rw [firstGood,surviving_succ]
    exact (sum_filter_add_sum_filter_not (surviving R good J) (good J) w).symm

lemma square_two (z w : ℂ) : ‖z+w‖^2≤2*‖z‖^2+2*‖w‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le z w) 2
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

omit [DecidableEq α] in
lemma approximation_energy [DecidableEq α] (R S : Finset α) (hS : S⊆R) (F B : α → ℂ) :
    (∑t∈S,‖F t‖^2) ≤ 2*(∑t∈S,‖B t‖^2)+2*(∑t∈R,‖F t-B t‖^2) := by
  calc
    _ ≤ ∑t∈S,(2*‖B t‖^2+2*‖F t-B t‖^2) := by
      apply sum_le_sum
      intro t ht
      have hh := square_two (B t) (F t-B t)
      have he : B t+(F t-B t)=F t := by ring
      rwa [he] at hh
    _ = 2*(∑t∈S,‖B t‖^2)+2*(∑t∈S,‖F t-B t‖^2) := by rw [sum_add_distrib,mul_sum,mul_sum]
    _ ≤ _ := by
      gcongr

theorem first_good_energy (R : Finset α) (good : ℕ → α → Prop) (J : ℕ)
    (F : α → ℂ) (B : ℕ → α → ℂ) :
    (∑t∈R,‖F t‖^2) ≤
      2*(∑j∈range J,∑t∈firstGood R good j,‖B j t‖^2)+
      2*(∑j∈range J,∑t∈R,‖F t-B j t‖^2)+
      2*(∑t∈surviving R good J,‖B 0 t‖^2)+
      2*(∑t∈R,‖F t-B 0 t‖^2) := by
  classical
  rw [sum_partition R good J (fun t => ‖F t‖^2)]
  have hmain : (∑j∈range J,∑t∈firstGood R good j,‖F t‖^2) ≤
      ∑j∈range J,(2*(∑t∈firstGood R good j,‖B j t‖^2)+2*(∑t∈R,‖F t-B j t‖^2)) := by
    apply sum_le_sum
    intro j hj
    exact approximation_energy R _ ((filter_subset _ _).trans (filter_subset _ _)) F (B j)
  have htail := approximation_energy R (surviving R good J) (filter_subset _ _) F (B 0)
  simp only [sum_add_distrib,←mul_sum] at hmain
  linarith

omit [DecidableEq α] [DecidableEq ι] in
lemma binned_energy [DecidableEq α] [DecidableEq ι]
    (S : Finset ι) (R : Finset α) (Q C : ι → α → ℂ) :
    (∑t∈R,‖∑i∈S,Q i t*C i t‖^2) ≤
      (S.card:ℝ)*∑i∈S,∑t∈R,‖Q i t‖^2*‖C i t‖^2 := by
  calc
    _ ≤ ∑t∈R,(S.card:ℝ)*∑i∈S,‖Q i t*C i t‖^2 := by
      apply sum_le_sum
      intro t ht
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq
    _ = _ := by simp_rw [norm_mul,mul_pow]; rw [←mul_sum,sum_comm]

omit [DecidableEq α] [DecidableEq ι] in
lemma sum_filter_exists_le [DecidableEq α] [DecidableEq ι]
    (R : Finset α) (S : Finset ι) (p : ι → α → Prop)
    (w : α → ℝ) (hw : ∀t∈R,0≤w t) :
    (∑t∈R.filter (fun t => ∃i∈S,p i t),w t) ≤ ∑i∈S,∑t∈R.filter (p i),w t := by
  classical
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro t ht
  split_ifs with hh
  · obtain ⟨i,hi,hp⟩ := hh
    calc
      _ = if p i t then w t else 0 := by simp [hp]
      _ ≤ _ := Finset.single_le_sum (f:=fun a => if p a t then w t else 0) (s:=S) (fun a ha => by split_ifs <;> simp_all) hi
  · exact sum_nonneg (fun i hi => by split_ifs <;> simp_all)

def allBinsGood (I : ℕ → Finset ι) (Q : ℕ → ι → α → ℂ) (V : ℕ → ι → ℝ)
    (j : ℕ) (t : α) : Prop := ∀i∈I j,‖Q j i t‖≤V j i

theorem next_stage_energy (R : Finset α) (I : ℕ → Finset ι)
    (Q C : ℕ → ι → α → ℂ) (V : ℕ → ι → ℝ) (j : ℕ) :
    (∑t∈firstGood R (allBinsGood I Q V) (j+1),‖∑i∈I (j+1),Q (j+1) i t*C (j+1) i t‖^2) ≤
      ((I (j+1)).card:ℝ)*∑i∈I (j+1),∑a∈I j,
        ∑t∈R.filter (fun t => V j a<‖Q j a t‖ ∧ ‖Q (j+1) i t‖≤V (j+1) i),
          ‖Q (j+1) i t‖^2*‖C (j+1) i t‖^2 := by
  classical
  apply (binned_energy (I (j+1)) _ (Q (j+1)) (C (j+1))).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro i hi
  let w : α → ℝ := fun t => ‖Q (j+1) i t‖^2*‖C (j+1) i t‖^2
  let p : ι → α → Prop := fun a t => V j a<‖Q j a t‖ ∧ ‖Q (j+1) i t‖≤V (j+1) i
  have hsub : firstGood R (allBinsGood I Q V) (j+1) ⊆ R.filter (fun t => ∃a∈I j,p a t) := by
    intro t ht
    rcases mem_filter.mp ht with ⟨ht,hgood⟩
    rcases mem_filter.mp ht with ⟨ht,hprev⟩
    have hh := hprev j (by omega)
    simp only [allBinsGood,not_forall,not_le] at hh
    obtain ⟨a,ha,hbad⟩ := hh
    exact mem_filter.mpr ⟨ht,a,ha,hbad,hgood i hi⟩
  apply (sum_le_sum_of_subset_of_nonneg hsub (fun t ht hn => by positivity)).trans
  simpa only [p,w] using sum_filter_exists_le R (I j) p w (fun t ht => by dsimp only [w]; positivity)

omit [DecidableEq ι] in
lemma sparse_union [DecidableEq ι] (S : Finset ι) (T : ι → Finset α) (H r : ℕ)
    (hr : 0<r) (hS : S.card^(2*r)≤H)
    (hT : ∀i∈S,(T i).card^(2*r)≤H) :
    (S.biUnion T).card^r≤H := by
  classical
  rcases S.eq_empty_or_nonempty with rfl|hne
  · simp [hr.ne']
  obtain ⟨i,hi,hmax⟩ := S.exists_max_image (fun i => (T i).card) hne
  have hc : (S.biUnion T).card≤S.card*(T i).card := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑_j∈S,(T i).card := sum_le_sum hmax
      _ = _ := by simp
  have hh := Nat.pow_le_pow_left hc r
  rw [mul_pow] at hh
  have ha : (S.card^r)^2≤H := by simpa only [←pow_mul,Nat.mul_comm r 2] using hS
  have hb : ((T i).card^r)^2≤H := by simpa only [←pow_mul,Nat.mul_comm r 2] using hT i hi
  have hprod := Nat.mul_le_mul ha hb
  have hsquare := Nat.pow_le_pow_left hh 2
  rw [mul_pow] at hsquare
  nlinarith

end OrdinaryFrequencyChain

end

end OAI
