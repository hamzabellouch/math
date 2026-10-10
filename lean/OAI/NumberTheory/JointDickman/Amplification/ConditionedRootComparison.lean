import OAI.NumberTheory.JointDickman.Amplification.UnoccupiedRootLaw

namespace OAI

/-! # Independent-root error at an unoccupied prime -/

namespace JointDickman
open Finset

theorem categorical_shift_l1 {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (q r : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
    (∑ S ∈ I.powerset, |categoricalSubsetMass I (fun _ => q) S -
      bernoulliSubsetMass I (fun _ => r) S|) ≤
        2*((I.card : ℝ)*q)^2+2*(I.card : ℝ)*|q-r| := by
  have h1 := categorical_bernoulli_l1_le I (fun _ => q) (fun _ _ => hq)
  have h2 := bernoulliSubsetMass_l1_perturb I (fun _ => q) (fun _ => r)
    (fun _ _ => hq) (fun _ _ => hr)
  have htri : (∑ S ∈ I.powerset, |categoricalSubsetMass I (fun _ => q) S -
      bernoulliSubsetMass I (fun _ => r) S|) ≤
      (∑ S ∈ I.powerset, |categoricalSubsetMass I (fun _ => q) S -
        bernoulliSubsetMass I (fun _ => q) S|)+
      ∑ S ∈ I.powerset, |bernoulliSubsetMass I (fun _ => q) S -
        bernoulliSubsetMass I (fun _ => r) S| := by
    rw [← sum_add_distrib]
    exact sum_le_sum (fun _ _ => abs_sub_le _ _ _)
  simp only [sum_const,nsmul_eq_mul] at h1 h2
  linarith only [htri,h1,h2]

theorem unoccupied_reciprocal_estimates (p M : ℕ) (hp : M < p) (hhalf : 2*M ≤ p) :
    1/((p-M : ℕ) : ℝ) ≤ 2/(p : ℝ) ∧
      |1/((p-M : ℕ) : ℝ)-1/(p : ℝ)| ≤ 2*(M : ℝ)/(p : ℝ)^2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_le M).trans_lt hp
  have hd0 : (0 : ℝ) < (p-M : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hp
  have hd : ((p-M : ℕ) : ℝ) = (p : ℝ)-M := Nat.cast_sub hp.le
  have hmreal : 2*(M : ℝ) ≤ (p : ℝ) := by exact_mod_cast hhalf
  have hden : (p : ℝ)/2 ≤ ((p-M : ℕ) : ℝ) := by rw [hd]; linarith only [hmreal]
  have hq : 1/((p-M : ℕ) : ℝ) ≤ 2/(p : ℝ) := by
    calc
      _ ≤ 1/((p : ℝ)/2) := one_div_le_one_div_of_le (by positivity) hden
      _ = _ := by ring
  refine ⟨hq,?_⟩
  have hdiff : 0 ≤ 1/((p-M : ℕ) : ℝ)-1/(p : ℝ) := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le hd0
    rw [hd]
    exact sub_le_self _ (Nat.cast_nonneg M)
  have he : 1/((p-M : ℕ) : ℝ)-1/(p : ℝ) =
      (1/((p-M : ℕ) : ℝ))*((M : ℝ)/p) := by
    field_simp
    rw [hd]
    ring
  rw [abs_of_nonneg hdiff,he]
  calc
    _ ≤ (2/(p : ℝ))*((M : ℝ)/p) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by ring

theorem unoccupied_categorical_l1 {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p M : ℕ) (hp : M < p) (hhalf : 2*M ≤ p) :
    (∑ S ∈ I.powerset,
      |categoricalSubsetMass I (fun _ => 1/((p-M : ℕ) : ℝ)) S -
        bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S|) ≤
          8*((I.card : ℝ)+(M : ℝ))^2/(p : ℝ)^2 := by
  have hpd : 0 < p-M := Nat.sub_pos_of_lt hp
  have hp0 : 0 < p := (Nat.zero_le M).trans_lt hp
  have hq : 0 ≤ 1/((p-M : ℕ) : ℝ) ∧ 1/((p-M : ℕ) : ℝ) ≤ 1 := by
    refine ⟨by positivity,?_⟩
    apply (div_le_one (by exact_mod_cast hpd : (0 : ℝ) < (p-M : ℕ))).mpr
    exact_mod_cast hpd
  have hr : 0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1 := by
    refine ⟨by positivity,?_⟩
    apply (div_le_one (by exact_mod_cast hp0 : (0 : ℝ) < p)).mpr
    exact_mod_cast hp0
  obtain ⟨h1,h2⟩ := unoccupied_reciprocal_estimates p M hp hhalf
  apply (categorical_shift_l1 I _ _ hq hr).trans
  have hcard : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  calc
    _ ≤ 2*((I.card : ℝ)*(2/(p : ℝ)))^2+
        2*(I.card : ℝ)*(2*(M : ℝ)/(p : ℝ)^2) := by gcongr
    _ ≤ 8*((I.card : ℝ)+(M : ℝ))^2/(p : ℝ)^2 := by
      have hnon : 0 ≤ (12*(I.card : ℝ)*(M : ℝ)+8*(M : ℝ)^2)/(p : ℝ)^2 := by positivity
      have he : 8*((I.card : ℝ)+(M : ℝ))^2/(p : ℝ)^2 =
          2*((I.card : ℝ)*(2/(p : ℝ)))^2+2*(I.card : ℝ)*(2*(M : ℝ)/(p : ℝ)^2)+
            (12*(I.card : ℝ)*(M : ℝ)+8*(M : ℝ)^2)/(p : ℝ)^2 := by ring
      rw [he]
      linarith only [hnon]

theorem unoccupied_roots_test_bound {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} [NeZero p] (root : ι → ZMod p)
    (hinj : Set.InjOn root I) (forbidden : Finset (ZMod p))
    (hsize : forbidden.card < p) (hhalf : 2*forbidden.card ≤ p)
    (havoid : ∀ i ∈ I, root i ∉ forbidden)
    (F : Finset ι → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ S ∈ I.powerset, |F S| ≤ L) :
    |(∑ r ∈ univ \ forbidden, F (rootHitSet I root r))/((p-forbidden.card : ℕ) : ℝ) -
      ∑ S ∈ I.powerset, bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S * F S| ≤
        8*L*((I.card : ℝ)+(forbidden.card : ℝ))^2/(p : ℝ)^2 := by
  rw [root_site_uniform_outside_mean I root hinj forbidden hsize havoid F,
    ← sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ S ∈ I.powerset,
        |categoricalSubsetMass I (fun _ => 1/((p-forbidden.card : ℕ) : ℝ)) S -
          bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S| * L := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro S hS
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hF S hS) (abs_nonneg _)
    _ = L*(∑ S ∈ I.powerset,
        |categoricalSubsetMass I (fun _ => 1/((p-forbidden.card : ℕ) : ℝ)) S -
          bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S|) := by rw [← sum_mul]; ring
    _ ≤ L*(8*((I.card : ℝ)+(forbidden.card : ℝ))^2/(p : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (unoccupied_categorical_l1 I p forbidden.card hsize hhalf) hL
    _ = _ := by ring

end JointDickman

end OAI
