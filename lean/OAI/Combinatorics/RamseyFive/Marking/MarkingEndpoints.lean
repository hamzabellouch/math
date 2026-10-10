import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.HighGeometryClosure
import OAI.Combinatorics.RamseyFive.Marking.TwoScan

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
local instance markingEndpointsPointDecEq : DecidableEq (ℙ K V) := Classical.decEq _
local instance markingEndpointsDualDecEq : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance markingEndpointsPairDecEq : DecidableEq (FlagPair K V) := Classical.decEq _

omit [Finite K] [FiniteDimensional K V] in
lemma mem_popularDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r l : ℕ) (z : FlagPair K V) : z∈popularDomain W r l ↔
    finrank K (W z.2)=r ∧ ((levelSet W l).card:ℝ)/(16*Nat.card K)≤
      memberships W (levelSet W l) z.2 ∧ z.1.submodule≤(W z.2).dualCoannihilator := by
  simp only [popularDomain,Finset.mem_filter,Finset.mem_product,Finset.mem_univ,true_and]
  tauto

omit [Finite K] [FiniteDimensional K V] in
lemma mem_poorDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r l : ℕ) (z : FlagPair K V) : z∈poorDomain W r l ↔
    (((levelSet W l).filter fun y=>Incident z.1 y).card:ℝ)≤
      ((levelSet W l).card:ℝ)/(8*Nat.card K) ∧ finrank K (W z.2)≤r ∧
      Incident z.1 z.2 := by
  simp only [poorDomain,Finset.mem_filter,Finset.mem_product,Finset.mem_univ,
    true_and,upperSet]
  tauto

omit [FiniteDimensional K V] in
lemma typed_popular_second (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r : Fin 5) :
    (((typedDomain W r true).image Prod.snd).card:ℝ)≤32*(Nat.card K:ℝ)^r.val := by
  unfold typedDomain
  simp only [↓reduceIte]
  split_ifs with hz
  · have hsub : (popularDomain W r.val (chooseLevel W r.val)).image Prod.snd ⊆
        Finset.univ.filter fun b : ℙ K (Dual K V)=>
          ((levelSet W (chooseLevel W r.val)).card:ℝ)/(16*Nat.card K)≤
            memberships W (levelSet W (chooseLevel W r.val)) b := by
      intro b hb
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_popularDomain _ _ _ _).mp hz |>.2.1⟩
    have hc := popular_count W _ hz (chooseLevel W r.val)
      (fun y hy=>(Finset.mem_filter.mp hy).2)
    have hc' : ((((popularDomain W r.val (chooseLevel W r.val)).image Prod.snd).card):ℝ)≤
        32*(Nat.card K:ℝ)^(chooseLevel W r.val) :=
      (show _ ≤ (_:ℝ) from by exact_mod_cast Finset.card_le_card hsub).trans hc
    exact hc'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by exact_mod_cast (Finite.one_lt_card (α:=K)).le)
        (chooseLevel_le W r.val)) (by norm_num))
  · simp only [Finset.image_empty,Finset.card_empty,Nat.cast_zero]
    positivity

lemma typed_popular_partner (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5) (b : ℙ K (Dual K V)) :
    ((Finset.univ.filter fun a=>(a,b)∈typedDomain W r true).card:ℝ)≤
      2*(Nat.card K:ℝ)^(4-r.val) := by
  unfold typedDomain
  simp only [↓reduceIte]
  split_ifs with hz
  · by_cases hr : finrank K (W b)=r.val
    · have hsub : (Finset.univ.filter fun a=>(a,b)∈popularDomain W r.val (chooseLevel W r.val)) ⊆
          Finset.univ.filter fun a : ℙ K V=>a.submodule≤(W b).dualCoannihilator := by
        intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ((mem_popularDomain _ _ _ _).mp (Finset.mem_filter.mp ha).2).2.2⟩
      have hc : ((Finset.univ.filter fun a=>(a,b)∈popularDomain W r.val (chooseLevel W r.val)).card:ℝ) ≤
          ((Finset.univ.filter fun a : ℙ K V=>a.submodule≤(W b).dualCoannihilator).card:ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hc.trans (coannihilator_card_bound hdim _ _ hr (by omega))
    · have he : (Finset.univ.filter fun a=>(a,b)∈popularDomain W r.val (chooseLevel W r.val))=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hr ((mem_popularDomain _ _ _ _).mp (Finset.mem_filter.mp ha).2).1
      rw [he]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  · have he : (Finset.univ.filter fun a : ℙ K V=>(a,b)∈(∅:Finset (FlagPair K V)))=∅ := by
      ext a
      simp only [Finset.mem_filter,Finset.notMem_empty,and_false]
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

omit [Finite K] [FiniteDimensional K V] in
lemma typed_poor_second (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5) :
    (((typedDomain W r false).image Prod.snd).card:ℝ)≤
      5*((levelSet W (chooseLevel W r.val)).card:ℝ) := by
  unfold typedDomain
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs with hz
  · have hsub : (poorDomain W r.val (chooseLevel W r.val)).image Prod.snd⊆upperSet W r.val := by
      intro b hb
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((mem_poorDomain _ _ _ _).mp hz).2.1⟩
    have hc : ((upperSet W r.val).card:ℝ)≤5*((levelSet W (chooseLevel W r.val)).card:ℝ) := by
      exact_mod_cast (chooseLevel_large W r.val).trans (Nat.mul_le_mul_right _ (by omega))
    exact (show _ ≤ (_:ℝ) from by exact_mod_cast Finset.card_le_card hsub).trans hc
  · simp only [Finset.image_empty,Finset.card_empty,Nat.cast_zero]
    positivity

lemma typed_poor_first (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5) :
    (((typedDomain W r false).image Prod.fst).card:ℝ)*
      ((levelSet W (chooseLevel W r.val)).card:ℝ)≤16*(Nat.card K:ℝ)^5 := by
  let A := (typedDomain W r false).image Prod.fst
  let Z := levelSet W (chooseLevel W r.val)
  apply sparse_rectangle_size (d:=4) hdim (by decide) A Z
  rw [incidences_eq_degrees]
  have hpoor (a : ℙ K V) (ha : a∈A) :
      ((Z.filter fun y=>Incident a y).card:ℝ)≤(Z.card:ℝ)/(8*Nat.card K) := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    unfold typedDomain at hz
    simp only [Bool.false_eq_true, ↓reduceIte] at hz
    split_ifs at hz with hn
    · have hh : z∈poorDomain W r.val (chooseLevel W r.val) := hz
      exact ((mem_poorDomain W r.val (chooseLevel W r.val) z).mp hh).1
    · exact False.elim (Finset.notMem_empty _ hz)
  calc
    _ ≤ ∑ _a∈A,(Z.card:ℝ)/(8*Nat.card K) := Finset.sum_le_sum hpoor
    _ = (A.card:ℝ)*Z.card/(8*Nat.card K) := by simp; ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by
      have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
      positivity) (by nlinarith [Nat.cast_nonneg (α:=ℝ) (Nat.card K)])

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators

def clampParameter (q M : ℝ) : ℝ := max (Real.log q) (min (4*Real.log q) (Real.log M))

lemma exp_clampParameter {q M : ℝ} (hq : 0<q) (hM : 0<M) :
    Real.exp (clampParameter q M)=max q (min (q^4) M) := by
  unfold clampParameter
  rw [Real.exp_monotone.map_max, Real.exp_monotone.map_min, Real.exp_log hq,
    show (4:ℝ)*Real.log q=(4:ℕ)*Real.log q by norm_num, Real.exp_nat_mul,
    Real.exp_log hq, Real.exp_log hM]

lemma clampParameter_bounds {q M : ℝ} (hq : 1≤q) :
    Real.log q≤clampParameter q M ∧ clampParameter q M≤4*Real.log q := by
  have hs : 0≤Real.log q := Real.log_nonneg hq
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

lemma clamped_reciprocal_caps {q M A B : ℝ} (hq : 1≤q) (hM : 0<M)
    (hA : 0≤A) (_hB : 0≤B) (hAa : A≤2*q^4) (hBa : B≤2*q^4)
    (hAM : A*M≤16*q^5) (hBM : B≤5*M) :
    A≤32*Real.exp (5*Real.log q-clampParameter q M) ∧
    B≤32*Real.exp (clampParameter q M) := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hq4 : q≤q^4 := by nlinarith [sq_nonneg (q-1), sq_nonneg (q^2-1)]
  have hexp := exp_clampParameter hq0 hM
  have hnum : Real.exp (5*Real.log q)=q^5 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hq0] using Real.exp_nat_mul (Real.log q) 5
  rw [Real.exp_sub, hnum, hexp, ←mul_div_assoc]
  by_cases hMq : M≤q
  · have he : max q (min (q^4) M)=q := max_eq_left ((min_le_right _ _).trans hMq)
    rw [he]
    constructor
    · apply (le_div_iff₀ hq0).mpr
      nlinarith [mul_le_mul_of_nonneg_right hAa hq0.le, pow_pos hq0 5]
    · linarith
  · by_cases hM4 : M≤q^4
    · have he : max q (min (q^4) M)=M := by rw [min_eq_right hM4, max_eq_right (le_of_not_ge hMq)]
      rw [he]
      constructor
      · apply (le_div_iff₀ hM).mpr
        nlinarith [pow_pos hq0 5]
      · linarith
    · have he : max q (min (q^4) M)=q^4 := by rw [min_eq_left (le_of_not_ge hM4),max_eq_right hq4]
      rw [he]
      constructor
      · apply (le_div_iff₀ (pow_pos hq0 4)).mpr
        have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hM4) hA
        nlinarith [pow_pos hq0 5]
      · linarith

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
local instance clampedPointDecEq : DecidableEq (ℙ K V) := Classical.decEq _
local instance clampedDualDecEq : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance clampedPairDecEq : DecidableEq (FlagPair K V) := Classical.decEq _

omit [Finite K] [FiniteDimensional K V] in
lemma typedDomain_level_nonempty (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r : Fin 5) (pop : Bool) (h : (typedDomain W r pop).Nonempty) :
    (levelSet W (chooseLevel W r.val)).Nonempty := by
  by_contra hn
  rw [typedDomain, ite_eq_right hn] at h
  exact Finset.not_nonempty_empty h

theorem typed_poor_reciprocal (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5)
    (h : (typedDomain W r false).Nonempty) :
    let u:=clampParameter (Nat.card K) (levelSet W (chooseLevel W r.val)).card
    (((typedDomain W r false).image Prod.fst).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u) ∧
    (((typedDomain W r false).image Prod.snd).card:ℝ)≤32*Real.exp u := by
  have hq : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have hcA : Fintype.card (ℙ K V)≤2*Nat.card K^4 := projective_card_le_two_pow hdim hq
  have hcB : Fintype.card (ℙ K (Dual K V))≤2*Nat.card K^4 :=
    projective_card_le_two_pow (by simpa using hdim) hq
  apply clamped_reciprocal_caps (by exact_mod_cast (show 1≤Nat.card K by omega))
    (by exact_mod_cast (typedDomain_level_nonempty W r false h).card_pos) (by positivity) (by positivity)
  · exact_mod_cast (Finset.card_le_univ _).trans hcA
  · exact_mod_cast (Finset.card_le_univ _).trans hcB
  · exact typed_poor_first hdim W r
  · exact typed_poor_second W r

end SharpRamseyFive.Marking

end

end OAI
