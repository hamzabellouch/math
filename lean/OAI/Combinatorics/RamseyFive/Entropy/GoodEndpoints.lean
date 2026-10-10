import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BlockReveal

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

theorem scaled_heavy_atom_mass (p : Law α) (N M K : ℝ) (hN : 0 < N) (hK : 0 < K)
    (hcap : ((support p).card:ℝ) ≤ M) :
    eventProbability p (Finset.univ.filter fun a => N*p a > Real.exp K) ≤
      (Real.log N-entropy p+M/N)/K := by
  let E := Finset.univ.filter fun a => N*p a > Real.exp K
  have hpoint (a : α) :
      (if a ∈ E then K*p a else 0)-(if a ∈ support p then 1/N else 0) ≤
        p a*Real.log (N*p a) := by
    by_cases hp : p a=0
    · have hE : a ∉ E := by simp only [E,Finset.mem_filter,Finset.mem_univ,true_and,hp,mul_zero]; exact (Real.exp_pos K).not_gt
      have hs : a ∉ support p := by simp [mem_support,hp]
      simp only [hp,hE,hs,ite_false,sub_zero,zero_mul,le_refl]
    · have hp' := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
      have hs := (mem_support p a).mpr hp'
      by_cases he : a ∈ E
      · have hh : Real.exp K < N*p a := (Finset.mem_filter.mp he).2
        have hl : K ≤ Real.log (N*p a) := (Real.le_log_iff_exp_le (by positivity)).mpr hh.le
        simp only [he,hs,ite_true]
        nlinarith [mul_le_mul_of_nonneg_right hl (p.nonneg a),div_pos zero_lt_one hN]
      · have hh := point_log_ratio (p a) (1/N) (p.nonneg a) (by positivity) (fun _ => by positivity)
        have heq : p a/(1/N)=N*p a := by field_simp
        rw [heq] at hh
        simp only [he,hs,ite_false,ite_true,zero_sub]
        nlinarith [p.nonneg a]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  have hlog : (∑ a,p a*Real.log (N*p a))=Real.log N-entropy p := by
    calc
      _ = ∑ a,(p a*Real.log N+p a*Real.log (p a)) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases hp : p a=0
        · simp [hp]
        · rw [Real.log_mul (ne_of_gt hN) hp]
          ring
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.sum_mul,p.sum_one,one_mul]; simp only [entropy,sub_neg_eq_add]
  rw [Finset.sum_sub_distrib,hlog] at h
  have he : (∑ a,if a ∈ E then K*p a else 0)=K*eventProbability p E := by
    rw [Finset.sum_ite_mem,Finset.univ_inter]
    simp only [eventProbability,Finset.mul_sum]
  have hs : (∑ a,if a ∈ support p then 1/N else 0)=((support p).card:ℝ)/N := by
    rw [Finset.sum_ite_mem]
    simp [div_eq_mul_inv]
  rw [he,hs] at h
  have hfrac : ((support p).card:ℝ)/N ≤ M/N := div_le_div_of_nonneg_right hcap hN.le
  apply (le_div_iff₀ hK).mpr
  dsimp [E] at h
  nlinarith

lemma small_atom_mass (p : Law α) (N K : ℝ) (hN : 0<N)
    (hcap : ((support p).card : ℝ) ≤ N) :
    eventMass p (Finset.univ.filter fun a => p a < Real.exp (-K)/N) ≤ Real.exp (-K) := by
  let E := Finset.univ.filter fun a => p a < Real.exp (-K)/N
  have hp (a : α) : (if a ∈ E then p a else 0) ≤
      if a ∈ support p then Real.exp (-K)/N else 0 := by
    by_cases hs : a ∈ support p
    · simp only [hs,ite_true]
      split_ifs with he
      · exact (Finset.mem_filter.mp he).2.le
      · positivity
    · have hz := outside_support p hs
      simp [hs,hz]
  have hh := Finset.sum_le_sum fun a (_ : a∈Finset.univ) => hp a
  calc
    _ = ∑ a, if a∈E then p a else 0 := by simp [eventMass, E, Finset.sum_filter]
    _ ≤ ∑ a, if a ∈ support p then Real.exp (-K)/N else 0 := hh
    _ = (support p).card * (Real.exp (-K)/N) := by simp [Finset.sum_ite_mem]
    _ ≤ N * (Real.exp (-K)/N) := mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = Real.exp (-K) := by field_simp

def heavyRow (p : Law (α × β)) (N K : ℝ) (a : α) : Finset β :=
  Finset.univ.filter fun b => Real.exp K < N*p (a,b)

def goodFirstEndpoints (p : Law (α × β)) (NA N K : ℝ) : Finset α :=
  Finset.univ.filter fun a => Real.exp (-K)/NA ≤ first p a ∧
    eventMass (fiber p a) (heavyRow p N K a) ≤ (1:ℝ)/50

lemma weighted_heavy_rows (p : Law (α × β)) (N K : ℝ) :
    (∑ a,first p a * eventMass (fiber p a) (heavyRow p N K a)) =
      eventProbability p (Finset.univ.filter fun z => Real.exp K < N*p z) := by
  simp only [eventMass,heavyRow,eventProbability,Finset.sum_filter,Finset.mul_sum,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp only [mul_zero, mass_eq_first_mul_fiber]

lemma bad_conditional_row_mass (p : Law (α × β)) (N K : ℝ) :
    eventMass (first p) (Finset.univ.filter fun a =>
      (1:ℝ)/50 < eventMass (fiber p a) (heavyRow p N K a)) ≤
      50 * eventProbability p (Finset.univ.filter fun z => Real.exp K < N*p z) := by
  rw [←weighted_heavy_rows, Finset.mul_sum]
  unfold eventMass
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with ha
  · have hn := (first p).nonneg a
    nlinarith
  · exact mul_nonneg (by norm_num) (mul_nonneg ((first p).nonneg a)
      (Finset.sum_nonneg fun b _ => (fiber p a).nonneg b))

theorem bad_first_endpoint_mass (p : Law (α × β)) (NA N M K : ℝ)
    (hNA : 0<NA) (hN : 0<N) (hK : 0<K)
    (hA : ((support (first p)).card : ℝ) ≤ NA)
    (hflag : ((support p).card : ℝ) ≤ M) :
    eventMass (first p) (goodFirstEndpoints p NA N K)ᶜ ≤
      Real.exp (-K) + 50*(Real.log N-entropy p+M/N)/K := by
  let A := Finset.univ.filter fun a => first p a < Real.exp (-K)/NA
  let B := Finset.univ.filter fun a => (1:ℝ)/50 < eventMass (fiber p a) (heavyRow p N K a)
  have hsub : (goodFirstEndpoints p NA N K)ᶜ ⊆ A ∪ B := by
    intro a ha
    simp only [goodFirstEndpoints,Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and] at ha
    simp only [A,B,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases h : first p a < Real.exp (-K)/NA
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge (fun hb => ha ⟨le_of_not_gt h,hb⟩))
  have hmass : eventMass (first p) (goodFirstEndpoints p NA N K)ᶜ ≤
      eventMass (first p) A + eventMass (first p) B := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => (first p).nonneg a))
    have hle (a : α) : (if a ∈ A ∪ B then first p a else 0) ≤
        (if a ∈ A then first p a else 0)+(if a ∈ B then first p a else 0) := by
      by_cases ha : a ∈ A <;> by_cases hb : a ∈ B <;>
        simp [ha,hb,(first p).nonneg a]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hle a)
    simpa only [eventMass,Finset.sum_add_distrib, Finset.sum_ite_mem,Finset.univ_inter] using hh
  have ha := small_atom_mass (first p) NA K hNA hA
  have hb := bad_conditional_row_mass p N K
  have hc := scaled_heavy_atom_mass p N M K hN hK hflag
  dsimp only [A,B] at hmass
  have hh := add_le_add ha (hb.trans (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤50)))
  apply hmass.trans
  convert hh using 1; ring

lemma goodFirst_positive (p : Law (α × β)) (NA N K : ℝ) (hNA : 0<NA)
    (a : α) (ha : a ∈ goodFirstEndpoints p NA N K) : 0 < first p a := by
  exact (div_pos (Real.exp_pos _) hNA).trans_le (Finset.mem_filter.mp ha).2.1

lemma goodFirst_conditional_cap (p : Law (α × β)) (NA N K : ℝ)
    (hNA : 0<NA) (hN : 0<N) (a : α) (ha : a∈goodFirstEndpoints p NA N K)
    (b : β) (hb : b ∉ heavyRow p N K a) :
    fiber p a b ≤ Real.exp (2*K)*NA/N := by
  have hlo := (Finset.mem_filter.mp ha).2.1
  have hfp := goodFirst_positive p NA N K hNA a ha
  have hj : N*p (a,b) ≤ Real.exp K := by
    simpa only [heavyRow,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hb
  have hscale : (Real.exp (-K)/NA) * (Real.exp (2*K)*NA/N) = Real.exp K/N := by
    have hexp : Real.exp (-K) * Real.exp (2*K) = Real.exp K := by rw [←Real.exp_add]; congr 1; ring
    rw [div_mul_div_comm]
    calc
      _ = (Real.exp (-K)*Real.exp (2*K))/N := by field_simp
      _ = _ := by rw [hexp]
  have hprod := mul_le_mul_of_nonneg_right hlo (show 0 ≤ Real.exp (2*K)*NA/N by positivity)
  rw [hscale] at hprod
  have hmass : first p a * fiber p a b ≤ Real.exp K/N := by
    rw [←mass_eq_first_mul_fiber]
    exact (le_div_iff₀ hN).mpr (by simpa [mul_comm] using hj)
  exact (mul_le_mul_iff_right₀ hfp).mp (hmass.trans hprod)
end
end SharpRamseyFive.FiniteEntropy

end OAI
