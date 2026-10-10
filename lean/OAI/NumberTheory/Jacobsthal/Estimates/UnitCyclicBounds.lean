import OAI.NumberTheory.Jacobsthal.Harmonic.CharacterChord
import OAI.NumberTheory.Jacobsthal.Sieve.DivisorHarmonic

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbola

theorem harmonicWeight_eq (N : ℕ) : harmonicWeight N = (harmonic N : ℝ) := by
  simp only [harmonicWeight,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,
    Rat.cast_natCast,one_div]

noncomputable def harmonicConstant : ℝ := 1 + 1/Real.log 2

theorem harmonicConstant_pos : 0 < harmonicConstant := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold harmonicConstant
  positivity

theorem harmonicWeight_log_le (N : ℕ) (hN : 0 < N) :
    harmonicWeight N ≤ harmonicConstant * Real.log (2*(N : ℝ)) := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : Real.log 2 ≤ Real.log (2*(N : ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have h1 : (1 : ℝ) ≤ Real.log (2*(N : ℝ))/Real.log 2 :=
    (le_div_iff₀ htwo).mpr (by simpa using h2)
  have hlog : Real.log (N : ℝ) ≤ Real.log (2*(N : ℝ)) :=
    Real.log_le_log hp (by linarith)
  calc
    _ ≤ 1+Real.log (N : ℝ) := by rw [harmonicWeight_eq]; exact harmonic_le_one_add_log N
    _ ≤ Real.log (2*(N : ℝ))/Real.log 2+Real.log (2*(N : ℝ)) :=
      add_le_add h1 hlog
    _ = _ := by unfold harmonicConstant; ring

theorem gcd_harmonic_log_le (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc 1 N, Real.sqrt (Nat.gcd n N)/(n : ℝ)) ≤
      (N.divisors.card : ℝ)*harmonicConstant*Real.log (2*(N : ℝ)) := by
  calc
    _ ≤ (N.divisors.card : ℝ)*harmonicWeight N := gcd_harmonic_sum_le N hN
    _ ≤ (N.divisors.card : ℝ)*(harmonicConstant*Real.log (2*(N : ℝ))) :=
      mul_le_mul_of_nonneg_left (harmonicWeight_log_le N hN) (Nat.cast_nonneg _)
    _ = _ := by ring

end ErdosHyperbola

end

section

open scoped BigOperators

namespace ErdosHyperbola

open ErdosHyperbolaFourier

attribute [local instance] Classical.decEq

theorem cyclic_weight_sum_le (N : ℕ) [NeZero N] (w : ZMod N → ℝ)
    (hw : ∀ r, 0 ≤ w r) (heven : ∀ r, w (-r) = w r) :
    (∑ r : ZMod N, w r/(cyclicDistance N r : ℝ)) ≤
      2 * ∑ r : ZMod N, w r/(r.val : ℝ) := by
  have hp (r : ZMod N) :
      w r/(cyclicDistance N r : ℝ) ≤ w r/(r.val : ℝ) + w (-r)/((-r).val : ℝ) := by
    by_cases hr : r = 0
    · simp [hr,cyclicDistance]
    have hneg : (-r).val = N-r.val := by rw [ZMod.neg_val,ite_eq_right hr]
    have hdist : (cyclicDistance N r : ℝ) = min (r.val : ℝ) ((-r).val : ℝ) := by
      simp only [cyclicDistance,Nat.cast_min,hneg]
    rw [hdist,heven r]
    rcases le_total (r.val : ℝ) ((-r).val : ℝ) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (div_nonneg (hw _) (Nat.cast_nonneg _))
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (div_nonneg (hw _) (Nat.cast_nonneg _))
  have hsym : (∑ r : ZMod N,w (-r)/((-r).val : ℝ)) =
      ∑ r : ZMod N,w r/(r.val : ℝ) := by
    have h := Equiv.sum_comp (Equiv.neg (ZMod N)) (fun r => w r/(r.val : ℝ))
    simpa only [Equiv.neg_apply] using h
  calc
    _ ≤ ∑ r : ZMod N,(w r/(r.val : ℝ) + w (-r)/((-r).val : ℝ)) :=
      Finset.sum_le_sum (fun r _ => hp r)
    _ = _ := by rw [Finset.sum_add_distrib,hsym]; ring

theorem sum_representatives_le (N : ℕ) [NeZero N] (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0) :
    (∑ r : ZMod N, f r.val) ≤ ∑ n ∈ Finset.Icc 1 N, f n := by
  let S := (Finset.univ : Finset (ZMod N)).filter (· ≠ 0)
  have hzero : (∑ r ∈ S,f r.val) = ∑ r : ZMod N,f r.val := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : r = 0 <;> simp [hr,hf0]
  have hi : Set.InjOn (ZMod.val : ZMod N → ℕ) (S : Set (ZMod N)) :=
    (ZMod.val_injective N).injOn
  have hsub : S.image ZMod.val ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hn
    have hr0 := (Finset.mem_filter.mp hr).2
    have hval : 0 < r.val := Nat.pos_of_ne_zero (fun hz => hr0 ((ZMod.val_eq_zero r).mp hz))
    exact Finset.mem_Icc.mpr ⟨hval,r.val_lt.le⟩
  rw [← hzero]
  calc
    _ = ∑ n ∈ S.image ZMod.val,f n := by
      rw [Finset.sum_image]
      exact fun a ha b hb h => hi ha hb h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

end ErdosHyperbola

end

section

namespace ErdosHyperbolaWeighted

theorem log_two_mul_le_power {eps x : ℝ} (heps : 0 < eps) (hx : 0 < x) :
    Real.log (2*x) ≤ ((2 : ℝ)^eps/eps)*x^eps := by
  have h := Real.add_one_le_exp (eps*Real.log (2*x))
  have he : Real.exp (eps*Real.log (2*x)) = (2*x)^eps := by
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  rw [he, Real.mul_rpow (by norm_num) hx.le] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ heps).mpr
  nlinarith

end ErdosHyperbolaWeighted

end

section

open scoped BigOperators

namespace ErdosHyperbola

open ErdosHyperbolaFourier

theorem gcd_val_neg (N : ℕ) [NeZero N] (r : ZMod N) :
    Nat.gcd (-r).val N = Nat.gcd r.val N := by
  by_cases hr : r = 0
  · simp [hr]
  rw [ZMod.neg_val,ite_eq_right hr]
  exact Nat.gcd_self_sub_left r.val_lt.le

theorem cyclic_inverse_sum_le (N : ℕ) [NeZero N] :
    (∑ r : ZMod N, 1/(cyclicDistance N r : ℝ)) ≤
      (2*harmonicConstant)*Real.log (2*(N : ℝ)) := by
  have h := cyclic_weight_sum_le N (fun _ => 1) (fun _ => zero_le_one) (fun _ => rfl)
  have hr : (∑ r : ZMod N,1/(r.val : ℝ)) ≤ harmonicWeight N :=
    sum_representatives_le N (fun n => 1/(n : ℝ)) (fun _ => by positivity) (by simp)
  calc
    _ ≤ 2*harmonicWeight N := h.trans (mul_le_mul_of_nonneg_left hr (by norm_num))
    _ ≤ 2*(harmonicConstant*Real.log (2*(N : ℝ))) :=
      mul_le_mul_of_nonneg_left (harmonicWeight_log_le N (NeZero.pos N)) (by norm_num)
    _ = _ := by ring

theorem sqrt_gcd_cyclic_sum_le (N : ℕ) [NeZero N] :
    (∑ r : ZMod N, Real.sqrt (Nat.gcd r.val N)/(cyclicDistance N r : ℝ)) ≤
      (2*harmonicConstant)*(N.divisors.card : ℝ)*Real.log (2*(N : ℝ)) := by
  have heven (r : ZMod N) : Real.sqrt (Nat.gcd (-r).val N) = Real.sqrt (Nat.gcd r.val N) := by
    rw [gcd_val_neg]
  have h := cyclic_weight_sum_le N (fun r => Real.sqrt (Nat.gcd r.val N))
    (fun _ => Real.sqrt_nonneg _) heven
  have hr : (∑ r : ZMod N, Real.sqrt (Nat.gcd r.val N)/(r.val : ℝ)) ≤
      (N.divisors.card : ℝ)*harmonicWeight N :=
    (sum_representatives_le N (fun n => Real.sqrt (Nat.gcd n N)/(n : ℝ))
      (fun _ => by positivity) (by simp)).trans (gcd_harmonic_sum_le N (NeZero.pos N))
  calc
    _ ≤ 2*((N.divisors.card : ℝ)*harmonicWeight N) :=
      h.trans (mul_le_mul_of_nonneg_left hr (by norm_num))
    _ ≤ 2*((N.divisors.card : ℝ)*(harmonicConstant*Real.log (2*(N : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (harmonicWeight_log_le N (NeZero.pos N)) (Nat.cast_nonneg _))
        (by norm_num)
    _ = _ := by ring

end ErdosHyperbola

end

section

open scoped BigOperators

namespace ErdosHyperbola

open ErdosHyperbolaFourier

def mulUnitEquiv (N : ℕ) (u : (ZMod N)ˣ) : ZMod N ≃ ZMod N where
  toFun r := r*(u : ZMod N)
  invFun r := r*(↑u⁻¹ : ZMod N)
  left_inv r := by simp [mul_assoc]
  right_inv r := by simp [mul_assoc]

@[simp] theorem mulUnitEquiv_apply (N : ℕ) (u : (ZMod N)ˣ) (r : ZMod N) :
    mulUnitEquiv N u r = r*(u : ZMod N) := rfl

theorem gcd_mul_unit (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (r : ZMod N) :
    Nat.gcd (r*(u : ZMod N)).val N = Nat.gcd r.val N := by
  have hu : u.val.val.Coprime N := (ZMod.isUnit_iff_coprime u.val.val N).mp
    (by simpa only [ZMod.natCast_zmod_val] using u.isUnit)
  have he : r*(u : ZMod N) = ((r.val*u.val.val : ℕ) : ZMod N) := by simp
  rw [he,ZMod.val_natCast,← Nat.gcd_rec,Nat.gcd_comm N,hu.gcd_mul_right_cancel]

theorem unit_cyclic_inverse_sum_le (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (∑ r : ZMod N,1/(cyclicDistance N (r*(u : ZMod N)) : ℝ)) ≤
      (2*harmonicConstant)*Real.log (2*(N : ℝ)) := by
  have he := Equiv.sum_comp (mulUnitEquiv N u)
    (fun r => 1/(cyclicDistance N r : ℝ))
  simp only [mulUnitEquiv_apply] at he
  rw [he]
  exact cyclic_inverse_sum_le N

theorem unit_sqrt_gcd_cyclic_sum_le (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (∑ r : ZMod N,Real.sqrt (Nat.gcd r.val N)/
      (cyclicDistance N (r*(u : ZMod N)) : ℝ)) ≤
      (2*harmonicConstant)*(N.divisors.card : ℝ)*Real.log (2*(N : ℝ)) := by
  have he := Equiv.sum_comp (mulUnitEquiv N u)
    (fun r => Real.sqrt (Nat.gcd r.val N)/(cyclicDistance N r : ℝ))
  simp only [mulUnitEquiv_apply,gcd_mul_unit] at he
  rw [he]
  exact sqrt_gcd_cyclic_sum_le N

end ErdosHyperbola

end

end Erdos970

end OAI
