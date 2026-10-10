import OAI.Probability.ThorpShuffle.Reachability

namespace OAI

universe uG uΩ uΩ' uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace FiniteLaw
open Conditional

variable {G : Type uG} [Fintype G] [Group G]

def conv (μ ν : G → ℝ) (z : G) : ℝ := ∑ g, μ g * ν (g⁻¹ * z)

theorem conv_fairMass {Ω : Type uΩ} {Ω' : Type uΩ'} [Fintype Ω] [Fintype Ω']
    (a : Ω → G) (b : Ω' → G) :
    conv (fairMass a) (fairMass b) = fairMass (fun p : Ω × Ω' => a p.1 * b p.2) := by
  classical
  funext z
  unfold conv
  rw [fairMass_test]
  change mean (fun ω => mean (fun ω' => if b ω' = (a ω)⁻¹ * z then 1 else 0)) =
    mean (fun p : Ω × Ω' => if a p.1 * b p.2 = z then 1 else 0)
  rw [mean_prod]
  apply mean_congr
  intro ω
  apply mean_congr
  intro ω'
  rw [eq_inv_mul_iff_mul_eq]

theorem sum_inv_mul (f : G → ℝ) (z : G) : ∑ g, f (g⁻¹ * z) = ∑ g, f g := by
  exact Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulRight z)) f

theorem sum_mul_left (f : G → ℝ) (g : G) : ∑ z, f (g * z) = ∑ z, f z :=
  Equiv.sum_comp (Equiv.mulLeft g) f

theorem conv_uniform (μ : G → ℝ) (hμ : ∑ g, μ g = 1) :
    conv μ (fun _ => (1 : ℝ) / Fintype.card G) = fun _ => (1 : ℝ) / Fintype.card G := by
  funext z
  simp only [conv, ← Finset.sum_mul, hμ, one_mul]

theorem tv_conv_contract (μ ν : G → ℝ) (hμ : ∑ g, μ g = 1)
    (hν : ∑ g, ν g = 1) (c : ℝ) (hc : ∀ g, c ≤ μ g) :
    tv (conv μ ν) (fun _ => (1 : ℝ) / Fintype.card G) ≤
      (1 - (Fintype.card G : ℝ) * c) * tv ν (fun _ => (1 : ℝ) / Fintype.card G) := by
  let u : ℝ := 1 / Fintype.card G
  have hu : ∑ _ : G, u = 1 := by simp [u, Fintype.card_ne_zero]
  have hcenter (z : G) : ∑ g, (ν (g⁻¹ * z) - u) = 0 := by
    rw [Finset.sum_sub_distrib, sum_inv_mul, hν, hu, sub_self]
  have hid (z : G) : conv μ ν z - u = ∑ g, (μ g - c) * (ν (g⁻¹ * z) - u) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hcenter, mul_zero, sub_zero]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ, one_mul, conv]
  have hb : ∑ z, |conv μ ν z - u| ≤
      (1 - (Fintype.card G : ℝ) * c) * ∑ z, |ν z - u| := by
    calc
      _ = ∑ z, |∑ g, (μ g - c) * (ν (g⁻¹ * z) - u)| := by simp_rw [hid]
      _ ≤ ∑ z, ∑ g, (μ g - c) * |ν (g⁻¹ * z) - u| := by
        apply Finset.sum_le_sum
        intro z _
        have h := Finset.abs_sum_le_sum_abs (fun g => (μ g - c) * (ν (g⁻¹ * z) - u)) Finset.univ
        simpa only [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hc _))] using h
      _ = (∑ g, (μ g - c)) * ∑ z, |ν z - u| := by
        rw [Finset.sum_comm, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        rw [← Finset.mul_sum, sum_mul_left (fun z => |ν z - u|)]
      _ = _ := by simp [Finset.sum_sub_distrib, hμ]
  unfold tv
  change (1 / 2 : ℝ) * (∑ z, |conv μ ν z - u|) ≤ _
  nlinarith

omit [Fintype G] [Group G] in

theorem fairMass_lower_of_surjective {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω]
    (a : Ω → G) (ha : Function.Surjective a) (g : G) :
    1 / (Fintype.card Ω : ℝ) ≤ fairMass a g := by
  classical
  obtain ⟨ω, hω⟩ := ha g
  unfold fairMass
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := Finset.single_le_sum (f := fun ω => if a ω = g then (1 : ℝ) else 0)
    (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ ω)
  simpa only [hω, ↓reduceIte] using h

end FiniteLaw

theorem fairMass_eq_mean {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [DecidableEq α] (f : Ω → α) (a : α) :
    fairMass f a = Conditional.mean (fun ω => if f ω = a then (1 : ℝ) else 0) := by
  classical
  unfold fairMass Conditional.mean
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  dsimp only
  split_ifs <;> rfl

theorem law_add (d s t : ℕ) :
    law d (s + t) = FiniteLaw.conv (law d t) (law d s) := by
  classical
  rw [law, law, law, FiniteLaw.conv_fairMass]
  funext z
  rw [fairMass_eq_mean, fairMass_eq_mean]
  rw [Conditional.mean_history_add, Conditional.mean_prod, Conditional.mean_comm]
  simp only [Reachability.run_append]

namespace Reachability

theorem exists_surjective_run (d : ℕ) :
    ∃ T : ℕ, Function.Surjective (run (d + 1) T) := by
  classical
  choose t ht ω hω using attainable_return d
  let T : ℕ := ∑ g : State (d + 1), t g
  have hT : orderOf (rotate (d + 1)) ∣ T := Finset.dvd_sum (fun g _ => ht g)
  refine ⟨T, fun g => ?_⟩
  have hle : t g ≤ T := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  have hdvd : orderOf (rotate (d + 1)) ∣ T - t g := Nat.dvd_sub hT (ht g)
  have hid : run (d + 1) (T - t g) (fun _ => zeroCoins d) = 1 := by
    rw [run_false]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hh : ∃ a : History (d + 1) (t g + (T - t g)),
      run (d + 1) (t g + (T - t g)) a = g := by
    refine ⟨Fin.append (ω g) (fun _ => zeroCoins d), ?_⟩
    rw [run_append, hid, one_mul, hω]
  have he : t g + (T - t g) = T := by omega
  rw [he] at hh
  exact hh

end Reachability

end Thorp

end

end OAI
