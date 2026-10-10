import Mathlib
import OAI.Probability.ThorpCompatibility.ClumpParameters
import OAI.Probability.ThorpCompatibility.Normalization
import OAI.Probability.ThorpCompatibility.VariationalBound

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma log_normalizingFactor_upper (A D : ℕ) (hA : 0 < A) (hD : 0 < D) :
    Real.log ((Nat.factorial (A*D) : ℝ) /
      ((Nat.factorial D : ℝ)^A * (Nat.factorial A : ℝ)^D)) ≤
      (A:ℝ)*D + 1 + Real.log ((A:ℝ)*D) := by
  have hn := log_factorial_upper (A*D) (Nat.mul_pos hA hD)
  rw [Nat.cast_mul] at hn
  have hfA := log_descFactorial_lower A A le_rfl
  have hfD := log_descFactorial_lower D D le_rfl
  simp only [Nat.descFactorial_self] at hfA hfD
  have h₁ := mul_le_mul_of_nonneg_left hfA (Nat.cast_nonneg D : (0:ℝ) ≤ D)
  have h₂ := mul_le_mul_of_nonneg_left hfD (Nat.cast_nonneg A : (0:ℝ) ≤ A)
  have hAa : (A:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hA
  have hDd : (D:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [Real.log_mul hAa hDd] at hn ⊢
  nlinarith

lemma weightedCompatibility_bound {A D : ℕ} {m : ℝ}
    (hm : 4 ≤ m) (hmdef : m^2 = (A:ℝ)*D)
    (hl : 1000 ≤ Real.log m) (hθ : 0 < 1-1000/Real.log m)
    (hAl : m/2 ≤ A) (hAu : (A:ℝ) ≤ 2*m)
    (hDl : m/2 ≤ D) (hDu : (D:ℝ) ≤ 2*m)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2)
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ) :
    weightedCompatibility A D w v ≤
      Real.exp (50000*((A:ℝ)*D)^(54/100:ℝ)) *
        (∏ i, marginalFactor (1-1000/Real.log m) (w i)) *
        (∏ k, marginalFactor (1-1000/Real.log m) (v k)) := by
  have hm0 : 0 < m := by linarith
  have hA0 : 0 < A := by exact_mod_cast (show (0:ℝ) < A by linarith)
  have hD0 : 0 < D := by exact_mod_cast (show (0:ℝ) < D by linarith)
  have hD2 : 2 ≤ D := by exact_mod_cast (show (2:ℝ) ≤ D by linarith)
  let θ : ℝ := 1-1000/Real.log m
  let a : Grid A D → ℝ := compatibilityWeight w v
  have ha : ∀ x, 0 ≤ a x := compatibilityWeight_nonneg w v hw hv
  by_cases hz : (∑ x : Grid A D, a x) = 0
  · have hW : weightedCompatibility A D w v = 0 := by
      change _ * uniformMean a = 0
      rw [uniformMean, hz, zero_div, mul_zero]
    rw [hW]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (Finset.prod_nonneg (fun i _ => marginalFactor_nonneg θ (w i) (hw i))))
      (Finset.prod_nonneg (fun k _ => marginalFactor_nonneg θ (v k) (hv k)))
  have hZ : 0 < ∑ x : Grid A D, a x :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun x _ => ha x)) (Ne.symm hz)
  let Q : Law (Grid A D) := Law.tilt a ha hZ
  have hs (x : Grid A D) (hx : 0 < Q.mass x) : 0 < compatibilityWeight w v x :=
    (div_pos_iff_of_pos_right hZ).mp hx
  have hwr (i : Fin A) : 0 < marginalFactor θ (w i) :=
    (Q.map (fun x => x.1 i)).marginalFactor_pos θ (w i) (hw i)
      (Q.map_support_weight (fun x => x.1 i) (w i) (fun x hx =>
        (compatibilityWeight_support w v hw hv (hs x hx)).2.1 i))
  have hvc (k : Fin D) : 0 < marginalFactor θ (v k) :=
    (Q.map (fun x => x.2 k)).marginalFactor_pos θ (v k) (hv k)
      (Q.map_support_weight (fun x => x.2 k) (v k) (fun x hx =>
        (compatibilityWeight_support w v hw hv (hs x hx)).2.2 k))
  have hWP : 0 < ∏ i, marginalFactor θ (w i) := Finset.prod_pos (fun i _ => hwr i)
  have hVP : 0 < ∏ k, marginalFactor θ (v k) := Finset.prod_pos (fun k _ => hvc k)
  let F : ℝ := (Nat.factorial (A*D) : ℝ) /
      ((Nat.factorial D : ℝ)^A * (Nat.factorial A : ℝ)^D)
  have hF : 0 < F := by dsimp [F]; positivity
  have hU : 0 < uniformMean a := div_pos hZ (by exact_mod_cast Fintype.card_pos)
  have hL : 0 < weightedCompatibility A D w v := mul_pos hF hU
  have hR : 0 < Real.exp (50000*((A:ℝ)*D)^(54/100:ℝ)) *
      (∏ i, marginalFactor θ (w i)) * (∏ k, marginalFactor θ (v k)) :=
    mul_pos (mul_pos (Real.exp_pos _) hWP) hVP
  apply (Real.log_le_log_iff hL hR).mp
  change Real.log (F * uniformMean a) ≤ _
  rw [Real.log_mul hF.ne' hU.ne',
    Real.log_mul (mul_pos (Real.exp_pos _) hWP).ne' hVP.ne',
    Real.log_mul (Real.exp_pos _).ne' hWP.ne', Real.log_exp,
    Real.log_prod (fun i _ => (hwr i).ne'), Real.log_prod (fun k _ => (hvc k).ne')]
  have hnorm := log_normalizingFactor_upper A D hA0 hD0
  change Real.log F ≤ _ at hnorm
  have hcompat := compatibility_log_mean_bound hD2 hm0 hl hθ hmgf w v hw hv hZ
  change Real.log (uniformMean a) ≤ _ at hcompat
  have herr := entropy_normalization_error (by linarith : 1 ≤ m) hA0 hD0 hAu hDu
  have hp : m^(108/100:ℝ) = ((A:ℝ)*D)^(54/100:ℝ) := by
    calc
      _ = m^((2:ℝ)*(54/100:ℝ)) := by norm_num
      _ = (m^(2:ℝ))^(54/100:ℝ) := Real.rpow_mul hm0.le _ _
      _ = _ := by rw [Real.rpow_two, hmdef]
  have hlog : Real.log ((A:ℝ)*D) = 2*Real.log m := by
    rw [← hmdef, Real.log_pow]
    norm_num
  rw [hp] at herr
  rw [hlog] at hnorm
  change 0 < θ at hθ
  change Real.log (uniformMean a) ≤ -(A:ℝ)*D + _ + 1 +
      (∑ i, Real.log (marginalFactor θ (w i))) +
      (∑ k, Real.log (marginalFactor θ (v k))) at hcompat
  linarith

theorem weightedCompatibility_main : WeightedCompatibilityTheorem := by
  have hgood : ∀ᶠ m : ℝ in Filter.atTop,
      4 ≤ m ∧ 1000 ≤ Real.log m ∧ ∀ (A D : ℕ),
      (A:ℝ) ≤ 2*m → m/2 ≤ D → (D:ℝ) ≤ 2*m →
      uniformMean (fun r : Rows A D =>
        Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2 := by
    filter_upwards [Filter.eventually_ge_atTop (4:ℝ),
      Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1000:ℝ)),
      eventual_clump_mgf] with m hm hl hg
    exact ⟨hm,hl,hg⟩
  obtain ⟨b,hb⟩ := Filter.eventually_atTop.mp hgood
  refine ⟨1000,50000,max b 4, by norm_num, by norm_num, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (le_max_right b 4)
  · intro A D n m θ hm hθ hAl hAu hDl hDu w v hw hv
    have hh := hb m (le_trans (le_max_left b 4) hm)
    exact weightedCompatibility_bound hh.1 (Real.sq_sqrt (by positivity))
      hh.2.1 hθ hAl hAu hDl hDu (hh.2.2 A D hAu hDl hDu) w v hw hv

end ThorpCompatibility

theorem weightedCompatibility_main : ThorpCompatibility.WeightedCompatibilityTheorem :=
  ThorpCompatibility.weightedCompatibility_main

end OAI
