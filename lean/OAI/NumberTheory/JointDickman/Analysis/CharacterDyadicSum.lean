import OAI.NumberTheory.JointDickman.Analysis.CharacterLogPhase
import OAI.NumberTheory.JointDickman.Amplification.IntegerPartialSummation

namespace OAI

/-! # Weighted character sums on a dyadic interval -/
namespace JointDickman
open Complex Filter Finset
open scoped Topology

lemma character_cpow_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) {n : ℤ} (hn : 0 < n) :
    χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)) =
      (((n:ℝ)^(-σ):ℝ):ℂ)*(χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [show -((σ:ℂ)+(t:ℂ)*I) = ((-σ:ℝ):ℂ)+(-((t:ℂ)*I)) by push_cast; ring]
  rw [cpow_add _ _ (by exact_mod_cast (ne_of_gt hn))]
  rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp, ←ofReal_cpow hnR.le]
  ring

lemma rpow_weight_dyadic_bound {U L σ δ D : ℝ}
    (hU : 1 ≤ U) (hUL : U ≤ L) (hσ : 1 ≤ σ) (hD : 0 ≤ D) :
    D*U^(1-δ)*L^(-σ) ≤ D*U^(-δ) := by
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (hU.trans hUL)
  have hw : L^(-σ) ≤ U^(-1:ℝ) := by
    exact (Real.rpow_le_rpow_of_exponent_le (hU.trans hUL) (by linarith)).trans
      (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hU) hUL (by norm_num))
  calc
    _ ≤ D*U^(1-δ)*U^(-1:ℝ) := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = D*U^(-δ) := by rw [mul_assoc, ←Real.rpow_add (by linarith)]; congr 2; ring

/-- The logarithmic phase estimate survives the full Dirichlet-series weight,
with a decaying bound for each dyadic interval. -/
theorem character_dyadic_sum_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (σ t : ℝ) (L R : ℤ), 1 ≤ σ →
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc L R, χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤
          (q:ℝ)*A*U^(-δ) := by
  obtain ⟨A,δ,hA,hδ,hh⟩ := character_log_phase_uniform B hB
  refine ⟨A,δ,hA,hδ,?_⟩
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with U hh hU
  intro q _ χ σ t L R hσ hlo hhi hL hR
  have hL0 : 0 < L := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hU.trans hL))
  have he : (∑ n ∈ Icc L R, χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))) =
      ∑ n ∈ Icc L R, (((n:ℝ)^(-σ):ℝ):ℂ)*
        (χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))) := by
    apply sum_congr rfl
    intro n hn
    exact character_cpow_split χ σ t (hL0.trans_le (mem_Icc.mp hn).1)
  rw [he]
  have hb := rpow_weighted_sum_Icc_bound
    (fun n => χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))) L R hL0
    (D := (q:ℝ)*A*U^(1-δ)) (by positivity) (by linarith : 0 ≤ σ)
    (fun V _ hV => hh q χ t L V hlo hhi hL ((by exact_mod_cast hV : (V:ℝ) ≤ R).trans hR))
  exact hb.trans (rpow_weight_dyadic_bound hU hL hσ (by positivity))

end JointDickman

end OAI
