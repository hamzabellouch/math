import OAI.Combinatorics.ContingencyTables.Sampling.ExactIntegerProgram
import OAI.Combinatorics.ContingencyTables.Transport.RejectionLaw
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Exact law and geometric tail of integer rejection -/

namespace ContingencyTables.ExactIntegerChoice
open MatchingFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section
variable {r Q : ℕ} (w : Fin r → ℕ) (h : 0<totalWeight w) [NeZero Q]
variable (hQ : totalWeight w≤Q)

abbrev trialLaw : RationalLaw (Option (Fin r)) :=
  mapLaw (uniformLaw (α := Fin Q)) (weightedTrial w h hQ)

def failure : ℚ := 1-(totalWeight w:ℚ)/Q

lemma trialLaw_none : (trialLaw w h hQ).mass none=failure w (Q := Q) := by
  have ht := (trialLaw w h hQ).total
  rw [Fintype.sum_option] at ht
  simp_rw [weightedTrial_mass w h hQ] at ht
  rw [←Finset.sum_div,←Nat.cast_sum] at ht
  change _+(totalWeight w:ℚ)/Q=1 at ht
  unfold failure
  linarith

private lemma lifted_success (p : RationalLaw (Option (Fin r))) (i : Fin r) :
    successMass p (fun x => x.map some) (some i)=p.mass (some i) := by
  simp [successMass]

private lemma lifted_no_success (p : RationalLaw (Option (Fin r))) :
    successMass p (fun x => x.map some) none=0 := by
  simp [successMass]

private lemma lifted_failure (p : RationalLaw (Option (Fin r))) :
    failureMass p (fun x => x.map some)=p.mass none := by
  simp [failureMass]

/-- `none` records that all supplied independent trials rejected; it is
not a fallback table. This is the finite prefix law of exact rejection. -/
def retryIntegerLaw (N : ℕ) : RationalLaw (Option (Fin r)) :=
  retryLaw (trialLaw w h hQ) (fun x => x.map some) none N

lemma retryIntegerLaw_none (N : ℕ) :
    (retryIntegerLaw w h hQ N).mass none=(failure w (Q := Q))^N := by
  rw [retryIntegerLaw,retryLaw_mass,outputMass,lifted_no_success,lifted_failure,trialLaw_none]
  simp only [zero_mul,ite_true,zero_add]

lemma retryIntegerLaw_some (N : ℕ) (i : Fin r) :
    (retryIntegerLaw w h hQ N).mass (some i)=
      normalized w i*(1-(failure w (Q := Q))^N) := by
  rw [retryIntegerLaw,retryLaw_mass,outputMass,lifted_success,lifted_failure,trialLaw_none,
    weightedTrial_mass]
  simp only [reduceCtorEq,ite_false,add_zero]
  have hV : (totalWeight w:ℚ)≠0 := by exact_mod_cast h.ne'
  have hQt : (Q:ℚ)≠0 := by exact_mod_cast (NeZero.ne Q)
  have he : (w i:ℚ)/Q=normalized w i*(1-failure w (Q := Q)) := by
    unfold normalized failure
    field_simp
    ring
  rw [he,mul_assoc]
  congr 1
  have hg := geometric_balance (failure w (Q := Q)) N
  linarith

include hQ in
lemma failure_nonnegative : 0≤failure w (Q := Q) := by
  unfold failure
  have hQt : (0:ℚ)<Q := by exact_mod_cast (NeZero.pos Q)
  exact sub_nonneg.mpr ((div_le_one hQt).mpr (by exact_mod_cast hQ))

lemma failure_lt_half (hshort : Q<2*totalWeight w) : failure w (Q := Q)<1/2 := by
  unfold failure
  have hQt : (0:ℚ)<Q := by exact_mod_cast (NeZero.pos Q)
  have he : (1/2:ℚ)<(totalWeight w:ℚ)/Q := by
    rw [lt_div_iff₀ hQt]
    have hc : (Q:ℚ)<2*totalWeight w := by exact_mod_cast hshort
    linarith
  linarith

lemma retryIntegerLaw_failure_bound (hshort : Q<2*totalWeight w) (N : ℕ) :
    (retryIntegerLaw w h hQ N).mass none≤(1/2:ℚ)^N := by
  rw [retryIntegerLaw_none]
  exact pow_le_pow_left₀ (failure_nonnegative w hQ) (failure_lt_half w hshort).le N

lemma retryIntegerLaw_limit (hshort : Q<2*totalWeight w) (i : Fin r) :
    Filter.Tendsto (fun N => ((retryIntegerLaw w h hQ N).mass (some i):ℝ))
      Filter.atTop (nhds (normalized w i:ℝ)) := by
  have hf0 : (0:ℝ)≤failure w (Q := Q) := by exact_mod_cast failure_nonnegative w hQ
  have hf1 : (failure w (Q := Q):ℝ)<1 := by
    have hh : (failure w (Q := Q):ℝ)<1/2 := by
      have hh := (Rat.cast_lt (K := ℝ)).mpr (failure_lt_half w hshort)
      norm_num at hh ⊢
      exact hh
    linarith
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hf0 hf1
  have hout : Filter.Tendsto
      (fun N => (normalized w i:ℝ)*(1-(failure w (Q := Q):ℝ)^N))
      Filter.atTop (nhds ((normalized w i:ℝ)*(1-0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub ht)
  simpa only [retryIntegerLaw_some,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_pow,
    sub_zero,mul_one] using hout

/-- The expected number of independent integer proposals is less than two. -/
lemma retryIntegerLaw_expected_attempts (hshort : Q<2*totalWeight w) :
    Summable (fun N => ((retryIntegerLaw w h hQ N).mass none:ℝ)) ∧
      (∑' N,((retryIntegerLaw w h hQ N).mass none:ℝ))<2 := by
  have hf0 : (0:ℝ)≤failure w (Q := Q) := by exact_mod_cast failure_nonnegative w hQ
  have hfhalf : (failure w (Q := Q):ℝ)<1/2 := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr (failure_lt_half w hshort)
    norm_num at hh ⊢
    exact hh
  have hf1 : (failure w (Q := Q):ℝ)<1 := by linarith
  simp only [retryIntegerLaw_none,Rat.cast_pow]
  refine ⟨summable_geometric_of_lt_one hf0 hf1,?_⟩
  rw [tsum_geometric_of_lt_one hf0 hf1]
  rw [inv_lt_comm₀ (by linarith : (0:ℝ)<1-failure w (Q := Q)) (by norm_num)]
  linarith

lemma clog_power_lt_twice (V : ℕ) (hV : 0<V) : 2^(Nat.clog 2 V)<2*V := by
  by_cases hV1 : V=1
  · subst V
    simp
  · have h1 : 1<V := by omega
    have hc : 0<Nat.clog 2 V := Nat.clog_pos (by decide) h1
    have hp : 2^(Nat.clog 2 V-1)<V := by
      simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self (by decide : 1<2) h1
    rw [show Nat.clog 2 V=(Nat.clog 2 V-1)+1 by omega,pow_succ]
    omega

end
end ContingencyTables.ExactIntegerChoice

end OAI
