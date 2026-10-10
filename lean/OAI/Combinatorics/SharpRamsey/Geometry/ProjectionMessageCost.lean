import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.GeometricCover

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Validation
open scoped Classical
noncomputable section

lemma pair_header_log (A B : ℕ) :
    log ((((A+1)*(B+1):ℕ):ℝ)+1)≤log ((A:ℝ)+1)+log ((B:ℝ)+1)+1 := by
  have hm : (1:ℝ)≤((A:ℝ)+1)*((B:ℝ)+1) := by nlinarith [Nat.cast_nonneg (α:=ℝ) A,Nat.cast_nonneg (α:=ℝ) B]
  have he : ((((A+1)*(B+1):ℕ):ℝ)+1)≤2*(((A:ℝ)+1)*((B:ℝ)+1)) := by
    push_cast
    linarith
  have hh := log_le_log (by positivity) he
  rw [log_mul (by norm_num : (2:ℝ)≠0) (by positivity),log_mul (by positivity) (by positivity)] at hh
  have hl := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  linarith

lemma power_pair_log {N A B k : ℕ} (hk : k≠0) (hN : N≤(A*B)^k) :
    log ((N:ℝ)+1)≤(k:ℝ)*(log ((A:ℝ)+1)+log ((B:ℝ)+1)) := by
  have ha : (0:ℝ)≤A := by positivity
  have hb : (0:ℝ)≤B := by positivity
  have hp : ((A:ℝ)*B)^k+1≤((A:ℝ)*B+1)^k := by
    simpa only [one_pow] using pow_add_pow_le (mul_nonneg ha hb) (by norm_num : (0:ℝ)≤1) hk
  have hmul : (A:ℝ)*B+1≤((A:ℝ)+1)*((B:ℝ)+1) := by nlinarith
  have hc : (N:ℝ)≤((A:ℝ)*B)^k := by exact_mod_cast hN
  have he : (N:ℝ)+1≤(((A:ℝ)+1)*((B:ℝ)+1))^k :=
    (by linarith only [hc] : (N:ℝ)+1≤((A:ℝ)*B)^k+1).trans
      (hp.trans (pow_le_pow_left₀ (by positivity) hmul k))
  have hl := log_le_log (by positivity) he
  rwa [log_pow,log_mul (by positivity) (by positivity)] at hl

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedProjectionMessageCost_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedProjectionMessageCost_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedProjectionMessageCost_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

lemma domain_log_le (r : ℕ) (hdim : Module.finrank K V=r)
    (U : Finset (Projectivization K V)) :
    log ((U.card:ℝ)+1)≤((r:ℝ)+1)*Nat.card K := by
  apply le_trans _ (projective_log_card r hdim)
  apply log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right (card_le_univ U) 1

lemma header_log_le (r : ℕ) (hdim : Module.finrank K V=r)
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) :
    log ((((U.card+1)*(UT.card+1):ℕ):ℝ)+1)≤(2*(r:ℝ)+3)*Nat.card K := by
  have h1 := domain_log_le r hdim U
  have h2 := domain_log_le r (Subspace.dual_finrank_eq.trans hdim) UT
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have h := pair_header_log U.card UT.card
  linarith

end
end SharpLogRamsey.GeometricCover

end

end OAI
