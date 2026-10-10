import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.SupportThreshold

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)]

lemma projective_entropy_le {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (Projectivization K V)) :
    entropy p ≤ (n+3:ℕ)*log (Nat.card K) := by
  have hq : (2:ℝ)≤Nat.card K := by
    exact_mod_cast (show 2≤Nat.card K from Finite.one_lt_card)
  have hc : (Fintype.card (Projectivization K V):ℝ) ≤ (Nat.card K:ℝ)^(n+3) := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,
      Nat.cast_sum]
    simp only [Nat.cast_pow]
    apply (sum_powers_le_twice hq (by omega : 0<n+3)).trans
    simp only [show n+3-1=n+2 by omega]
    calc
      _ ≤ (Nat.card K:ℝ)*(Nat.card K:ℝ)^(n+2) :=
        mul_le_mul_of_nonneg_right hq (pow_nonneg (by linarith) _)
      _ = (Nat.card K:ℝ)^(n+3) := by
        simpa only [mul_comm] using (pow_succ (Nat.card K:ℝ) (n+2)).symm
  have hp : (0:ℝ)<Fintype.card (Projectivization K V) := by
    have : Nontrivial V := (Module.finrank_pos_iff (R := K)).mp (by omega)
    exact_mod_cast Fintype.card_pos (α := Projectivization K V)
  apply (entropy_le_log_card p univ (by simp)).trans
  simp only [card_univ]
  apply (log_le_log hp hc).trans
  rw [log_pow]

variable [Fintype (Projectivization K (Module.Dual K V))]

theorem eventually_reciprocal_auxiliary_choices (n : ℕ) (b C C₀ : ℝ)
    (hb : 0<b) (hC : 1≤C) (hC₀ : 0≤C₀) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (Projectivization K V)]
      [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=n+3 → log (Nat.card K)=σ →
      ∀ (p : Law (Projectivization K (Module.Dual K V) × Projectivization K V))
        (S : Finset (Projectivization K (Module.Dual K V) × Projectivization K V))
        (DA : Finset (Projectivization K (Module.Dual K V)))
        (DB : Finset (Projectivization K V)) (MA MB κ δ : ℝ),
        (∀ z,z∉S→p.mass z=0) →
        (∀ z,0<p.mass z→z.1.rep z.2.rep=0) →
        (∀ a,a∉DA→p.fst.mass a=0) →
        (∀ a,a∉DB→p.snd.mass a=0) →
        0<MA → 0<MB → (DA.card:ℝ)≤MA → (DB.card:ℝ)≤MB →
        MA*MB≤C*(Nat.card K:ℝ)^(n+3) →
        (S.card:ℝ)≤C₀*(Nat.card K:ℝ)^(n+2) →
        σ^(4*b)≤κ → δ≤κ*σ^(-2*b) → (n+2:ℕ)*σ-entropy p≤δ →
        Nonempty (AuxiliarySupport p.fst
          (univ.filter (goodFirst p MA ((n+2:ℕ)*σ) κ (1/50))) MA κ) ∧
        Nonempty (AuxiliarySupport p.snd
          (univ.filter (goodSecond p MB ((n+2:ℕ)*σ) κ (1/50))) MB κ) := by
  filter_upwards [eventually_support_small b C C₀ (n+3) hb hC hC₀ (by positivity),
      eventually_ge_atTop (1:ℝ)] with σ he hσ
  intro K V _ _ _ _ _ _ _ hdim hlog p S DA DB MA MB κ δ hs hf hDA hDB
    hMA hMB hA hB hcap hS hκ hδ hdef
  have hσ0 : 0<σ := by linarith
  have hκ0 : 0<κ := (rpow_pos_of_pos hσ0 (4*b)).trans_le hκ
  have hq : (0:ℝ)<Nat.card K := by
    exact_mod_cast (show 0<Nat.card K from Nat.zero_lt_one.trans Finite.one_lt_card)
  have hn : exp ((n+2:ℕ)*σ)=(Nat.card K:ℝ)^(n+2) := by
    rw [←hlog,exp_nat_mul,exp_log hq]
  have hSn : (S.card:ℝ)*exp (-((n+2:ℕ)*σ))≤C₀ := by
    have h := mul_le_mul_of_nonneg_right hS (le_of_lt (exp_pos (-((n+2:ℕ)*σ))))
    rw [←hn,mul_assoc,←exp_add,add_neg_cancel,exp_zero,mul_one] at h
    exact h
  have hHA := projective_entropy_le (V:=Module.Dual K V)
    (by simpa only [Subspace.dual_finrank_eq] using hdim) p.fst
  have hHB := projective_entropy_le hdim p.snd
  rw [hlog] at hHA hHB
  have hnlog : log (2*C*(Nat.card K:ℝ)^(n+2)) = log (2*C)+(n+2:ℕ)*σ := by
    rw [log_mul (by positivity : 2*C≠0) (pow_ne_zero _ hq.ne'),log_pow,hlog]
  apply reciprocal_auxiliary_choices hdim p S DA DB hs hf hDA hDB
    MA MB C ((n+2:ℕ)*σ) κ (1/50) hMA hMB hC hA hB hcap hκ0 (by norm_num)
  rw [hnlog]
  exact he κ δ (entropy p) (entropy p.fst) (entropy p.snd) ((n+2:ℕ)*σ)
    S.card hκ hδ hdef hSn (entropy_nonneg _)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hHA) (entropy_nonneg _)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hHB)

end
end SharpLogRamsey.Selection

end

end OAI
