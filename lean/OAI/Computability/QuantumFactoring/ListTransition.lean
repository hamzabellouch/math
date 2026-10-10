import Mathlib
import OAI.Computability.QuantumFactoring.RepeatedTrials
import OAI.Computability.QuantumFactoring.CRTLevels
import OAI.Computability.QuantumFactoring.OrderCandidateLaw

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


/-! The actual uniform-list transition in Section 5: its event, exact closed
probability, and unchanged repetition guarantee. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

noncomputable def FavorableBits {m n : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (p₀ : Component m) (b : ℕ) (x : Basis b) : Prop :=
  ∃ a : (ZMod m)ˣ, (a : ZMod m).val=(bitsValue x).toNat ∧ FavorableUnit hm hb p₀ a

lemma favorableBits_mass {m n b : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) (hmb : m ≤ 2^b) :
    outcomeMass (FavorableBits hm hb p₀ b) (fairState b)=
      (favorableCount m n : ℝ)/(2:ℝ)^b := by
  classical
  let : NeZero m := ⟨hm⟩
  let S : Finset (ZMod m)ˣ := Finset.univ.filter (FavorableUnit hm hb p₀)
  have he : (FavorableBits hm hb p₀ b)=
      (fun x => ∃ a∈S, (bitsValue x).toNat=(a : ZMod m).val) := by
    funext x
    apply propext
    simp only [FavorableBits,S,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun ⟨a,ha,hf⟩ => ⟨a,hf,ha.symm⟩,fun ⟨a,hf,ha⟩ => ⟨a,ha.symm,hf⟩⟩
  rw [he,outcomeMass_finite_union _ S _ (by
    intro x a c _ _ ha hc
    apply Units.ext
    exact ZMod.val_injective m (ha.symm.trans hc))]
  have hs : ∀ a∈S, outcomeMass (fun x : Basis b => (bitsValue x).toNat=(a : ZMod m).val)
      (fairState b)=1/(2:ℝ)^b := fun a _ =>
    fair_value_mass ((ZMod.val_lt (a : ZMod m)).trans_le hmb)
  rw [Finset.sum_congr rfl hs,Finset.sum_const,nsmul_eq_mul]
  have hc : S.card=favorableCount m n := by
    rw [favorableCount_eq_card hm hb hodd p₀,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hc,mul_one_div]

lemma coveringPower_le_twice {m : ℕ} (hm : 1 ≤ m) : 2^(Nat.clog 2 m) ≤ 2*m := by
  by_cases he : m=1
  · simp [he]
  · have hm' : 1 < m := by omega
    have hc := Nat.clog_pos (by decide : 1 < 2) hm'
    have hh := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hm'
    simp only [Nat.pred_eq_sub_one] at hh
    calc
      _ = 2^(Nat.clog 2 m-1)*2 := by rw [← pow_succ]; congr 1; omega
      _  ≤  2*m := by omega

lemma favorableBits_lower {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁ ≠ p₀) :
    1/(4*((n:ℝ)+1)) ≤  (favorableCount m n : ℝ)/(2:ℝ)^(Nat.clog 2 m) := by
  have hphi := totient_ratio_lower (by omega : 0 < m) hb
  have hhalf := totient_le_twice_favorableCount (by omega : m ≠ 0) hb hodd p₀ p₁ hne
  have hc := coveringPower_le_twice (by omega : 1 ≤ m)
  have hmR : (0:ℝ) < m := by positivity
  have hpR : (0:ℝ) < (2:ℝ)^(Nat.clog 2 m) := by positivity
  have hnR : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hphiR : (m:ℝ)/(n+1) ≤ m.totient := by
    have hh := (le_div_iff₀ hmR).mp hphi
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hh
  have hhalfR : (m.totient:ℝ) ≤ 2*favorableCount m n := by exact_mod_cast hhalf
  have hcR : (2:ℝ)^(Nat.clog 2 m) ≤ 2*m := by exact_mod_cast hc
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4*(n+1)) hpR).mpr
  have hh := (div_le_iff₀ hnR).mp hphiR
  nlinarith

noncomputable def GoodList {m n : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (p₀ : Component m) (K : ℕ) (x : Fin K→Basis (Nat.clog 2 m)) : Prop :=
  ∃ i, FavorableBits hm hb p₀ (Nat.clog 2 m) (x i)

/-- Source formula (5.4), over the literal independent fair-bit preparation. -/
theorem list_good_mass {m n : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) (K : ℕ) :
    outcomeMass (GoodList hm hb p₀ K) (tensorState (fairState (Nat.clog 2 m)) K)=
      1-(1-(favorableCount m n : ℝ)/(2:ℝ)^(Nat.clog 2 m))^K := by
  unfold GoodList
  rw [tensor_some_mass (fairState (Nat.clog 2 m)) K (FavorableBits hm hb p₀ (Nat.clog 2 m)) (fairState_normalized _),
    favorableBits_mass hm hb hodd p₀ (Nat.le_pow_clog (by decide) _)]

theorem list_good_lower {m n : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m < 2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁ ≠ p₀) :
    1-1/(2:ℝ)^(2*n) ≤ outcomeMass (GoodList (by omega : m ≠ 0) hb p₀ (n^5))
      (tensorState (fairState (Nat.clog 2 m)) (n^5)) := by
  rw [list_good_mass _ hb hodd p₀]
  have hl := favorableBits_lower hm hb hodd p₀ p₁ hne
  have hu := (mass_bounds (fairState (Nat.clog 2 m))
    (FavorableBits (by omega : m ≠ 0) hb p₀ (Nat.clog 2 m)) (fairState_normalized _)).2
  rw [favorableBits_mass _ hb hodd p₀ (Nat.le_pow_clog (by decide) _)] at hu
  apply repeated_success_lower hn _ hu
  calc
    _  ≤  1/(4*((n:ℝ)+1)) := by apply one_div_le_one_div_of_le (by positivity); nlinarith
    _  ≤  _ := hl

end ExactQuantumFactoring


end

end OAI
