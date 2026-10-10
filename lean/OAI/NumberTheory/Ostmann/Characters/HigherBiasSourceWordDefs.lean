import OAI.NumberTheory.Ostmann.Characters.BinEndpointSelection
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticRoles

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSourceWord
open Construction Preliminaries

def rolePrior {κ : Type*} [Fintype κ] (bulk top : FinitePrior κ) (m : ℕ) :
    Fin (m+1) → FinitePrior κ :=
  Fin.append (fun _ : Fin m => bulk) (fun _ : Fin 1 => top)

def wordLog {Q m : ℕ} (w : Fin (m+1) → PrimeUpTo Q) : ℝ :=
  ∑i,Real.log ((w i).val:ℝ)

def binMean {Q : ℕ} (bulk top : FinitePrior (PrimeUpTo Q)) (m : ℕ)
    (f : PrimeUpTo Q → ℤ → ℂ) (J n : ℤ) : ℂ :=
  (productPrior (rolePrior bulk top m)).cmean
    (fun w => if ⌊wordLog w⌋=J then ∏i,f (w i) n else 0)

def bins (τ : ℝ) : Finset ℤ := Finset.Icc ⌊τ⌋ ⌊(Real.exp 1+1)*τ⌋

private theorem prime_log_nonneg {Q : ℕ} (p : PrimeUpTo Q) : 0≤Real.log (p.val:ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast (primeUpTo_prime p).one_lt.le

theorem wordLog_bounds {Q m : ℕ} (bulk top : FinitePrior (PrimeUpTo Q))
    {τ T : ℝ} (hbulk : ∀p,bulk.mass p≠0 → Real.log (p.val:ℝ)≤T)
    (htop : ∀p,top.mass p≠0 → τ≤Real.log (p.val:ℝ) ∧ Real.log (p.val:ℝ)≤Real.exp 1*τ)
    (hsmall : (m:ℝ)*T≤τ) (w : Fin (m+1) → PrimeUpTo Q)
    (hw : (productPrior (rolePrior bulk top m)).mass w≠0) :
    τ≤wordLog w ∧ wordLog w≤(Real.exp 1+1)*τ := by
  change (∏i,(rolePrior bulk top m i).mass (w i))≠0 at hw
  have hmass : ∀i,(rolePrior bulk top m i).mass (w i)≠0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ _)
  have hb : ∀i : Fin m,Real.log ((w (Fin.castAdd 1 i)).val:ℝ)≤T := by
    intro i
    apply hbulk
    simpa only [rolePrior,Fin.append_left] using hmass (Fin.castAdd 1 i)
  have ht := htop (w (Fin.natAdd m (0:Fin 1))) (by
    simpa only [rolePrior,Fin.append_right] using hmass (Fin.natAdd m (0:Fin 1)))
  have hlo : 0≤∑i : Fin m,Real.log ((w (Fin.castAdd 1 i)).val:ℝ) :=
    Finset.sum_nonneg (fun i _ => prime_log_nonneg _)
  have hhi : (∑i : Fin m,Real.log ((w (Fin.castAdd 1 i)).val:ℝ))≤(m:ℝ)*T := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  have he : wordLog w=(∑i : Fin m,Real.log ((w (Fin.castAdd 1 i)).val:ℝ))+
      Real.log ((w (Fin.natAdd m (0:Fin 1))).val:ℝ) := by
    simp only [wordLog,Fin.sum_univ_add,Fin.sum_univ_one]
  rw [he]
  constructor <;> nlinarith

theorem floor_wordLog_mem_bins {Q m : ℕ} (bulk top : FinitePrior (PrimeUpTo Q))
    {τ T : ℝ} (hbulk : ∀p,bulk.mass p≠0 → Real.log (p.val:ℝ)≤T)
    (htop : ∀p,top.mass p≠0 → τ≤Real.log (p.val:ℝ) ∧ Real.log (p.val:ℝ)≤Real.exp 1*τ)
    (hsmall : (m:ℝ)*T≤τ) (w : Fin (m+1) → PrimeUpTo Q)
    (hw : (productPrior (rolePrior bulk top m)).mass w≠0) : ⌊wordLog w⌋∈bins τ := by
  have h := wordLog_bounds bulk top hbulk htop hsmall w hw
  exact Finset.mem_Icc.mpr ⟨Int.floor_mono h.1,Int.floor_mono h.2⟩

end Ostmann.Characters.HigherBiasSourceWord

end

end OAI
