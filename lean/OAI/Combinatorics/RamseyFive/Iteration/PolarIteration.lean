import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.TerminalStream
import OAI.Combinatorics.RamseyFive.Entropy.IteratedBudgets

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

def iterLength (n : ℕ) : ℕ→ℕ
  | 0 => n
  | i+1 => iterLength n i/20000

theorem eventually_iter_produce {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (m : ℕ) (c d Cm : ℝ) (hc : 0<c) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K α : Type) [Field K] [Finite K] [CharP K q₀]
      [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (M k₀ : ℝ)
      (_ : PolarState K α N n adm d 0 (10*σ) M),
      3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→(n:ℝ)≤k₀→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤M→M≤Cm*σ→
      Nonempty (PolarState K α N (iterLength n m) adm ((44:ℝ)^m*d)
        (k₀*iterA σ η m) (iterDelta σ η m) M) ∧
      (c/(40000:ℝ)^m)*(Nat.card K:ℝ)*σ^(1+η)≤(iterLength n m:ℝ) ∧ iterLength n m≤n := by
  induction m with
  | zero =>
    filter_upwards [] with σ
    intro q₀ K α _ _ _ _ _ N n adm M k₀ S _ _ _ _ _ _ hlen _ _ _ _ _
    simpa only [iterLength,iterA,iterDelta,pow_zero,one_mul,mul_zero,div_one] using
      (show Nonempty (PolarState K α N n adm d 0 (10*σ) M) ∧
        c*(Nat.card K:ℝ)*σ^(1+η)≤(n:ℝ) ∧ n≤n from ⟨⟨S⟩,hlen,le_rfl⟩)
  | succ m ih =>
    have hcp : 0<c/(40000:ℝ)^m := by positivity
    filter_upwards [ih,eventually_polar_compression hη hη' (c/(40000:ℝ)^m) ((44:ℝ)^m*d) Cm hcp hCm,
      eventually_marking_small hη (c/(40000:ℝ)^m) hcp,eventually_iterD_range hη hη']
      with σ hI hstep hsmall hrange
    intro q₀ K α _ _ _ _ _ N n adm M k₀ S hq3 hcard hσ hq hα hN hlen hn hk hklo hM hMhi
    obtain ⟨⟨T⟩,hTlen,hTn⟩:=hI q₀ K α N n adm M k₀ S hq3 hcard hσ hq hα hN hlen hn hk hklo hM hMhi
    have hs : 0<σ := zero_lt_one.trans_le hσ
    have hqpos : (0:ℝ)<Nat.card K := by rw [←hq];positivity
    have hkp : 0<k₀ := by
      have hh : 0<c*(Nat.card K:ℝ)*σ^(1+η) := by positivity
      linarith only [hh,hlen,hn]
    have hnum:=iter_budgets_nonneg hs.le (η:=η) m
    have hlarge:=(hsmall (iterLength n m) (by simpa only [hq] using hTlen)).1
    have hcut:=(stage_cuts (iterLength n m) hlarge).2.2.2.2.2
    have hout:=hstep q₀ K α N (iterLength n m) adm (k₀*iterA σ η m) (iterDelta σ η m) M k₀
      (iterD σ η m) T hq3 hcard hσ hq hα hN hTlen
      ((by exact_mod_cast hTn : (iterLength n m:ℝ)≤n).trans hn) hk hklo
      (mul_nonneg hkp.le hnum.2.1) hnum.2.2 hM hMhi
      (by rw [iterD_eq];congr 2;field_simp) hnum.1 (hrange m)
    refine ⟨?_,?_,(Nat.div_le_self _ _).trans hTn⟩
    · simpa only [iterLength,iterA,iterDelta,pow_succ,mul_assoc,mul_left_comm,mul_comm] using hout
    · change c/(40000:ℝ)^(m+1)*(Nat.card K:ℝ)*σ^(1+η)≤((iterLength n m/20000:ℕ):ℝ)
      have hid : c/(40000:ℝ)^(m+1)*(Nat.card K:ℝ)*σ^(1+η)=
          ((c/(40000:ℝ)^m)*(Nat.card K:ℝ)*σ^(1+η))/40000 := by
        rw [pow_succ];ring
      rw [hid]
      linarith only [hTlen,hcut]

theorem eventually_no_initial_polar {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c d Cm : ℝ) (hc : 0<c) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K α : Type) [Field K] [Finite K] [CharP K q₀]
      [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (M k₀ : ℝ)
      (_ : PolarState K α N n adm d 0 (10*σ) M),
      3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→(n:ℝ)≤k₀→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤M→M≤Cm*σ→False := by
  obtain ⟨m,hm⟩:=exists_nat_ge (4/η)
  have hm' : 1≤η*(m:ℝ)/4 := by have hh:=(div_le_iff₀ hη).mp hm;nlinarith
  let c':=c/(40000:ℝ)^(m+1)
  have hc' : 0<c' := by dsimp [c'];positivity
  filter_upwards [eventually_iter_produce hη hη' (m+1) c d Cm hc hCm,
    eventually_iter_terminal hη hη' m hm' c' hc',
    eventually_polar_terminal hη c' ((44:ℝ)^(m+1)*d) hc'] with σ hI hbudget hterminal
  intro q₀ K α _ _ _ _ _ N n adm M k₀ S hq3 hcard hσ hq hα hN hlen hn hk hklo hM hMhi
  obtain ⟨⟨T⟩,hTlen,hTn⟩:=hI q₀ K α N n adm M k₀ S hq3 hcard hσ hq hα hN hlen hn hk hklo hM hMhi
  have hkp : 0≤k₀ := (Nat.cast_nonneg n).trans hn
  exact hterminal K α N (iterLength n (m+1)) adm (k₀*iterA σ η (m+1)) (iterDelta σ η (m+1)) M k₀ T
    hσ hq hα hN hTlen hk (by nlinarith only [mul_le_mul_of_nonneg_left hbudget.1 hkp])
    (iter_budgets_nonneg (by linarith : 0≤σ) (m+1)).2.2 hbudget.2
end
end SharpRamseyFive.SelectedTuple

end OAI
