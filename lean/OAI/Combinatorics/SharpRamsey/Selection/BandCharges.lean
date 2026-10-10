import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalBands
import OAI.Combinatorics.SharpRamsey.Reciprocal.AuxiliaryCharges

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real ReciprocalBands
open scoped Classical BigOperators
noncomputable section

lemma integer_band_rank_bounds {d r : ℕ} {σ C κ gap u v : ℝ}
    (hσ : 0<σ) (hC : 0<C)
    (hu : IntegerBand r σ gap u) (hv : IntegerBand r σ gap v)
    (hsmall : log C+3*κ+gap<σ) :
    (r:ℝ)-1 < (d:ℝ)+1-(log (C*exp (((d:ℝ)+1)*σ-u))+3*κ)/σ ∧
    (d:ℝ)-r < (d:ℝ)+1-(log (C*exp v)+3*κ)/σ := by
  rw [IntegerBand,abs_le] at hu hv
  rw [log_mul hC.ne' (exp_ne_zero _),log_exp,
    log_mul hC.ne' (exp_ne_zero _),log_exp]
  constructor
  · have hh : (log C+(((d:ℝ)+1)*σ-u)+3*κ)/σ < (d:ℝ)+1-((r:ℝ)-1) := by
      apply (div_lt_iff₀ hσ).mpr
      nlinarith [hu.1]
    linarith
  · have hh : (log C+v+3*κ)/σ < (d:ℝ)+1-((d:ℝ)-r) := by
      apply (div_lt_iff₀ hσ).mpr
      nlinarith [hv.2]
    linarith

lemma open_band_rank_bounds {d r : ℕ} {σ C κ gap u v : ℝ}
    (hσ : 0<σ) (hC : 0<C)
    (hu : OpenBand r σ gap u) (hv : OpenBand r σ gap v)
    (hsmall : log C+3*κ<gap) :
    (r:ℝ)-1 < (d:ℝ)+1-(log (C*exp (((d:ℝ)+1)*σ-u))+3*κ)/σ ∧
    (d:ℝ)+1-r < (d:ℝ)+1-(log (C*exp v)+3*κ)/σ := by
  rw [log_mul hC.ne' (exp_ne_zero _),log_exp,
    log_mul hC.ne' (exp_ne_zero _),log_exp]
  constructor
  · have hh : (log C+(((d:ℝ)+1)*σ-u)+3*κ)/σ < (d:ℝ)+1-((r:ℝ)-1) := by
      apply (div_lt_iff₀ hσ).mpr
      nlinarith [hu.1]
    linarith
  · have hh : (log C+v+3*κ)/σ < (r:ℝ) := by
      apply (div_lt_iff₀ hσ).mpr
      linarith [hv.2]
    linarith

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype ι] [DecidableEq ι]

theorem integer_band_event_le
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (C κ gap u v a : ℝ) (d r : ℕ)
    (hdim : Module.finrank K V=d+1) (hC : 0<C) (hr : r≤d+1)
    (hu : IntegerBand r (log (Nat.card K)) gap u)
    (hv : IntegerBand r (log (Nat.card K)) gap v)
    (hsmall : log C+3*κ+gap<log (Nat.card K))
    (hκ : log (200/97)≤κ)
    (hconsistent : ∀ x,p.mass x≠0 →
      (x i).1.rep (x j).2.rep=0 → (x j).1.rep (x i).2.rep=0)
    (hcharge : (pairInformation p i j:ℝ)+
      (reciprocalCharges p Projectivization.rep Projectivization.rep
        (1/(100*((d:ℝ)+1))) r (d+1-r) i j:ℝ)≤a) :
    ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay =>
      goodFirst (p.marginal i) (C*exp (((d:ℝ)+1)*log (Nat.card K)-u))
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.1 ∧
      goodSecond (p.marginal j) (C*exp v)
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.2 ∧
      ay.1.rep ay.2.rep=0)) ≤ (20000*((d:ℝ)+1)^2+8)*a := by
  have hσ : 0<log (Nat.card K:ℝ) := log_pos (by exact_mod_cast Finite.one_lt_card (α:=K))
  have hd : (0:ℝ)<(d:ℝ)+1 := by positivity
  have he : (Module.finrank K V:ℝ)*(1/(100*((d:ℝ)+1)))=1/100 := by
    rw [hdim,Nat.cast_add,Nat.cast_one]
    field_simp
  obtain ⟨hrA,hrB⟩ := integer_band_rank_bounds (d:=d) hσ hC hu hv hsmall
  have hh := integer_good_event_le p i j
    (C*exp (((d:ℝ)+1)*log (Nat.card K)-u)) (C*exp v) κ
    (1/(100*((d:ℝ)+1))) (1/50) (1/2) a d r
    (by positivity) (by positivity) (by positivity) (by norm_num)
    (by rw [he]; norm_num) hr (by rw [he]; norm_num)
    (by simpa only [he,show (1:ℝ)-1/100-1/50=97/100 by norm_num,
      show (2:ℝ)/(97/100)=200/97 by norm_num] using hκ) hrA hrB hconsistent hcharge
  apply hh.trans_eq
  field_simp
  ring

theorem open_band_event_le
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (C κ gap u v a : ℝ) (d r : ℕ)
    (hdim : Module.finrank K V=d+1) (hC : 0<C) (hr : r≤d+1)
    (hu : OpenBand r (log (Nat.card K)) gap u)
    (hv : OpenBand r (log (Nat.card K)) gap v)
    (hsmall : log C+3*κ<gap)
    (hκ : log (200/97)≤κ)
    (hconsistent : ∀ x,p.mass x≠0 →
      (x i).1.rep (x j).2.rep=0 → (x j).1.rep (x i).2.rep=0)
    (hinfo : (pairInformation p i j:ℝ)≤a) :
    ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay =>
      goodFirst (p.marginal i) (C*exp (((d:ℝ)+1)*log (Nat.card K)-u))
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.1 ∧
      goodSecond (p.marginal j) (C*exp v)
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.2 ∧
      ay.1.rep ay.2.rep=0)) ≤ (20000*((d:ℝ)+1)^2)*a := by
  have hσ : 0<log (Nat.card K:ℝ) := log_pos (by exact_mod_cast Finite.one_lt_card (α:=K))
  have hd : (0:ℝ)<(d:ℝ)+1 := by positivity
  have he : (Module.finrank K V:ℝ)*(1/(100*((d:ℝ)+1)))=1/100 := by
    rw [hdim,Nat.cast_add,Nat.cast_one]
    field_simp
  obtain ⟨hrA,hrB⟩ := open_band_rank_bounds (d:=d) hσ hC hu hv hsmall
  have hh := open_good_event_le p i j
    (C*exp (((d:ℝ)+1)*log (Nat.card K)-u)) (C*exp v) κ
    (1/(100*((d:ℝ)+1))) (1/50) a d r
    (by positivity) (by positivity) (by positivity) hdim hr
    (by rw [he]; norm_num)
    (by simpa only [he,show (1:ℝ)-1/100-1/50=97/100 by norm_num,
      show (2:ℝ)/(97/100)=200/97 by norm_num] using hκ) hrA hrB hconsistent hinfo
  apply hh.trans_eq
  field_simp
  ring

end
end SharpLogRamsey.Selection

end

end OAI
