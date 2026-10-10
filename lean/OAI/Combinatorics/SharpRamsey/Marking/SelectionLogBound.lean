import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.FinalMarking

namespace OAI

section
namespace SharpLogRamsey.Selection
open Real
open scoped Classical
noncomputable section

theorem log_choose_bound {N ℓ : ℕ} (hℓ : 0<ℓ) (hN : ℓ≤N) :
    log (N.choose ℓ:ℝ)≤(ℓ:ℝ)*(1+log (N:ℝ)-log (ℓ:ℝ)) := by
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  have hn : (0:ℝ)<N := by exact_mod_cast hℓ.trans_le hN
  have hf : (0:ℝ)<ℓ.factorial := by exact_mod_cast Nat.factorial_pos ℓ
  have he := Real.pow_div_factorial_le_exp (ℓ:ℝ) hl.le ℓ
  have hp : (0:ℝ)<(ℓ:ℝ)^ℓ := pow_pos hl _
  have hfac : (ℓ:ℝ)^ℓ/exp ℓ≤(ℓ.factorial:ℝ) := by
    apply (div_le_iff₀ (exp_pos _)).mpr
    have h := (div_le_iff₀ hf).mp he
    nlinarith
  have hc := (Nat.choose_le_pow_div ℓ N : (N.choose ℓ:ℝ)≤(N:ℝ)^ℓ/ℓ.factorial)
  have hc' : (N.choose ℓ:ℝ)≤exp ℓ*((N:ℝ)/(ℓ:ℝ))^ℓ := by
    calc
      _ ≤ (N:ℝ)^ℓ/ℓ.factorial := hc
      _ ≤ (N:ℝ)^ℓ/((ℓ:ℝ)^ℓ/exp ℓ) :=
        div_le_div_of_nonneg_left (pow_nonneg hn.le _) (div_pos hp (exp_pos _)) hfac
      _ = exp ℓ*((N:ℝ)/(ℓ:ℝ))^ℓ := by rw [div_pow]; field_simp
  have hcpos : (0:ℝ)<N.choose ℓ := by exact_mod_cast Nat.choose_pos hN
  have H := log_le_log hcpos hc'
  rw [log_mul (ne_of_gt (exp_pos _)) (ne_of_gt (pow_pos (div_pos hn hl) _)),
    log_exp,log_pow,log_div (ne_of_gt hn) (ne_of_gt hl)] at H
  nlinarith

variable {α : Type*} [Fintype α] [Nonempty α]

theorem selected_entropy_log_bound {N ℓ : ℕ} (hℓ : 0<ℓ) (hN : ℓ≤N)
    (p : Law ((Fin N→α)×(Fin ℓ→α))) (reverse : (Fin ℓ→α)→(Fin ℓ→α))
    {C : ℝ} (hC : 0<C)
    (hdom : ∀ g,p.fst.mass g≤C/(Fintype.card α:ℝ)^N)
    (hselect : ∀ g f,p.mass (g,f)≠0→Occurs f g ∨ Occurs (reverse f) g) :
    (ℓ:ℝ)*(log (Fintype.card α:ℝ)-1-log (N:ℝ)+log (ℓ:ℝ))-log (2*C)≤
      entropy p.snd := by
  have H := selected_entropy_bound hN p reverse hC hdom hselect
  have hc := log_choose_bound hℓ hN
  have hp : (0:ℝ)<N.choose ℓ := by exact_mod_cast Nat.choose_pos hN
  rw [log_mul (ne_of_gt (by positivity : (0:ℝ)<2*C)) (ne_of_gt hp)] at H
  nlinarith

theorem selected_entropy_source_scales {N ℓ d : ℕ} (hd : 1≤d)
    (hℓ : 0<ℓ) (hN : ℓ≤N)
    (p : Law ((Fin N→α)×(Fin ℓ→α))) (reverse : (Fin ℓ→α)→(Fin ℓ→α))
    {C q σ η c : ℝ} (hC : 0<C) (hq : 0<q) (hσ : 0<σ) (hc : 0<c)
    (hdom : ∀ g,p.fst.mass g≤C/(Fintype.card α:ℝ)^N)
    (hselect : ∀ g f,p.mass (g,f)≠0→Occurs f g ∨ Occurs (reverse f) g)
    (hsize : (N:ℝ)≤q^d*σ) (hlength : c*q*σ^(1+η)≤(ℓ:ℝ))
    (halphabet : q^(2*d-1)≤(Fintype.card α:ℝ)) :
    (ℓ:ℝ)*((d:ℝ)*log q+η*log σ+log c-1)-log (2*C)≤entropy p.snd := by
  have hn : (0:ℝ)<N := by exact_mod_cast hℓ.trans_le hN
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  have hlN := log_le_log hn hsize
  rw [log_mul (ne_of_gt (pow_pos hq _)) (ne_of_gt hσ),log_pow] at hlN
  have hlL := log_le_log (by positivity : 0<c*q*σ^(1+η)) hlength
  rw [log_mul (by positivity : c*q≠0) (ne_of_gt (rpow_pos_of_pos hσ _)),
    log_mul (ne_of_gt hc) (ne_of_gt hq),log_rpow hσ] at hlL
  have hlA := log_le_log (pow_pos hq (2*d-1)) halphabet
  rw [log_pow] at hlA
  have has : ((2*d-1:ℕ):ℝ)=2*(d:ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  rw [has] at hlA
  have hpoint : (d:ℝ)*log q+η*log σ+log c-1≤
      log (Fintype.card α:ℝ)-1-log (N:ℝ)+log (ℓ:ℝ) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hpoint hl.le
  exact (sub_le_sub_right hh _).trans
    (selected_entropy_log_bound hℓ hN p reverse hC hdom hselect)

end
end SharpLogRamsey.Selection

end

end OAI
