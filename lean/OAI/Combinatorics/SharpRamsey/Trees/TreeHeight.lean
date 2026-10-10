import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.BalancedWindows

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree
open Finset Filter Real BinaryTree
open scoped Classical Topology
noncomputable section

lemma eventually_natLog_small (β C a : ℝ) (hβ : 0<β) (hC : 0<C) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,(n:ℝ)≤C*x^a → (Nat.log 2 n:ℝ)+1≤x^β := by
  have hp : Tendsto (fun x : ℝ=>x^(-β)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hβ
  have hl := (isLittleO_log_rpow_atTop hβ).tendsto_div_nhds_zero
  have ht : Tendsto (fun x : ℝ=>(log C/log 2+1)*x^(-β)+(a/log 2)*(log x/x^β))
      atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (hp.const_mul (log C/log 2+1)).add (hl.const_mul (a/log 2))
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_ge_atTop (1:ℝ)] with x hx hx1 n hn
  have hx0 : 0<x := by linarith
  have hp0 : 0<x^β := rpow_pos_of_pos hx0 _
  have hd : 0<log (2:ℝ) := log_pos (by norm_num)
  have hlog : (log C/log 2+1)+(a/log 2)*log x≤x^β := by
    have he : (log C/log 2+1)*x^(-β)+(a/log 2)*(log x/x^β)=
        ((log C/log 2+1)+(a/log 2)*log x)/x^β := by
      rw [rpow_neg hx0.le]
      ring
    rw [he] at hx
    simpa only [one_mul] using ((div_lt_iff₀ hp0).mp hx).le
  rcases eq_or_ne n 0 with rfl|hn0
  · simpa using one_le_rpow hx1 hβ.le
  · have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnlog : log (n:ℝ)≤log C+a*log x := by
      calc
        _ ≤ log (C*x^a) := log_le_log hnpos hn
        _ = _ := by rw [log_mul hC.ne' (rpow_pos_of_pos hx0 a).ne',log_rpow hx0]
    have hnat := Real.natLog_le_logb n 2
    dsimp only [logb] at hnat
    norm_num only [Nat.cast_ofNat] at hnat
    calc
      (Nat.log 2 n:ℝ)+1 ≤ log (n:ℝ)/log 2+1 := by linarith only [hnat]
      _ ≤ (log C+a*log x)/log 2+1 := by gcongr
      _ = (log C/log 2+1)+(a/log 2)*log x := by ring
      _ ≤ _ := hlog

theorem eventually_liveTree_height (β C a : ℝ) (hβ : 0<β) (hC : 0<C) :
    ∀ᶠ x : ℝ in atTop, ∀ w : ℕ,(w:ℝ)≤C*x^a →
      ∀ (live : Finset (Fin w)) (fallback : Fin w),
        ((liveTree live fallback).height:ℝ)≤x^β := by
  filter_upwards [eventually_natLog_small β C a hβ hC] with x hx w hw live fallback
  have hcard : (live.card:ℝ)≤(w:ℝ) := by
    exact_mod_cast (show live.card≤w by simpa using card_le_univ live)
  calc
    _ ≤ (Nat.log 2 live.card:ℝ)+1 := by exact_mod_cast liveTree_height live fallback
    _ ≤ x^β := hx live.card (hcard.trans hw)
end
end SharpLogRamsey.ChronologicalTree

end

end OAI
