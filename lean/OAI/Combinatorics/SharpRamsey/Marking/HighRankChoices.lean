import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.WindowChoices
import OAI.Combinatorics.SharpRamsey.Windows.LogWindow
import OAI.Combinatorics.SharpRamsey.Marking.HighRankOrdered

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Real Filter SourceScales Selection.Windows
open scoped Topology
noncomputable section

theorem eventually_high_window (η c : ℝ) (hη : 0 < η) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ q D : ℝ, ∀ m : ℕ,
      exp σ=q → σ^beta η ≤ D → D ≤ σ^(1-η/2) → c*q*σ^(1+η) ≤ m →
      let n:=m/8
      let k:=⌊q*D*σ^(3000*beta η)⌋₊
      2 ≤ n ∧ 0 < k ∧ k ≤ n ∧ 4*(n+k) ≤ m ∧
      (m:ℝ) ≤ 8*(2*(n+k):ℕ) ∧ (m:ℝ)/64 ≤ ((n+k)/2:ℕ) ∧
      (1/2)*q*D*σ^(3000*beta η) ≤ (k:ℝ) := by
  have he : 1-η/2+3000*beta η < 1+η:=by unfold beta;linarith
  have hs:=eventually_monomial_le_power 16 (1-η/2+3000*beta η) (1+η) c he hc
  have hpow : Tendsto (fun σ : ℝ=>σ^(1+η)) atTop atTop:=tendsto_rpow_atTop (by linarith)
  filter_upwards [hs,hpow.eventually_ge_atTop (16/c),eventually_ge_atTop (1:ℝ)]
    with σ hsmall hlarge hσ q D m heq hDl hDu hm
  have hσ0 : 0 < σ:=by linarith
  have hq : 2 ≤ q:=by have hh:=add_one_le_exp σ;rw [heq] at hh;linarith
  have hq0 : 0 < q:=by linarith
  have hD : 1 ≤ D:=(one_le_rpow hσ (beta_pos hη).le).trans hDl
  have hp : 1 ≤ σ^(3000*beta η):=one_le_rpow hσ (by unfold beta;positivity)
  have hx : 2 ≤ q*D*σ^(3000*beta η):=
    (hq.trans (le_mul_of_one_le_right hq0.le hD)).trans
      (le_mul_of_one_le_right (by positivity) hp)
  have hmp : 16 ≤ m:=by
    have hh:=(div_le_iff₀ hc).mp hlarge
    have hh' := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ q by linarith)
      (by positivity : 0 ≤ c*σ^(1+η))
    exact_mod_cast (show (16:ℝ) ≤ m by nlinarith only [hm,hh,hh'])
  have hk : (⌊q*D*σ^(3000*beta η)⌋₊:ℝ) ≤ q*D*σ^(3000*beta η):=Nat.floor_le (by positivity)
  have hk' : 16*(⌊q*D*σ^(3000*beta η)⌋₊:ℝ) ≤ m:=by
    calc
      _ ≤ 16*(q*D*σ^(3000*beta η)):=by linarith only [hk]
      _ ≤ 16*(q*σ^(1-η/2)*σ^(3000*beta η)):=by gcongr
      _ = q*(16*σ^(1-η/2+3000*beta η)):=by rw [mul_assoc q,←rpow_add hσ0];ring
      _ ≤ q*(c*σ^(1+η)):=mul_le_mul_of_nonneg_left hsmall hq0.le
      _ ≤ _:=by nlinarith only [hm]
  have hkNat : 16*⌊q*D*σ^(3000*beta η)⌋₊ ≤ m:=by exact_mod_cast hk'
  obtain ⟨_,hkpos,_,hklo,_,_⟩:=rounded_window hx hx le_rfl
  dsimp only
  refine ⟨by omega,hkpos,by omega,by omega,?_,?_,?_⟩
  · exact_mod_cast (show m ≤ 8*(2*(m/8+⌊q*D*σ^(3000*beta η)⌋₊)) by omega)
  · have hh : m ≤ 64*((m/8+⌊q*D*σ^(3000*beta η)⌋₊)/2):=by omega
    have hh' : (m:ℝ) ≤ 64*((m/8+⌊q*D*σ^(3000*beta η)⌋₊)/2:ℕ):=by exact_mod_cast hh
    linarith
  · linarith only [hklo]

theorem eventually_high_cost (η c : ℝ) (d : ℕ) (hη : 0 < η) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ q D m : ℝ,
      exp σ=q → 1 ≤ D → c*q*σ^(1+η) ≤ m →
      4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ) ≤ D*σ^(-η/3)*m := by
  have hgap : beta η+1 < 1+2*η/3:=by unfold beta;linarith
  filter_upwards [eventually_monomial_le_power (8*((d:ℝ)+1)) (beta η+1)
    (1+2*η/3) c hgap hc,eventually_ge_atTop (1:ℝ)] with σ hs hσ q D m he hD hm
  have hσ0 : 0 < σ:=by linarith
  have hq0 : 0 < q:=he ▸ exp_pos _
  have hrow : (rawRows σ η:ℝ) ≤ 2*q*σ^beta η:=by
    simpa only [rawRows,HighRankBudgets.beta,SourceScales.beta,he] using
      (HighRankBudgets.row_size (one_le_exp hσ0.le) (one_le_rpow hσ (beta_pos hη).le)).2
  have hl : log (2:ℝ) ≤ σ:=
    (log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by linarith)
  have hlast:=mul_le_mul_of_nonneg_left hm (mul_nonneg (by linarith : 0 ≤ D)
    (rpow_nonneg hσ0.le (-η/3)))
  have hp : σ^(-η/3)*σ^(1+η)=σ^(1+2*η/3):=by rw [←rpow_add hσ0];congr 1;ring
  calc
    _ ≤ 4*(2*q*σ^beta η)*(((d:ℝ)+1)*σ):=by gcongr;linarith
    _ = (8*((d:ℝ)+1)*σ^(beta η+1))*q:=by rw [rpow_add hσ0,rpow_one];ring
    _ ≤ c*σ^(1+2*η/3)*q:=mul_le_mul_of_nonneg_right hs hq0.le
    _ ≤ D*(c*σ^(1+2*η/3)*q):=le_mul_of_one_le_left (by positivity) hD
    _ = D*σ^(-η/3)*(c*q*σ^(1+η)):=by
      linear_combination -(D*c*q)*hp
    _ ≤ _:=hlast

theorem eventually_high_domain (η : ℝ) (d : ℕ) (hη : 0 < η) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, 0 ≤ D →
      ((d:ℝ)+1)*scaleK σ η D ≤ 16*scaleKstar σ η D := by
  have ht:=tendsto_rpow_atTop (show 0 < 3*beta η by unfold beta;positivity)
  filter_upwards [ht.eventually_ge_atTop (((d:ℝ)+1)/16),eventually_gt_atTop (0:ℝ)]
    with σ hs hσ D hD
  have hh : (d:ℝ)+1 ≤ 16*σ^(3*beta η):=by linarith
  have hp : σ^(3*beta η)*σ^(3*beta η)=σ^(6*beta η):=by rw [←rpow_add hσ];congr 1;ring
  unfold scaleK scaleKstar
  have hk:=mul_le_mul_of_nonneg_right hh (mul_nonneg hD (rpow_nonneg hσ.le (3*beta η)))
  nlinarith only [hk,show 16*D*(σ^(3*beta η)*σ^(3*beta η))=16*D*σ^(6*beta η) by rw [hp]]
end
end SharpLogRamsey.ActualHighRank

end

end OAI
