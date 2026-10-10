import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.SourceScales
import OAI.Combinatorics.SharpRamsey.Windows.WindowPacking

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

def stageD (σ η : ℝ) (k : ℕ) (Λ Δ : ℝ) : ℝ :=
  σ^beta η*(1+Λ/(k:ℝ)+Δ*σ^(-η))

lemma stage_normalized {σ η Λ Δ : ℝ} {k : ℕ} (hσ : 0 < σ) :
    stageD σ η k Λ Δ*σ^(-beta η)=1+Λ/(k:ℝ)+Δ*σ^(-η) := by
  unfold stageD
  rw [mul_right_comm,←rpow_add hσ,add_neg_cancel,rpow_zero,one_mul]

lemma stage_budget_bound {σ η Λ Δ q c A E : ℝ} {k N : ℕ}
    (hσ : 0 < σ) (hk : 0 < k) (hΛ : 0 ≤ Λ) (hΔ : 0 ≤ Δ)
    (hq : 0 < q) (hc : 0 < c) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hkup : (k:ℝ) ≤ q*σ^(1+η)) (hNlo : c*q*σ^(1+η) ≤ N) :
    Λ+(N:ℝ)*A+E*q*σ*Δ ≤
      ((1+E)/c+A)*(N:ℝ)*(stageD σ η k Λ Δ*σ^(-beta η)) := by
  let Dn:=stageD σ η k Λ Δ*σ^(-beta η)
  have hkn : (0:ℝ) < k:=by exact_mod_cast hk
  have hNorm : Dn=1+Λ/(k:ℝ)+Δ*σ^(-η):=stage_normalized hσ
  have hl0 : 0 ≤ Λ/(k:ℝ):=div_nonneg hΛ hkn.le
  have hd0 : 0 ≤ Δ*σ^(-η):=by positivity
  have hDn : 1 ≤ Dn:=by rw [hNorm];linarith
  have hl : Λ ≤ (k:ℝ)*Dn := by
    have h:=mul_le_mul_of_nonneg_left (show Λ/(k:ℝ) ≤ Dn by rw [hNorm];linarith) hkn.le
    rwa [mul_div_cancel₀ Λ hkn.ne'] at h
  have hdel : Δ*σ^(-η) ≤ Dn:=by rw [hNorm];linarith
  have hcancel : σ^(-η)*σ^(1+η)=σ := by
    rw [←rpow_add hσ,show -η+(1+η)=(1:ℝ) by ring,rpow_one]
  have hdel' : q*σ*Δ ≤ q*σ^(1+η)*Dn := by
    have hh:=mul_le_mul_of_nonneg_left hdel (by positivity : 0 ≤ q*σ^(1+η))
    have heq : q*σ^(1+η)*(Δ*σ^(-η))=q*σ*Δ := by
      calc
        _ = q*Δ*(σ^(-η)*σ^(1+η)):=by ring
        _ = _:=by rw [hcancel];ring
    rwa [heq] at hh
  have hN : q*σ^(1+η) ≤ (N:ℝ)/c := (le_div_iff₀ hc).mpr (by nlinarith only [hNlo])
  have hΛN : Λ ≤ ((N:ℝ)/c)*Dn:=hl.trans (mul_le_mul_of_nonneg_right (hkup.trans hN) (by linarith))
  have hΔN : E*q*σ*Δ ≤ E*((N:ℝ)/c)*Dn := by
    have hh:=mul_le_mul_of_nonneg_left (hdel'.trans (mul_le_mul_of_nonneg_right hN (by linarith))) hE
    nlinarith only [hh]
  have hAN : (N:ℝ)*A ≤ (N:ℝ)*A*Dn:=le_mul_of_one_le_right (by positivity) hDn
  calc
    _ ≤ ((N:ℝ)/c)*Dn+(N:ℝ)*A*Dn+E*((N:ℝ)/c)*Dn:=by linarith
    _ = _:=by ring

lemma class_budget_scale {B Dn x : ℝ} {K N m : ℕ}
    (hK : 0 < K) (hB : 0 ≤ B) (hDn : 0 ≤ Dn)
    (hNm : N ≤ 4*K*m) (hx : x ≤ B*(N:ℝ)*Dn) :
    x ≤ ((4*(K:ℝ)^2*B)*(m:ℝ)*Dn)/(K:ℝ) := by
  have hk : (0:ℝ) < K:=by exact_mod_cast hK
  calc
    x ≤ B*(N:ℝ)*Dn:=hx
    _ ≤ B*(4*(K:ℝ)*m)*Dn:=by gcongr;exact_mod_cast hNm
    _ = _:=by field_simp

theorem eventually_class_packing (η c Ecoef : ℝ) (K : ℕ)
    (hη : 0 < η) (hc : 0 < c) (_hE : 0 ≤ Ecoef) (hK : 0 < K) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℝ) (N : ℕ), exp σ=q →
      c*q*σ^(1+η) ≤ N →
      let m:=N/(2*K)
      0 < m ∧ N ≤ 4*K*m ∧ K*m ≤ N ∧
      ((K*m:ℕ):ℝ)+Ecoef*q*σ ≤ N ∧
      (c/(4*K))*q*σ^(1+η) ≤ m := by
  have ht:=tendsto_rpow_atTop hη
  filter_upwards [ht.eventually_ge_atTop (max (2*Ecoef/c) (4*K/c)),
    eventually_ge_atTop (1:ℝ)] with σ hh hσ q N he hN
  have hσ0 : 0 < σ:=by linarith
  have hq : 1 ≤ q:=by rw [←he];exact one_le_exp hσ0.le
  have hq0 : 0 < q:=by linarith
  have ha : σ^(1+η)=σ*σ^η:=by rw [rpow_add hσ0,rpow_one]
  have hlarge : (4*(K:ℝ)) ≤ c*q*σ^(1+η) := by
    have hh':=(div_le_iff₀ hc).mp ((le_max_right _ _).trans hh)
    have hqs : 1 ≤ q*σ:=by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hσ)]
    rw [ha]
    nlinarith [mul_le_mul_of_nonneg_left hqs (by positivity : 0 ≤ c*σ^η)]
  have hNbig : 2*(2*K) ≤ N := by
    have hh : 4*K ≤ N := by exact_mod_cast hlarge.trans hN
    omega
  obtain ⟨hm,hpack,hhalf⟩:=Selection.Windows.packing_bounds N (2*K) (by omega) hNbig
  have hNm : N ≤ 4*K*(N/(2*K)) := by
    have hh : (N:ℝ) ≤ 2*((N/(2*K))*(2*K):ℕ):=by linarith
    push_cast at hh
    exact_mod_cast (show (N:ℝ) ≤ 4*K*(N/(2*K):ℕ) by nlinarith only [hh])
  have hKm : K*(N/(2*K)) ≤ N := by nlinarith only [hpack]
  refine ⟨by omega,hNm,hKm,?_,?_⟩
  · have hec : 2*Ecoef*q*σ ≤ c*q*σ^(1+η):=by
      have hh':=(div_le_iff₀ hc).mp ((le_max_left _ _).trans hh)
      rw [ha]
      nlinarith [mul_le_mul_of_nonneg_right hh' (by positivity : 0 ≤ q*σ)]
    have hh : ((N/(2*K))*(2*K):ℕ) ≤ (N:ℝ):=by exact_mod_cast hpack
    push_cast at hh ⊢
    linarith
  · have hn : (N:ℝ) ≤ 4*(K:ℝ)*(N/(2*K):ℕ):=by exact_mod_cast hNm
    apply (mul_le_mul_iff_right₀ (show (0:ℝ) < 4*K by positivity)).mp
    have heq : ((c/(4*K))*q*σ^(1+η))*(4*K)=c*q*σ^(1+η):=by field_simp
    nlinarith only [heq,hN,hn]
end
end SharpLogRamsey.SourceScales

end

end OAI
