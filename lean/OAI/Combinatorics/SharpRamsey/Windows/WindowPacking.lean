import Mathlib

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Real
noncomputable section

lemma packing_bounds (m L : ℕ) (hL : 0 < L) (hm : 2*L ≤ m) :
    1 ≤ m/L ∧ (m/L)*L ≤ m ∧ (m:ℝ)/2 ≤ ((m/L)*L:ℕ) := by
  have hw : 1 ≤ m/L := (Nat.le_div_iff_mul_le hL).mpr (by omega)
  have hlt:=Nat.mod_lt m hL
  have he:=Nat.mod_add_div m L
  have hl:=(Nat.div_mul_le_self m L)
  refine ⟨hw,hl,?_⟩
  have hv : m ≤ 2*((m/L)*L) := by
    have hh : L ≤ (m/L)*L:=by nlinarith
    nlinarith
  have hv' : (m:ℝ) ≤ 2*((m/L)*L:ℕ):=by exact_mod_cast hv
  linarith

lemma packing_scales (m L : ℕ) {q σ η D c C : ℝ}
    (hq : 0 < q) (hσ : 0 < σ) (_ : 0 < D) (hc : 0 < c) (hC : 0 < C)
    (hL : 0 < L) (hm : 2*L ≤ m)
    (hmlo : c*q*σ^(1+η) ≤ m) (hmhi : (m:ℝ) ≤ C*q*σ^(1+η))
    (hLlo : q*D*σ^(η/2) ≤ L) (hLhi : (L:ℝ) ≤ C*q*D*σ^(η/2)) :
    1 ≤ m/L ∧ (m/L)*L ≤ m ∧ (m:ℝ)/2 ≤ ((m/L)*L:ℕ) ∧
    (c/(2*C))*σ^(1+η/2) ≤ (m/L:ℕ)*D ∧
    (m/L:ℕ)*D ≤ C*σ^(1+η/2) := by
  obtain ⟨hw,hpack,hhalf⟩:=packing_bounds m L hL hm
  have hp : 0 < σ^(η/2):=rpow_pos_of_pos hσ _
  have hr : σ^(1+η)=σ^(1+η/2)*σ^(η/2) := by
    rw [←rpow_add hσ]
    congr 1
    ring
  have hqP : 0 < q*σ^(η/2):=mul_pos hq hp
  have hw0 : (0:ℝ) ≤ (m/L:ℕ):=Nat.cast_nonneg _
  have hpcast : ((m/L)*L:ℕ)=(m/L:ℕ)*(L:ℝ):=by norm_cast
  have hlow : c*q*σ^(1+η) ≤ 2*(m/L:ℕ)*(L:ℝ) := by
    rw [hpcast] at hhalf
    linarith
  have hupp : (m/L:ℕ)*(q*D*σ^(η/2)) ≤ C*q*σ^(1+η) := by
    have hpc : (m/L:ℕ)*(L:ℝ) ≤ m:=by exact_mod_cast hpack
    exact (mul_le_mul_of_nonneg_left hLlo hw0).trans (hpc.trans hmhi)
  have hlarg := hlow.trans (mul_le_mul_of_nonneg_left hLhi (by positivity : (0:ℝ) ≤ 2*(m/L:ℕ)))
  rw [hr] at hupp hlarg
  have hi : (m/L:ℕ)*D ≤ C*σ^(1+η/2) := by
    apply (mul_le_mul_iff_right₀ hqP).mp
    nlinarith only [hupp]
  have hlo : (c/(2*C))*σ^(1+η/2) ≤ (m/L:ℕ)*D := by
    apply (mul_le_mul_iff_right₀ (mul_pos (by positivity : 0 < 2*C) hqP)).mp
    have he : (2*C*(q*σ^(η/2)))*((c/(2*C))*σ^(1+η/2))=
        c*q*(σ^(1+η/2)*σ^(η/2)) := by field_simp
    rw [he]
    nlinarith only [hlarg]
  exact ⟨hw,hpack,hhalf,hlo,hi⟩
end
end SharpLogRamsey.Selection.Windows

end

end OAI
