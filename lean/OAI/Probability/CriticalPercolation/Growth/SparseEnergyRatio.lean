import Mathlib
import OAI.Probability.CriticalPercolation.Growth.RealSparseDoubling

namespace OAI

section
noncomputable section
namespace CriticalPercolation.HarmonicAnalysis

lemma exists_small_relative_dissipation (E N : ℕ → ℝ)
    (hpos : ∀ n, 0<E n) (hm : Antitone E)
    (hdis : ∀ n, N n≤E n-E (n+1))
    (d : ℕ) (C : ℝ) (hC : 0≤C)
    (hg : ∀ R, ∃ n≥R, (E n)⁻¹≤C*(n:ℝ)^d)
    (ε : ℝ) (hε : 0<ε) : ∃ n, N n≤ε*E n := by
  by_contra! hbad
  have hmono : Monotone (fun n => (E n)⁻¹) := by
    intro i j hij
    exact (inv_le_inv₀ (hpos i) (hpos j)).mpr (hm hij)
  obtain ⟨R,hR⟩ := exists_nat_gt ((2:ℝ)^(d+1)/ε)
  obtain ⟨r,hr,hgood⟩ := sparse_real_doubling (fun n => (E n)⁻¹) hmono
    0 (fun n _ => inv_pos.mpr (hpos n)) C hC d 2 (by omega) hg R
  have hratio : E r≤(2:ℝ)^(d+1)*E (2*r) := by
    have hh : 1/E (2*r)≤(2:ℝ)^(d+1)/E r := by
      simpa only [Nat.cast_ofNat,one_div,div_eq_mul_inv,one_mul] using hgood
    have hh' := (div_le_div_iff₀ (hpos (2*r)) (hpos r)).mp hh
    simpa only [one_mul] using hh'
  have hεr : (2:ℝ)^(d+1)<(r:ℝ)*ε := by
    have hh : (R:ℝ)≤r := by exact_mod_cast (le_max_left R 0).trans hr
    have hh' := (div_lt_iff₀ hε).mp hR
    nlinarith
  have ht : ∀ i≤r, (i:ℝ)*ε*E (2*r)≤E r-E (r+i) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have H := ih (by omega)
      have HD := (hbad (r+i)).le.trans (hdis (r+i))
      have HM := mul_le_mul_of_nonneg_left (hm (by omega : r+i≤2*r)) hε.le
      push_cast
      have he : r+(i+1)=r+i+1 := by omega
      rw [he]
      nlinarith
  have hh := ht r le_rfl
  rw [←two_mul] at hh
  have hh' := mul_lt_mul_of_pos_right hεr (hpos (2*r))
  nlinarith [hpos (2*r)]

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
