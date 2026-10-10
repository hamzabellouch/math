import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticSmallSum

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem sum_Ioc_residue_blocks {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (d J : ℕ) :
    (∑ w ∈ Finset.Ioc 0 (J*d), f w) =
      ∑ r : Fin d, ∑ j ∈ Finset.range J, f (r.val+1+d*j) := by
  have hshift (W : ℕ) : (∑ w ∈ Finset.Ioc 0 W,f w)=∑ j ∈ Finset.range W,f (j+1) := by
    induction W with
    | zero => simp
    | succ W ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le _),Finset.sum_range_succ,ih]
  rw [hshift,← Fin.sum_univ_eq_sum_range]
  have he := (finProdFinEquiv : Fin J × Fin d ≃ Fin (J*d)).sum_comp
    (fun w => f (w.val+1))
  rw [← he,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  change f (r.val+d*j.val+1)=f (r.val+1+d*j.val)
  congr 1
  omega

def witnessProgression (d J : ℕ) (N α : ℝ) (r : Fin d) : ℂ :=
  ∑ j ∈ Finset.range J, weylPhase (α*((r.val+1+d*j:ℕ):ℝ)^2)*
    cutoffFourier ((((r.val+1+d*j:ℕ):ℝ)/N)^2)

theorem normalized_sum_residue_blocks (d J : ℕ) [NeZero d]
    {N : ℝ} (hN : 0 < N) (hcover : ⌊N⌋₊ ≤ J*d) (A : ZMod d → ℂ) (α : ℝ) :
    normalizedSmoothQuadraticSum 1 N (fun w => A (w:ZMod d)) α =
      ((N⁻¹:ℝ):ℂ)*∑ r : Fin d,A ((r.val+1:ℕ):ZMod d)*witnessProgression d J N α r := by
  rw [normalizedSmoothQuadraticSum_truncation hN hcover]
  simp only [Nat.one_dvd,Finset.filter_true]
  rw [sum_Ioc_residue_blocks]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  unfold witnessProgression
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have ha : ((r.val+1+d*j:ℕ):ZMod d)=((r.val+1:ℕ):ZMod d) := by
    push_cast
    simp
  rw [ha]
  ring

theorem exists_large_witness_progression (d J : ℕ) [NeZero d]
    {N L ε : ℝ} (hN : 0 < N) (hL : 0 < L)
    (hcover : ⌊N⌋₊ ≤ J*d) (A : ZMod d → ℂ) (α : ℝ)
    (hA : ∑ r : Fin d, ‖A ((r.val+1:ℕ):ZMod d)‖ ≤ (d:ℝ)*L)
    (hlarge : L*ε ≤ ‖normalizedSmoothQuadraticSum 1 N (fun w => A (w:ZMod d)) α‖) :
    ∃ r : Fin d, (N/d)*ε ≤ ‖witnessProgression d J N α r‖ := by
  classical
  have hd : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_neZero d
  obtain ⟨r,hr,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun r : Fin d => ‖witnessProgression d J N α r‖) Finset.univ_nonempty
  refine ⟨r,?_⟩
  have hbound : ‖normalizedSmoothQuadraticSum 1 N (fun w => A (w:ZMod d)) α‖ ≤
      N⁻¹*((d:ℝ)*L)*‖witnessProgression d J N α r‖ := by
    rw [normalized_sum_residue_blocks d J hN hcover A α,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hN.le)]
    calc
      _ ≤ N⁻¹*∑ a : Fin d, ‖A ((a.val+1:ℕ):ZMod d)*witnessProgression d J N α a‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hN.le)
      _ ≤ N⁻¹*∑ a : Fin d, ‖A ((a.val+1:ℕ):ZMod d)‖*‖witnessProgression d J N α r‖ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hN.le)
        apply Finset.sum_le_sum
        intro a ha
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmax a ha) (norm_nonneg _)
      _ = N⁻¹*(∑ a : Fin d, ‖A ((a.val+1:ℕ):ZMod d)‖)*‖witnessProgression d J N α r‖ := by
        rw [← Finset.sum_mul,mul_assoc]
      _ ≤ _ := by gcongr
  have hh := mul_le_mul_of_nonneg_left (hlarge.trans hbound) hN.le
  have hcancel : N*(N⁻¹*((d:ℝ)*L)*‖witnessProgression d J N α r‖)=
      (d:ℝ)*L*‖witnessProgression d J N α r‖ := by field_simp
  rw [hcancel] at hh
  have hh' : N*ε ≤ (d:ℝ)*‖witnessProgression d J N α r‖ :=
    (mul_le_mul_iff_left₀ hL).mp (by nlinarith only [hh])
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  simpa only [mul_comm] using hh'

end Ostmann.QuadraticCenter

end

end OAI
