import OAI.Combinatorics.SquareDifference.PowerParameters

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma sourceTau_lt_halfBeta (d : ℕ) : sourceTau d < sourceBeta/2 :=
  (sourceTau_le d).trans_lt (by norm_num [sourceBeta,sourceGamma])

lemma eventual_cutoff_size (a : ℝ) (ha : 0<a) (ha5 : 5*a<1) :
    ∀ᶠ N : ℕ in atTop,LiftSizeConditions N (powerCutoff N a) := by
  have hh := eventually_rpow_dominate 2 a 1 (by linarith)
  filter_upwards [hh,eventually_ge_atTop 1] with N hN hN1
  refine ⟨by omega,powerCutoff_pos N hN1 a ha.le,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left (powerCutoff_le N a) (by norm_num)).trans (by simpa only [Real.rpow_one] using hN)
  · calc
      (powerCutoff N a:ℝ)^5 ≤ ((N:ℝ)^a)^5 := pow_le_pow_left₀ (Nat.cast_nonneg _) (powerCutoff_le N a) _
      _ = (N:ℝ)^(5*a) := by rw [←Real.rpow_mul_natCast (Nat.cast_nonneg _)]; congr 1; ring
      _ ≤ N := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) ha5.le

lemma childLength_sqrt_lower (d M N q : ℕ) (hN : 1≤N)
    (hq : (q:ℝ)≤(N:ℝ)^(sourceTau d)) (hD : 0<M*q)
    (hscale : (M:ℝ)^2*(N:ℝ)^(2*sourceTau d+(1:ℝ)/2)≤N) :
    (N:ℝ)^((1:ℝ)/2)≤(childLength N (M*q):ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hd : (0:ℝ)<(M*q:ℕ) := by exact_mod_cast hD
  apply le_trans _ (childLength_lower N (M*q))
  apply (le_div_iff₀ (pow_pos hd 2)).mpr
  calc
    _ = (M:ℝ)^2*(q:ℝ)^2*(N:ℝ)^((1:ℝ)/2) := by push_cast; ring
    _ ≤ (M:ℝ)^2*((N:ℝ)^(sourceTau d))^2*(N:ℝ)^((1:ℝ)/2) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hq _) (sq_nonneg _)) (by positivity)
    _ = (M:ℝ)^2*(N:ℝ)^(2*sourceTau d+(1:ℝ)/2) := by
      rw [←Real.rpow_mul_natCast hn.le, mul_assoc,←Real.rpow_add hn]
      congr 2; ring
    _ ≤ N := hscale

lemma child_power_cutoff (N L : ℕ) (h : (N:ℝ)^((1:ℝ)/2)≤(L:ℝ)) :
    powerCutoff N (sourceBeta/2)≤powerCutoff L sourceBeta := by
  apply powerCutoff_mono
  calc
    _ = ((N:ℝ)^((1:ℝ)/2))^sourceBeta := by rw [←Real.rpow_mul (Nat.cast_nonneg _)]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h sourceBeta_pos.le

lemma cutoff_product_le (d N q : ℕ) (hq : (q:ℝ)≤(N:ℝ)^(sourceTau d))
    (hN : 1≤N) (hlower : 2≤(N:ℝ)^sourceBeta)
    (hscale : 2*(N:ℝ)^(sourceBeta/2+sourceTau d)≤(N:ℝ)^sourceBeta) :
    powerCutoff N (sourceBeta/2)*q≤powerCutoff N sourceBeta := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hh : (powerCutoff N (sourceBeta/2):ℝ)*(q:ℝ)≤(powerCutoff N sourceBeta:ℝ) := by
    calc
      _ ≤ (N:ℝ)^(sourceBeta/2)*(N:ℝ)^(sourceTau d) :=
        mul_le_mul (powerCutoff_le N _) hq (Nat.cast_nonneg _) (by positivity)
      _ = (N:ℝ)^(sourceBeta/2+sourceTau d) := (Real.rpow_add hn _ _).symm
      _ ≤ (N:ℝ)^sourceBeta/2 := by linarith
      _ ≤ _ := powerCutoff_lower N sourceBeta hlower
  exact_mod_cast hh

lemma eventual_transfer_scales (d M : ℕ) (hM : 2≤M) :
    ∀ᶠ N : ℕ in atTop,∀q : ℕ,0<q → (q:ℝ)≤(N:ℝ)^(sourceTau d) →
      let L := childLength N (M*q)
      let Q := powerCutoff N sourceBeta
      let H := powerCutoff N (sourceBeta/2)
      let Qc := powerCutoff L sourceBeta
      0<L ∧ L<N ∧ (N:ℝ)^((1:ℝ)/2)≤L ∧
        LiftSizeConditions N Q ∧ LiftSizeConditions L Qc ∧ Q≤N ∧ Qc≤N ∧
        0<H ∧ H*q≤Q ∧ H≤Qc ∧ N≤(M*q)^2*L ∧
        1≤((M*q:ℕ):ℝ)^2*L/N ∧ ((M*q:ℕ):ℝ)^2*L/N≤2 := by
  have hsz := eventual_cutoff_size sourceBeta sourceBeta_pos (by norm_num [sourceBeta])
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hsz
  have hs := eventually_rpow_dominate ((M:ℝ)^2) (2*sourceTau d+(1:ℝ)/2) 1 (by have := sourceTau_lt_quarter d; linarith)
  have hcut := eventually_rpow_dominate 2 (sourceBeta/2+sourceTau d) sourceBeta (by have := sourceTau_lt_halfBeta d; linarith)
  have hl := ((tendsto_rpow_atTop sourceBeta_pos).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hchild := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop N₀
  have hfactor := eventually_rpow_dominate ((M:ℝ)^2) (2*sourceTau d) 1 (by have := sourceTau_lt_quarter d; linarith)
  filter_upwards [hs,hcut,hl,hchild,hfactor,hsz,eventually_ge_atTop 2] with N hs hcut hl hchild hfac hsz hN
  intro q hq hq'
  dsimp only
  have hd : 2≤M*q := (by simpa only [mul_one] using Nat.mul_le_mul hM (show 1≤q by omega))
  have hn : 0<N := by omega
  have hhalf := childLength_sqrt_lower d M N q (by omega) hq' (by omega) (by simpa only [Real.rpow_one] using hs)
  have hL0 := childLength_pos N (M*q) hn (by omega)
  have hLle := childLength_lt N (M*q) hN hd
  have hLc : N₀≤childLength N (M*q) := by exact_mod_cast hchild.trans hhalf
  have hF := childLength_factor N (M*q) hn (by omega)
  refine ⟨hL0,hLle,hhalf,hsz,hN₀ _ hLc,
    powerCutoff_le_self N (by omega) _ sourceBeta_le,
    (powerCutoff_le_self _ (by omega) _ sourceBeta_le).trans hLle.le,
    powerCutoff_pos N (by omega) _ (by have := sourceBeta_pos; linarith),
    cutoff_product_le d N q hq' (by omega) hl hcut,child_power_cutoff N _ hhalf,
    childLength_cover N (M*q) (by omega),hF.1,?_⟩
  have hnorm : ((M*q:ℕ):ℝ)^2≤N := by
    calc
      _ = (M:ℝ)^2*(q:ℝ)^2 := by push_cast; ring
      _ ≤ (M:ℝ)^2*((N:ℝ)^(sourceTau d))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hq' _) (sq_nonneg _)
      _ = (M:ℝ)^2*(N:ℝ)^(2*sourceTau d) := by
        rw [←Real.rpow_mul_natCast (Nat.cast_nonneg _)]; congr 2; ring
      _ ≤ N := by simpa only [Real.rpow_one] using hfac
  have hr : ((M*q:ℕ):ℝ)^2/N≤1 := (div_le_one (by exact_mod_cast hn)).mpr hnorm
  linarith [hF.2]

end SquareDifference

end

end OAI
