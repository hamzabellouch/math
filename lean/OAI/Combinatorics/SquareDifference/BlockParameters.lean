import OAI.Combinatorics.SquareDifference.IntervalTransfer

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

noncomputable def blockLength (N K : ℕ) : ℕ := ⌈(N:ℝ)/K⌉₊

lemma blockLength_pos (N K : ℕ) (hN : 0<N) (hK : 0<K) : 0<blockLength N K :=
  Nat.ceil_pos.mpr (div_pos (by exact_mod_cast hN) (by exact_mod_cast hK))

lemma blockLength_cover (N K : ℕ) (hK : 0<K) : N≤K*blockLength N K := by
  have hk : (0:ℝ)<K := by exact_mod_cast hK
  have h := (div_le_iff₀ hk).mp (Nat.le_ceil ((N:ℝ)/K))
  change (N:ℝ)≤(blockLength N K:ℝ)*(K:ℝ) at h
  have h' : N≤blockLength N K*K := by exact_mod_cast h
  simpa only [mul_comm] using h'

lemma blockLength_factor (N K : ℕ) (hN : 0<N) (hK : 0<K) (hKN : K≤N) :
    (K:ℝ)*(blockLength N K:ℝ)/N≤2 ∧ (N:ℝ)/(blockLength N K:ℝ)≤K := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hk : (0:ℝ)<K := by exact_mod_cast hK
  constructor
  · have hc := Nat.ceil_lt_add_one (show 0≤(N:ℝ)/K by positivity)
    change (blockLength N K:ℝ)<(N:ℝ)/K+1 at hc
    have hm := mul_lt_mul_of_pos_left hc hk
    have hK' : (K:ℝ)≤N := by exact_mod_cast hKN
    apply (div_le_iff₀ hn).mpr
    have he : (K:ℝ)*((N:ℝ)/K+1)=N+K := by field_simp
    rw [he] at hm
    linarith
  · apply (div_le_iff₀ (show (0:ℝ)<blockLength N K by exact_mod_cast blockLength_pos N K hN hK)).mpr
    exact_mod_cast blockLength_cover N K hK

lemma source_d_tau (d : ℕ) : (d:ℝ)*sourceTau d≤ sourceBeta*sourceGamma/1000 := by
  unfold sourceTau
  have hd : 0<(d:ℝ)+1 := by positivity
  have hf : (d:ℝ)/((d:ℝ)+1)≤1 := (div_le_one hd).mpr (by linarith)
  calc
    _ = sourceBeta*sourceGamma/1000*((d:ℝ)/((d:ℝ)+1)) := by field_simp
    _ ≤ _ := mul_le_of_le_one_right (by norm_num [sourceBeta,sourceGamma]) hf

lemma source_beta_d_tau_gap (d : ℕ) : sourceBeta/2+(d:ℝ)*sourceTau d<sourceBeta := by
  have hd := source_d_tau d
  norm_num [sourceBeta,sourceGamma] at *
  linarith

lemma blockLength_half_lower (d N : ℕ) (hN : 1≤N) :
    (N:ℝ)^((1:ℝ)/2)≤(blockLength N (powerCutoff N (sourceTau d)):ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hk : (0:ℝ)<powerCutoff N (sourceTau d) := by exact_mod_cast powerCutoff_pos N hN _ (sourceTau_pos d).le
  apply le_trans _ (Nat.le_ceil _)
  apply (le_div_iff₀ hk).mpr
  calc
    _ ≤ (N:ℝ)^((1:ℝ)/2)*(N:ℝ)^(sourceTau d) :=
      mul_le_mul_of_nonneg_left (powerCutoff_le N _) (by positivity)
    _ = (N:ℝ)^((1:ℝ)/2+sourceTau d) := (Real.rpow_add hn _ _).symm
    _ ≤ N := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤N by exact_mod_cast hN)
        (show (1:ℝ)/2+sourceTau d≤1 by have := sourceTau_lt_quarter d; linarith)
      simpa only [Real.rpow_one] using h

lemma eventual_block_scales (d M : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      let K := powerCutoff N (sourceTau d)
      let L := blockLength N K
      let Q := powerCutoff N sourceBeta
      let H := powerCutoff N (sourceBeta/2)
      1≤N ∧ 0<K ∧ 0<L ∧ N≤K*L ∧ (K:ℝ)*L/N≤2 ∧ (N:ℝ)/L≤K ∧
      LiftSizeConditions L Q ∧ Q≤N ∧ 0<H ∧ H*K^d≤Q ∧
      ((M:ℝ)*(K:ℝ)^d≤(N:ℝ)^((1:ℝ)/1000)) ∧ (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000) ∧
      8≤(N:ℝ)^((1:ℝ)/16) ∧ (N:ℝ)^(sourceTau d/2)≤K ∧ (N:ℝ)^(sourceBeta/3)≤H := by
  have hsize := eventually_rpow_dominate 2 sourceBeta ((1:ℝ)/2) (by norm_num [sourceBeta])
  have hprod := eventually_rpow_dominate 2 (sourceBeta/2+(d:ℝ)*sourceTau d) sourceBeta (source_beta_d_tau_gap d)
  have hQ := ((tendsto_rpow_atTop sourceBeta_pos).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hD := eventually_rpow_dominate M ((d:ℝ)*sourceTau d) ((1:ℝ)/1000) (by
    apply (source_d_tau d).trans_lt
    norm_num [sourceBeta,sourceGamma])
  have hlarge := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/16)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 8
  have hK := eventual_cutoff_rpow_lower (sourceTau d) (sourceTau d/2) (by have := sourceTau_pos d; linarith) (by have := sourceTau_pos d; linarith)
  have hH := eventual_cutoff_rpow_lower (sourceBeta/2) (sourceBeta/3) (by have := sourceBeta_pos; linarith) (by have := sourceBeta_pos; linarith)
  filter_upwards [hsize,hprod,hQ,hD,hlarge,hK,hH,eventually_ge_atTop 1] with N hsize hprod hQ hD hlarge hK hH hN
  dsimp only
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hk := powerCutoff_pos N hN (sourceTau d) (sourceTau_pos d).le
  have hl := blockLength_pos N _ (by omega) hk
  have hKN := powerCutoff_le_self N hN (sourceTau d) (by have := sourceTau_lt_quarter d; linarith)
  have hfac := blockLength_factor N _ (by omega) hk hKN
  have hhalf := blockLength_half_lower d N hN
  have hpow : (powerCutoff N (sourceTau d):ℝ)^d≤(N:ℝ)^((d:ℝ)*sourceTau d) := by
    calc
      _ ≤ ((N:ℝ)^(sourceTau d))^d := pow_le_pow_left₀ (Nat.cast_nonneg _) (powerCutoff_le N _) _
      _ = _ := by rw [←Real.rpow_mul_natCast hn.le]; congr 1; ring
  refine ⟨hN,hk,hl,blockLength_cover N _ hk,hfac.1,hfac.2,
    ⟨hl,powerCutoff_pos N hN sourceBeta sourceBeta_pos.le,?_,?_⟩,
    powerCutoff_le_self N hN sourceBeta sourceBeta_le,
    powerCutoff_pos N hN _ (by have := sourceBeta_pos; linarith),?_,?_,?_,hlarge,hK,hH⟩
  · exact ((mul_le_mul_of_nonneg_left (powerCutoff_le N sourceBeta) (by norm_num)).trans hsize).trans hhalf
  · apply le_trans _ hhalf
    calc
      _ ≤ ((N:ℝ)^sourceBeta)^5 := pow_le_pow_left₀ (Nat.cast_nonneg _) (powerCutoff_le N _) _
      _ = (N:ℝ)^(5*sourceBeta) := by rw [←Real.rpow_mul_natCast hn.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num [sourceBeta])
  · have hprod' : (powerCutoff N (sourceBeta/2):ℝ)*(powerCutoff N (sourceTau d):ℝ)^d≤(powerCutoff N sourceBeta:ℝ) := by
      calc
        _ ≤ (N:ℝ)^(sourceBeta/2)*(N:ℝ)^((d:ℝ)*sourceTau d) :=
          mul_le_mul (powerCutoff_le N _) hpow (pow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        _ = (N:ℝ)^(sourceBeta/2+(d:ℝ)*sourceTau d) := (Real.rpow_add hn _ _).symm
        _ ≤ (N:ℝ)^sourceBeta/2 := by linarith
        _ ≤ _ := powerCutoff_lower N sourceBeta hQ
    exact_mod_cast hprod'
  · exact (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg M)).trans hD
  · exact (powerCutoff_le N _).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num [sourceBeta]))

end SquareDifference

end

end OAI
