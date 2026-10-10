import OAI.Combinatorics.SquareDifference.TransferParameters

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma source_exponent_gap_third (d : ℕ) :
    sourceTau d+(d:ℝ)*sourceLoss d+sourceSigma d<sourceBeta*sourceGamma/3 := by
  have ht := sourceTau_pos d
  have hd : 0≤(d:ℝ) := Nat.cast_nonneg _
  have hl : (d:ℝ)*sourceLoss d≤ sourceTau d/100 := by
    unfold sourceLoss
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<100)).mpr
    rw [show (d:ℝ)*(sourceGamma*sourceTau d/(100*((d:ℝ)+1)))*100=
        sourceGamma*sourceTau d*((d:ℝ)/((d:ℝ)+1)) by field_simp]
    have hf : (d:ℝ)/((d:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ ≤ sourceGamma*sourceTau d := mul_le_of_le_one_right (mul_nonneg sourceGamma_pos.le ht.le) hf
      _ ≤ sourceTau d := by unfold sourceGamma; linarith
  have hs : sourceSigma d≤ sourceTau d/4 := by unfold sourceSigma sourceGamma; linarith
  have hb := sourceTau_le d
  have hp : 0<sourceBeta*sourceGamma := mul_pos sourceBeta_pos sourceGamma_pos
  linarith

lemma eventual_cutoff_rpow_lower (a b : ℝ) (hb : 0<b) (hba : b<a) :
    ∀ᶠ N : ℕ in atTop,(N:ℝ)^b≤(powerCutoff N a:ℝ) := by
  have ha : 0<a := hb.trans hba
  have hh := eventually_rpow_dominate 2 b a hba
  have htwo := ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [hh,htwo] with N hh htwo
  exact (by linarith : (N:ℝ)^b≤(N:ℝ)^a/2).trans (powerCutoff_lower N a htwo)

lemma transfer_error_bound (d M N H q : ℕ) (C l : ℝ) (hN : 1≤N) (hC : 0≤C)
    (hl : 0≤l) (hl2 : l≤2)
    (hH : (N:ℝ)^(sourceBeta/3)≤(H:ℝ)) (hq : (q:ℝ)≤(N:ℝ)^(sourceTau d)) :
    (d:ℝ)*(H:ℝ)^(-sourceGamma)*(C*(N:ℝ)^(sourceLoss d))^d*
      (l^d+(q:ℝ)*(M:ℝ)^d)≤
      ((d:ℝ)*C^d*((2:ℝ)^d+(M:ℝ)^d))*(N:ℝ)^(-sourceSigma d) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hnp : (1:ℝ)≤N := by exact_mod_cast hN
  have hg : (H:ℝ)^(-sourceGamma)≤(N:ℝ)^(-(sourceBeta*sourceGamma/3)) := by
    calc
      _ ≤ ((N:ℝ)^(sourceBeta/3))^(-sourceGamma) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hn _) hH (neg_nonpos.mpr sourceGamma_pos.le)
      _ = _ := by rw [←Real.rpow_mul hn.le]; congr 1; ring
  have hlq : l^d+(q:ℝ)*(M:ℝ)^d≤((2:ℝ)^d+(M:ℝ)^d)*(N:ℝ)^(sourceTau d) := by
    have ht : 1≤(N:ℝ)^(sourceTau d) := Real.one_le_rpow hnp (sourceTau_pos d).le
    calc
      _ ≤ (2:ℝ)^d+(N:ℝ)^(sourceTau d)*(M:ℝ)^d :=
        add_le_add (pow_le_pow_left₀ hl hl2 _) (mul_le_mul_of_nonneg_right hq (by positivity))
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) d]
  calc
    _ ≤ (d:ℝ)*(N:ℝ)^(-(sourceBeta*sourceGamma/3))*(C*(N:ℝ)^(sourceLoss d))^d*
        (((2:ℝ)^d+(M:ℝ)^d)*(N:ℝ)^(sourceTau d)) := by
      apply mul_le_mul _ hlq (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)) (by positivity)
    _ = ((d:ℝ)*C^d*((2:ℝ)^d+(M:ℝ)^d))*
        (N:ℝ)^(-(sourceBeta*sourceGamma/3)+sourceLoss d*d+sourceTau d) := by
      rw [mul_pow,←Real.rpow_mul_natCast hn.le]
      rw [Real.rpow_add hn,Real.rpow_add hn]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hnp
      have := source_exponent_gap_third d
      nlinarith

noncomputable def transferFactor (d M N : ℕ) : ℝ :=
  (1+(M:ℝ)^2*(N:ℝ)^(2*sourceTau d-1))^d

lemma transferFactor_nonneg (d M N : ℕ) : 0≤transferFactor d M N := by unfold transferFactor; positivity

lemma transferFactor_limit (d M : ℕ) : Tendsto (fun N : ℕ => transferFactor d M N) atTop (𝓝 1) := by
  have ht : 0<1-2*sourceTau d := by have := sourceTau_lt_quarter d; linarith
  have hh := (tendsto_rpow_neg_atTop ht).comp tendsto_natCast_atTop_atTop
  have he : -(1-2*sourceTau d)=2*sourceTau d-1 := by ring
  have hh' : Tendsto (fun N : ℕ => (N:ℝ)^(2*sourceTau d-1)) atTop (𝓝 0) := by
    simpa only [he,Function.comp_def] using hh
  have h : Tendsto (fun N : ℕ => (1+(M:ℝ)^2*(N:ℝ)^(2*sourceTau d-1))^d) atTop (𝓝 ((1+(M:ℝ)^2*0)^d)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hh')).pow d
  simpa only [mul_zero,add_zero,one_pow,transferFactor] using h

lemma child_factor_le (d M N q : ℕ) (hN : 0<N) (hD : 0<M*q)
    (hq : (q:ℝ)≤(N:ℝ)^(sourceTau d)) :
    (((M*q:ℕ):ℝ)^2*(childLength N (M*q):ℝ)/N)^d≤transferFactor d M N := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  apply pow_le_pow_left₀ (by positivity)
  have hh := (childLength_factor N (M*q) hN hD).2.le
  apply hh.trans
  apply add_le_add_right
  calc
    ((M*q:ℕ):ℝ)^2/(N:ℝ) ≤ ((M:ℝ)^2*((N:ℝ)^(sourceTau d))^2)/N := by
      apply div_le_div_of_nonneg_right _ hn.le
      push_cast
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hq _) (sq_nonneg _)
    _ = (M:ℝ)^2*(N:ℝ)^(2*sourceTau d-1) := by
      rw [←Real.rpow_mul_natCast hn.le,Real.rpow_sub hn,Real.rpow_one]
      ring_nf

end SquareDifference

end

end OAI
