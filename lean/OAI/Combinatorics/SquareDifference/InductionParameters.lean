import OAI.Combinatorics.SquareDifference.MixedCrude

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma childLength_rpow_bound (N D : ℕ) (hN : 0<N) (hD : 0<D) (a : ℝ) (ha : 0≤a) :
    (childLength N D:ℝ)^(-a)≤(D:ℝ)^(2*a)*(N:ℝ)^(-a) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  calc
    _ ≤ ((N:ℝ)/(D:ℝ)^2)^(-a) := Real.rpow_le_rpow_of_nonpos (div_pos hn (pow_pos hd 2)) (childLength_lower N D) (neg_nonpos.mpr ha)
    _ = _ := by
      rw [Real.div_rpow hn.le (sq_nonneg _),←Real.rpow_natCast_mul hd.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (2:ℝ)*(-a)= -(2*a) by ring,Real.rpow_neg hd.le,div_inv_eq_mul,mul_comm]

lemma childLength_product_rpow_bound (N M q : ℕ) (hN : 0<N) (hM : 0<M) (hq : 0<q) (a : ℝ) (ha : 0≤a) :
    (childLength N (M*q):ℝ)^(-a)≤(M:ℝ)^(2*a)*(N:ℝ)^(-a)*(q:ℝ)^(2*a) := by
  have hh := childLength_rpow_bound N (M*q) hN (Nat.mul_pos hM hq) a ha
  rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hh
  exact hh.trans_eq (by ring)

lemma source_crude_tail_exponent (d : ℕ) :
    2*(d:ℝ)*sourceLoss d-sourceTau d≤ -sourceSigma d := by
  have ht := sourceTau_pos d
  have hd : (0:ℝ)<(d:ℝ)+1 := by positivity
  unfold sourceLoss sourceSigma
  unfold sourceGamma
  apply (sub_le_iff_le_add).mpr
  field_simp
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) d) ht.le]

lemma crude_tail_rate (d N : ℕ) (hN : 1≤N) (C : ℝ) (hC : 0≤C) :
    ((N:ℝ)^(-sourceTau d)/4)*(C*(N:ℝ)^(2*(d:ℝ)*sourceLoss d))≤
      C*(N:ℝ)^(-sourceSigma d) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have he : ((N:ℝ)^(-sourceTau d)/4)*(C*(N:ℝ)^(2*(d:ℝ)*sourceLoss d))=
      (C/4)*(N:ℝ)^(2*(d:ℝ)*sourceLoss d-sourceTau d) := by
    rw [show 2*(d:ℝ)*sourceLoss d-sourceTau d= -sourceTau d+2*(d:ℝ)*sourceLoss d by ring,Real.rpow_add hn]
    ring
  rw [he]
  apply mul_le_mul (by linarith : C/4≤C) _ (Real.rpow_nonneg hn.le _) hC
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (source_crude_tail_exponent d)

lemma exists_induction_exponent (M : ℕ) (hM : 0<M) (ρ σ : ℝ) (hρ : 0<ρ) (_ : ρ≤1) (hσ : 0<σ) :
    ∃a : ℝ,0<a ∧ a<σ ∧ 2*a≤1 ∧ (M:ℝ)^(2*a)*(1-3*ρ/4)<1 := by
  have hm : (M:ℝ)≠0 := by exact_mod_cast hM.ne'
  have hc : ContinuousAt (fun a : ℝ => (M:ℝ)^(2*a)*(1-3*ρ/4)) 0 :=
    ((Real.continuous_const_rpow hm).continuousAt.comp (continuousAt_const.mul continuousAt_id)).mul_const _
  have hg : (M:ℝ)^(2*(0:ℝ))*(1-3*ρ/4)<1 := by simp only [mul_zero,Real.rpow_zero,one_mul]; linarith
  have he : ∀ᶠ a : ℝ in 𝓝 0,(M:ℝ)^(2*a)*(1-3*ρ/4)<1 ∧ a<σ ∧ a<(1:ℝ)/2 :=
    (hc.eventually (eventually_lt_nhds hg)).and ((eventually_lt_nhds hσ).and (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)))
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp he
  have hh := hb (show dist (δ/2) (0:ℝ)<δ by rw [Real.dist_eq,sub_zero,abs_of_pos (by linarith)]; linarith)
  exact ⟨δ/2,by linarith,hh.2.1,by linarith [hh.2.2],hh.1⟩

end SquareDifference

end

end OAI
