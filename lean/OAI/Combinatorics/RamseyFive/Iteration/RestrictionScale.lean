import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Beta

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma dyadic_levels_le (q r : ℕ) (σ : ℝ) (hσ : 1 ≤ σ)
    (hq : (q:ℝ)=Real.exp σ) (hr : r ≤ 5) :
    (Nat.log 2 (q^r)+1:ℝ) ≤ (5/Real.log 2+1)*σ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : 0 ≤ σ := le_trans (by norm_num) hσ
  have hh := Real.natLog_le_logb (q^r) 2
  norm_num only [Nat.cast_ofNat] at hh
  have he : Real.logb (2:ℝ) ((q^r:ℕ):ℝ) = (r:ℝ)*σ/Real.log 2 := by
    rw [Real.logb,Nat.cast_pow,hq,Real.log_pow,Real.log_exp]
  rw [he] at hh
  have hr' : (r:ℝ)≤5 := by exact_mod_cast hr
  have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hr' hs) hl.le
  calc
    _ ≤ (r:ℝ)*σ/Real.log 2+1 := by linarith only [hh]
    _ ≤ 5*σ/Real.log 2+σ := add_le_add hm hσ
    _ = _ := by ring

lemma root_density_scale {σ τ β : ℝ} {j d : ℕ} (hσ : 1≤σ) (hτ : 0≤τ)
    (hβ : 0≤β) (hj : 2≤j) (hjd : j<d)
    (h : τ≤σ^(-200*(2:ℝ)^(d-2)*β)) :
    Real.sqrt τ ≤ σ^(-200*(2:ℝ)^(j-2)*β) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hpow : (2:ℝ)^(j-2)*2≤(2:ℝ)^(d-2) := by
    rw [←pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have he : -200*(2:ℝ)^(d-2)*β ≤ 2*(-200*(2:ℝ)^(j-2)*β) := by
    have := mul_le_mul_of_nonneg_right hpow hβ
    nlinarith
  have h' := h.trans (Real.rpow_le_rpow_of_exponent_le hσ he)
  have hh : σ^(2*(-200*(2:ℝ)^(j-2)*β))=(σ^(-200*(2:ℝ)^(j-2)*β))^2 := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hs.le (-200*(2:ℝ)^(j-2)*β) 2)
  rw [hh] at h'
  exact (sq_le_sq₀ (Real.sqrt_nonneg τ) (Real.rpow_nonneg hs.le _)).mp
    (by simpa only [Real.sq_sqrt hτ] using h')

theorem eventually_restriction_overheads {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D R b Cb : ℝ) (q r : ℕ), Range η σ D R →
      (q:ℝ)=Real.exp σ → r≤5 → b≤Cb*D*σ^(6*beta η) →
      Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤D*σ^(6*beta η) ∧
      Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤P η σ D R ∧
      b+Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤(Cb+1)*D*σ^(6*beta η) := by
  let C : ℝ := 400*(5/Real.log 2+1)
  have hC : 0<C := by dsimp [C]; positivity
  have hb : 0<7*beta η := mul_pos (by norm_num) (beta_pos hη)
  have hlog : Tendsto (fun σ : ℝ=>(Real.log C+Real.log σ)/σ^(7*beta η)) atTop (𝓝 0) := by
    have hc : Tendsto (fun σ : ℝ=>Real.log C/σ^(7*beta η)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hb)
    have hv := (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero
    simpa only [add_div,add_zero] using hc.add hv
  filter_upwards [eventually_ge_atTop (1:ℝ),hlog.eventually_lt_const (by norm_num : (0:ℝ)<1)] with σ hσ hh
  intro D R b Cb q r hr hq hd hbb
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hbound : Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤σ^(7*beta η) := by
    have hl := Real.log_le_log (by positivity : (0:ℝ)<400*(Nat.log 2 (q^r)+1:ℝ))
      (mul_le_mul_of_nonneg_left (dyadic_levels_le q r σ hσ hq hd) (by norm_num : (0:ℝ)≤400))
    have he : 400*((5/Real.log 2+1)*σ)=C*σ := by dsimp [C];ring
    rw [he,Real.log_mul hC.ne' hs.ne'] at hl
    exact hl.trans (by simpa only [one_mul] using (div_le_iff₀ (Real.rpow_pos_of_pos hs _)).mp hh.le)
  have hdlo : σ^(7*beta η)≤D*σ^(6*beta η) := by
    calc
      _ = σ^beta η*σ^(6*beta η) := by rw [←Real.rpow_add hs];congr 1;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hr.dlo (Real.rpow_nonneg hs.le _)
  have hp : σ^(7*beta η)≤P η σ D R :=
    (Real.rpow_le_rpow_of_exponent_le hσ (by have := beta_pos hη;linarith)).trans
      (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
  refine ⟨hbound.trans hdlo,hbound.trans hp,?_⟩
  nlinarith only [hbb,hbound,hdlo]

end SharpRamseyFive.ParameterHierarchy

end OAI
