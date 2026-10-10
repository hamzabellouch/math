import OAI.NumberTheory.TotientAsymptotic.BootstrapNonNormal
import OAI.NumberTheory.TotientAsymptotic.BootstrapSquareDecay

namespace OAI

/-! All failures of regularity are negligible relative to the finite envelope. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_regularity_exception : ∃ ε : ℕ → ℝ,Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ J : ℕ in atTop,∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ v ≤ 2^J ∧
      ¬CountingRegular (loglogCutoff (bootstrapBottom (B ((2:ℝ)^J)))) ((2:ℝ)^J) v) →
    (Q.card:ℝ) ≤ ε J*(dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J)) := by
  classical
  obtain ⟨C,D,hC,hD,hreg⟩ := regular_value_exception_count
  obtain ⟨η,hη,hnormal⟩ := bootstrap_non_normal_exception
  have he0 : Tendsto (fun b : ℝ => Real.exp (-b/4)) atTop (nhds 0) := by
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) (1/4) (by norm_num)
    convert hh using 1
    funext b
    simp only [Real.rpow_zero,one_mul]
    congr 1
    ring
  have he2 : Tendsto (fun b : ℝ => Real.exp (-2*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero,one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) 2 (by norm_num))
  have hb2 : Tendsto (fun b : ℝ => b*Real.exp (-2*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) 2 (by norm_num))
  let ε := fun J : ℕ => C*Real.exp (-B ((2:ℝ)^J)/4)+2*Real.exp (-2*B ((2:ℝ)^J))+
    D*(B ((2:ℝ)^J)*Real.exp (-2*B ((2:ℝ)^J)))+η J
  have hlim : Tendsto ε atTop (nhds 0) := by
    have hh := ((((he0.comp dyadic_B_tendsto).const_mul C).add
      ((he2.comp dyadic_B_tendsto).const_mul 2)).add
      ((hb2.comp dyadic_B_tendsto).const_mul D)).add hη
    simpa only [Function.comp_apply,mul_zero,add_zero] using hh
  refine ⟨ε,hlim,?_⟩
  have hxlim : Tendsto (fun J : ℕ => (2:ℝ)^J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hnormal,dyadic_B_tendsto.eventually (eventually_ge_atTop 1000000000000000000),
    hxlim.eventually (eventually_ge_atTop (Real.exp (Real.exp 1))),eventually_ge_atTop (2:ℕ)]
    with J hnormal hb hx hJ
  let x := (2:ℝ)^J
  let b := B x
  let S := loglogCutoff (bootstrapBottom b)
  have hb0 : 0 ≤ b := by dsimp [b,x]; linarith
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hX4 : 4 ≤ (2:ℕ)^J := by
    have hh : (2:ℕ)^2 ≤ 2^J := Nat.pow_le_pow_right (by norm_num) hJ
    simpa using hh
  have hx4 : (4:ℝ) ≤ x := by
    change (4:ℝ) ≤ (2:ℝ)^J
    exact_mod_cast hX4
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hE1 : 1 ≤ dyadicTotientEnvelope J := dyadicTotientEnvelope_one_le J
  have hbase : 0 ≤ x/Real.log x := by positivity
  have hbaseE : x/Real.log x ≤ dyadicTotientEnvelope J*x/Real.log x := by
    have hh := mul_le_mul_of_nonneg_right hE1 hbase
    simpa only [one_mul,mul_div_assoc] using hh
  have hinv : (Real.log x)⁻¹=Real.exp (-b) := by
    rw [Real.exp_neg,show Real.exp b=Real.log x from Real.exp_log hlog]
  have hS : Real.exp (3*b) ≤ (S:ℝ) := bootstrap_square_cutoff hb
  have hSplus : Real.exp (3*b) ≤ (S+1:ℕ) := by push_cast; linarith
  have hrec : ((S+1:ℕ):ℝ)⁻¹ ≤ Real.exp (-3*b) := by
    have hh := inv_anti₀ (Real.exp_pos (3*b)) hSplus
    simpa only [← Real.exp_neg,neg_mul] using hh
  intro Q hQ
  have hmain := hreg S (2^J) hX4 (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hx) Q (by
    intro v hv
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hQ v hv)
  have hN := hnormal (nonNormalValues S x) (by
    intro v hv
    obtain ⟨hv,n,p,hn,hφ,hp,hpn,hbad⟩ := Finset.mem_filter.mp hv
    have hval := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2
    exact ⟨n,p,hn,hφ,hp,hpn,(Nat.cast_le.mpr hval).trans (Nat.floor_le hx0.le),hbad⟩)
  have hheavy : C*x*(Real.log x)^(-5/4:ℝ) ≤
      C*Real.exp (-b/4)*(dyadicTotientEnvelope J*x/Real.log x) := by
    have hid : C*x*(Real.log x)^(-5/4:ℝ)=C*Real.exp (-b/4)*(x/Real.log x) := by
      have hpow : (Real.log x)^(-5/4:ℝ)=Real.exp (-b/4)*Real.exp (-b) := by
        rw [Real.rpow_def_of_pos hlog,← Real.exp_add]
        congr 1
        dsimp [b,B]
        ring
      rw [hpow]
      simp only [div_eq_mul_inv,hinv]
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left hbaseE (by positivity)
  have hsquare : (2*x+D*x*b)/(S+1:ℕ) ≤
      (2*Real.exp (-2*b)+D*(b*Real.exp (-2*b)))*(dyadicTotientEnvelope J*x/Real.log x) := by
    have hpos : 0 ≤ 2*x+D*x*b := by positivity
    have hh := mul_le_mul_of_nonneg_left hrec hpos
    have hid : (2*x+D*x*b)*Real.exp (-3*b)=
        (2*Real.exp (-2*b)+D*(b*Real.exp (-2*b)))*(x/Real.log x) := by
      rw [div_eq_mul_inv,hinv]
      have he : Real.exp (-3*b)=Real.exp (-2*b)*Real.exp (-b) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    calc
      _ ≤ (2*x+D*x*b)*Real.exp (-3*b) := by simpa only [div_eq_mul_inv] using hh
      _ = _ := hid
      _ ≤ _ := mul_le_mul_of_nonneg_left hbaseE (by positivity)
  have hmain' : (Q.card:ℝ) ≤ C*x*(Real.log x)^(-5/4:ℝ)+
      (2*x+D*x*b)/(S+1:ℕ)+(nonNormalValues S x).card := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hmain
  calc
    _ ≤ C*x*(Real.log x)^(-5/4:ℝ)+(2*x+D*x*b)/(S+1:ℕ)+(nonNormalValues S x).card := hmain'
    _ ≤ C*Real.exp (-b/4)*(dyadicTotientEnvelope J*x/Real.log x)+
        (2*Real.exp (-2*b)+D*(b*Real.exp (-2*b)))*(dyadicTotientEnvelope J*x/Real.log x)+
        η J*(dyadicTotientEnvelope J*x/Real.log x) := by linarith only [hheavy,hsquare,hN]
    _ = _ := by dsimp [ε,b,x]; ring

end TotientAsymptotic

end

end OAI
