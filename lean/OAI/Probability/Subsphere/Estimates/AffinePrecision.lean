import Mathlib
import OAI.Probability.Subsphere.Geometry.Affine

namespace OAI

noncomputable section

namespace SubsphereCurrent.Affine
open scoped ENNReal NNReal

lemma log_two_bounds : (1/2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1/2)
    rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,Real.log_inv] at h
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith

lemma log_thousand_lower : (4 : ℝ) ≤ Real.log 1000 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 256) (by norm_num : (256 : ℝ) ≤ 1000)
  rw [show (256 : ℝ) = 2^(8 : ℕ) by norm_num,Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [log_two_bounds.1]

lemma affine_parameters {d n ell : ℕ} (hd : 128 ≤ d) (hn : (d+1)/2 + 2*ell ≤ n) :
    let q := (n-1)/4
    2 ≤ q ∧ n ≤ 5*q ∧ d ≤ 2*n ∧ d/16 ≤ q ∧ d/8 ≤ 2*q ∧
      2*(d/32) ≤ 2*q ∧ ell*(d/16)/q+1 ≤ ell+1 := by
  dsimp
  have hq : 2 ≤ (n-1)/4 := by omega
  have hm : d/16 ≤ (n-1)/4 := by omega
  refine ⟨hq,by omega,by omega,hm,by omega,by omega,?_⟩
  have := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left ell hm)
  omega

lemma log_card_of_width {d J : ℕ} {W : ℝ} (hd : 128 ≤ d) (hJ : 1 ≤ J)
    (hJW : (J : ℝ) ≤ W) (hbudget : W^(1/((d/8 : ℕ) : ℝ)) ≤ (2 : ℝ)^d) :
    Real.log (J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2 := by
  have hp : (0 : ℝ) < (d/8 : ℕ) := by exact_mod_cast (by omega : 0 < d/8)
  have hJp : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hWp : 0 < W := hJp.trans_le hJW
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hWp _) hbudget
  rw [Real.log_rpow hWp,Real.log_pow] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hp.le
  have he : ((d/8 : ℕ) : ℝ)*(1/((d/8 : ℕ) : ℝ)*Real.log W) = Real.log W := by
    field_simp
  rw [he] at hmul
  exact (Real.log_le_log hJp hJW).trans (by nlinarith [hmul])

lemma affine_raw_bound {d n ell J : ℕ} {η : ℝ}
    (hd : 128 ≤ d) (hn : (d+1)/2 + 2*ell ≤ n) (hell : 1 ≤ ell)
    (hJ : 1 ≤ J)
    (hbudget : Real.log (J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2)
    (hη : 0 < η) (hsmall : 16*((1000 : ℝ)^32)^ell*η ≤ 1) :
    ((3 : ℝ)*4^n * η^(2*((n-1)/4))) *
      ((32768 : ℝ)^n * (J : ℝ)^(1/(((n-1)/4 : ℕ) : ℝ)))^
        (ell*(d/16)/((n-1)/4)+1) ≤
      (16*((1000 : ℝ)^32)^ell*η)^(2*(d/32)) := by
  let q := (n-1)/4
  let a := 2*(d/32)
  let b := ell*(d/16)/q+1
  let c : ℝ := 16*((1000 : ℝ)^32)^ell
  obtain ⟨hq,hnq,hdn,_,hpq,haq,hb⟩ := affine_parameters hd hn
  have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hJp : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hnp : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnr : (n : ℝ) ≤ 5*q := by exact_mod_cast hnq
  have hdr : (d : ℝ) ≤ 2*n := by exact_mod_cast hdn
  have hpr : ((d/8 : ℕ) : ℝ) ≤ 2*q := by exact_mod_cast hpq
  have hbr : (b : ℝ) ≤ ell+1 := by exact_mod_cast hb
  have her : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have har : (a : ℝ) ≤ 2*q := by exact_mod_cast haq
  have hcp : 0 < c := by dsimp [c]; positivity
  have hlogη : Real.log η ≤ -Real.log c := by
    have hl := Real.log_le_log (mul_pos hcp hη) hsmall
    rw [Real.log_mul hcp.ne' hη.ne',Real.log_one] at hl
    linarith
  have hMQ : Real.log (J : ℝ)/q ≤ 2*d := by
    apply (div_le_iff₀ hqp).2
    have hh := mul_le_mul_of_nonneg_left log_two_bounds.2
      (show 0 ≤ ((d/8 : ℕ) : ℝ)*d by positivity)
    have hh' := mul_le_mul_of_nonneg_right hpr (Nat.cast_nonneg d)
    nlinarith
  have hlog32 : Real.log (32768 : ℝ) ≤ 15 := by
    rw [show (32768 : ℝ) = 2^(15 : ℕ) by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_two_bounds.2]
  have hi : (n : ℝ)*Real.log 32768 + Real.log (J : ℝ)/q ≤ 19*n := by
    have := mul_le_mul_of_nonneg_left hlog32 (Nat.cast_nonneg n)
    linarith
  have hfull : (b : ℝ)*((n : ℝ)*Real.log 32768 + Real.log (J : ℝ)/q) ≤ 38*n*ell := by
    calc
      _ ≤ (b : ℝ)*(19*n) := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg b)
      _ ≤ ((ell : ℝ)+1)*(19*n) := mul_le_mul_of_nonneg_right hbr (by positivity)
      _ ≤ 38*n*ell := by nlinarith [mul_nonneg (Nat.cast_nonneg n (α := ℝ)) (sub_nonneg.mpr her)]
  have hlogc : 128*(ell : ℝ) ≤ Real.log c := by
    dsimp [c]
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
    have := mul_le_mul_of_nonneg_left log_thousand_lower (show 0 ≤ (ell : ℝ)*32 by positivity)
    have h16 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hcost : Real.log 3 + (n : ℝ)*Real.log 4 +
      (b : ℝ)*((n : ℝ)*Real.log 32768 + Real.log (J : ℝ)/q) ≤ 2*q*Real.log c := by
    have h3 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 3)
    have h4 := mul_le_mul_of_nonneg_left (Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4))
      (Nat.cast_nonneg n)
    have hqc := mul_le_mul_of_nonneg_left hlogc (show (0 : ℝ) ≤ 2*q by positivity)
    have hnell := mul_le_mul_of_nonneg_right hnr (Nat.cast_nonneg ell)
    have hne : (n : ℝ) ≤ n*ell := by nlinarith
    nlinarith
  have hηcost := mul_le_mul_of_nonneg_left hlogη (sub_nonneg.mpr har)
  apply (Real.log_le_log_iff (by positivity) (by positivity : 0 < (c*η)^a)).1
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,Real.log_pow,
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_rpow hJp,
    Real.log_pow,Real.log_mul hcp.ne' hη.ne']
  change Real.log 3 + (n : ℝ)*Real.log 4 + ((2*q : ℕ) : ℝ)*Real.log η +
    (b : ℝ)*((n : ℝ)*Real.log 32768 + (1/(q : ℝ))*Real.log (J : ℝ)) ≤
      (a : ℝ)*(Real.log c+Real.log η)
  rw [show (1/(q : ℝ))*Real.log (J : ℝ) = Real.log (J : ℝ)/q by ring]
  push_cast
  nlinarith

lemma affine_zero_bound {n a : ℕ} {η : ℝ} (hn : 3 ≤ n) (ha : a ≤ n-1)
    (hη : 0 ≤ η) (hsmall : 16*η ≤ 1) :
    (3 : ℝ)*4^n * η^(n-1) ≤ (16*η)^a := by
  have he : n = (n-3)+3 := by omega
  have he' : n-1 = (n-3)+2 := by omega
  have hc : (3 : ℝ)*4^n ≤ 16^(n-1) := by
    calc
      (3 : ℝ)*4^n = 192*4^(n-3) := by
        conv_lhs => rw [he,pow_add]
        norm_num
        ring
      _ ≤ 256*16^(n-3) := by
        have hh : (4 : ℝ)^(n-3) ≤ 16^(n-3) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        have h0 : (0 : ℝ) ≤ 4^(n-3) := by positivity
        linarith
      _ = (16 : ℝ)^(n-1) := by rw [he',pow_add]; norm_num; ring
  calc
    _ ≤ 16^(n-1)*η^(n-1) := mul_le_mul_of_nonneg_right hc (pow_nonneg hη _)
    _ = (16*η)^(n-1) := by rw [mul_pow]
    _ ≤ _ := pow_le_pow_of_le_one (by positivity) hsmall ha

end SubsphereCurrent.Affine
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u v
namespace SubsphereCurrent.Affine

lemma simulated_numeric_bound {d n ell : ℕ} (hd : 128 ≤ d)
    (hn : (d+1)/2+2*ell ≤ n) (A : Test d n)
    {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (hbudget : Real.log (Fintype.card J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2)
    (L : Fixed.Stream A.space J (ell*(d/16))) (hL : L.BorelRules)
    {η : ℝ} (hη : 0 < η) (hsmall : 16*((1000 : ℝ)^32)^ell*η ≤ 1) :
    (∫⁻ z : Sphere A.space × (Fin (ell*(d/16)) → A.space),
      L.euclideanSuccess η z.1.val z.2
        ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space (ell*(d/16)))) ≤
      ENNReal.ofReal ((16*((1000 : ℝ)^32)^ell*η)^(2*(d/32))) := by
  have hnpos : 0 < n := by omega
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hnpos)
  obtain ⟨hq,_,_,_,_,haq,_⟩ := affine_parameters hd hn
  by_cases hell : ell = 0
  · subst ell
    revert L
    rw [Nat.zero_mul]
    simp only [pow_zero,mul_one]
    intro L hL
    simp only [pow_zero,mul_one] at hsmall
    have hη1 : η ≤ 1 := by nlinarith
    have hb := Fixed.Stream.average_euclideanSuccess_zero_bound (E := A.space) (J := J)
      L hL hη hη1
    rw [A.dimension,← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3*4^n)] at hb
    exact hb.trans (ENNReal.ofReal_le_ofReal (affine_zero_bound (a := 2*(d/32)) (n := n) (by omega) (by omega) hη.le hsmall))
  · let q := (n-1)/4
    let a := 2*q
    let b := ell*(d/16)/q+1
    have ha : 2*a ≤ Module.finrank ℝ A.space-1 := by rw [A.dimension]; dsimp [a,q]; omega
    have hb := L.average_euclideanSuccess_bound hL hη ha hq (le_refl a)
    have ht : (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ A.space) * ENNReal.ofReal (η^a)) *
        SubsphereRegression.streamFactor (E := A.space) (J := J) q ^ b ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top (SubsphereRegression.streamFactor_ne_top q))
    have hr := ENNReal.toReal_mono ht hb
    have hr' : (∫⁻ z : Sphere A.space × (Fin (ell*(d/16)) → A.space),
        L.euclideanSuccess η z.1.val z.2
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space (ell*(d/16)))).toReal ≤
        ((3 : ℝ)*4^n * η^(2*((n-1)/4))) *
          ((32768 : ℝ)^n * (Fintype.card J : ℝ)^(1/(((n-1)/4 : ℕ) : ℝ)))^
            (ell*(d/16)/((n-1)/4)+1) := by
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3*4^n),
        ENNReal.toReal_ofReal (by positivity : 0 ≤ η^a),SubsphereRegression.streamFactor,
        ENNReal.toReal_pow,← ENNReal.toReal_rpow,A.dimension,a,q,b, sphereLaw,Fixed.sphereLaw] using hr
    apply (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ht hb) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal (by positivity)]
    exact hr'.trans (affine_raw_bound hd hn (by omega) Fintype.card_pos hbudget hη hsmall)

lemma estimate_one_seed {d n ell : ℕ} (hd : 128 ≤ d)
    (hn : (d+1)/2+2*ell ≤ n) (A : Test d n)
    {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (hbudget : Real.log (Fintype.card J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2)
    (L : Fixed.Stream (Vector d) J (ell*(d/16))) (hL : L.BorelRules)
    (hu : ∀ q, ∀ᵐ y ∂L.output q, ‖y‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ z : Sphere A.space × (Fin (ell*(d/16)) → Vector d),
      L.angularSuccess ε (A.point z.1) z.2
        ∂(sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) (ell*(d/16)))) ≤
      ENNReal.ofReal (((16*((1000 : ℝ)^32)^ell*ε)/A.radius)^(2*(d/32))) := by
  have hnpos : 0 < n := by omega
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hnpos)
  let : IsProbabilityMeasure (sphereLaw A.space) := Fixed.sphereLaw_probability
  by_cases hsmall : 16*((1000 : ℝ)^32)^ell*(ε/A.radius) ≤ 1
  · apply Simulation.average_le_of_simulated A L hL hu ε
    intro w
    simpa only [mul_div_assoc] using simulated_numeric_bound hd hn A hbudget
      (Simulation.stream A L w) (Simulation.borel A L hL w) (div_pos hε A.radius_positive) hsmall
  · calc
      _ ≤ ∫⁻ _ : Sphere A.space × (Fin (ell*(d/16)) → Vector d), (1 : ℝ≥0∞)
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) (ell*(d/16))) :=
        lintegral_mono (fun _ => prob_le_one)
      _ = 1 := by simp
      _ ≤ _ := ENNReal.one_le_ofReal.2 (one_le_pow₀ (by simpa only [mul_div_assoc] using le_of_lt (lt_of_not_ge hsmall)))

theorem all_affine_estimate : AllAffineEstimate.{u,v} := by
  refine ⟨128,?_⟩
  intro d hd k hk W hW J _ _ _ _ hJW hbudget ε hε hε1 Ω _ ρ hρ L hL ell hell state n hn A hmexp
  let : IsProbabilityMeasure ρ := hρ
  have hnpos : 0 < n := by omega
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hnpos)
  let : IsProbabilityMeasure (sphereLaw A.space) := Fixed.sphereLaw_probability
  let : IsFiniteMeasure (Fixed.rowsLaw (Vector d) (ell*(d/16))) := inferInstance
  let : SFinite (Fixed.rowsLaw (Vector d) (ell*(d/16))) := by
    let : SigmaFinite (Fixed.rowsLaw (Vector d) (ell*(d/16))) := IsFiniteMeasure.toSigmaFinite _
    infer_instance
  have hlog := log_card_of_width hd Fintype.card_pos hJW hbudget
  let e := swapFirstTwo Ω (Sphere A.space) (Fin (ell*(d/16)) → Vector d)
  have hp := measurePreserving_swapFirstTwo ρ (sphereLaw A.space) (Fixed.rowsLaw (Vector d) (ell*(d/16)))
  have hm' := hmexp.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  have he := hp.lintegral_comp_emb e.measurableEmbedding
    (fun z : Sphere A.space × (Ω × (Fin (ell*(d/16)) → Vector d)) =>
      ((L z.2.1).suffix ((k-ell)*(d/16)) (ell*(d/16)) state).angularSuccess ε (A.point z.1) z.2.2)
  dsimp only [Function.comp_def] at hm'
  rw [← he,lintegral_prod _ hm']
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (((16*((1000 : ℝ)^32)^ell*ε)/A.radius)^(2*(d/32))) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [hL] with ω hω
      exact estimate_one_seed hd hn A hlog
        ((L ω).suffix ((k-ell)*(d/16)) (ell*(d/16)) state)
        (fun t q a => hω.1 _ q a) hω.2 hε
    _ = _ := by simp

end SubsphereCurrent.Affine
end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u v
namespace SubsphereCurrent.Affine

theorem all_affine_full_estimate : AllAffineFullEstimate.{u,v} := by
  refine ⟨128,?_⟩
  intro d hd k hk W hW J _ _ _ _ hJW hbudget ε hε hε1 Ω _ ρ hρ L hL ell hell state n hn A
  let : IsProbabilityMeasure ρ := hρ
  have hnpos : 0 < n := by omega
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hnpos)
  let : IsProbabilityMeasure (sphereLaw A.space) := Fixed.sphereLaw_probability
  let : IsFiniteMeasure (Fixed.rowsLaw (Vector d) (ell*(d/16))) := inferInstance
  let : SFinite (Fixed.rowsLaw (Vector d) (ell*(d/16))) := by
    let : SigmaFinite (Fixed.rowsLaw (Vector d) (ell*(d/16))) := IsFiniteMeasure.toSigmaFinite _
    infer_instance
  have hlog := log_card_of_width hd Fintype.card_pos hJW hbudget
  let e := swapFirstTwo Ω (Sphere A.space) (Fin (ell*(d/16)) → Vector d)
  have hp := measurePreserving_swapFirstTwo ρ (sphereLaw A.space) (Fixed.rowsLaw (Vector d) (ell*(d/16)))
  have he := hp.lintegral_comp_emb e.measurableEmbedding
    (fun z : Sphere A.space × (Ω × (Fin (ell*(d/16)) → Vector d)) =>
      ((L z.2.1).suffix ((k-ell)*(d/16)) (ell*(d/16)) state).angularSuccess ε (A.point z.1) z.2.2)
  rw [← he]
  apply (lintegral_prod_le _).trans
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (((16*((1000 : ℝ)^32)^ell*ε)/A.radius)^(2*(d/32))) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [hL] with ω hω
      exact estimate_one_seed hd hn A hlog
        ((L ω).suffix ((k-ell)*(d/16)) (ell*(d/16)) state)
        (fun t q a => hω.1 _ q a) hω.2 hε
    _ = _ := by simp

end SubsphereCurrent.Affine

end

end OAI
