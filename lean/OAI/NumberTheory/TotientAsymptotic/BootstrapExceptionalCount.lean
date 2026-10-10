import OAI.NumberTheory.TotientAsymptotic.BootstrapGoodValues
import OAI.NumberTheory.TotientAsymptotic.CountingEnvelopeReal
import OAI.NumberTheory.TotientAsymptotic.BootstrapGaussianBudget

namespace OAI

/-! Explicit, rather than merely vanishing, preliminary exceptional-value bounds. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def bootstrapErrorWeight (b : ℝ) : ℝ :=
  (b+4)^6*Real.exp (9*(Real.log (b+4))^2-b/600000000)

lemma bootstrap_error_weight_pos {b : ℝ} (hb : 0 ≤ b) :
    0 < bootstrapErrorWeight b := by unfold bootstrapErrorWeight; positivity

lemma bootstrap_error_weight_dominates {b c : ℝ} (hb : 0 ≤ b)
    (hc : (1/600000000:ℝ) ≤ c) :
    Real.exp (-c*b) ≤ bootstrapErrorWeight b := by
  have hp : 1 ≤ (b+4)^6 := one_le_pow₀ (by linarith : (1:ℝ) ≤ b+4)
  have he : Real.exp (-c*b) ≤ Real.exp (9*(Real.log (b+4))^2-b/600000000) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hc hb
    nlinarith only [hh,sq_nonneg (Real.log (b+4))]
  apply he.trans
  change Real.exp (9*(Real.log (b+4))^2-b/600000000) ≤
    (b+4)^6*Real.exp (9*(Real.log (b+4))^2-b/600000000)
  nlinarith only [hp,Real.exp_pos (9*(Real.log (b+4))^2-b/600000000)]

lemma bootstrap_non_normal_nat_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ X : ℕ in atTop,∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧ v ≤ X ∧
      ¬IsNormalPrime (loglogCutoff (bootstrapBottom (B X))) p) →
    (Q.card:ℝ) ≤ C*bootstrapErrorWeight (B X)*(X/Real.log X) := by
  obtain ⟨C,hC,hcount⟩ := uniform_non_normal_value_count
  obtain ⟨E,hE,henv⟩ := counting_envelope_real_bound
  refine ⟨C*E*Real.exp (1/3:ℝ),by positivity,?_⟩
  have hBX : Tendsto (fun X : ℕ => B X) atTop atTop := B_tendsto.comp tendsto_natCast_atTop_atTop
  filter_upwards [hBX.eventually (eventually_ge_atTop 300000000),
    eventually_ge_atTop (256:ℕ)] with X hb hX
  let b := B X
  let S := loglogCutoff (bootstrapBottom b)
  let J := countingDyadicIndex X
  have hx : (256:ℝ) ≤ X := by exact_mod_cast hX
  have hx4 : (4:ℝ) ≤ X := by linarith only [hx]
  have hb0 : 0 ≤ b := by dsimp [b]; linarith only [hb]
  have hS := bootstrap_normality_factor hb
  change 2 < (S:ℝ) ∧ 0 ≤ B S ∧ (Real.log S)^(-1/6:ℝ) ≤
    Real.exp (1/3:ℝ)*Real.exp (-b/600000000) at hS
  have hJ := counting_dyadic_index_bounds hx4
  have hpoly := counting_normality_polynomial hx4 hb0
  have henv := henv X hx4
  have hnorm0 : 0 ≤ (Real.log S)^(-1/6:ℝ) := Real.rpow_nonneg
    (Real.log_pos (by linarith only [hS.1] : (1:ℝ)<S)).le _
  have hlogJ : 0 ≤ 1+Real.log J := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ J by exact_mod_cast hJ.1)
    linarith only [hh]
  have hB2 : 0 ≤ B (2*(X:ℝ)) := by
    have hh : B X ≤ B (2*(X:ℝ)) := Real.log_le_log (Real.log_pos (by linarith only [hx]))
      (Real.log_le_log (by linarith only [hx]) (by linarith only [hx]))
    exact hb0.trans hh
  have hpoly0 : 0 ≤ (B (2*(X:ℝ)))^5*(1+Real.log J) := by positivity
  have hw : dyadicTotientEnvelope J*((B (2*(X:ℝ)))^5*(1+Real.log J))*
      (Real.log S)^(-1/6:ℝ) ≤ E*Real.exp (1/3:ℝ)*bootstrapErrorWeight b := by
    have hp := mul_le_mul henv hpoly hpoly0 (by positivity)
    have hh := mul_le_mul hp hS.2.2 hnorm0 (by positivity)
    apply hh.trans_eq
    unfold bootstrapErrorWeight
    rw [show 9*(Real.log (b+4))^2-b/600000000=
      9*(Real.log (b+4))^2+(-b/600000000) by ring,Real.exp_add]
    ring
  intro Q hQ
  have hh := hcount S X J hS.1 hS.2.1 hx hJ.1 hJ.2.1 Q (by
    intro v hv
    obtain ⟨n,p,hn,hφ,hp,hpn,hvX,hbad⟩ := hQ v hv
    exact ⟨n,p,hn,hφ,hp,hpn,by exact_mod_cast hvX,hbad⟩)
  have hcoef : 0 ≤ C*((X:ℝ)/Real.log X) := by
    have hlog : 0 < Real.log X := Real.log_pos (by linarith only [hx])
    positivity
  calc
    _ ≤ C*dyadicTotientEnvelope J*X/Real.log X*
        (B (2*(X:ℝ)))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := hh
    _ = (C*(X/Real.log X))*(dyadicTotientEnvelope J*
        ((B (2*(X:ℝ)))^5*(1+Real.log J))*(Real.log S)^(-1/6:ℝ)) := by ring
    _ ≤ (C*(X/Real.log X))*(E*Real.exp (1/3:ℝ)*bootstrapErrorWeight b) :=
      mul_le_mul_of_nonneg_left hw hcoef
    _ = _ := by ring

lemma bootstrap_error_weight_mul {b : ℝ} (hb : 0 ≤ b) :
    b*Real.exp (-2*b) ≤ bootstrapErrorWeight b := by
  have hbexp : b ≤ Real.exp b := by linarith only [Real.add_one_le_exp b]
  calc
    _ ≤ Real.exp b*Real.exp (-2*b) := mul_le_mul_of_nonneg_right hbexp (Real.exp_pos _).le
    _ = Real.exp (-b) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by simpa only [neg_one_mul] using bootstrap_error_weight_dominates hb (by norm_num : (1/600000000:ℝ) ≤ 1)

lemma bootstrap_regularity_nat_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ X : ℕ in atTop,∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧
      ¬CountingRegular (loglogCutoff (bootstrapBottom (B X))) X v) →
    (Q.card:ℝ) ≤ C*bootstrapErrorWeight (B X)*(X/Real.log X) := by
  classical
  obtain ⟨C,D,hC,hD,hreg⟩ := regular_value_exception_count
  obtain ⟨N,hN,hnormal⟩ := bootstrap_non_normal_nat_count
  refine ⟨C+2+D+N,by positivity,?_⟩
  have hBX : Tendsto (fun X : ℕ => B X) atTop atTop := B_tendsto.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnormal,hBX.eventually (eventually_ge_atTop 1000000000000000000),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp (Real.exp 1))),
    eventually_ge_atTop (4:ℕ)] with X hnormal hb hx hX
  let b := B X
  let S := loglogCutoff (bootstrapBottom b)
  have hb0 : 0 ≤ b := by dsimp [b]; linarith only [hb]
  have hX0 : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hbase : 0 ≤ (X:ℝ)/Real.log X := by positivity
  have hinv : (Real.log X)⁻¹=Real.exp (-b) := by
    rw [Real.exp_neg,show Real.exp b=Real.log X from Real.exp_log hlog]
  have hS : Real.exp (3*b) ≤ (S:ℝ) := bootstrap_square_cutoff hb
  have hSplus : Real.exp (3*b) ≤ (S+1:ℕ) := by push_cast; linarith only [hS]
  have hrec : ((S+1:ℕ):ℝ)⁻¹ ≤ Real.exp (-3*b) := by
    have hh := inv_anti₀ (Real.exp_pos (3*b)) hSplus
    simpa only [← Real.exp_neg,neg_mul] using hh
  have hheavy : C*X*(Real.log X)^(-5/4:ℝ) ≤
      C*bootstrapErrorWeight b*(X/Real.log X) := by
    have hid : C*X*(Real.log X)^(-5/4:ℝ)=C*Real.exp (-b/4)*(X/Real.log X) := by
      have hpow : (Real.log X)^(-5/4:ℝ)=Real.exp (-b/4)*Real.exp (-b) := by
        rw [Real.rpow_def_of_pos hlog,← Real.exp_add]
        congr 1
        dsimp [b,B]
        ring
      rw [hpow]
      simp only [div_eq_mul_inv,hinv]
      ring
    rw [hid]
    have he : Real.exp (-b/4) ≤ bootstrapErrorWeight b := by
      convert bootstrap_error_weight_dominates hb0 (by norm_num : (1/600000000:ℝ) ≤ 1/4) using 1
      ring_nf
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC.le) hbase
  have hsquare : (2*(X:ℝ)+D*X*b)/(S+1:ℕ) ≤
      (2+D)*bootstrapErrorWeight b*(X/Real.log X) := by
    have hpos : 0 ≤ 2*(X:ℝ)+D*X*b := by positivity
    have hh := mul_le_mul_of_nonneg_left hrec hpos
    have hid : (2*(X:ℝ)+D*X*b)*Real.exp (-3*b)=
        (2*Real.exp (-2*b)+D*(b*Real.exp (-2*b)))*(X/Real.log X) := by
      rw [div_eq_mul_inv,hinv]
      have he : Real.exp (-3*b)=Real.exp (-2*b)*Real.exp (-b) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [he]
      ring
    have he : Real.exp (-2*b) ≤ bootstrapErrorWeight b :=
      bootstrap_error_weight_dominates hb0 (by norm_num)
    have he' := bootstrap_error_weight_mul hb0
    calc
      _ ≤ (2*(X:ℝ)+D*X*b)*Real.exp (-3*b) := by simpa only [div_eq_mul_inv] using hh
      _ = _ := hid
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hbase
        nlinarith only [he,mul_le_mul_of_nonneg_left he' hD.le]
  intro Q hQ
  have hmain := hreg S X hX hx Q hQ
  have hnorm := hnormal (nonNormalValues S X) (by
    intro v hv
    obtain ⟨hv,n,p,hn,hφ,hp,hpn,hbad⟩ := Finset.mem_filter.mp hv
    have hvX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2
    exact ⟨n,p,hn,hφ,hp,hpn,by simpa using hvX,hbad⟩)
  calc
    _ ≤ C*X*(Real.log X)^(-5/4:ℝ)+(2*X+D*X*b)/(S+1:ℕ)+
        (nonNormalValues S X).card := hmain
    _ ≤ C*bootstrapErrorWeight b*(X/Real.log X)+
        (2+D)*bootstrapErrorWeight b*(X/Real.log X)+
        N*bootstrapErrorWeight b*(X/Real.log X) := by linarith only [hheavy,hsquare,hnorm]
    _ = _ := by ring

lemma bootstrap_good_nat_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ X : ℕ in atTop,∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧ ¬BootstrapGood X v) →
    (Q.card:ℝ) ≤ C*bootstrapErrorWeight (B X)*(X/Real.log X) := by
  classical
  obtain ⟨A,hA,hreg⟩ := bootstrap_regularity_nat_count
  obtain ⟨C,hC,hviol⟩ := bootstrap_regular_violation
  refine ⟨A+C,by positivity,?_⟩
  have hBX : Tendsto (fun X : ℕ => B X) atTop atTop := B_tendsto.comp tendsto_natCast_atTop_atTop
  filter_upwards [hreg,hviol,hBX.eventually (eventually_ge_atTop (0:ℝ)),
    eventually_ge_atTop (4:ℕ)] with X hreg hviol hB hX
  let S := loglogCutoff (bootstrapBottom (B X))
  have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hbase : 0 ≤ (X:ℝ)/Real.log X := by positivity
  intro Q hQ
  let R := Q.filter (fun v => ¬CountingRegular S X v)
  let T := Q\R
  have hR := hreg R (by
    intro v hv
    obtain ⟨hv,hr⟩ := Finset.mem_filter.mp hv
    exact ⟨(hQ v hv).1,(hQ v hv).2.1,hr⟩)
  have hT := hviol T (by
    intro v hv
    obtain ⟨hv,hvR⟩ := Finset.mem_sdiff.mp hv
    have hr : CountingRegular S X v := by
      by_contra hh
      exact hvR (Finset.mem_filter.mpr ⟨hv,hh⟩)
    have hf : ¬∀ n : ℕ,0 < n → n.totient=v →
        a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B X := by
      intro hh
      exact (hQ v hv).2.2 ⟨hr,hh⟩
    push Not at hf
    obtain ⟨n,hn,hφ,hbad⟩ := hf
    exact ⟨(hQ v hv).2.1,hr,n,hn,hφ,hbad⟩)
  have ht : (T.card:ℝ) ≤ C*bootstrapErrorWeight (B X)*(X/Real.log X) := by
    have hid : C*X*(Real.log X)^(-201/200:ℝ)=C*Real.exp (-B X/200)*(X/Real.log X) := by
      have hinv : (Real.log X)⁻¹=Real.exp (-B X) := by rw [Real.exp_neg,B,Real.exp_log hlog]
      have hp : (Real.log X)^(-201/200:ℝ)=Real.exp (-B X/200)*Real.exp (-B X) := by
        rw [Real.rpow_def_of_pos hlog,← Real.exp_add]
        congr 1
        unfold B
        ring
      rw [hp]
      simp only [div_eq_mul_inv,hinv]
      ring
    have he : Real.exp (-B X/200) ≤ bootstrapErrorWeight (B X) := by
      convert bootstrap_error_weight_dominates hB (by norm_num : (1/600000000:ℝ) ≤ 1/200) using 1
      ring_nf
    exact hT.trans (hid ▸ mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC.le) hbase)
  have hcard : (Q.card:ℝ)=(R.card:ℝ)+(T.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card (show R ⊆ Q from Finset.filter_subset _ _)
    exact_mod_cast (show Q.card=R.card+T.card by dsimp [T]; omega)
  rw [hcard]
  calc
    _ ≤ A*bootstrapErrorWeight (B X)*(X/Real.log X)+C*bootstrapErrorWeight (B X)*(X/Real.log X) := add_le_add hR ht
    _ = _ := by ring

theorem bootstrap_good_nat_gaussian : ∃ C : ℝ,0 < C ∧
    ∀ᶠ X : ℕ in atTop,∀ Ψ : ℕ,Ψ ≤ m X → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧ ¬BootstrapGood X v) →
    (Q.card:ℝ) ≤ C*(X/Real.log X)*G X (m X)*Real.exp (-(Ψ:ℝ)^2/4) := by
  obtain ⟨C,hC,hcount⟩ := bootstrap_good_nat_count
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,tendsto_natCast_atTop_atTop.eventually
    (bootstrap_error_gaussian_budget (by norm_num : (0:ℝ)<1/600000000)),
    tendsto_natCast_atTop_atTop.eventually central_volume_one_le,
    eventually_ge_atTop (4:ℕ)] with X hc hb hG hX
  intro Ψ hΨ Q hQ
  have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hbase : 0 ≤ C*((X:ℝ)/Real.log X) := by positivity
  have hsq : (Ψ:ℝ)^2 ≤ (m X:ℝ)^2 := by
    have hh : (Ψ:ℝ) ≤ m X := by exact_mod_cast hΨ
    nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) Ψ,Nat.cast_nonneg (α:=ℝ) (m X)]
  have hw : bootstrapErrorWeight (B X) ≤ Real.exp (-(Ψ:ℝ)^2/4) := by
    have hh : bootstrapErrorWeight (B X) ≤ Real.exp (-(m X:ℝ)^2/4) := by
      simpa only [bootstrapErrorWeight,div_eq_mul_inv,one_mul,mul_comm] using hb
    exact hh.trans (Real.exp_le_exp.mpr (by linarith only [hsq]))
  calc
    _ ≤ C*bootstrapErrorWeight (B X)*(X/Real.log X) := hc Q hQ
    _ = (C*(X/Real.log X))*bootstrapErrorWeight (B X) := by ring
    _ ≤ (C*(X/Real.log X))*Real.exp (-(Ψ:ℝ)^2/4) := mul_le_mul_of_nonneg_left hw hbase
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hG hbase
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
