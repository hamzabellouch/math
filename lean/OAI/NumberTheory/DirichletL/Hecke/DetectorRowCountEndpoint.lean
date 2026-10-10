import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountOptimization
import OAI.NumberTheory.DirichletL.Endpoint

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

lemma denominator_endpoint (x : ℝ) : denominator x=Endpoint.denominator (1/2-x) := by
  unfold denominator Endpoint.denominator
  ring

lemma primeWeight_endpoint (x : ℝ) : primeWeight x=Endpoint.primeWeight (1/2-x) := by
  unfold primeWeight Endpoint.primeWeight
  ring

theorem balanced_cutoff_bounds {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    1≤Endpoint.balancedCutoff δ (1/2-x) ∧ Endpoint.balancedCutoff δ (1/2-x)≤3/2 := by
  have hy : 0≤1/2-x := by linarith
  have hy' : 1/2-x≤1/2 := by linarith
  have hd := Endpoint.denominator_bounds hy hy'
  have hp := Endpoint.primeWeight_bounds hy hy'
  have hJ := Endpoint.balanceDenominator_bounds hδ hδ' hy hy'
  have hJp : 0<Endpoint.balanceDenominator δ (1/2-x) := by linarith [hJ.1]
  unfold Endpoint.balancedCutoff
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hδ (by linarith [hp.1])) (by positivity))
  · have hnum : δ*Endpoint.primeWeight (1/2-x)≤Endpoint.balanceDenominator δ (1/2-x) := by
      unfold Endpoint.balanceDenominator
      have hh := mul_nonneg (sub_nonneg.mpr hδ') (show 0≤Endpoint.denominator (1/2-x) by linarith [hd.1])
      linarith
    have hh : δ*Endpoint.primeWeight (1/2-x)/(2*Endpoint.balanceDenominator δ (1/2-x))≤1/2 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith

theorem balanced_count_identity {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    max (shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x)))
        (longExponent δ (Endpoint.balancedCutoff δ (1/2-x))) =
      Endpoint.balancedRowCount δ (1/2-x) := by
  have hy : 0≤1/2-x := by linarith
  have hy' : 1/2-x≤1/2 := by linarith
  have hDb : 0<Endpoint.denominator (1/2-x) := by
    have hh := Endpoint.denominator_bounds hy hy'
    linarith [hh.1]
  have hJb : 0<Endpoint.balanceDenominator δ (1/2-x) := by
    have hh := Endpoint.balanceDenominator_bounds hδ hδ' hy hy'
    linarith [hh.1]
  have hl : longExponent δ (Endpoint.balancedCutoff δ (1/2-x))=
      Endpoint.balancedRowCount δ (1/2-x) := by
    unfold longExponent Endpoint.balancedRowCount
    ring
  have hs : shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x))=
      Endpoint.balancedRowCount δ (1/2-x) := by
    unfold shortExponent
    rw [denominator_endpoint,primeWeight_endpoint]
    unfold Endpoint.balancedRowCount Endpoint.balancedCutoff
    generalize hDd : Endpoint.denominator (1/2-x) = D at *
    generalize hPd : Endpoint.primeWeight (1/2-x) = P at *
    generalize hJd : Endpoint.balanceDenominator δ (1/2-x) = J at *
    have hJdef : J=(5/6-δ)*D+δ*P := by
      rw [←hJd, Endpoint.balanceDenominator, hDd, hPd]
    have hD : D ≠ 0 := hDb.ne'
    have hJ : J ≠ 0 := hJb.ne'
    field_simp [hD,hJ]
    rw [hJdef]
    ring
  rw [hl,hs,max_self]

theorem high_bin_count {B C U δ r ε γ : ℝ}
    (hC : 0≤C) (hU : 1≤U) (hδ : 5/6≤δ) (hδ' : δ≤1)
    (hγ : 0≤γ) (hr : 1-γ≤r)
    (hI : B≤C*U^(max 1 ((1+5*r)/6)-δ*r+ε)) :
    B≤C*U^(1-δ+ε+γ) := by
  apply hI.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  by_cases hr1 : 1≤r
  · rw [max_eq_right (show 1≤(1+5*r)/6 by linarith)]
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hδ) (sub_nonneg.mpr hr1)
    nlinarith
  · rw [max_eq_left (show (1+5*r)/6≤1 by linarith)]
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤δ by linarith)
    have hh' := mul_le_mul_of_nonneg_right hδ' hγ
    nlinarith

theorem high_bin_endpoint {δ q R loss : ℝ} (_hδ : 5/6≤δ)
    (hq : q≤δ/2) (hR : R≤1-δ+loss) :
    -(1/48 : ℝ)+(2/3)*δ+q/6-(13/16)*(1-R)≤
      -1/48-δ/16+(13/16)*loss := by
  linarith

theorem balanced_endpoint_with_loss {δ x R loss : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hR : R≤max (shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x)))
      (longExponent δ (Endpoint.balancedCutoff δ (1/2-x)))+loss) :
    -(1/48 : ℝ)+(2/3)*δ+(δ*x)/6-(13/16)*(1-R)≤
      -49/440640+(13/16)*loss := by
  rw [balanced_count_identity hδ hδ' hx hx'] at hR
  have hh := Endpoint.balanced_endpoint_margin hδ hδ'
    (show 0≤1/2-x by linarith) (show 1/2-x≤1/2 by linarith)
  unfold Endpoint.balancedExponent at hh
  nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI
