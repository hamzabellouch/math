import OAI.MathematicalPhysics.Transonic.Exterior.TraceRun
import OAI.MathematicalPhysics.Transonic.Exterior.Weight

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open PowerSeries FixedInterval ShootingParameters NormalizedTrace

def scaledReflected (u : Series) : Series := rescale (1/256) (reflected u)

lemma scaledReflected_zero {u : Series} (h : coeff 0 u=1) :
    coeff 0 (scaledReflected u)=0 := by
  simp only [scaledReflected,coeff_rescale,pow_zero,one_mul,reflected_zero h]
lemma scaledReflected_one {u : Series} {s:ℝ} (h : coeff 1 u=s) :
    coeff 1 (scaledReflected u)=s/256 := by
  simp only [scaledReflected,coeff_rescale,pow_one,reflected_one h];ring
lemma scaledReflected_equation (sigma kappa c : ℝ) (u : Series)
    (he : Formal.residual sigma kappa c u=0) :
    scaledResidual (1/256) sigma kappa c (scaledReflected u)=0 := by
  rw [scaledReflected,scaledResidual_rescale,reflected_equation sigma kappa c u he]
  simp
lemma scaled_ratio_identity {t:ℝ} (ht : t∈Set.Icc leftEnd rightEnd) :
    ratio t*(2*(1-sigma t)*(slope t/256))=
      (1/256)*(1-(3/5:ℝ))*(2*kappa t+3)-2*(1-sigma t)*(slope t/256) := by
  linear_combination (1/256:ℝ)*(ratio_identity ht)

lemma enclose_source {Q : ℤ} (hQ : 0<Q) (boxes : Weights) (tr : Trace)
    (hv : Valid Q 7 73 boxes tr) {t : ℝ} (ht : t∈Set.Icc leftEnd rightEnd)
    (ha : WeightsHold Q boxes (1/256) (sigma t) (kappa t) (3/5))
    (h1 : Holds Q (tr.b 1) (slope t/256))
    (hd : ∀ n, 2≤n → n≤73 → Holds Q (tr.den n)
      (2*(1-sigma t)*(slope t/256)*(ratio t-n)))
    (u : Series) (hu0 : coeff 0 u=1) (hu1 : coeff 1 u=slope t)
    (he : Formal.residual (sigma t) (kappa t) (3/5) u=0) :
    ∀ n, 1≤n → n≤73 → Holds Q (tr.b n) (coeff n (scaledReflected u)) ∧
      (2≤n → Holds Q (tr.r n) (coeff n (scaledReflected u)/coeff (n-1) (scaledReflected u)) ∧
        Holds Q (tr.sc n) (squareRatio (scaledReflected u) n)) := by
  exact run hQ 7 73 (by norm_num) boxes (1/256) (sigma t) (kappa t) (3/5)
    (slope t/256) (ratio t) ha tr hv (scaledReflected u) (scaledReflected_zero hu0)
    (scaledReflected_one hu1) (scaledReflected_equation _ _ _ _ he)
    (scaled_ratio_identity ht) h1 hd

lemma source_coeff74_pos {Q : ℤ} (hQ : 0<Q) (boxes : Weights) (tr : Trace)
    (hv : Valid Q 7 73 boxes tr) (hv74 : ValidRow Q 7 74 boxes tr)
    (hn74 : 0<(tr.num 74).center-(tr.num 74).radius)
    {t : ℝ} (ht : t∈Set.Icc leftEnd rightEnd)
    (ha : WeightsHold Q boxes (1/256) (sigma t) (kappa t) (3/5))
    (h1 : Holds Q (tr.b 1) (slope t/256))
    (hd : ∀ n, 2≤n → n≤73 → Holds Q (tr.den n)
      (2*(1-sigma t)*(slope t/256)*(ratio t-n)))
    (u : Series) (hu0 : coeff 0 u=1) (hu1 : coeff 1 u=slope t)
    (he : Formal.residual (sigma t) (kappa t) (3/5) u=0) : 0<coeff 74 u := by
  let w := scaledReflected u
  have hbound := enclose_source hQ boxes tr hv ht ha h1 hd u hu0 hu1 he
  have hb : ∀ j, 1≤j → j<74 → Holds Q (tr.b j) (coeff j w) := by
    intro j hj hj';exact (hbound j hj (by omega)).1
  have hbpos : ∀ j, 1≤j → j<74 → 0<(tr.b j).center-(tr.b j).radius := by
    intro j hj hj';exact hv.bpos j hj (by omega)
  have h74 := row_enclosed hQ 7 74 (by norm_num) (by norm_num) boxes (1/256)
    (sigma t) (kappa t) (3/5) ha tr hv74 w (scaledReflected_zero hu0) hb hbpos
    (fun j hj hj' => ((hbound j (by omega) (by omega)).2 hj).1)
    (fun j hj hj' => hv.rpos j hj (by omega))
    (fun j hj hj' => ((hbound j (by omega) (by omega)).2 hj).2)
  have hp73 : 0<coeff 73 w := enclosed_pos hQ (hb 73 (by norm_num) (by norm_num))
    (hbpos 73 (by norm_num) (by norm_num))
  have hp74 := enclosed_pos hQ h74.2 hn74
  have hrec := scaled_normalized_recurrence (1/256) (sigma t) (kappa t) (3/5)
    (slope t/256) (ratio t) w (scaledReflected_zero hu0) (scaledReflected_one hu1)
    (scaledReflected_equation _ _ _ _ he) (scaled_ratio_identity ht) 74 (by norm_num)
    (by simpa using ne_of_gt hp73)
  have hdneg : 2*(1-sigma t)*(slope t/256)*(ratio t-74)<0 :=
    mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) (sub_pos.mpr (sigma_bounds ht).2))
      (div_pos (slope_pos ht) (by norm_num))) (sub_neg.mpr (ratio_bounds ht).2)
  norm_num only [Nat.cast_ofNat,show 74-1=73 by norm_num] at hrec hp74
  have hdivneg : coeff 74 w/coeff 73 w<0 := by
    by_contra hh
    have hm := mul_nonpos_of_nonpos_of_nonneg hdneg.le (le_of_not_gt hh)
    rw [hrec] at hm
    exact not_lt_of_ge hm hp74
  have hwneg : coeff 74 w<0 := by simpa using (div_lt_iff₀ hp73).mp hdivneg
  have heq : coeff 74 w= -((1/256:ℝ)^74*coeff 74 u) := by
    simp [w,scaledReflected,reflected,coeff_rescale]
    norm_num
  rw [heq] at hwneg
  have hh : 0<(1/256:ℝ)^74 := by positivity
  nlinarith

end SepticProfile.ExteriorJet

end
end

end OAI
