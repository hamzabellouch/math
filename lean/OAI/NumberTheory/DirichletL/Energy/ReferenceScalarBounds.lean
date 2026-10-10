import OAI.NumberTheory.DirichletL.Energy.ReferenceDivisors

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceScalarBounds
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource

lemma radical_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(d:ℝ)(hd:0≤d):
    (s.puncture.radical.absNorm:ℝ)^d≤Z^(Bmask*d):=by
  have hh:=Real.rpow_le_rpow (Nat.cast_nonneg _) s.radical_bound hd
  simpa only [←Real.rpow_mul (zero_lt_one.trans_le s.base_ge_one).le] using hh

lemma conductor_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap d:ℝ)(hs:s.width≤Mcap)(hd:0≤d):
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))^d*Z^(Mcap*d):=by
  have hZ:0<Z:=zero_lt_one.trans_le s.base_ge_one
  have hM:0≤Mcap:=s.width_nonneg.trans hs
  have hz:1≤Z^Mcap:=Real.one_le_rpow s.base_ge_one hM
  have hc:1≤max 1 ((fixedConductorFactor:ℝ)*bΦ):=le_max_left _ _
  have hbase:max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))*Z^Mcap:=by
    apply max_le
    · nlinarith
    · apply le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hZ.le _))
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hs)
        (zero_le_one.trans hc)
  have hh:=Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hbase hd
  rw [Real.mul_rpow (zero_le_one.trans hc) (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le] at hh
  exact hh

lemma radial_scale {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):
    max 1 s.radial.scale≤Z^s.width:=by
  rw [s.scale_eq]
  apply max_le (Real.one_le_rpow s.base_ge_one s.width_nonneg)
  apply Real.rpow_le_rpow_of_exponent_le s.base_ge_one
  exact le_add_of_nonneg_right s.character_nonneg

lemma physical_slot_product {α:Type*}[Fintype α](Z:ℝ)(hZ:1≤Z)(w:α→ℝ)(Mcap:ℝ)
    (hwidth:(∑i,w i)≤Mcap): (∏i,Z^(w i))≤Z^Mcap:=by
  rw [←Real.rpow_sum_of_pos (zero_lt_one.trans_le hZ)]
  exact Real.rpow_le_rpow_of_exponent_le hZ hwidth

lemma short_slot_mass {α:Type*}[Fintype α]{Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap:ℝ)(hs:s.width≤Mcap)(w:α→ℝ)(hwidth:(∑i,w i)≤Mcap):
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))≤Z^(s.width+5*Mcap/4):=by
  have hz:0<Z:=zero_lt_one.trans_le s.base_ge_one
  calc
    _≤Z^s.width*Z^(Mcap/4)*Z^Mcap:=by
      apply mul_le_mul (mul_le_mul (radial_scale s)
        (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
        (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
        (physical_slot_product Z s.base_ge_one w Mcap hwidth)
        (Finset.prod_nonneg (fun i _=>Real.rpow_nonneg hz.le _)) (by positivity)
    _=Z^(s.width+5*Mcap/4):=by rw [←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring

lemma log_interval (Z L d:ℝ)(hZ:1≤Z)(hL:0≤L)(hd:0<d):
    1+2*(L*Real.log Z)≤(1+2*L/d)*Z^d:=by
  have hlog:=Real.log_le_rpow_div (zero_le_one.trans hZ) hd
  have hone:=Real.one_le_rpow hZ hd.le
  have hh:=mul_le_mul_of_nonneg_left hlog (show 0≤2*L by positivity)
  calc
    _≤Z^d+2*L*(Z^d/d):=by nlinarith
    _=(1+2*L/d)*Z^d:=by ring

end SevenEighths.CenteredMomentEnergyReferenceScalarBounds

end

end OAI
