import Mathlib
import OAI.Probability.SKFluctuations.RealSKPressureL1

namespace OAI

/-! Comparison Cap Travel. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem cap_travel_identity {a b : ℝ} (hab : a≤b) {α M : ℝ → ℝ} {C : ℝ≥0}
    (hα : LipschitzOnWith C α (Icc a b)) (hm : StrictMonoOn α (Icc a b))
    (hM : ∀ r ∈ Icc a b, 0<M (α r))
    (hd : ∀ᵐ r, r ∈ Icc a b → deriv α r=M (α r)) :
    (∫ u in α a..α b, 1/M u)=b-a := by
  have hab' : α a≤α b := hm.monotoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  have he := lipschitz_interval_integral_image hab hα hm.injOn (fun u => 1/M u)
  rw [hα.continuousOn.image_Icc_of_monotoneOn hab hm.monotoneOn] at he
  rw [intervalIntegral.integral_of_le hab',←integral_Icc_eq_integral_Ioc,he]
  calc
    (∫ r in Icc a b, |deriv α r| *(1/M (α r)))=∫ r in Icc a b, (1:ℝ) := by
      apply setIntegral_congr_ae measurableSet_Icc
      filter_upwards [hd] with r hr hri
      rw [hr hri,abs_of_pos (hM r hri)]
      field_simp [(hM r hri).ne']
    _ = b-a := by simp [sub_nonneg.mpr hab]

 theorem comparisonCap_first_term {N δ U L E d u : ℝ} (hN : 0<N)
    (hU : 0<U) (hL : 0<L) (hE : 0<E) (hd : 0≤d) (hu : 0≤u) :
    0<comparisonCap N δ U L E d u ∧
      1/comparisonCap N δ U L E d u≤(L/N^δ)*(1/(u+U)) := by
  have hq : 0<N^δ := Real.rpow_pos_of_pos hN _
  have hU' : 0<u+U := by linarith
  have hb : N^δ*((u+U)/L)≤comparisonCap N δ U L E d u := by
    unfold comparisonCap
    have hh : 0≤(d^3/E)*(u+U)^2 := by positivity
    nlinarith
  have hpos : 0<N^δ*((u+U)/L) := by positivity
  refine ⟨hpos.trans_le hb,?_⟩
  calc
    1/comparisonCap N δ U L E d u≤1/(N^δ*((u+U)/L)) :=
      one_div_le_one_div_of_le hpos hb
    _ = (L/N^δ)*(1/(u+U)) := by field_simp

 theorem comparisonCap_log_travel {N δ U L E d a b : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hE : 0<E) (hd : 0≤d)
    (ha : 0≤a) (hab : a≤b) :
    (∫ u in a..b, 1/comparisonCap N δ U L E d u)≤
      (L/N^δ)*Real.log ((b+U)/(a+U)) := by
  have hpos (u : ℝ) (hu : u ∈ Icc a b) := comparisonCap_first_term (δ:=δ) hN hU hL hE hd (ha.trans hu.1)
  have hi : IntervalIntegrable (fun u => 1/comparisonCap N δ U L E d u) volume a b :=
    (continuousOn_const.div (comparisonCap_continuous N δ U L E d).continuousOn
      (fun u hu => (hpos u hu).1.ne')).intervalIntegrable_of_Icc hab
  have hj : IntervalIntegrable (fun u => (L/N^δ)*(1/(u+U))) volume a b :=
    ((continuousOn_const.div (continuous_id.add continuous_const).continuousOn
      (fun u hu => ne_of_gt (by linarith [hu.1] : 0<u+U))).const_mul _).intervalIntegrable_of_Icc hab
  have he : (∫ u in a..b, (L/N^δ)*(1/(u+U)))=
      (L/N^δ)*Real.log ((b+U)/(a+U)) := by
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_add_right (f := fun u : ℝ => 1/u),
      integral_one_div_of_pos (by linarith) (by linarith)]
  rw [←he]
  exact intervalIntegral.integral_mono_on hab hi hj (fun u hu => (hpos u hu).2)

 theorem comparisonCap_band_travel {N δ U L E d a b v : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hE : 0<E) (hd : 0<d)
    (hv : 0<v) (hva : v≤a+U) (ha : 0≤a) (hab : a≤b) :
    (∫ u in a..b, 1/comparisonCap N δ U L E d u)≤
      (b-a)*E/(N^δ*d^3*v^2) := by
  have hq : 0<N^δ := Real.rpow_pos_of_pos hN _
  have hpos (u : ℝ) (hu : u ∈ Icc a b) := comparisonCap_first_term (δ:=δ) hN hU hL hE hd.le (ha.trans hu.1)
  have hi : IntervalIntegrable (fun u => 1/comparisonCap N δ U L E d u) volume a b :=
    (continuousOn_const.div (comparisonCap_continuous N δ U L E d).continuousOn
      (fun u hu => (hpos u hu).1.ne')).intervalIntegrable_of_Icc hab
  have hbnd (u : ℝ) (hu : u ∈ Icc a b) :
      1/comparisonCap N δ U L E d u≤E/(N^δ*d^3*v^2) := by
    have hvu : v≤u+U := by linarith [hu.1]
    have hbase : N^δ*(d^3/E)*v^2≤comparisonCap N δ U L E d u := by
      unfold comparisonCap
      have hlin : 0≤(u+U)/L := div_nonneg (by linarith [hu.1]) hL.le
      have hs : v^2≤(u+U)^2 := sq_le_sq₀ hv.le (by linarith) |>.mpr hvu
      nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0≤N^δ*(d^3/E))]
    calc
      _ ≤ 1/(N^δ*(d^3/E)*v^2) := one_div_le_one_div_of_le (by positivity) hbase
      _ = E/(N^δ*d^3*v^2) := by field_simp
  have hb := intervalIntegral.integral_mono_on hab hi (intervalIntegrable_const)
    hbnd
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hb
  convert hb using 1; ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open Set

def comparisonBracket (p r S B : ℝ) : ℝ := (2-p)*r-2*(1-p)*S-p*B/r

 theorem comparisonBracket_antitone {p q r S B : ℝ} (hr : 0<r)
    (hB : S^2≤B) (hpq : p≤q) : comparisonBracket q r S B≤comparisonBracket p r S B := by
  have he : (comparisonBracket p r S B-comparisonBracket q r S B)*r=
      (q-p)*((r-S)^2+(B-S^2)) := by
    unfold comparisonBracket
    field_simp
    ring
  have h0 : 0≤(q-p)*((r-S)^2+(B-S^2)) := mul_nonneg (sub_nonneg.mpr hpq)
    (add_nonneg (sq_nonneg _) (sub_nonneg.mpr hB))
  nlinarith

 theorem comparisonBracket_nonneg_geometry {p r S B : ℝ} (hr : 0<r)
    (hp : p ∈ Icc (0:ℝ) 1) (hS : 0≤S) (hB : S^2≤B)
    (hG : 0≤comparisonBracket p r S B) : S≤r ∧ p*B≤2*r^2 := by
  have he : comparisonBracket p r S B*r=2*r*(r-S)-p*((r-S)^2+(B-S^2)) := by
    unfold comparisonBracket
    field_simp
    ring
  have h0 := mul_nonneg hG hr.le
  have hz : 0≤p*((r-S)^2+(B-S^2)) := mul_nonneg hp.1
    (add_nonneg (sq_nonneg _) (sub_nonneg.mpr hB))
  have hSr : S≤r := by nlinarith
  refine ⟨hSr,?_⟩
  have hpS : 0≤(1-p)*S := mul_nonneg (sub_nonneg.mpr hp.2) hS
  have he' : comparisonBracket p r S B*r=(2-p)*r^2-2*(1-p)*S*r-p*B := by
    unfold comparisonBracket
    field_simp
  nlinarith [mul_nonneg hpS hr.le,mul_nonneg hp.1 (sq_nonneg r)]

 theorem comparisonBracket_increment {a b p Sa Sb Ba Bb : ℝ}
    (ha : 0<a) (hab : a≤b) (hba : b≤2*a) (hp : p ∈ Icc (0:ℝ) 1)
    (hBb : p*Bb≤2*b^2) (hB : Ba≤Bb)
    (hleft : comparisonBracket p a Sa Ba≤0) (hright : 0≤comparisonBracket p b Sb Bb) :
    2*(1-p)*(Sb-Sa)≤6*(b-a) := by
  have hb : 0<b := ha.trans_le hab
  have he : (comparisonBracket p b Sb Bb-comparisonBracket p a Sa Ba)*a*b=
      ((2-p)*(b-a)-2*(1-p)*(Sb-Sa))*a*b+p*(Ba*b-Bb*a) := by
    unfold comparisonBracket
    field_simp
    ring
  have hsign : 0≤(comparisonBracket p b Sb Bb-comparisonBracket p a Sa Ba)*a*b := by
    exact mul_nonneg (mul_nonneg (by linarith) ha.le) hb.le
  have hcomp : p*(Ba*b-Bb*a)≤p*Bb*(b-a) := by
    have hh := mul_nonneg (mul_nonneg hp.1 (sub_nonneg.mpr hB)) hb.le
    nlinarith
  have hbnd : p*Bb*(b-a)≤2*b^2*(b-a) := mul_le_mul_of_nonneg_right hBb (sub_nonneg.mpr hab)
  have hratio : 2*b^2*(b-a)≤4*a*b*(b-a) := by
    have hh := mul_nonneg (mul_nonneg (sub_nonneg.mpr hba) hb.le) (sub_nonneg.mpr hab)
    nlinarith
  have hpterm : (2-p)*(b-a)*a*b≤2*(b-a)*a*b := by
    have hh := mul_nonneg (mul_nonneg (mul_nonneg hp.1 (sub_nonneg.mpr hab)) ha.le) hb.le
    nlinarith
  have hall : (2*(1-p)*(Sb-Sa)-6*(b-a))*(a*b)≤0 := by
    nlinarith
  have ht : 2*(1-p)*(Sb-Sa)-6*(b-a)≤0 :=
    nonpos_of_mul_nonpos_left hall (mul_pos ha hb)
  exact sub_nonpos.mp ht

 theorem comparisonBracket_endpoint_increment {a b p q Sa Sb Ba Bb : ℝ}
    (ha : 0<a) (hab : a≤b) (hba : b≤2*a)
    (hpq : p≤q) (hq : q ∈ Icc (0:ℝ) 1)
    (hSb : 0≤Sb) (hBa : Sa^2≤Ba) (hBb : Sb^2≤Bb) (hB : Ba≤Bb)
    (hleft : comparisonBracket p a Sa Ba≤0) (hright : 0≤comparisonBracket q b Sb Bb) :
    Sb≤b ∧ 2*(1-q)*(Sb-Sa)≤6*(b-a) := by
  have hg := comparisonBracket_nonneg_geometry (ha.trans_le hab) hq hSb hBb hright
  exact ⟨hg.1,comparisonBracket_increment ha hab hba hq hg.2 hB
    ((comparisonBracket_antitone ha hBa hpq).trans hleft) hright⟩

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology

 theorem potential_integral_eq_sub {a b : ℝ} (hab : a≤b) {H J G : ℝ → ℝ}
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hd : ∀ᵐ t, t ∈ Icc a b → HasDerivAt H (J t*G t) t) :
    (∫ t in a..b, J t*G t)=H b-H a := by
  rw [←hH.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hd] with t ht hti
  rw [uIoc_of_le hab] at hti
  exact (ht ⟨hti.1.le,hti.2⟩).deriv.symm

 theorem potential_negative_left_witness {a b : ℝ} (hab : a<b) {H J G : ℝ → ℝ}
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hJ : ∀ t ∈ Icc a b, 0<J t)
    (hd : ∀ᵐ t, t ∈ Icc a b → HasDerivAt H (J t*G t) t)
    (hdec : H b<H a) : ∃ t ∈ Ioo a b, G t<0 := by
  by_contra hx
  push Not at hx
  have hnon : 0≤∫ t in a..b, J t*G t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab.le
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [volume.ae_ne a,volume.ae_ne b] with t hta htb hti
    exact mul_nonneg (hJ t hti).le (hx t ⟨lt_of_le_of_ne hti.1 hta.symm,
      lt_of_le_of_ne hti.2 htb⟩)
  rw [potential_integral_eq_sub hab.le hH hd] at hnon
  linarith

 theorem potential_positive_right_witness {a b : ℝ} (hab : a<b) {H J G : ℝ → ℝ}
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hJ : ∀ t ∈ Icc a b, 0<J t)
    (hd : ∀ᵐ t, t ∈ Icc a b → HasDerivAt H (J t*G t) t)
    (hinc : H a<H b) : ∃ t ∈ Ioo a b, 0<G t := by
  by_contra hx
  push Not at hx
  have hnon : (∫ t in a..b, J t*G t)≤0 := by
    rw [intervalIntegral.integral_of_le hab.le]
    apply integral_nonpos_of_ae
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [volume.ae_ne b] with t htb hti
    exact mul_nonpos_of_nonneg_of_nonpos (hJ t ⟨hti.1.le,hti.2⟩).le
      (hx t ⟨hti.1,lt_of_le_of_ne hti.2 htb⟩)
  rw [potential_integral_eq_sub hab.le hH hd] at hnon
  linarith

 theorem potential_cap_witnesses {a b r : ℝ} {H J G : ℝ → ℝ}
    (hr : r ∈ Ioo a b) (hH : AbsolutelyContinuousOnInterval H a b)
    (hJ : ∀ t ∈ Icc a b, 0<J t)
    (hd : ∀ᵐ t, t ∈ Icc a b → HasDerivAt H (J t*G t) t)
    (ha : H a=0) (hb : H b=0) (hneg : H r<0) :
    (∃ t ∈ Ioo a r, G t<0) ∧ (∃ t ∈ Ioo r b, 0<G t) := by
  have hab := hr.1.trans hr.2
  constructor
  · apply potential_negative_left_witness hr.1
      (hH.mono (by simp only [uIcc_of_le hab.le,uIcc_of_le hr.1.le]; exact Icc_subset_Icc le_rfl hr.2.le))
      (fun t ht => hJ t ⟨ht.1,ht.2.trans hr.2.le⟩)
      (hd.mono fun t ht hti => ht ⟨hti.1,hti.2.trans hr.2.le⟩)
    simpa only [ha] using hneg
  · apply potential_positive_right_witness hr.2
      (hH.mono (by simp only [uIcc_of_le hab.le,uIcc_of_le hr.2.le]; exact Icc_subset_Icc hr.1.le le_rfl))
      (fun t ht => hJ t ⟨hr.1.le.trans ht.1,ht.2⟩)
      (hd.mono fun t ht hti => ht ⟨hr.1.le.trans hti.1,hti.2⟩)
    simpa only [hb] using hneg

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology

 theorem comparisonBracket_mono_moments {p r S T B C : ℝ} (hr : 0<r)
    (hp : p ∈ Icc (0:ℝ) 1) (hST : S≤T) (hBC : B≤C) :
    comparisonBracket p r T C≤comparisonBracket p r S B := by
  unfold comparisonBracket
  have hs := mul_le_mul_of_nonneg_left hST (by linarith [hp.2] : 0≤2*(1-p))
  have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBC hp.1) hr.le
  linarith

 theorem comparisonBracket_left_mismatch {a r p S B : ℝ} (ha : 0<a)
    (har : a≤r) (hp : p ∈ Icc (0:ℝ) 1) (hS : 0≤S) (hSr : S≤r)
    (hB : S^2≤B) (hleft : comparisonBracket p a S B≤0) :
    (S-r)^2≤16*(r-a)^2+2*(B-S^2) := by
  have hr : 0<r := ha.trans_le har
  have he : comparisonBracket p a S B*a=(2-p)*a^2-2*(1-p)*S*a-p*B := by
    unfold comparisonBracket
    field_simp
  have hh : (2-p)*a^2-2*(1-p)*S*a-p*B≤0 := by
    rw [←he]
    exact mul_nonpos_of_nonpos_of_nonneg hleft ha.le
  have hpos : 0≤(1-p)*S := mul_nonneg (sub_nonneg.mpr hp.2) hS
  have hdiff : (2-p)*(r^2-a^2)-2*(1-p)*S*(r-a)≤4*r*(r-a) := by
    have hp0 := mul_nonneg hp.1 (by nlinarith : 0≤r^2-a^2)
    have hsub := mul_nonneg hpos (sub_nonneg.mpr har)
    nlinarith [sq_nonneg (r-a)]
  have hD : 0≤B-S^2 := sub_nonneg.mpr hB
  have hpD : p*(B-S^2)≤B-S^2 := mul_le_of_le_one_left hD hp.2
  have hcoef : r*(r-S)≤(r-S)*((2-p)*r+p*S) := by
    have h1 := mul_nonneg (sub_nonneg.mpr hp.2) hr.le
    have h2 := mul_nonneg hp.1 hS
    have h3 := mul_nonneg (sub_nonneg.mpr hSr) (add_nonneg h1 h2)
    nlinarith
  have hlin : r*(r-S)≤4*r*(r-a)+(B-S^2) := by nlinarith
  have hsmall : (r-S)^2≤4*(r-a)*(r-S)+(B-S^2) := by
    by_cases hbig : r-S≤4*(r-a)
    · have ht := mul_le_mul_of_nonneg_right hbig (sub_nonneg.mpr hSr)
      nlinarith
    · have ht := mul_nonneg hS (by linarith : 0≤r-S-4*(r-a))
      nlinarith
  nlinarith [sq_nonneg ((r-S)-4*(r-a))]

 theorem comparisonBracket_endpoint_increment_uniform {a b p q Sa Sb Ba Bb κ : ℝ}
    (ha : 0<a) (hab : a≤b) (hκ : 0<κ) (hpq : p≤q)
    (hq : q ∈ Icc (0:ℝ) (1-κ)) (hSa : 0≤Sa) (hSb : 0≤Sb)
    (hBa : Sa^2≤Ba) (hBb : Sb^2≤Bb) (hB : Ba≤Bb)
    (hleft : comparisonBracket p a Sa Ba≤0) (hright : 0≤comparisonBracket q b Sb Bb) :
    κ*(Sb-Sa)≤3*(b-a) := by
  have hq' : q ∈ Icc (0:ℝ) 1 := ⟨hq.1,by linarith [hq.2]⟩
  have hκ1 : κ≤1 := by linarith [hq.1,hq.2]
  by_cases hba : b≤2*a
  · have ht := (comparisonBracket_endpoint_increment ha hab hba hpq hq' hSb hBa hBb hB hleft hright).2
    by_cases hinc : Sa≤Sb
    · have hle := mul_le_mul_of_nonneg_right (show κ≤1-q by linarith [hq.2]) (sub_nonneg.mpr hinc)
      linarith
    · have ht' := mul_nonpos_of_nonneg_of_nonpos hκ.le (by linarith : Sb-Sa≤0)
      linarith
  · have hSb' := (comparisonBracket_nonneg_geometry (ha.trans_le hab) hq' hSb hBb hright).1
    have ht := mul_le_mul_of_nonneg_left (show Sb-Sa≤b by linarith) hκ.le
    have ht' := mul_le_of_le_one_left (ha.trans_le hab).le hκ1
    linarith

 theorem cap_S_le_right {a b r : ℝ} {H J p S B : ℝ → ℝ}
    (ha : 0≤a) (hr : r ∈ Ioo a b)
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hJ : ∀ t ∈ Icc a b, 0<J t)
    (hd : ∀ᵐ t, t ∈ Icc a b → HasDerivAt H (J t*comparisonBracket (p t) t (S t) (B t)) t)
    (hb : H b=0) (hneg : H r<0)
    (hp : ∀ t ∈ Ioo a b, p t ∈ Icc (0:ℝ) 1)
    (hS : MonotoneOn S (Ioo a b))
    (hS0 : ∀ t ∈ Ioo a b, 0≤S t) (hB : ∀ t ∈ Ioo a b, (S t)^2≤B t) :
    S r≤b := by
  have hab := hr.1.trans hr.2
  obtain ⟨t,ht,hgt⟩ := potential_positive_right_witness hr.2
    (hH.mono (by simp only [uIcc_of_le hab.le,uIcc_of_le hr.2.le]; exact Icc_subset_Icc hr.1.le le_rfl))
    (fun t ht => hJ t ⟨hr.1.le.trans ht.1,ht.2⟩)
    (hd.mono fun t ht hti => ht ⟨hr.1.le.trans hti.1,hti.2⟩) (by simpa only [hb] using hneg)
  have hti : t ∈ Ioo a b := ⟨hr.1.trans ht.1,ht.2⟩
  have hg := (comparisonBracket_nonneg_geometry (ha.trans_lt hti.1) (hp t hti)
    (hS0 t hti) (hB t hti) hgt.le).1
  exact (hS hr hti ht.1.le).trans (hg.trans ht.2.le)

 theorem cap_interior_increment {a b s t κ : ℝ} {H J p S B : ℝ → ℝ}
    (ha : 0≤a) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s≤t) (hκ : 0<κ)
    (hH : AbsolutelyContinuousOnInterval H a b) (hJ : ∀ r ∈ Icc a b, 0<J r)
    (hd : ∀ᵐ r, r ∈ Icc a b → HasDerivAt H (J r*comparisonBracket (p r) r (S r) (B r)) r)
    (haH : H a=0) (hbH : H b=0) (hsH : H s<0) (htH : H t<0)
    (hp : MonotoneOn p (Ioo a b)) (hpB : ∀ r ∈ Ioo a b, p r ∈ Icc (0:ℝ) (1-κ))
    (hS : MonotoneOn S (Ioo a b)) (hBm : MonotoneOn B (Ioo a b))
    (hS0 : ∀ r ∈ Ioo a b, 0≤S r) (hB : ∀ r ∈ Ioo a b, (S r)^2≤B r) :
    κ*(S t-S s)≤3*(b-a) := by
  obtain ⟨⟨l,hl,hgl⟩,_⟩ := potential_cap_witnesses hs hH hJ hd haH hbH hsH
  obtain ⟨_,r,hr,hgr⟩ := potential_cap_witnesses ht hH hJ hd haH hbH htH
  have hli : l ∈ Ioo a b := ⟨hl.1,hl.2.trans hs.2⟩
  have hri : r ∈ Ioo a b := ⟨ht.1.trans hr.1,hr.2⟩
  have hlr : l≤r := hl.2.le.trans (hst.trans hr.1.le)
  have hh := comparisonBracket_endpoint_increment_uniform (ha.trans_lt hl.1) hlr hκ
    (hp hli hri hlr) (hpB r hri) (hS0 l hli) (hS0 r hri) (hB l hli) (hB r hri)
    (hBm hli hri hlr) hgl.le hgr.le
  have hSl := hS hli hs hl.2.le
  have hSr := hS ht hri hr.1.le
  have hmul := mul_le_mul_of_nonneg_left (show S t-S s≤S r-S l by linarith) hκ.le
  linarith [hl.1,hr.2]

 theorem cap_interior_mismatch {a b r : ℝ} {H J p S B : ℝ → ℝ}
    (ha : 0≤a) (hr : r ∈ Ioo a b) (hH : AbsolutelyContinuousOnInterval H a b)
    (hJ : ∀ t ∈ Icc a b, 0<J t)
    (hd : ∀ᵐ t, t ∈ Icc a b → HasDerivAt H (J t*comparisonBracket (p t) t (S t) (B t)) t)
    (haH : H a=0) (hbH : H b=0) (hneg : H r<0)
    (hp : MonotoneOn p (Ioo a b)) (hpB : ∀ t ∈ Ioo a b, p t ∈ Icc (0:ℝ) 1)
    (hS : MonotoneOn S (Ioo a b)) (hBm : MonotoneOn B (Ioo a b))
    (hS0 : ∀ t ∈ Ioo a b, 0≤S t) (hB : ∀ t ∈ Ioo a b, (S t)^2≤B t) :
    (S r-r)^2≤16*(b-a)^2+2*(B r-(S r)^2) := by
  have hD : 0≤B r-(S r)^2 := sub_nonneg.mpr (hB r hr)
  by_cases hSr : S r≤r
  · obtain ⟨⟨l,hl,hgl⟩,_⟩ := potential_cap_witnesses hr hH hJ hd haH hbH hneg
    have hli : l ∈ Ioo a b := ⟨hl.1,hl.2.trans hr.2⟩
    have hleft := (comparisonBracket_mono_moments (ha.trans_lt hl.1) (hpB r hr)
      (hS hli hr hl.2.le) (hBm hli hr hl.2.le)).trans
      ((comparisonBracket_antitone (ha.trans_lt hl.1) (hB l hli) (hp hli hr hl.2.le)).trans hgl.le)
    have hh := comparisonBracket_left_mismatch (ha.trans_lt hl.1) hl.2.le (hpB r hr)
      (hS0 r hr) hSr (hB r hr) hleft
    have he : (r-l)^2≤(b-a)^2 := sq_le_sq₀ (sub_nonneg.mpr hl.2.le)
      (by linarith [hr.1,hr.2] : 0≤b-a) |>.mpr (by linarith [hl.1,hr.2])
    linarith
  · have hh := cap_S_le_right ha hr hH hJ hd hbH hneg hpB hS hS0 hB
    have he : (S r-r)^2≤(b-a)^2 := sq_le_sq₀ (by linarith : 0≤S r-r)
      (by linarith [hr.1,hr.2] : 0≤b-a) |>.mpr (by linarith [hr.1])
    nlinarith [sq_nonneg (b-a)]

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem comparisonBracket_nonpos_of_radius_le {p r S B : ℝ} (hr : 0<r)
    (hp : 0≤p) (hSr : r≤S) (hB : S^2≤B) :
    comparisonBracket p r S B≤0 := by
  have he : comparisonBracket p r S B*r=2*r*(r-S)-p*((r-S)^2+(B-S^2)) := by
    unfold comparisonBracket
    field_simp
    ring
  have hz := mul_nonneg hp (add_nonneg (sq_nonneg (r-S)) (sub_nonneg.mpr hB))
  have hh := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤2*r) (sub_nonpos.mpr hSr)
  exact nonpos_of_mul_nonpos_left (by linarith : comparisonBracket p r S B*r≤0) hr

 theorem cap_travel_le_total {a b : ℝ} (hab : a≤b) {α M : ℝ → ℝ} {C : ℝ≥0}
    (hα : LipschitzOnWith C α (Icc a b)) (hm : StrictMonoOn α (Icc a b))
    (hαr : ∀ r ∈ Icc a b, α r ∈ Icc (0:ℝ) 1)
    (hMc : ContinuousOn M (Icc (0:ℝ) 1)) (hM : ∀ u ∈ Icc (0:ℝ) 1, 0<M u)
    (hd : ∀ᵐ r, r ∈ Icc a b → deriv α r=M (α r)) :
    b-a≤∫ u in (0:ℝ)..1, 1/M u := by
  rw [←cap_travel_identity hab hα hm (fun r hr => hM _ (hαr r hr)) hd]
  have hab' := hm.monotoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  have hsub : Ioc (α a) (α b) ⊆ Ioc (0:ℝ) 1 :=
    Ioc_subset_Ioc (hαr a ⟨le_rfl,hab⟩).1 (hαr b ⟨hab,le_rfl⟩).2
  have hi : IntegrableOn (fun u => 1/M u) (Ioc (0:ℝ) 1) :=
    ((continuousOn_const.div hMc (fun u hu => (hM u hu).ne')).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le hab',intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]
  apply setIntegral_mono_set hi _ (Eventually.of_forall fun u hu => hsub hu)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  change 0≤1/M u
  exact one_div_nonneg.mpr (hM u ⟨hu.1.le,hu.2⟩).le

 theorem potential_negative_center_bound {a r : ℝ} {H J p S B α M : ℝ → ℝ} {C : ℝ≥0}
    (ha : 0≤a) (hr : r ∈ Ioc a 1)
    (hH : AbsolutelyContinuousOnInterval H a 1)
    (hJ : ∀ t ∈ Icc a 1, 0<J t)
    (hd : ∀ᵐ t, t ∈ Icc a 1 → HasDerivAt H (J t*comparisonBracket (p t) t (S t) (B t)) t)
    (hcap : ∀ᵐ t, t ∈ Icc a 1 → H t<0 → deriv α t=M (α t))
    (hneg : H r<0) (hp : ∀ t ∈ Ioc a 1, 0≤p t)
    (hS : MonotoneOn S (Ioc a 1)) (hS1 : S r≤1)
    (hB : ∀ t ∈ Ioc a 1, (S t)^2≤B t)
    (hα : LipschitzOnWith C α (Icc a 1)) (hm : StrictMonoOn α (Icc a 1))
    (hαr : ∀ t ∈ Icc a 1, α t ∈ Icc (0:ℝ) 1)
    (hMc : ContinuousOn M (Icc (0:ℝ) 1)) (hM : ∀ u ∈ Icc (0:ℝ) 1, 0<M u) :
    S r≤r+(∫ u in (0:ℝ)..1, 1/M u) := by
  have ha1 : a≤1 := hr.1.le.trans hr.2
  have hnon : 0≤∫ u in (0:ℝ)..1, 1/M u :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u hu => (hM u ⟨hu.1,hu.2⟩).le |> one_div_nonneg.mpr)
  by_cases hSr : S r≤r
  · linarith
  have hrs : r≤S r := by linarith
  have hsub : Icc r (S r) ⊆ Icc a 1 := Icc_subset_Icc hr.1.le hS1
  have hneg' (t : ℝ) (ht : t ∈ Icc r (S r)) : H t<0 := by
    have hrt : r≤t := ht.1
    have ht1 : t≤1 := ht.2.trans hS1
    have hH' : AbsolutelyContinuousOnInterval H r t :=
      hH.mono (by simpa only [uIcc_of_le ha1,uIcc_of_le hrt] using (Icc_subset_Icc hr.1.le ht1 : Icc r t ⊆ Icc a 1))
    have hD' := hd.mono (fun s hs (hsi : s ∈ Icc r t) => hs ⟨hr.1.le.trans hsi.1,hsi.2.trans ht1⟩)
    have hi : (∫ s in r..t, J s*comparisonBracket (p s) s (S s) (B s))≤0 := by
      rw [intervalIntegral.integral_of_le hrt]
      apply integral_nonpos_of_ae
      apply (ae_restrict_iff' measurableSet_Ioc).mpr
      filter_upwards [] with s hsi
      have hsi' : s ∈ Ioc a 1 := ⟨hr.1.trans hsi.1,hsi.2.trans ht1⟩
      apply mul_nonpos_of_nonneg_of_nonpos (hJ s ⟨hsi'.1.le,hsi'.2⟩).le
      apply comparisonBracket_nonpos_of_radius_le (ha.trans_lt hsi'.1) (hp s hsi') _ (hB s hsi')
      exact (hsi.2.trans ht.2).trans (hS hr hsi' hsi.1.le)
    rw [potential_integral_eq_sub hrt hH' hD'] at hi
    linarith
  have ht := cap_travel_le_total hrs (hα.mono hsub) (hm.mono hsub)
    (fun t ht => hαr t (hsub ht)) hMc hM
    (hcap.mono fun t ht hti => ht (hsub hti) (hneg' t hti))
  linarith

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem potential_future_center_bound {a r s : ℝ}
    {H J p S B α M k : ℝ → ℝ} {C : ℝ≥0}
    (ha : 0≤a) (hr : r ∈ Ioc a 1) (hrs : r ≤ s) (hs : s ≤ 1)
    (hH : AbsolutelyContinuousOnInterval H a 1)
    (hJ : ∀ t ∈ Icc a 1, 0<J t)
    (hd : ∀ᵐ t, t ∈ Icc a 1 → HasDerivAt H (J t*comparisonBracket (p t) t (S t) (B t)) t)
    (hcap : ∀ᵐ t, t ∈ Icc a 1 → H t<0 → deriv α t=M (α t))
    (hfloor : ∀ᵐ t, t ∈ Icc a 1 → 0<H t → deriv α t=k t)
    (hzero : ∀ᵐ t, t ∈ Icc a 1 → H t=0 → S t≤t)
    (hp : ∀ t ∈ Ioc a 1, 0≤p t)
    (hS : MonotoneOn S (Ioc a 1)) (hS1 : ∀ t ∈ Ioc a 1, S t≤1)
    (hB : ∀ t ∈ Ioc a 1, (S t)^2≤B t)
    (hα : LipschitzOnWith C α (Icc a 1)) (hm : StrictMonoOn α (Icc a 1))
    (hαr : ∀ t ∈ Icc a 1, α t ∈ Icc (0:ℝ) 1)
    (hMc : ContinuousOn M (Icc (0:ℝ) 1)) (hM : ∀ u ∈ Icc (0:ℝ) 1, 0<M u)
    (hki : IntegrableOn k (Icc (0:ℝ) 1)) (hk : ∀ t ∈ Icc (0:ℝ) 1, 0≤k t)
    (hinc : (∫ t in (0:ℝ)..1, k t)<α s-α r) :
    S r≤ s+(∫ u in (0:ℝ)..1, 1/M u) := by
  let T := ∫ u in (0:ℝ)..1, 1/M u
  have hT : 0≤T := intervalIntegral.integral_nonneg (by norm_num)
    (fun u hu => one_div_nonneg.mpr (hM u hu).le)
  by_contra hnot
  have hlarge : s+T<S r := lt_of_not_ge hnot
  have hsub : Icc r s ⊆ Icc a 1 := Icc_subset_Icc hr.1.le hs
  have hsub₀ : Icc r s ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc (ha.trans hr.1.le) hs
  have hf : ∀ᵐ t, t ∈ Icc r s → deriv α t=k t := by
    filter_upwards [hfloor,hzero] with t hf hz hti
    have hti' : t ∈ Ioc a 1 := ⟨hr.1.trans_le hti.1,hti.2.trans hs⟩
    have hmom := hS hr hti' hti.1
    have hpos : 0<H t := by
      rcases lt_trichotomy (H t) 0 with hneg|heq|hpos
      · have hc := potential_negative_center_bound ha hti' hH hJ hd hcap hneg hp hS
          (hS1 t hti') hB hα hm hαr hMc hM
        change S t≤t+T at hc
        linarith [hti.2]
      · linarith [hz (hsub hti) heq,hti.2]
      · exact hpos
    exact hf (hsub hti) hpos
  have hαac : AbsolutelyContinuousOnInterval α r s := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K:=C)
    simpa only [uIcc_of_le hrs] using hα.mono hsub
  have he : α s-α r=∫ t in r..s, k t := by
    rw [←hαac.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hf] with t ht hti
    rw [uIoc_of_le hrs] at hti
    exact ht ⟨hti.1.le,hti.2⟩
  have hb : (∫ t in r..s, k t)≤∫ t in (0:ℝ)..1, k t := by
    rw [intervalIntegral.integral_of_le hrs,intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]
    apply setIntegral_mono_set (hki.mono_set Ioc_subset_Icc_self) _
      (Eventually.of_forall fun t ht => (Ioc_subset_Ioc (ha.trans hr.1.le) hs) ht)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hk t ⟨ht.1.le,ht.2⟩
  linarith

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology

 theorem comparisonFloor_antiderivative {N δ U r : ℝ} (hN : 0<N) (hU : 0<U)
    (hr : 0≤r) :
    HasDerivAt (fun t => -(N^δ*U^2)/(t+N^(2*δ)*U)) (comparisonFloor N δ U r) r := by
  have hz : r+N^(2*δ)*U≠0 := ne_of_gt (by positivity)
  have hh := (hasDerivAt_const r (-(N^δ*U^2))).div
    ((hasDerivAt_id r).add_const (N^(2*δ)*U)) hz
  exact hh.congr_deriv (by simp only [comparisonFloor,id_eq]; ring)

 theorem comparisonFloor_integral {N δ U : ℝ} (hN : 0<N) (hU : 0<U) :
    (∫ r in (0:ℝ)..1, comparisonFloor N δ U r)=
      N^δ*U^2/(N^(2*δ)*U)-N^δ*U^2/(1+N^(2*δ)*U) := by
  have hc := comparisonFloor_continuousOn (δ:=δ) hN hU (show (0:ℝ)≤0 by rfl)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (hr : r ∈ uIcc (0:ℝ) 1) => comparisonFloor_antiderivative hN hU
      (by
        have hr' : r ∈ Icc (0:ℝ) 1 := by simpa using hr
        exact hr'.1))
    (hc.intervalIntegrable_of_Icc (show (0:ℝ)≤1 by norm_num))
  convert hh using 1; simp; ring

 theorem comparisonFloor_total_mass {N δ U : ℝ} (hN : 0<N) (hU : 0<U) :
    (∫ r in (0:ℝ)..1, comparisonFloor N δ U r)≤N^(-δ)*U := by
  rw [comparisonFloor_integral hN hU]
  have he : N^δ*U^2/(N^(2*δ)*U)=N^(-δ)*U := by
    rw [mul_comm (2:ℝ) δ,Real.rpow_mul hN.le,Real.rpow_two,Real.rpow_neg hN.le]
    field_simp [hU.ne',(Real.rpow_pos_of_pos hN δ).ne']
  rw [he]
  exact sub_le_self _ (by positivity)

 theorem comparisonFloor_region_mass {N δ U r₀ : ℝ} (hN : 0<N) (hU : 0<U)
    (hr₀ : r₀ ∈ Icc (0:ℝ) 1) (A : Set ℝ) (hA : MeasurableSet A) (α : ℝ → ℝ)
    (hd : ∀ᵐ r, r ∈ Icc r₀ 1 → r ∈ A → deriv α r=comparisonFloor N δ U r) :
    (∫ r in Icc r₀ 1, A.indicator (deriv α) r)≤N^(-δ)*U := by
  have he : (∫ r in Icc r₀ 1, A.indicator (deriv α) r)=
      ∫ r in Icc r₀ 1, A.indicator (comparisonFloor N δ U) r := by
    apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [hd] with r hr hri
    by_cases hra : r ∈ A
    · simp only [indicator_of_mem hra,hr hri hra]
    · simp only [indicator_of_notMem hra]
  rw [he]
  have hki : IntegrableOn (comparisonFloor N δ U) (Icc (0:ℝ) 1) :=
    (comparisonFloor_continuousOn (δ:=δ) hN hU (show (0:ℝ)≤0 by rfl)).integrableOn_Icc
  have hik : IntegrableOn (A.indicator (comparisonFloor N δ U)) (Icc (0:ℝ) 1) :=
    hki.indicator hA
  have hsub : Icc r₀ 1 ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc hr₀.1 le_rfl
  calc
    _ ≤ ∫ r in Icc (0:ℝ) 1, A.indicator (comparisonFloor N δ U) r := by
      apply setIntegral_mono_set hik _ (Filter.Eventually.of_forall fun r hr => hsub hr)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      change 0≤A.indicator (comparisonFloor N δ U) r
      by_cases hra : r ∈ A
      · simpa only [indicator_of_mem hra] using (comparisonFloor_pos (δ:=δ) hN hU hr.1).le
      · simp only [indicator_of_notMem hra,le_refl]
    _ ≤ ∫ r in Icc (0:ℝ) 1, comparisonFloor N δ U r := by
      apply integral_mono_ae hik hki
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      by_cases hra : r ∈ A
      · simp only [indicator_of_mem hra,le_refl]
      · simpa only [indicator_of_notMem hra] using (comparisonFloor_pos (δ:=δ) hN hU hr.1).le
    _ = ∫ r in (0:ℝ)..1, comparisonFloor N δ U r := by
      rw [intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num),integral_Icc_eq_integral_Ioc]
    _ ≤ _ := comparisonFloor_total_mass hN hU

end SKFluctuations.Hierarchy

end

end OAI
