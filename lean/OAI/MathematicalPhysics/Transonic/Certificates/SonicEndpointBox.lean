import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section

namespace SepticProfile.SonicEndpointBox
open Polynomial FixedInterval

noncomputable def endpointBox (Q : ℤ) (w : ℕ → Box) (δ : ℚ) : Box :=
  add (add ⟨Q,0⟩ (sumBox 8 0 221 (fun i => rscale ((5/6:ℚ)^i) (w i))))
    (ratBox Q (δ*(5/6:ℚ)^140))

lemma holds_endpoint {Q : ℤ} (hQ : 0<Q) (w : ℕ → Box) (f : PowerSeries ℝ) (δ : ℚ)
    (hw : ∀ n≤220, Holds Q (w n) (PowerSeries.coeff n (f-1))) :
    Holds Q (endpointBox Q w δ) ((EulerPolynomial.barrier f (δ:ℝ)).eval (5/6)) := by
  have hsum := holds_sumBox 8 0 221 (fun i => rscale ((5/6:ℚ)^i) (w i))
    (fun i => ((5/6:ℝ)^i)*PowerSeries.coeff i (f-1)) (by norm_num)
    (fun i _ hi => by
      simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] using holds_rscale ((5/6:ℚ)^i) (hw i (by omega)))
  have he : (∑ i ∈ Finset.Ico 0 221, (5/6:ℝ)^i*PowerSeries.coeff i (f-1))=
      (PowerSeries.trunc 221 (f-1)).eval (5/6) := by
    rw [Nat.Ico_zero_eq_range]
    change _=Polynomial.eval₂ (RingHom.id ℝ) (5/6) (PowerSeries.trunc 221 (f-1))
    rw [PowerSeries.eval₂_trunc_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [RingHom.id_apply,mul_comm]
  have hone : PowerSeries.trunc 221 (1:PowerSeries ℝ)=1 := PowerSeries.trunc_one 220
  have heval : (PowerSeries.trunc 221 (f-1)).eval (5/6)=
      (PowerSeries.trunc 221 f).eval (5/6)-1 := by
    rw [PowerSeries.trunc_sub,hone,Polynomial.eval_sub,Polynomial.eval_one]
  rw [he,heval] at hsum
  have hbase := holds_add (holds_exact Q 1) hsum
  simp only [Int.cast_one,mul_one,add_sub_cancel] at hbase
  have htail := holds_ratBox hQ (δ*(5/6:ℚ)^140)
  have hh := holds_add hbase htail
  unfold endpointBox
  rw [EulerPolynomial.eval_barrier]
  simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] using hh

lemma lower_from_box {Q R a : ℤ} {b : Box} {x : ℝ}
    (hQ : 0<Q) (hR : 0<R) (hx : Holds Q b x)
    (hbd : Q*a≤R*(b.center-b.radius)) : (a:ℝ)/R≤x := by
  have hq : (0:ℝ)<Q := by exact_mod_cast hQ
  have hr : (0:ℝ)<R := by exact_mod_cast hR
  have hb := (bounds hx).1
  have hmul : (Q:ℝ)*a≤R*((b.center:ℝ)-b.radius) := by exact_mod_cast hbd
  apply (div_le_iff₀ hr).mpr
  nlinarith [mul_le_mul_of_nonneg_left hb hr.le]

lemma upper_from_box {Q R a : ℤ} {b : Box} {x : ℝ}
    (hQ : 0<Q) (hR : 0<R) (hx : Holds Q b x)
    (hbd : R*(b.center+b.radius)≤Q*a) : x≤(a:ℝ)/R := by
  have hq : (0:ℝ)<Q := by exact_mod_cast hQ
  have hr : (0:ℝ)<R := by exact_mod_cast hR
  have hb := (bounds hx).2
  have hmul : R*((b.center:ℝ)+b.radius)≤(Q:ℝ)*a := by exact_mod_cast hbd
  apply (le_div_iff₀ hr).mpr
  nlinarith [mul_le_mul_of_nonneg_left hb hr.le]

end SepticProfile.SonicEndpointBox


end

end OAI
