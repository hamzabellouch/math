import OAI.Analysis.FourierLLogL.Paths.Energies
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


lemma sky_variance (s : Scene M) (h : Climb s) (u : Grid M) (L : ℝ)
    (hp : ∀ b, energy (s.smaller b) u ≤ L) :
    gust s u^2 ≤ 100*L*(fax s+shower u s) := by
  let v := meanV s u; let n := nub s u
  let m := matter s; let g := shell s
  let d := fun i z => mist u s (s.smaller i) z
  let G := energy s u; let J := fax s; let V := shower u s
  let A (z) := g z*‖v z‖^2; let B (z) := duet (v z) (n z)
  let D (i : Bool) := ∑ z, d i z
  have H (b : Bool) :
      energy (s.smaller b) u=G+curl b*((∑ z,A z)+2*∑ z,B z)+D b := by
    unfold D G
    rw [sun_energy (h.child b),sun_energy h.fit]
    simp_rw [sun_shift h,Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib,Finset.mul_sum]
    exact le_antisymm le_rfl le_rfl
  have hm := matter_nonneg h.fit
  have hA : (∑ z,A z)^2 ≤ G*J := by
    unfold G J fax
    rw [sun_energy h.fit]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => (sun_rays h.fit _ _).1)
      (fun i _ => pierce_nonneg h.fit i) (fun i _ => ?_)
    change (shell s i*‖v i‖^2)^2 ≤ (m i*‖v i‖^2)*pierce s i
    rw [mul_pow,shell_sq h i]
    have hN : ‖v i‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (mean_hold s h.fit _ _).2
    change (m i * _) * _ ≤ _
    rw [pow_two (‖v i‖^2)]
    have HE : 0 ≤ (m i*pierce s i)*‖v i‖^2 :=
      mul_nonneg (mul_nonneg (hm _) (pierce_nonneg h.fit i)) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hN HE]
  have hB : (∑ z,B z)^2 ≤ G*(4*V) := by
    unfold V shower G
    rw [sun_energy h.fit, Finset.mul_sum]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => (sun_rays h.fit _ _).1)
      (fun i _ => mul_nonneg (by norm_num) (dew_nonneg _ h _)) (fun i _ => ?_)
    have Hq := nub_innovation s h u i
    have HE : (B i)^2 ≤ (‖v i‖ * ‖n i‖)^2 := by
      rw [←sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (duet_limit _ _) _
    rw [mul_pow] at HE
    change _ ≤ m i*‖v i‖^2 * _
    change ‖n i‖^2 ≤ 4*m i*_ at Hq
    nlinarith [mul_le_mul_of_nonneg_left Hq (sq_nonneg ‖v i‖)]
  let R := (D false-D true)/2
  have hD : V=(D false+D true)/2 := by
    unfold V D shower dew; rw [← Finset.sum_div,Finset.sum_add_distrib]
  have hH : |R| ≤ V := by
    have HH (i) : 0 ≤ D i := Finset.sum_nonneg (fun _ _ => mist_nonneg u s _ (h.child i) _)
    rw [abs_le,hD]; unfold R; constructor <;> linarith [HH false,HH true]
  have hL₁ := (energy_small h.fit u).1
  have hL₂ : 0 ≤ V := shower_nonneg h
  have hF : 0 ≤ J := (fax_floor h).1
  have hQ : G+V ≤ L := by rw [show G+V=_ from (wet_average s h u).symm]; linarith [hp false,hp true]
  have hr : R^2 ≤ V*L := by
    change 0 ≤ G at hL₁
    have HH := abs_le.mp hH
    nlinarith
  rw [gust,H false,H true]
  simp only [curl,Bool.false_eq_true,↓reduceIte,neg_mul,one_mul]
  let a := ∑ z,A z; let b := ∑ z,B z
  change ((G+(a+2*b)+D false-(G+ -(a+2*b)+D true))/2)^2 ≤ 100*L*(J+V)
  rw [show (G+(a+2*b)+D false-(G+ -(a+2*b)+D true))/2=a+2*b+R by unfold R; ring]
  change a^2 ≤ _ at hA; change b^2 ≤ _ at hB
  have hG : 0 ≤ G := hL₁
  have hT : (a+2*b+R)^2 ≤ 3*(a^2+(2*b)^2+R^2) := by nlinarith [sq_nonneg (a-2*b),sq_nonneg (2*b-R),sq_nonneg (a-R)]
  nlinarith

lemma factor_bill (s : Scene M) (h : Climb s) (u : Grid M) :
    (∑ z : Grid M, ‖factor s u z‖)^2 ≤
      16*(energy s u* fax s + shower u s) := by
  let n := nub s u; let v := meanV s u; let m := matter s; let g := shell s
  let G := energy s u; let J := fax s; let V := shower u s
  let f (z : Grid M) := |g z| * ‖v z‖; let k (z : Grid M) := ‖n z‖
  have hm := matter_nonneg h.fit
  have H (z : Grid M) : ‖factor s u z‖ ≤ f z+k z := by
    rw [show factor s u z=(↑(g z):ℂ)*v z+n z by unfold n v g nub; ring]
    apply (norm_add_le _ _).trans; rw [norm_scaleC]
  have hF : (∑ z,f z)^2 ≤ G*J := by
    unfold G J fax; rw [sun_energy h.fit]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun i _ => (sun_rays h.fit _ _).1) (fun i _ => pierce_nonneg h.fit _) (fun i _ => ?_)
    change (|shell s i| * ‖v i‖)^2 ≤ matter s i* ‖v i‖^2 * pierce s i
    rw [mul_pow,sq_abs,shell_sq h]
    exact le_of_eq (by ring)
  have hK : (∑ z,k z)^2 ≤ 2*(4*V) := by
    apply le_trans (b:=share s*(4*V))
    · rw [← matter_sum h.fit]
      unfold V shower; rw [Finset.mul_sum]
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => hm i)
        (fun i _ => mul_nonneg (by norm_num) (dew_nonneg _ h _)) (fun i _ => ?_)
      have Hh := nub_innovation _ h u i; change ‖nub s u i‖^2 ≤ _
      linarith
    · exact mul_le_mul_of_nonneg_right h.tight (mul_nonneg (by norm_num) (shower_nonneg h))
  let a := ∑ z,f z; let b := ∑ z,k z; let c := ∑ z,‖factor s u z‖
  have he : c ≤ a+b := by unfold c a b; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _ => H i
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ => norm_nonneg _
  change a^2 ≤ _ at hF; change b^2 ≤ _ at hK; change c^2 ≤ 16*(G*J+V)
  nlinarith [sq_nonneg (a-b)]

lemma shell_bill (s : Scene M) (h : Climb s) :
    (∑ z,|shell s z|)^2 ≤ 2*fax s := by
  apply le_trans (b:=share s*fax s)
  · rw [←matter_sum h.fit]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => matter_nonneg h.fit i)
      (fun i _ => pierce_nonneg h.fit i) (fun i _ => ?_)
    rw [sq_abs,shell_sq h]
  exact mul_le_mul_of_nonneg_right h.tight (fax_floor h).1


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
