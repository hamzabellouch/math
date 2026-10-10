import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasure

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
namespace GraphSourceScale
open Real Filter

lemma two_rpow_N_mul (N s : ℝ) :
    (2:ℝ)^(N*s) = ((2:ℝ)^N)^s := by
  rw [Real.rpow_mul (by norm_num)]

lemma length_scale {N a p v L sig : ℝ}
    (hh : p-a ≤ v-p+2*sig*N) (hL : L ≤ v-p+2*sig*N) :
    (2:ℝ)^(p-a) ≤ (2:ℝ)^(v-p)*((2:ℝ)^N)^(2*sig) ∧
    (2:ℝ)^L ≤ (2:ℝ)^(v-p)*((2:ℝ)^N)^(2*sig) := by
  have he : (2:ℝ)^(v-p+2*sig*N) = (2:ℝ)^(v-p)*((2:ℝ)^N)^(2*sig) := by
    rw [Real.rpow_add (by norm_num),show 2*sig*N=N*(2*sig) by ring,two_rpow_N_mul]
  constructor <;> rw [← he]
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hh
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hL

lemma derivative_scale {R sig U V : ℝ} (hR : 1 ≤ R) (_hsig : 0 ≤ sig)
    (hV : 0 ≤ V) (hU : U ≤ V*R^(2*sig)) :
    R^sig*max 1 (U*R^(-50*sig)) ≤ R^sig+V*R^(-47*sig) := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hstep : U*R^(-50*sig) ≤ V*R^(-48*sig) := by
    calc
      _ ≤ (V*R^(2*sig))*R^(-50*sig) := mul_le_mul_of_nonneg_right hU (by positivity)
      _ = V*R^(-48*sig) := by rw [mul_assoc,←Real.rpow_add hRp]; congr 2; ring
  calc
    _ ≤ R^sig*(1+V*R^(-48*sig)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply max_le
      · linarith [mul_nonneg hV (Real.rpow_nonneg hRp.le (-48*sig))]
      · linarith
    _ = R^sig+V*R^(-47*sig) := by
      rw [mul_add,mul_one,show R^sig*(V*R^(-48*sig))=V*(R^sig*R^(-48*sig)) by ring,
        ←Real.rpow_add hRp]
      congr 2; ring_nf

lemma inverse_cap_scale {c R sig H : ℝ} (hc : 0 < c) (hR : 0 < R) (hH : 0 < H) :
    (min c (H⁻¹*R^(10*sig)))⁻¹ ≤ c⁻¹+H*R^(-10*sig) := by
  have hx : 0 < H⁻¹*R^(10*sig) := by positivity
  have hi : (H⁻¹*R^(10*sig))⁻¹=H*R^(-10*sig) := by
    rw [mul_inv_rev,inv_inv,←Real.rpow_neg hR.le]
    ring_nf
  by_cases hh : c ≤ H⁻¹*R^(10*sig)
  · rw [min_eq_left hh]
    linarith [mul_nonneg hH.le (Real.rpow_nonneg hR.le (-10*sig))]
  · rw [min_eq_right (le_of_not_ge hh),hi]
    linarith [inv_pos.mpr hc]

lemma cap_scale_bound {c R sig H V : ℝ}
    (hc : 0 < c) (hR : 1 ≤ R) (hH : 0 < H) (_hV : 0 ≤ V)
    (hHV : H ≤ V*R^(2*sig)) :
    (min c (H⁻¹*R^(10*sig)))⁻¹ ≤ c⁻¹+V*R^(-8*sig) := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  apply (inverse_cap_scale hc hRp hH).trans
  apply add_le_add le_rfl
  calc
    _ ≤ (V*R^(2*sig))*R^(-10*sig) := mul_le_mul_of_nonneg_right hHV (by positivity)
    _ = V*R^(-8*sig) := by rw [mul_assoc,←Real.rpow_add hRp]; congr 2; ring

lemma ratio_scale {c R sig H V U G : ℝ}
    (hc : 0 < c) (hR : 1 ≤ R) (hsig : 0 ≤ sig) (hH : 0 < H) (hV : 1 ≤ V)
    (hG : 0 ≤ G) (hHV : H ≤ V*R^(2*sig)) (hUV : U ≤ V*R^(2*sig)) :
    (2+R^sig*max 1 (U*R^(-50*sig))+(min c (H⁻¹*R^(10*sig)))⁻¹+
      G*H*R^(-30*sig))/(V*R^(30*sig)) ≤ (5+c⁻¹+G)*R^(-29*sig) := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hVp : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hs := Real.one_le_rpow hR hsig
  have hder := derivative_scale hR hsig (zero_le_one.trans hV) hUV
  have hcap := cap_scale_bound hc hR hH (zero_le_one.trans hV) hHV
  have hgeo : G*H*R^(-30*sig) ≤ G*V*R^(-28*sig) := by
    calc
      _ ≤ G*(V*R^(2*sig))*R^(-30*sig) := by gcongr
      _ = G*V*R^(-28*sig) := by rw [←mul_assoc G V, mul_assoc (G*V),←Real.rpow_add hRp]; congr 2; ring
  have hm (x : ℝ) (hx : x ≤ sig) : R^x ≤ R^sig :=
    Real.rpow_le_rpow_of_exponent_le hR hx
  have hnum : 2+R^sig*max 1 (U*R^(-50*sig))+(min c (H⁻¹*R^(10*sig)))⁻¹+
      G*H*R^(-30*sig) ≤ (5+c⁻¹+G)*V*R^sig := by
    have hVR : 1 ≤ V*R^sig := one_le_mul_of_one_le_of_one_le hV hs
    have hsVR : R^sig ≤ V*R^sig := le_mul_of_one_le_left (by positivity) hV
    have h₁ : V*R^(-47*sig) ≤ V*R^sig := mul_le_mul_of_nonneg_left (hm _ (by linarith)) hVp.le
    have h₂ : V*R^(-8*sig) ≤ V*R^sig := mul_le_mul_of_nonneg_left (hm _ (by linarith)) hVp.le
    have h₃ : G*V*R^(-28*sig) ≤ G*(V*R^sig) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hm _ (by linarith)) hVp.le) hG
    have hci : c⁻¹ ≤ c⁻¹*(V*R^sig) := le_mul_of_one_le_right (by positivity) hVR
    nlinarith
  calc
    _ ≤ ((5+c⁻¹+G)*V*R^sig)/(V*R^(30*sig)) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = (5+c⁻¹+G)*R^(-29*sig) := by
      rw [show ((5+c⁻¹+G)*V*R^sig)/(V*R^(30*sig)) = (5+c⁻¹+G)*(R^sig/R^(30*sig)) by field_simp,
        ←Real.rpow_sub hRp]
      congr 2; ring

lemma source_error_scale {c R sig X Y C G : ℝ}
    (hR : 1 ≤ R) (hsig : 0 ≤ sig) (hX : 0 < X) (hY : 0 < Y)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hlarge : 8*C*G+4*G ≤ R^(20*sig)) :
    4*(C*min c (X/Y*R^(10*sig)))*(G/X)+2*(G/Y) ≤
      (Y⁻¹*R^(30*sig))/2 := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hp : 1 ≤ R^(10*sig) := Real.one_le_rpow hR (by positivity)
  have hd : min c (X/Y*R^(10*sig)) ≤ X/Y*R^(10*sig) := min_le_right _ _
  have hh : 4*(C*min c (X/Y*R^(10*sig)))*(G/X) ≤ 4*C*G/Y*R^(10*sig) := by
    calc
      _ ≤ 4*(C*(X/Y*R^(10*sig)))*(G/X) := by gcongr
      _ = _ := by field_simp
  have h₂ : 2*(G/Y) ≤ 2*G/Y*R^(10*sig) := by
    rw [show 2*(G/Y)=2*G/Y by ring]
    exact le_mul_of_one_le_right (show 0 ≤ 2*G/Y by positivity) hp
  have ht : (8*C*G+4*G)*R^(10*sig) ≤ R^(30*sig) := by
    calc
      _ ≤ R^(20*sig)*R^(10*sig) := mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = R^(30*sig) := by rw [←Real.rpow_add hRp]; congr 1; ring
  have hy : 0 < 2*Y := by positivity
  have hh' : 4*C*G/Y*R^(10*sig)+2*G/Y*R^(10*sig) ≤ (Y⁻¹*R^(30*sig))/2 := by
    apply (mul_le_mul_iff_left₀ hy).mp
    field_simp
    rw [show sig*30=30*sig by ring]
    nlinarith
  exact (add_le_add hh h₂).trans hh'

lemma ratio_power_decay {c R sig H V U G T : ℝ} {m : ℕ}
    (hc : 0 < c) (hR : 1 ≤ R) (hsig : 0 ≤ sig) (hH : 0 < H) (hV : 1 ≤ V)
    (hG : 0 ≤ G) (_hU : 0 ≤ U) (hHV : H ≤ V*R^(2*sig)) (hUV : U ≤ V*R^(2*sig))
    (hm : T ≤ 29*sig*m) :
    ((2+R^sig*max 1 (U*R^(-50*sig))+(min c (H⁻¹*R^(10*sig)))⁻¹+
      G*H*R^(-30*sig))/(V*R^(30*sig)))^m ≤ (5+c⁻¹+G)^m*R^(-T) := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hc0 : 0 < min c (H⁻¹*R^(10*sig)) := lt_min hc (by positivity)
  calc
    _ ≤ ((5+c⁻¹+G)*R^(-29*sig))^m :=
      pow_le_pow_left₀ (by positivity) (ratio_scale hc hR hsig hH hV hG hHV hUV) m
    _ = (5+c⁻¹+G)^m*R^((-29*sig)*m) := by rw [mul_pow,Real.rpow_mul_natCast hRp.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) (by positivity)

end GraphSourceScale
end
end

end OAI
