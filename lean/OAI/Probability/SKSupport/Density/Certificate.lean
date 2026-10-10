import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
namespace ZeroTemperatureSK.Certificate
noncomputable section

abbrev A : ℝ := 1 / 13
abbrev C : ℝ := 53 / 24
abbrev k : ℝ := 19 / 16
abbrev T₀ : ℝ := 73 / 48
abbrev g₀ : ℝ := 2331 / 10000
abbrev h : ℝ := 87 / 2500
abbrev x₀ : ℝ := 4663 / 5000
abbrev y : ℝ := 6853 / 10000
abbrev m : ℝ := -1051 / 400
abbrev n₀ : ℝ := -1073 / 500

def Q (R K v b : ℝ) : ℝ := A * v * b + C * v ^ 2 + k * K * v - 2*k*R*b + T₀*R*v
def T (R v j : ℝ) : ℝ := g₀*R*v + h*j*v
def F₁ (R K v b j : ℝ) : ℝ :=
  b^2*(2*R*k-A*v) + b*(-2*K*k*v-R*g₀*v-2*R*T₀*v-2*C*v^2-h*j*v)
def F₂ (R K v b j : ℝ) : ℝ := x₀*v^2*j + y*v^3 + m*K*v^2 + n₀*R*v^2 - F₁ R K v b j

def P₀ (R v b j : ℝ) : ℝ := R*j*(b-7*v)^2
def P₁ (R v b B : ℝ) : ℝ := R*B*(b-7/3*v)^2
def P₂ (K v b : ℝ) : ℝ := K*v*(b-9/2*v)^2
def P₃ (R K v B : ℝ) : ℝ := v*B*(K+1/4*R-1/7*v)^2
def P₄ (R K v b : ℝ) : ℝ := (v*b-14/5*v^2-13/4*K*v+4/3*R*v)^2

def weightedSquares (R K v b B j : ℝ) : ℝ :=
  337/10000*P₀ R v b j + 183/2500*P₁ R v b B + 411/10000*P₂ K v b +
    11461/5000*P₃ R K v B + 647/10000*P₄ R K v b

def remainder (R K v B j : ℝ) : ℝ :=
  223/160000*R^2*v^2 + 4007/240000*R^2*v*B + 1097/120000*R^2*B^2 +
  83/80000*R*K*v^2 + 3343/24000*R*K*v*B + 16259/23400000*R*v^3 +
  30179/5460000*R*v^2*B + 26/625*R*v^2*j + 107/15000*R*v*B^2 +
  3/2500*R*v*B*j + 121/32500*R*B^3 + 11/10000*R*B^2*j +
  579/20000*K^2*v^2 + 207/2500*K^2*v*B + 911/975000*K*v^3 +
  349/420000*K*v^2*B + 5011/5000*K*v^2*j + 133/130000*K*v*B^2 +
  87/2500*K*v*B*j + 1661507/1521000000*v^4 +
  633799/621075000*v^3*B + 10657/1690000*v^2*B^2

def F₂R (_R _K v b _j : ℝ) : ℝ := n₀*v^2 - 2*k*b^2 + (g₀+2*T₀)*b*v
def F₂K (_R _K v b _j : ℝ) : ℝ := m*v^2 + 2*k*b*v
def F₂v (R K v b j : ℝ) : ℝ :=
  2*x₀*v*j + 3*y*v^2 + 2*m*K*v + 2*n₀*R*v + A*b^2 +
    b*(2*K*k + R*g₀ + 2*R*T₀ + 4*C*v + h*j)
def F₂b (R K v b j : ℝ) : ℝ := 2*Q R K v b + T R v j
def F₂j (_R _K v b _j : ℝ) : ℝ := x₀*v^2 + h*b*v

def DF₂ (R K v b j z L : ℝ) : ℝ :=
  (2*R*v)*F₂R R K v b j + (2*v*K+R*j)*F₂K R K v b j +
  (-R*b)*F₂v R K v b j + (-z-b*v)*F₂b R K v b j +
  (-j*v+K*b-L)*F₂j R K v b j

def WF₂ (R K v b j z L : ℝ) : ℝ := DF₂ R K v b j z L + (v+R-K)*F₂ R K v b j

theorem rational_identity (R K v b j z L : ℝ) :
    z^2 - 12*R*v*b^2 + 6*v^4 =
      (z+Q R K v b)^2 + (z+b*v-2*R*b)*T R v j +
      weightedSquares R K v b (b-2*v) j + WF₂ R K v b j z L +
      L*(x₀*v^2+h*b*v) + remainder R K v (b-2*v) j := by
  unfold Q T weightedSquares P₀ P₁ P₂ P₃ P₄ WF₂ DF₂ F₂R F₂K F₂v F₂b F₂j F₂ F₁
  unfold Q T remainder A C k T₀ g₀ h x₀ y m n₀
  ring

theorem hasDerivAt_F₂ {R K v b j : ℝ → ℝ} {R' K' v' b' j' x : ℝ}
    (hR : HasDerivAt R R' x) (hK : HasDerivAt K K' x)
    (hv : HasDerivAt v v' x) (hb : HasDerivAt b b' x) (hj : HasDerivAt j j' x) :
    HasDerivAt (fun t => F₂ (R t) (K t) (v t) (b t) (j t))
      (R' * F₂R (R x) (K x) (v x) (b x) (j x) +
       K' * F₂K (R x) (K x) (v x) (b x) (j x) +
       v' * F₂v (R x) (K x) (v x) (b x) (j x) +
       b' * F₂b (R x) (K x) (v x) (b x) (j x) +
       j' * F₂j (R x) (K x) (v x) (b x) (j x)) x := by
  have hM := ((hR.const_mul 2).mul_const k).sub (hv.const_mul A)
  have hN := ((((((hK.const_mul (-2)).mul_const k).mul hv).sub
    ((hR.mul_const g₀).mul hv)).sub (((hR.const_mul 2).mul_const T₀).mul hv)).sub
    ((hv.pow 2).const_mul (2*C))).sub ((hj.const_mul h).mul hv)
  have hF₁ := ((hb.pow 2).mul hM).add (hb.mul hN)
  have hF₂ := ((((((hv.pow 2).const_mul x₀).mul hj).add ((hv.pow 3).const_mul y)).add
    ((hK.const_mul m).mul (hv.pow 2))).add ((hR.const_mul n₀).mul (hv.pow 2))).sub hF₁
  convert! hF₂ using 1
  simp only [F₂R, F₂K, F₂v, F₂b, F₂j, Q, T,
    Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  ring

theorem remainder_lower_bound {R K v B j : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hv : 0 ≤ v) (hB : 0 ≤ B) (hj : 0 ≤ j) :
    (1661507 / 1521000000 : ℝ) * v^4 ≤ remainder R K v B j := by
  unfold remainder
  have hrest : 0 ≤
      223/160000*R^2*v^2 + 4007/240000*R^2*v*B + 1097/120000*R^2*B^2 +
      83/80000*R*K*v^2 + 3343/24000*R*K*v*B + 16259/23400000*R*v^3 +
      30179/5460000*R*v^2*B + 26/625*R*v^2*j + 107/15000*R*v*B^2 +
      3/2500*R*v*B*j + 121/32500*R*B^3 + 11/10000*R*B^2*j +
      579/20000*K^2*v^2 + 207/2500*K^2*v*B + 911/975000*K*v^3 +
      349/420000*K*v^2*B + 5011/5000*K*v^2*j + 133/130000*K*v*B^2 +
      87/2500*K*v*B*j + 633799/621075000*v^3*B + 10657/1690000*v^2*B^2 := by
    positivity
  linarith only [hrest]

theorem pointwise_coercivity {R K v b j z L : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hv : 0 ≤ v) (hj : 0 ≤ j)
    (hB : 0 ≤ b - 2*v) (hL : 0 ≤ L) (hS : 0 ≤ z+b*v-2*R*b) :
    (1661507 / 1521000000 : ℝ) * v^4 + WF₂ R K v b j z L ≤
      z^2 - 12*R*v*b^2 + 6*v^4 := by
  have hb : 0 ≤ b := by linarith
  have hT : 0 ≤ T R v j := by unfold T g₀ h; positivity
  have hST : 0 ≤ (z+b*v-2*R*b)*T R v j := mul_nonneg hS hT
  have hsq : 0 ≤ weightedSquares R K v b (b-2*v) j := by
    unfold weightedSquares P₀ P₁ P₂ P₃ P₄
    positivity
  have hcorr : 0 ≤ L*(x₀*v^2+h*b*v) := by unfold x₀ h; positivity
  have hrem := remainder_lower_bound hR hK hv hB hj
  have hid := rational_identity R K v b j z L
  have hz : 0 ≤ (z+Q R K v b)^2 := sq_nonneg _
  linarith only [hST, hsq, hcorr, hrem, hid, hz]

theorem coercivity_constant : (1 / 1000 : ℝ) < 1661507 / 1521000000 := by
  norm_num

theorem hasDerivAt_flux {r s ρ R K v b j : ℝ → ℝ}
    {dR dK dv db dj z L x : ℝ}
    (hr : HasDerivAt r (v x) x)
    (hρ : HasDerivAt ρ ((r x - s x) * ρ x) x)
    (hR : HasDerivAt R dR x) (hK : HasDerivAt K dK x)
    (hv : HasDerivAt v dv x) (hb : HasDerivAt b db x)
    (hj : HasDerivAt j dj x)
    (hRval : R x = (r x)^2) (hKval : K x = r x * s x)
    (hDR : r x*dR = 2*R x*v x)
    (hDK : r x*dK = 2*v x*K x + R x*j x)
    (hDv : r x*dv = -R x*b x)
    (hDb : r x*db = -z-b x*v x)
    (hDj : r x*dj = -j x*v x+K x*b x-L) :
    HasDerivAt (fun t => r t * F₂ (R t) (K t) (v t) (b t) (j t) * ρ t)
      (ρ x * WF₂ (R x) (K x) (v x) (b x) (j x) z L) x := by
  have hF := hasDerivAt_F₂ hR hK hv hb hj
  have hD : r x * (dR * F₂R (R x) (K x) (v x) (b x) (j x) +
      dK * F₂K (R x) (K x) (v x) (b x) (j x) +
      dv * F₂v (R x) (K x) (v x) (b x) (j x) +
      db * F₂b (R x) (K x) (v x) (b x) (j x) +
      dj * F₂j (R x) (K x) (v x) (b x) (j x)) =
      DF₂ (R x) (K x) (v x) (b x) (j x) z L := by
    calc
      _ = (r x*dR) * F₂R (R x) (K x) (v x) (b x) (j x) +
        (r x*dK) * F₂K (R x) (K x) (v x) (b x) (j x) +
        (r x*dv) * F₂v (R x) (K x) (v x) (b x) (j x) +
        (r x*db) * F₂b (R x) (K x) (v x) (b x) (j x) +
        (r x*dj) * F₂j (R x) (K x) (v x) (b x) (j x) := by ring
      _ = _ := by rw [hDR, hDK, hDv, hDb, hDj]; rfl
  convert! (hr.mul hF).mul hρ using 1
  simp only [Pi.mul_apply]
  unfold WF₂
  rw [← hD, hRval, hKval]
  ring

open MeasureTheory Filter
open scoped Topology

theorem integrated_coercivity_of_flux {r ρ R K v b j z L : ℝ → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x)
    (hR : ∀ x, 0 ≤ R x) (hK : ∀ x, 0 ≤ K x) (hv : ∀ x, 0 ≤ v x)
    (hj : ∀ x, 0 ≤ j x) (hB : ∀ x, 0 ≤ b x - 2*v x)
    (hL : ∀ x, 0 ≤ L x) (hS : ∀ x, 0 ≤ z x+b x*v x-2*R x*b x)
    (hderiv : ∀ x, HasDerivAt
      (fun t => r t * F₂ (R t) (K t) (v t) (b t) (j t) * ρ t)
      (ρ x * WF₂ (R x) (K x) (v x) (b x) (j x) (z x) (L x)) x)
    (hbot : Tendsto (fun t => r t * F₂ (R t) (K t) (v t) (b t) (j t) * ρ t)
      atBot (𝓝 0))
    (htop : Tendsto (fun t => r t * F₂ (R t) (K t) (v t) (b t) (j t) * ρ t)
      atTop (𝓝 0))
    (hv4 : Integrable (fun t => ρ t * (v t)^4))
    (hW : Integrable (fun t => ρ t * WF₂ (R t) (K t) (v t) (b t) (j t) (z t) (L t)))
    (hI : Integrable (fun t => ρ t * ((z t)^2-12*R t*v t*(b t)^2+6*(v t)^4))) :
    (1661507 / 1521000000 : ℝ) * (∫ t, ρ t * (v t)^4) ≤
      ∫ t, ρ t * ((z t)^2-12*R t*v t*(b t)^2+6*(v t)^4) := by
  have hzero : (∫ t, ρ t * WF₂ (R t) (K t) (v t) (b t) (j t) (z t) (L t)) = 0 := by
    simpa using integral_of_hasDerivAt_of_tendsto hderiv hW hbot htop
  have hpoint : ∀ t, (1661507 / 1521000000 : ℝ) * (ρ t * (v t)^4) +
      ρ t * WF₂ (R t) (K t) (v t) (b t) (j t) (z t) (L t) ≤
      ρ t * ((z t)^2-12*R t*v t*(b t)^2+6*(v t)^4) := by
    intro t
    have hh := mul_le_mul_of_nonneg_left
      (pointwise_coercivity (hR t) (hK t) (hv t) (hj t) (hB t) (hL t) (hS t)) (hρ t)
    nlinarith only [hh]
  have hint := integral_mono ((hv4.const_mul _).add hW) hI hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add (hv4.const_mul _) hW, integral_const_mul, hzero, add_zero] at hint
  exact hint

theorem coercivity_constant_integral {ρ v : ℝ → ℝ} (hρ : ∀ t, 0 ≤ ρ t) :
    (1 / 1000 : ℝ) * (∫ t, ρ t * (v t)^4) ≤
      (1661507 / 1521000000 : ℝ) * (∫ t, ρ t * (v t)^4) := by
  apply mul_le_mul_of_nonneg_right (le_of_lt coercivity_constant)
  apply integral_nonneg
  intro t
  exact mul_nonneg (hρ t) (pow_nonneg (sq_nonneg (v t)) 2) |>.trans_eq (by ring)

end
end ZeroTemperatureSK.Certificate

end

end OAI
