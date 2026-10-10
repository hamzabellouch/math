import Mathlib
import OAI.Geometry.HypersurfaceGerms.Differentials

namespace OAI

/-! Isolation for the plane curve and its prepared pullbacks. -/

noncomputable section

namespace AmbientMultiplicity.PlaneAnalytic

section AlgebraicIsolation
local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
open Polynomial Filter Topology
section Definitions
variable {R : Type*} [CommRing R]
def q1 (u w : R) : R := (u - w - w ^ 8) * (u - w - 2 * w ^ 8) * (u - w ^ 2)
def q2 (u w : R) : R := q1 u w - u ^ 2

def q1u (u w : R) : R :=
  (u - w - 2 * w ^ 8) * (u - w ^ 2) +
  (u - w - w ^ 8) * (u - w ^ 2) +
  (u - w - w ^ 8) * (u - w - 2 * w ^ 8)
def q1w (u w : R) : R :=
  (-1 - 8 * w ^ 7) * (u - w - 2 * w ^ 8) * (u - w ^ 2) +
  (u - w - w ^ 8) * (-1 - 16 * w ^ 7) * (u - w ^ 2) +
  (u - w - w ^ 8) * (u - w - 2 * w ^ 8) * (-2 * w)
def q2u (u w : R) : R := q1u u w - 2 * u
def q2w (u w : R) : R := q1w u w

def d0 (u w : R) : R := u * q1 u w * q2 u w
def d0u (u w : R) : R := q1 u w * q2 u w + u * q1u u w * q2 u w + u * q1 u w * q2u u w
def d0w (u w : R) : R := u * q1w u w * q2 u w + u * q1 u w * q2w u w

def psi0 (u w : R) : R := u * (u - w ^ 2) * q2 u w
def psi0u (u w : R) : R := (2 * u - w ^ 2) * q2 u w + u * (u - w ^ 2) * q2u u w
def psi0w (u w : R) : R := -2 * u * w * q2 u w + u * (u - w ^ 2) * q2w u w

def psi (x w : R) : R := psi0 (x + w) w
def psix (x w : R) : R := psi0u (x + w) w
def psiw (x w : R) : R := psi0u (x + w) w + psi0w (x + w) w

def d1 (x w : R) : R := psi x w * (x - psi x w ^ 2) * (x - 2 * psi x w ^ 2)
def d1x (x w : R) : R :=
  psi x w * (2*x-3*(psi x w)^2) + psix x w *
    (x^2-9*x*(psi x w)^2+10*(psi x w)^4)
def d1w (x w : R) : R :=
  psiw x w * (x^2-9*x*(psi x w)^2+10*(psi x w)^4)
end Definitions

abbrev B := Polynomial (Polynomial ℤ)
def P0 : B := d0u X (C X)
def Q0 : B := d0w X (C X)
def P1 : B := d1x X (C X)
def Q1 : B := d1w X (C X)
def res0 : Polynomial ℤ := P0.resultant Q0 6 6
def res1 : Polynomial ℤ := P1.resultant Q1 24 24

def mod11 : Polynomial ℤ →+* ZMod 11 :=
  Polynomial.eval₂RingHom (Int.castRingHom (ZMod 11)) 2

lemma eleven_zero : (11 : Polynomial (ZMod 11)) = 0 := by
  exact CharP.cast_eq_zero (Polynomial (ZMod 11)) 11

lemma P0_degree : P0.natDegree ≤ 6 := by
  dsimp only [P0, d0u, d0w, d1x, d1w, psi, psix, psiw, psi0, psi0u, psi0w, q2, q2u, q2w, q1, q1u, q1w, Polynomial.eval₂_pow]
  compute_degree!

lemma Q0_degree : Q0.natDegree ≤ 6 := by
  dsimp only [Q0, d0u, d0w, d1x, d1w, psi, psix, psiw, psi0, psi0u, psi0w, q2, q2u, q2w, q1, q1u, q1w, Polynomial.eval₂_pow]
  compute_degree!

lemma P1_degree : P1.natDegree ≤ 24 := by
  dsimp only [P1, d0u, d0w, d1x, d1w, psi, psix, psiw, psi0, psi0u, psi0w, q2, q2u, q2w, q1, q1u, q1w, Polynomial.eval₂_pow]
  compute_degree!

lemma Q1_degree : Q1.natDegree ≤ 24 := by
  dsimp only [Q1, d0u, d0w, d1x, d1w, psi, psix, psiw, psi0, psi0u, psi0w, q2, q2u, q2w, q1, q1u, q1w, Polynomial.eval₂_pow]
  compute_degree!

def P0mod : Polynomial (ZMod 11) := 3 + 3* X + 7* X^2 + 8* X^3 + 8* X^4 + 10* X^5 + 7* X^6
def Q0mod : Polynomial (ZMod 11) := 9* X + 1* X^2 + 4* X^3 + 1* X^4 + 4* X^5 + 4* X^6
def A0mod : Polynomial (ZMod 11) := 4 + 3* X + 6* X^2 + 2* X^3 + 4* X^4 + 6* X^5
def B0mod : Polynomial (ZMod 11) := 5 + 8* X + 3* X^2 + 1* X^3 + 5* X^4 + 6* X^5
lemma P0_map : P0.map mod11 = P0mod := by
  norm_num [P0, d0u, d0w, d1x, d1w, psi, psix, psiw, psi0, psi0u, psi0w, q2, q2u, q2w, q1, q1u, q1w, map_add, map_sub, map_mul, map_pow, map_ofNat, Polynomial.map_X, Polynomial.map_C, mod11, Polynomial.eval₂_X, P0mod]
  linear_combination ((25579552791) + (-26175197673)* X + (5246802475)* X^2 + (-77019272)* X^3 + (397432)* X^4 + (-848)* X^5) * eleven_zero

lemma Q0_map : Q0.map mod11 = Q0mod := by
  norm_num [Q0, d0u, d0w, d1x, d1w, psi, psix, psiw, psi0, psi0u, psi0w, q2, q2u, q2w, q1, q1u, q1w, map_add, map_sub, map_mul, map_pow, map_ofNat, Polynomial.map_X, Polynomial.map_C, mod11, Polynomial.eval₂_X, Q0mod]
  linear_combination ((458347193157)* X + (-220535797027)* X^2 + (27389244212)* X^3 + (-227994951)* X^4 + (629262)* X^5 + (-560)* X^6) * eleven_zero

lemma coprime0 : IsCoprime P0mod Q0mod := by
  refine ⟨A0mod, B0mod, ?_⟩
  unfold A0mod B0mod P0mod Q0mod
  linear_combination ((1) + (6)* X + (12)* X^2 + (12)* X^3 + (15)* X^4 + (22)* X^5 + (26)* X^6 + (22)* X^7 + (17)* X^8 + (12)* X^9 + (12)* X^10 + (6)* X^11) * eleven_zero

lemma P0mod_degree : P0mod.natDegree = 6 := by
  unfold P0mod
  compute_degree!

lemma Q0mod_degree : Q0mod.natDegree = 6 := by
  unfold Q0mod
  compute_degree!

lemma res0_nonzero : res0 ≠ 0 := by
  intro hz
  have h := Polynomial.resultant_ne_zero P0mod Q0mod coprime0
  rw [P0mod_degree, Q0mod_degree, ← P0_map, ← Q0_map,
    Polynomial.resultant_map_map] at h
  exact h (by change mod11 res0 = 0; rw [hz, map_zero])

def P1mod : Polynomial (ZMod 11) := 9 + 7* X + 8* X^2 + 2* X^3 + 7* X^4 + 6* X^5 + 6* X^6 + 5* X^7 + 3* X^8 + 2* X^9 + 1* X^11 + 8* X^12 + 7* X^14 + 7* X^15 + 6* X^16 + 2* X^17 + 7* X^18 + 6* X^19 + 4* X^20 + 3* X^22 + 2* X^23 + 6* X^24
def Q1mod : Polynomial (ZMod 11) := 9 + 4* X + 5* X^2 + 7* X^3 + 10* X^4 + 5* X^5 + 6* X^6 + 2* X^8 + 10* X^9 + 3* X^10 + 3* X^11 + 2* X^12 + 3* X^13 + 7* X^15 + 9* X^16 + 8* X^17 + 6* X^18 + 4* X^19 + 5* X^20 + 3* X^21 + 7* X^22 + 8* X^23 + 8* X^24
def A1mod : Polynomial (ZMod 11) := 8* X + 10* X^2 + 3* X^3 + 6* X^5 + 4* X^6 + 7* X^7 + 10* X^10 + 7* X^11 + 6* X^12 + 6* X^13 + 10* X^15 + 10* X^16 + 9* X^17 + 5* X^18 + 9* X^19 + 4* X^20 + 9* X^21 + 8* X^22 + 7* X^23
def B1mod : Polynomial (ZMod 11) := 5 + 2* X + 7* X^2 + 7* X^3 + 1* X^4 + 6* X^5 + 8* X^6 + 7* X^7 + 5* X^9 + 6* X^10 + 5* X^11 + 10* X^12 + 7* X^13 + 9* X^14 + 6* X^15 + 2* X^18 + 6* X^19 + 5* X^20 + 5* X^21 + 3* X^22 + 3* X^23
lemma P1_map : P1.map mod11 = P1mod := by
  norm_num [P1, d0u, d0w, d1x, d1w, psi, psix, psiw, psi0, psi0u, psi0w, q2, q2u, q2w, q1, q1u, q1w, map_add, map_sub, map_mul, map_pow, map_ofNat, Polynomial.map_X, Polynomial.map_C, mod11, Polynomial.eval₂_X, P1mod]
  linear_combination ((-582975214750617766828792969403) + (610090740416415152584979137259)* X + (1270572075576268404922707829112)* X^2 + (-2066854906517368367698171310822)* X^3 + (38544455003012312340148783123)* X^4 + (1404584020367942304218762310840)* X^5 + (-615147991543832834095024294493)* X^6 + (-304411418884327278444153149999)* X^7 + (273720187971892840098095339943)* X^8 + (-10972378158199196238664166502)* X^9 + (-43127403837760117084622971000)* X^10 + (11510490478035358377266957053)* X^11 + (1487420018520880338178266519)* X^12 + (-1037656074770702188025881146)* X^13 + (137197329779420615283835498)* X^14 + (-3737390441949840880980485)* X^15 + (49232978403219617313934)* X^16 + (-387322593619032776422)* X^17 + (1986721014555992123)* X^18 + (-6908645223097786)* X^19 + (16461352187146)* X^20 + (-26516509720)* X^21 + (27630987)* X^22 + (-16822)* X^23 + (4)* X^24) * eleven_zero

lemma Q1_map : Q1.map mod11 = Q1mod := by
  norm_num [Q1, d0u, d0w, d1x, d1w, psi, psix, psiw, psi0, psi0u, psi0w, q2, q2u, q2w, q1, q1u, q1w, map_add, map_sub, map_mul, map_pow, map_ofNat, Polynomial.map_X, Polynomial.map_C, mod11, Polynomial.eval₂_X, Q1mod]
  linear_combination ((13253572476704076852730634508101) + (-32053310663191002446457567264396)* X + (14836960979240998414954598777953)* X^2 + (24104092400717951810698770663707)* X^3 + (-26338639516793896768006481253094)* X^4 + (-1064445371267909541261889147579)* X^5 + (12079612254066496417525839806463)* X^6 + (-3890685145460139309266601875968)* X^7 + (-2068669469221452199871833058758)* X^8 + (1405746844803641475968821130674)* X^9 + (-3558998089671811285511282201)* X^10 + (-183995405746453976305097203905)* X^11 + (39386375532579022087691465030)* X^12 + (5923108224203312585685368006)* X^13 + (-3163609751261032741321528830)* X^14 + (362848860600619268352505906)* X^15 + (-8368297579174157931857819)* X^16 + (92343904114516389909512)* X^17 + (-600738956563223973026)* X^18 + (2503054936112967676)* X^19 + (-6892072304243845)* X^20 + (12513106265327)* X^21 + (-14430849417)* X^22 + (9589112)* X^23 + (-2798)* X^24) * eleven_zero

lemma coprime1 : IsCoprime P1mod Q1mod := by
  refine ⟨A1mod, B1mod, ?_⟩
  unfold A1mod B1mod P1mod Q1mod
  linear_combination ((4) + (10)* X + (22)* X^2 + (27)* X^3 + (23)* X^4 + (31)* X^5 + (42)* X^6 + (47)* X^7 + (38)* X^8 + (45)* X^9 + (47)* X^10 + (56)* X^11 + (60)* X^12 + (61)* X^13 + (65)* X^14 + (78)* X^15 + (85)* X^16 + (92)* X^17 + (91)* X^18 + (97)* X^19 + (92)* X^20 + (105)* X^21 + (109)* X^22 + (113)* X^23 + (107)* X^24 + (107)* X^25 + (92)* X^26 + (92)* X^27 + (85)* X^28 + (94)* X^29 + (87)* X^30 + (80)* X^31 + (62)* X^32 + (64)* X^33 + (70)* X^34 + (72)* X^35 + (64)* X^36 + (62)* X^37 + (49)* X^38 + (43)* X^39 + (32)* X^40 + (32)* X^41 + (25)* X^42 + (24)* X^43 + (16)* X^44 + (16)* X^45 + (10)* X^46 + (6)* X^47) * eleven_zero

lemma P1mod_degree : P1mod.natDegree = 24 := by
  unfold P1mod
  compute_degree!

lemma Q1mod_degree : Q1mod.natDegree = 24 := by
  unfold Q1mod
  compute_degree!

lemma res1_nonzero : res1 ≠ 0 := by
  intro hz
  have h := Polynomial.resultant_ne_zero P1mod Q1mod coprime1
  rw [P1mod_degree, Q1mod_degree, ← P1_map, ← Q1_map,
    Polynomial.resultant_map_map] at h
  exact h (by change mod11 res1 = 0; rw [hz, map_zero])

lemma polynomial_isolate_zero (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∀ᶠ w in 𝓝 (0 : ℂ), p.eval w = 0 → w = 0 := by
  have hf : ({w : ℂ | p.IsRoot w} \ {0}).Finite :=
    (Polynomial.finite_setOfPred_isRoot hp).sdiff
  have ho : ({w : ℂ | p.IsRoot w} \ {0})ᶜ ∈ 𝓝 (0 : ℂ) :=
    hf.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [ho] with w hw hz
  by_contra hw0
  exact hw ⟨hz, by simpa using hw0⟩

lemma intPolynomial_isolate_zero (p : Polynomial ℤ) (hp : p ≠ 0) :
    ∀ᶠ w in 𝓝 (0 : ℂ), p.eval₂ (Int.castRingHom ℂ) w = 0 → w = 0 := by
  have hn : p.map (Int.castRingHom ℂ) ≠ 0 := by
    intro h
    exact hp ((Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective) (by simpa using h))
  simpa only [Polynomial.eval_map] using polynomial_isolate_zero (p.map (Int.castRingHom ℂ)) hn

lemma eval_resultant_zero (F G : Polynomial (Polynomial ℤ)) (m n : ℕ)
    (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n) (hN : m ≠ 0 ∨ n ≠ 0)
    (x w : ℂ)
    (hx : F.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) w) x = 0)
    (hy : G.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) w) x = 0) :
    (F.resultant G m n).eval₂ (Int.castRingHom ℂ) w = 0 := by
  obtain ⟨p,q,hp,hq,he⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant F G hF hG hN
  have h := congrArg (Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Int.castRingHom ℂ) w) x) he
  simpa only [map_add, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    hx, hy, zero_mul, zero_add] using h.symm

lemma P0_eval (x w : ℂ) :
    P0.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) w) x = d0u x w := by
  simp [P0, d0u, q2, q2u, q1, q1u, Polynomial.eval₂_pow]

lemma Q0_eval (x w : ℂ) :
    Q0.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) w) x = d0w x w := by
  simp [Q0, d0w, q2, q2w, q1, q1w, Polynomial.eval₂_pow]

lemma critical_res0 (x w : ℂ) (hx : d0u x w = 0)
    (hw : d0w x w = 0) : res0.eval₂ (Int.castRingHom ℂ) w = 0 := by
  apply eval_resultant_zero P0 Q0 _ _ P0_degree Q0_degree (by norm_num) x w
  · simpa only [P0_eval] using hx
  · simpa only [Q0_eval] using hw

lemma P1_eval (x w : ℂ) :
    P1.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) w) x = d1x x w := by
  simp [P1, d1x, psi, psix, psi0, psi0u, q2, q2u, q1, q1u, Polynomial.eval₂_pow]

lemma Q1_eval (x w : ℂ) :
    Q1.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) w) x = d1w x w := by
  simp [Q1, d1w, psi, psiw, psi0, psi0u, psi0w, q2, q2u, q2w, q1, q1u, q1w, Polynomial.eval₂_pow]

lemma critical_res1 (x w : ℂ) (hx : d1x x w = 0)
    (hw : d1w x w = 0) : res1.eval₂ (Int.castRingHom ℂ) w = 0 := by
  apply eval_resultant_zero P1 Q1 _ _ P1_degree Q1_degree (by norm_num) x w
  · simpa only [P1_eval] using hx
  · simpa only [Q1_eval] using hw

def sliceUnit1 (x : ℂ) : ℂ :=
  (x-1)*(2-3*x^7*(x-1)^2) + (5*x-4)*(1-9*x^7*(x-1)^2+10*x^14*(x-1)^4)
lemma d1x_slice (x : ℂ) : d1x x 0 = x^5*sliceUnit1 x := by
  simp only [d1x, psi, psix, psi0, psi0u, q2, q2u, q1, q1u, sliceUnit1]
  ring

 

theorem d0_gradient_isolated : ∀ᶠ p : ℂ × ℂ in 𝓝 (0 : ℂ × ℂ),
    d0u p.1 p.2 = 0 → d0w p.1 p.2 = 0 → p = 0 := by
  have hw := (continuous_snd.tendsto (0 : ℂ × ℂ)).eventually
    (intPolynomial_isolate_zero res0 res0_nonzero)
  filter_upwards [hw] with p hp hx hy
  have hpw : p.2 = 0 := hp (critical_res0 _ _ hx hy)
  rw [hpw] at hx hy
  have hu : p.1^5=0 := by
    dsimp [d0u, d0w, q2, q2u, q2w, q1, q1u, q1w] at hx hy
    linear_combination -(2/5 : ℂ)*hx - (7/10 : ℂ)*hy
  exact Prod.ext (eq_zero_of_pow_eq_zero hu) hpw

 
theorem d1_gradient_isolated : ∀ᶠ p : ℂ × ℂ in 𝓝 (0 : ℂ × ℂ),
    d1x p.1 p.2 = 0 → d1w p.1 p.2 = 0 → p = 0 := by
  have hw := (continuous_snd.tendsto (0 : ℂ × ℂ)).eventually
    (intPolynomial_isolate_zero res1 res1_nonzero)
  have hc : Continuous (fun p : ℂ × ℂ => sliceUnit1 p.1) := by unfold sliceUnit1; fun_prop
  have hu := hc.continuousAt.eventually_ne (by norm_num [sliceUnit1] : sliceUnit1 (0 : ℂ × ℂ).1 ≠ 0)
  filter_upwards [hw, hu] with p hp hn hx hy
  have hpw : p.2 = 0 := hp (critical_res1 _ _ hx hy)
  rw [hpw, d1x_slice] at hx
  exact Prod.ext (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hx).resolve_right hn)) hpw

end AlgebraicIsolation
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {U W : E → ℂ} {DU DW : E →L[ℂ] ℂ} {p : E}

lemma q1_deriv (hu : HasFDerivAt U DU p) (hw : HasFDerivAt W DW p) :
    HasFDerivAt (fun p => q1 (U p) (W p))
      (q1u (U p) (W p) • DU + q1w (U p) (W p) • DW) p := by
  convert! (((hu.sub hw).sub (hw.pow 8)).mul
    ((hu.sub hw).sub ((hw.pow 8).const_mul 2))).mul (hu.sub (hw.pow 2)) using 1
  ext v
  simp only [Pi.sub_apply, Pi.mul_apply, add_apply, sub_apply, smul_apply, smul_eq_mul, q1u, q1w]
  norm_num only
  ring

lemma q2_deriv (hu : HasFDerivAt U DU p) (hw : HasFDerivAt W DW p) :
    HasFDerivAt (fun p => q2 (U p) (W p))
      (q2u (U p) (W p) • DU + q2w (U p) (W p) • DW) p := by
  convert! (q1_deriv hu hw).sub (hu.pow 2) using 1
  ext v
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, q2u, q2w]
  norm_num only
  ring

lemma d0_deriv (hu : HasFDerivAt U DU p) (hw : HasFDerivAt W DW p) :
    HasFDerivAt (fun p => d0 (U p) (W p))
      (d0u (U p) (W p) • DU + d0w (U p) (W p) • DW) p := by
  convert! (hu.mul (q1_deriv hu hw)).mul (q2_deriv hu hw) using 1
  ext v
  simp only [Pi.mul_apply, add_apply, smul_apply, smul_eq_mul, d0u, d0w]
  ring

lemma psi0_deriv (hu : HasFDerivAt U DU p) (hw : HasFDerivAt W DW p) :
    HasFDerivAt (fun p => psi0 (U p) (W p))
      (psi0u (U p) (W p) • DU + psi0w (U p) (W p) • DW) p := by
  convert! (hu.mul (hu.sub (hw.pow 2))).mul (q2_deriv hu hw) using 1
  ext v
  simp only [Pi.sub_apply, Pi.mul_apply, add_apply, sub_apply, smul_apply, smul_eq_mul, psi0u, psi0w]
  norm_num only
  ring

lemma psi_deriv (hu : HasFDerivAt U DU p) (hw : HasFDerivAt W DW p) :
    HasFDerivAt (fun p => psi (U p) (W p))
      (psix (U p) (W p) • DU + psiw (U p) (W p) • DW) p := by
  convert! psi0_deriv (hu.add hw) hw using 1
  ext v
  simp only [Pi.add_apply, add_apply, smul_apply, smul_eq_mul, psix, psiw]
  ring

lemma d1_deriv (hu : HasFDerivAt U DU p) (hw : HasFDerivAt W DW p) :
    HasFDerivAt (fun p => d1 (U p) (W p))
      (d1x (U p) (W p) • DU + d1w (U p) (W p) • DW) p := by
  have hp := psi_deriv hu hw
  convert! (hp.mul (hu.sub (hp.pow 2))).mul (hu.sub ((hp.pow 2).const_mul 2)) using 1
  ext v
  simp only [Pi.sub_apply, Pi.mul_apply, add_apply, sub_apply, smul_apply, smul_eq_mul, d1x, d1w]
  norm_num only
  ring

end AmbientMultiplicity.PlaneAnalytic
namespace AmbientMultiplicity.Preparation
open Filter Topology

abbrev planeFst : (ℂ × ℂ) →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ ℂ ℂ
abbrev planeSnd : (ℂ × ℂ) →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ ℂ ℂ

def planeEmbed (s : ℂ) : (ℂ × ℂ) →L[ℂ] V 4 :=
  ContinuousLinearMap.pi ![planeFst, 0, 0, s • planeSnd]

def planeSlice (s : ℂ) : V 4 →L[ℂ] (ℂ × ℂ) :=
  (proj 0).prod (s⁻¹ • proj 3)

lemma planeEmbed_slice (s : ℂ) (hs : s ≠ 0) (x : V 4) (hy : x 1 = 0) (hz : x 2 = 0) :
    planeEmbed s (planeSlice s x) = x := by
  ext i
  fin_cases i <;> simp [planeEmbed, planeSlice, hy, hz, hs]

lemma f5_plane (s : ℂ) (hs : s ≠ 0) (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (fun p : ℂ × ℂ => f5 s a b (planeEmbed s p)) =ᶠ[𝓝 0]
      (fun p => PlaneAnalytic.d0 p.1 p.2) := by
  have ht : Tendsto (planeEmbed s) (𝓝 0) (𝓝 0) := by
    simpa using (planeEmbed s).continuous.tendsto 0
  filter_upwards [ht.eventually (chart0_implicit s)] with p hp
  have he : eliminated0 s (planeEmbed s p) = p.1 ^ 2 + q1 p.1 p.2 := by
    simpa [eliminated0, planeEmbed, hs] using hp
  rw [f5, he]
  simp [planeEmbed, perturbation, ha, hb, PlaneAnalytic.d0, PlaneAnalytic.q2]
  change p.1 * q1 p.1 p.2 * (p.1 ^ 2 + q1 p.1 p.2 - 2 * p.1 ^ 2) =
    p.1 * q1 p.1 p.2 * (q1 p.1 p.2 - p.1 ^ 2)
  ring

lemma f4_plane (s : ℂ) (hs : s ≠ 0) (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (fun p : ℂ × ℂ => f4 s a b (planeEmbed s p)) =ᶠ[𝓝 0]
      (fun p => PlaneAnalytic.d1 p.1 p.2) := by
  have ht : Tendsto (planeEmbed s) (𝓝 0) (𝓝 0) := by
    simpa using (planeEmbed s).continuous.tendsto 0
  filter_upwards [ht.eventually (chart1_implicit s)] with p hp
  have he : eliminated1 s (planeEmbed s p) = psi p.1 p.2 := by
    simpa [eliminated1, planeEmbed, hs] using hp
  rw [f4, he]
  simp [planeEmbed, perturbation, ha, hb, PlaneAnalytic.d1, PlaneAnalytic.psi,
    PlaneAnalytic.psi0, PlaneAnalytic.q2, PlaneAnalytic.q1, psi, q2, q1]

lemma two_partials_zero (A B : ℂ) (h : A • planeFst + B • planeSnd = 0) :
    A = 0 ∧ B = 0 := by
  constructor
  · simpa using congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L (1, 0)) h
  · simpa using congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L (0, 1)) h

lemma f5_plane_critical_isolated (s : ℂ) (hs : s ≠ 0) (a b : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 0, fderiv ℂ (f5 s a b) (planeEmbed s p) = 0 → p = 0 := by
  have ht : Tendsto (planeEmbed s) (𝓝 0) (𝓝 0) := by
    simpa using (planeEmbed s).continuous.tendsto 0
  filter_upwards [(f5_plane s hs a b ha hb).eventuallyEq_nhds,
    ht.eventually (f5_analytic s a b).eventually_analyticAt,
    PlaneAnalytic.d0_gradient_isolated] with p he hf hi hc
  have hf' : HasFDerivAt (f5 s a b) (0 : V 4 →L[ℂ] ℂ) (planeEmbed s p) := by
    simpa only [hc] using hf.differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun p => f5 s a b (planeEmbed s p)) (0 : (ℂ × ℂ) →L[ℂ] ℂ) p := by
    convert! hf'.comp p (planeEmbed s).hasFDerivAt using 1
  have hzero : HasFDerivAt (fun p : ℂ × ℂ => PlaneAnalytic.d0 p.1 p.2) (0 : (ℂ × ℂ) →L[ℂ] ℂ) p :=
    hcomp.congr_of_eventuallyEq he.symm
  have hd := PlaneAnalytic.d0_deriv (planeFst.hasFDerivAt (x := p))
    (planeSnd.hasFDerivAt (x := p))
  obtain ⟨hu, hw⟩ := two_partials_zero _ _ (hd.unique hzero)
  exact hi hu hw

lemma f4_plane_critical_isolated (s : ℂ) (hs : s ≠ 0) (a b : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 0, fderiv ℂ (f4 s a b) (planeEmbed s p) = 0 → p = 0 := by
  have ht : Tendsto (planeEmbed s) (𝓝 0) (𝓝 0) := by
    simpa using (planeEmbed s).continuous.tendsto 0
  filter_upwards [(f4_plane s hs a b ha hb).eventuallyEq_nhds,
    ht.eventually (f4_analytic s a b).eventually_analyticAt,
    PlaneAnalytic.d1_gradient_isolated] with p he hf hi hc
  have hf' : HasFDerivAt (f4 s a b) (0 : V 4 →L[ℂ] ℂ) (planeEmbed s p) := by
    simpa only [hc] using hf.differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun p => f4 s a b (planeEmbed s p)) (0 : (ℂ × ℂ) →L[ℂ] ℂ) p := by
    convert! hf'.comp p (planeEmbed s).hasFDerivAt using 1
  have hzero : HasFDerivAt (fun p : ℂ × ℂ => PlaneAnalytic.d1 p.1 p.2) (0 : (ℂ × ℂ) →L[ℂ] ℂ) p :=
    hcomp.congr_of_eventuallyEq he.symm
  have hd := PlaneAnalytic.d1_deriv (planeFst.hasFDerivAt (x := p))
    (planeSnd.hasFDerivAt (x := p))
  obtain ⟨hu, hw⟩ := two_partials_zero _ _ (hd.unique hzero)
  exact hi hu hw

 
theorem f5_critical_isolated (s : ℂ) (hs : s ≠ 0) (a b : ℕ)
    (ha : 11 ≤ a) (hb : 11 ≤ b) :
    ∀ᶠ x in 𝓝 (0 : V 4), fderiv ℂ (f5 s a b) x = 0 → x = 0 := by
  have ht : Tendsto (planeSlice s) (𝓝 (0 : V 4)) (𝓝 0) := by
    simpa using (planeSlice s).continuous.tendsto 0
  filter_upwards [f5_critical_vertical_zero s hs a b ha hb,
    ht.eventually (f5_plane_critical_isolated s hs a b (by omega) (by omega))] with x hv hp hc
  obtain ⟨hy, hz⟩ := hv hc
  have he := planeEmbed_slice s hs x hy hz
  have hz : planeSlice s x = 0 := hp (by simpa only [he] using hc)
  rw [← he, hz, map_zero]

theorem f4_critical_isolated (s : ℂ) (hs : s ≠ 0) (a b : ℕ)
    (ha : 11 ≤ a) (hb : 11 ≤ b) :
    ∀ᶠ x in 𝓝 (0 : V 4), fderiv ℂ (f4 s a b) x = 0 → x = 0 := by
  have ht : Tendsto (planeSlice s) (𝓝 (0 : V 4)) (𝓝 0) := by
    simpa using (planeSlice s).continuous.tendsto 0
  filter_upwards [f4_critical_vertical_zero s hs a b ha hb,
    ht.eventually (f4_plane_critical_isolated s hs a b (by omega) (by omega))] with x hv hp hc
  obtain ⟨hy, hz⟩ := hv hc
  have he := planeEmbed_slice s hs x hy hz
  have hz : planeSlice s x = 0 := hp (by simpa only [he] using hc)
  rw [← he, hz, map_zero]

end AmbientMultiplicity.Preparation

end

end OAI
