import OAI.NumberTheory.Jacobsthal.Estimates.SiegelWalfisz

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

noncomputable def cubeHeight (X : ℝ) : ℝ := (Real.log X)^((1:ℝ)/3)

lemma cubeHeight_pos {X : ℝ} (hX : 1 < X) : 0 < cubeHeight X :=
  Real.rpow_pos_of_pos (Real.log_pos hX) _

lemma cubeHeight_pow_three {X : ℝ} (hX : 1 ≤ X) : (cubeHeight X)^3 = Real.log X := by
  unfold cubeHeight
  rw [← Real.rpow_mul_natCast (Real.log_nonneg hX)]
  norm_num

lemma cubeHeight_mono {X Y : ℝ} (hX : 1 < X) (hXY : X ≤ Y) : cubeHeight X ≤ cubeHeight Y :=
  Real.rpow_le_rpow (Real.log_pos hX).le (Real.log_le_log (by linarith) hXY) (by norm_num)

lemma cubeHeight_tendsto : Tendsto cubeHeight atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp Real.tendsto_log_atTop

lemma eventually_polynomial_le_exp (K : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ h : ℝ in atTop, 1 ≤ h ∧ K*h^n ≤ Real.exp (c*h) := by
  have hl : Tendsto (fun h:ℝ => K*h^n*Real.exp (-c*h)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,mul_assoc,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) c hc).const_mul K
  filter_upwards [eventually_ge_atTop (1:ℝ),hl.eventually (gt_mem_nhds zero_lt_one)] with h hh hsmall
  refine ⟨hh,?_⟩
  have hm := mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos (c*h)).le
  have he : Real.exp (-c*h)*Real.exp (c*h)=1 := by rw [← Real.exp_add,show -c*h+c*h=0 by ring,Real.exp_zero]
  simpa only [mul_assoc,he,mul_one,one_mul] using hm

lemma exponential_height_bound {h : ℝ} (hh : Real.log 7 ≤ h) (q : ℕ) [NeZero q]
    (hq : (q:ℝ) ≤ Real.exp h) : modulusHeight q (Real.exp h) ≤ 3*h := by
  have hh0 : 0 < h := (Real.log_pos (by norm_num : (1:ℝ)<7)).trans_le hh
  have hT : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh0.le
  have hq0 : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hql : Real.log (q:ℝ) ≤ h := by
    have he := Real.log_le_log hq0 hq
    simpa only [Real.log_exp] using he
  have hsum : Real.exp h+6 ≤ 7*Real.exp h := by linarith
  have hl : Real.log (Real.exp h+6) ≤ Real.log 7+h := by
    have he := Real.log_le_log (by positivity : 0 < Real.exp h+6) hsum
    rwa [Real.log_mul (by norm_num : (7:ℝ)≠0) (Real.exp_ne_zero h),Real.log_exp] at he
  unfold modulusHeight
  rw [abs_of_pos (Real.exp_pos h)]
  linarith

lemma exponential_left_saving {a X : ℝ} (ha : 0 < a) (hX : 1 < X)
    (hh : Real.log 7 ≤ cubeHeight X) (q : ℕ) [NeZero q]
    (hq : (q:ℝ) ≤ Real.exp (cubeHeight X)) :
    Real.exp (-a*Real.log X/(modulusHeight q (Real.exp (cubeHeight X)))^2) ≤
      Real.exp (-(a/9)*cubeHeight X) := by
  let h := cubeHeight X
  let H := modulusHeight q (Real.exp h)
  have hh0 : 0 < h := cubeHeight_pos hX
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (modulusHeight_ge_one q _)
  have hHle : H ≤ 3*h := exponential_height_bound hh q hq
  have hsq : H^2 ≤ 9*h^2 := by nlinarith [sq_nonneg (3*h-H)]
  have hcube : h^3 = Real.log X := cubeHeight_pow_three hX.le
  apply Real.exp_le_exp.mpr
  change -a*Real.log X/H^2 ≤ -(a/9)*h
  apply (div_le_iff₀ (sq_pos_of_pos hH)).mpr
  rw [← hcube]
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (a/9)*h by positivity)
  nlinarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma eventually_exponential_contour_savings {a : ℝ} (ha : 0 < a) (ha100 : a ≤ 1/100) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧ ∀ᶠ X : ℝ in atTop,
      3 ≤ X ∧ 1 ≤ Real.log X ∧ ∀ (q : ℕ) [NeZero q],
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      let T := Real.exp (cubeHeight X)
      let H := modulusHeight q T
      H^3*Real.exp (-a*Real.log X/H^2) ≤ Real.exp (-c*cubeHeight X) ∧
      H^3/(1+T^2) ≤ Real.exp (-c*cubeHeight X) ∧
      Real.log X/T ≤ Real.exp (-c*cubeHeight X) := by
  let c : ℝ := a/18
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : c ≤ 1/2 := by dsimp [c]; linarith
  refine ⟨c,hc,hc2,?_⟩
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (Real.log 7)),
    cubeHeight_tendsto.eventually (eventually_polynomial_le_exp 27 3 hc)] with X hX hh7 hhpoly
  have hx1 : 1 < X := by linarith
  have hx0 : 0 < X := by linarith
  have hL : 1 ≤ Real.log X :=
    ((Real.lt_log_iff_exp_lt hx0).mpr (Real.exp_one_lt_three.trans_le hX)).le
  refine ⟨hX,hL,?_⟩
  intro q _ hq
  let h := cubeHeight X
  let T := Real.exp h
  let H := modulusHeight q T
  have hh : 0 < h := cubeHeight_pos hx1
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (modulusHeight_ge_one q _)
  have hHle : H ≤ 3*h := exponential_height_bound hh7 q hq
  have hHp : H^3 ≤ Real.exp (c*h) := by
    have hp := pow_le_pow_left₀ hH.le hHle 3
    calc
      _ ≤ (3*h)^3 := hp
      _ = 27*h^3 := by ring
      _ ≤ _ := hhpoly.2
  have hLp : Real.log X ≤ Real.exp (c*h) := by
    calc
      _ = h^3 := (cubeHeight_pow_three hx1.le).symm
      _ ≤ 27*h^3 := by nlinarith [pow_nonneg hh.le 3]
      _ ≤ _ := hhpoly.2
  have hs := exponential_left_saving ha hx1 hh7 q hq
  have hT2 : T^2 = Real.exp (2*h) := by
    dsimp [T]
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ Real.exp (c*h)*Real.exp (-(a/9)*h) :=
        mul_le_mul hHp hs (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-c*h) := by rw [← Real.exp_add]; congr 1; dsimp [c]; ring
  · calc
      _ ≤ H^3/T^2 := div_le_div_of_nonneg_left (by positivity) (by dsimp [T]; positivity) (by linarith)
      _ ≤ Real.exp (c*h)/T^2 := div_le_div_of_nonneg_right hHp (sq_nonneg _)
      _ = Real.exp (c*h-2*h) := by rw [hT2,Real.exp_sub]
      _ ≤ Real.exp (-c*h) := Real.exp_le_exp.mpr (by nlinarith)
  · calc
      _ ≤ Real.exp (c*h)/T := div_le_div_of_nonneg_right hLp (by dsimp [T]; positivity)
      _ = Real.exp (c*h-h) := by dsimp [T]; rw [Real.exp_sub]
      _ ≤ Real.exp (-c*h) := Real.exp_le_exp.mpr (by nlinarith)

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem riesz_character_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
        K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨a,ha,ha100,C,hC,B,hB,hcontour⟩ := exists_uniform_riesz_contour_bound
  obtain ⟨c,hc,hc2,hsavings⟩ := eventually_exponential_contour_savings ha ha100
  let P : ℝ := 4*Real.pi*C+16*C*Real.exp 1+8*(B+1)*Real.exp 1
  let K : ℝ := (1/(2*Real.pi))*P
  have hP : 0 < P := by dsimp only [P]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨c,K,hc,hc2,hK,?_⟩
  filter_upwards [hsavings] with X hX
  intro q _ chi hchi hq
  obtain ⟨hX3,hL1,hSavings⟩ := hX
  obtain ⟨hleft,hhor,hratio⟩ := hSavings q hq
  let L : ℝ := Real.log X
  let T : ℝ := Real.exp (cubeHeight X)
  let R : ℝ := Real.exp (-c*cubeHeight X)
  let H : ℝ := modulusHeight q T
  let sigma : ℝ := 1+L⁻¹
  have hXp : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hLp : 0 < L := by linarith
  have hTp : 0 < T := Real.exp_pos _
  have hs1 : 1 < sigma := by
    have hi : 0 < L⁻¹ := inv_pos.mpr hLp
    dsimp only [sigma]
    linarith
  have hs2 : sigma ≤ 2 := by
    have hinv : L⁻¹ ≤ 1 := by rw [← one_div]; exact (div_le_iff₀ hLp).mpr (by linarith)
    dsimp only [sigma]
    linarith
  have h := hcontour q chi hchi X sigma T (by linarith) hs1 hs2 hTp
  have hrightpow : X^sigma = X*Real.exp 1 := rpow_perron_sigma hX1
  have hleftpow : X^(rieszContourLeft a q T) = X*Real.exp (-a*L/H^2) := rpow_rieszContourLeft hXp a q T
  have hinv : (sigma-1)⁻¹ = L := by dsimp only [sigma]; rw [add_sub_cancel_left,inv_inv]
  rw [hrightpow,hleftpow,hinv] at h
  change H^3*Real.exp (-a*L/H^2) ≤ R at hleft
  change H^3/(1+T^2) ≤ R at hhor
  change L/T ≤ R at hratio
  have hBL := mul_le_mul_of_nonneg_left (show 1 ≤ L by linarith) hB
  have hLB : L+B ≤ (B+1)*L := by nlinarith only [hBL]
  have htail : (L+B)/T ≤ (B+1)*R := by
    calc
      _ ≤ ((B+1)*L)/T := div_le_div_of_nonneg_right hLB hTp.le
      _ = (B+1)*(L/T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hleft (show 0 ≤ 4*Real.pi*C*X by positivity)
  have h2 := mul_le_mul_of_nonneg_left hhor (show 0 ≤ 16*C*Real.exp 1*X by positivity)
  have h3 := mul_le_mul_of_nonneg_left htail (show 0 ≤ 8*Real.exp 1*X by positivity)
  have he : 4*Real.pi*C*H^3*(X*Real.exp (-a*L/H^2)) +
      16*C*H^3*(X*Real.exp 1)/(1+T^2)+8*(L+B)*(X*Real.exp 1)/T ≤ P*X*R := by
    calc
      _ = (4*Real.pi*C*X)*(H^3*Real.exp (-a*L/H^2)) +
          (16*C*Real.exp 1*X)*(H^3/(1+T^2))+(8*Real.exp 1*X)*((L+B)/T) := by ring
      _ ≤ (4*Real.pi*C*X)*R+(16*C*Real.exp 1*X)*R+
          (8*Real.exp 1*X)*((B+1)*R) := add_le_add (add_le_add h1 h2) h3
      _ = _ := by dsimp only [P]; ring
  apply h.trans
  calc
    _ ≤ (1/(2*Real.pi))*(P*X*R) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = K*X*Real.exp (-c*cubeHeight X) := by dsimp only [K,R]; ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma cubeHeight_le_log {X : ℝ} (hX : 1 ≤ X) (hh : 1 ≤ cubeHeight X) :
    cubeHeight X ≤ Real.log X := by
  have hp : 1 ≤ (cubeHeight X)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ cubeHeight X by linarith)
  rw [← cubeHeight_pow_three hX]
  nlinarith

lemma exponential_recovery_scale {d X : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hX : 3 ≤ X) (hh : 1 ≤ cubeHeight X) :
    let delta := Real.exp (-d*cubeHeight X)
    let Y := (1+delta)*X
    0 < delta ∧ delta ≤ 1 ∧ 1 ≤ delta*X ∧ X ≤ Y ∧ Y ≤ 2*X ∧
      cubeHeight X ≤ cubeHeight Y ∧ Real.log Y ≤ 2*Real.log X := by
  let delta := Real.exp (-d*cubeHeight X)
  let Y := (1+delta)*X
  have hx0 : 0 < X := by linarith
  have hx1 : 1 < X := by linarith
  have hh0 : 0 < cubeHeight X := cubeHeight_pos hx1
  have hdpos : 0 < delta := Real.exp_pos _
  have hdle : delta ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hsmall : d*cubeHeight X ≤ Real.log X := by
    calc
      _ ≤ cubeHeight X := by nlinarith
      _ ≤ _ := cubeHeight_le_log hx1.le hh
  have hpower : Real.exp (d*cubeHeight X) ≤ X := by
    simpa only [Real.exp_log hx0] using Real.exp_le_exp.mpr hsmall
  have hid : delta*Real.exp (d*cubeHeight X)=1 := by
    dsimp [delta]
    rw [← Real.exp_add,show -d*cubeHeight X+d*cubeHeight X=0 by ring,Real.exp_zero]
  have hdX : 1 ≤ delta*X := by
    have hm := mul_le_mul_of_nonneg_left hpower hdpos.le
    rwa [hid] at hm
  have hXY : X ≤ Y := by dsimp [Y]; nlinarith
  have hY2 : Y ≤ 2*X := by dsimp [Y]; nlinarith
  have hY0 : 0 < Y := hx0.trans_le hXY
  have hhY : cubeHeight X ≤ cubeHeight Y := cubeHeight_mono hx1 hXY
  have hlog2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) (by linarith)
  have hlogY : Real.log Y ≤ 2*Real.log X := by
    have h := Real.log_le_log hY0 hY2
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx0.ne'] at h
    linarith
  exact ⟨hdpos,hdle,hdX,hXY,hY2,hhY,hlogY⟩

lemma exponential_recovery_tail {c X : ℝ} (hc : 0 < c) (hc2 : c ≤ 1/2)
    (hX : 3 ≤ X) (hh : 1 ≤ cubeHeight X)
    (hpoly : (cubeHeight X)^3 ≤ Real.exp ((c/4)*cubeHeight X)) :
    let delta := Real.exp (-(c/2)*cubeHeight X)
    (delta*X+1)*Real.log ((1+delta)*X) ≤ 4*X*Real.exp (-(c/4)*cubeHeight X) := by
  let delta := Real.exp (-(c/2)*cubeHeight X)
  obtain ⟨hd,_,hdX,hXY,_,_,hlogY⟩ := exponential_recovery_scale (d:=c/2)
    (by positivity) (by linarith) hX hh
  have hx0 : 0 < X := by linarith
  have hY0 : 0 < (1+delta)*X := by positivity
  have hlogY0 : 0 ≤ Real.log ((1+delta)*X) := Real.log_nonneg (by linarith)
  have hprod : delta*Real.log X ≤ Real.exp (-(c/4)*cubeHeight X) := by
    calc
      _ = delta*(cubeHeight X)^3 := by rw [cubeHeight_pow_three (by linarith : 1≤X)]
      _ ≤ delta*Real.exp ((c/4)*cubeHeight X) := mul_le_mul_of_nonneg_left hpoly hd.le
      _ = _ := by dsimp [delta]; rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (2*delta*X)*(2*Real.log X) := mul_le_mul (by nlinarith) hlogY hlogY0 (by positivity)
    _ = 4*X*(delta*Real.log X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem sharp_character_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
        K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,C,hc,hc2,hC,hRiesz⟩ := riesz_character_exponential
  obtain ⟨X0,hX0⟩ := eventually_atTop.mp hRiesz
  refine ⟨c/4,5*C+4,by positivity,by linarith,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop X0,eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_polynomial_le_exp 1 3 (by positivity : 0<c/4))]
    with X hthreshold hX hpoly
  intro q _ chi hchi hq
  let h := cubeHeight X
  let delta := Real.exp (-(c/2)*h)
  let Y := (1+delta)*X
  let f : ℕ → ℂ := fun n => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)
  have hx0 : 0 < X := by linarith
  have hx1 : 1 < X := by linarith
  have hh0 : 0 < h := cubeHeight_pos hx1
  obtain ⟨hd,hd1,hdX,hXY,hY2,hhY,_⟩ := exponential_recovery_scale (d:=c/2)
    (by positivity) (by linarith) hX hpoly.1
  have hqY : (q:ℝ) ≤ Real.exp (cubeHeight Y) := hq.trans (Real.exp_le_exp.mpr hhY)
  have hx := hX0 X hthreshold q chi hchi hq
  have hy := hX0 Y (hthreshold.trans hXY) q chi hchi hqY
  have hdecay : Real.exp (-c*cubeHeight Y) ≤ Real.exp (-c*h) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hy' : ‖rieszSum f Y‖ ≤ 2*C*X*Real.exp (-c*h) := by
    calc
      _ ≤ C*Y*Real.exp (-c*cubeHeight Y) := hy
      _ ≤ C*Y*Real.exp (-c*h) := mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ ≤ C*(2*X)*Real.exp (-c*h) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hY2 hC.le) (Real.exp_pos _).le
      _ = _ := by ring
  have hnum : (1+delta)*‖rieszSum f Y‖+‖rieszSum f X‖ ≤ 5*C*X*Real.exp (-c*h) := by
    have h1 := mul_le_mul_of_nonneg_left hy' (show 0 ≤ 1+delta by linarith)
    have h2 := mul_le_mul_of_nonneg_right (show 1+delta ≤ 2 by linarith)
      (show 0 ≤ 2*C*X*Real.exp (-c*h) by positivity)
    apply (add_le_add (h1.trans h2) hx).trans_eq
    ring
  have hterm : ((1+delta)*‖rieszSum f Y‖+‖rieszSum f X‖)/delta ≤
      5*C*X*Real.exp (-(c/4)*h) := by
    calc
      _ ≤ (5*C*X*Real.exp (-c*h))/delta := div_le_div_of_nonneg_right hnum hd.le
      _ = 5*C*X*Real.exp (-(c/2)*h) := by
        dsimp [delta]
        rw [mul_div_assoc,← Real.exp_sub]
        congr 1
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  have htail := exponential_recovery_tail hc hc2 hX hpoly.1 (by simpa only [one_mul] using hpoly.2)
  have hcoeff : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ Real.log (n:ℝ) :=
    fun n _ => character_vonMangoldt_norm_le chi n
  have hsharp := sharpSum_norm_le_riesz f hcoeff (show 1 ≤ X by linarith) hd
  apply (hsharp.trans (add_le_add hterm htail)).trans_eq
  ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma eventually_polynomial_le_X_exp (K : ℝ) (n : ℕ) (d : ℝ) :
    ∀ᶠ X : ℝ in atTop, K*(cubeHeight X)^n ≤ X*Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (d+1)),
    cubeHeight_tendsto.eventually (eventually_polynomial_le_exp K n (by norm_num : (0:ℝ)<1))]
    with X hX hd hp
  let h := cubeHeight X
  have hh : 0 ≤ h := by linarith [hp.1]
  have hh2 : h ≤ h^2 := by nlinarith [hp.1]
  have hsq : d+1 ≤ h^2 := hd.trans hh2
  have hm := mul_le_mul_of_nonneg_right hsq hh
  have hcube : h^3=Real.log X := cubeHeight_pow_three (by linarith)
  have he : h ≤ Real.log X-d*h := by rw [← hcube]; nlinarith
  calc
    _ ≤ Real.exp h := by simpa only [one_mul] using hp.2
    _ ≤ Real.exp (Real.log X-d*h) := Real.exp_le_exp.mpr he
    _ = X*Real.exp (-d*h) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by linarith : 0<X)]; congr 1; congr 1; ring

lemma eventually_sqrt_le_X_exp (d : ℝ) :
    ∀ᶠ X : ℝ in atTop, Real.sqrt X ≤ X*Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (max 1 (2*d)))] with X hX hh
  let h := cubeHeight X
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hhd : 2*d ≤ h := (le_max_right _ _).trans hh
  have hsq : 2*d ≤ h^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq (show 0 ≤ h by linarith)
  have hcube : h^3=Real.log X := cubeHeight_pow_three (by linarith)
  have he : Real.log X*((1:ℝ)/2) ≤ Real.log X-d*h := by rw [← hcube]; nlinarith
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by linarith : 0<X)]
  calc
    _ ≤ Real.exp (Real.log X-d*h) := Real.exp_le_exp.mpr he
    _ = X*Real.exp (-d*h) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by linarith : 0<X)]; congr 1; congr 1; ring

lemma eventually_exp_sqrt_log_le {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    ∀ᶠ X : ℝ in atTop,
      Real.exp (-a*Real.sqrt (Real.log X)) ≤ Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    cubeHeight_tendsto.eventually (eventually_ge_atTop (max 1 ((d/a)^2)))] with X hX hh
  let h := cubeHeight X
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hh0 : 0 ≤ h := by linarith
  have hsq : (d/a)^2 ≤ h := (le_max_right _ _).trans hh
  have hda : d/a ≤ Real.sqrt h := (Real.le_sqrt (by positivity) hh0).mpr hsq
  have hmul : d ≤ a*Real.sqrt h := by
    have he := (div_le_iff₀ ha).mp hda
    simpa only [mul_comm] using he
  have hsqrt : Real.sqrt (Real.log X) = h*Real.sqrt h := by
    rw [← cubeHeight_pow_three (by linarith : 1≤X),show (cubeHeight X)^3=(cubeHeight X)^2*cubeHeight X by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hh0]
  have hm := mul_le_mul_of_nonneg_right hmul hh0
  apply Real.exp_le_exp.mpr
  rw [hsqrt]
  nlinarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma ordinary_psi_exponential {d : ℝ} (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ‖sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ)‖ ≤
        K*X*Real.exp (-d*cubeHeight X) := by
  obtain ⟨a,ha,hPNT⟩ := _root_.Erdos970.Strong_PNT
  obtain ⟨K,hK,hbound⟩ := hPNT.exists_pos
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound.bound,eventually_exp_sqrt_log_le ha hd,
    eventually_ge_atTop (3:ℝ)] with X hb he hX
  have hx0 : 0 < X := by linarith
  change ‖_root_.Erdos970.ChebyshevPsi X-X‖ ≤ K*‖X*Real.exp (-a*(Real.log X)^(1/2:ℝ))‖ at hb
  rw [sharpSum_vonMangoldt_eq hx0.le,← Complex.ofReal_sub,Complex.norm_real]
  simp only [Real.norm_eq_abs] at hb ⊢
  rw [abs_of_nonneg (by positivity : 0≤X*Real.exp (-a*(Real.log X)^(1/2:ℝ))),
    ← Real.sqrt_eq_rpow] at hb
  calc
    _ ≤ K*(X*Real.exp (-a*Real.sqrt (Real.log X))) := hb
    _ ≤ K*(X*Real.exp (-d*cubeHeight X)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hx0.le) hK.le
    _ = _ := by ring

lemma principal_difference_exponential (d : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤ X*Real.exp (-d*cubeHeight X) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),eventually_polynomial_le_X_exp (1/Real.log 2) 4 d]
    with X hX hpoly
  intro q _ hq
  have hx1 : 1 < X := by linarith
  have hL : 0 ≤ Real.log X := (Real.log_pos hx1).le
  have hq0 : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hql : Real.log (q:ℝ) ≤ cubeHeight X := by
    have he := Real.log_le_log hq0 hq
    simpa only [Real.log_exp] using he
  calc
    _ ≤ (Real.log X/Real.log 2)*Real.log (q:ℝ) := norm_principal_sharp_difference_real q hx1.le
    _ ≤ (Real.log X/Real.log 2)*cubeHeight X := mul_le_mul_of_nonneg_left hql (by positivity)
    _ = (1/Real.log 2)*(cubeHeight X)^4 := by rw [← cubeHeight_pow_three hx1.le]; ring
    _ ≤ _ := hpoly

theorem principal_character_exponential {d : ℝ} (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q],
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ)‖ ≤
        K*X*Real.exp (-d*cubeHeight X) := by
  obtain ⟨K,hK,hOrd⟩ := ordinary_psi_exponential hd
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [principal_difference_exponential d,hOrd] with X hDiff hOrd
  intro q _ hq
  have hn := norm_add_le
    (sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
      sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X)
    (sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X-(X:ℂ))
  rw [sub_add_sub_cancel] at hn
  apply (hn.trans (add_le_add (hDiff q hq) hOrd)).trans_eq
  ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem all_character_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)‖ ≤ K*X*Real.exp (-c*cubeHeight X) := by
  classical
  obtain ⟨c,C,hc,hc2,hC,hNon⟩ := sharp_character_exponential
  obtain ⟨D,hD,hPrin⟩ := principal_character_exponential hc
  refine ⟨c,C+D,hc,hc2,by positivity,?_⟩
  filter_upwards [hNon,hPrin,eventually_ge_atTop (3:ℝ)] with X hNon hPrin hX
  intro q _ chi hq
  have hx0 : 0 ≤ X := by linarith
  have hcb : C*X*Real.exp (-c*cubeHeight X) ≤ (C+D)*X*Real.exp (-c*cubeHeight X) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hx0) (Real.exp_pos _).le
  have hdb : D*X*Real.exp (-c*cubeHeight X) ≤ (C+D)*X*Real.exp (-c*cubeHeight X) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hx0) (Real.exp_pos _).le
  by_cases hchi : chi=1
  · subst chi
    simpa using! (hPrin q hq).trans hdb
  · simpa [hchi] using! (hNon q chi hchi hq).trans hcb

theorem residuePsi_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      |residuePsi a X-X/(q.totient:ℝ)| ≤ K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,K,hc,hc2,hK,hall⟩ := all_character_exponential
  refine ⟨c,K,hc,hc2,hK,?_⟩
  filter_upwards [hall] with X hX
  intro q _ a ha hq
  have h := residuePsi_error_le a ha X (K*X*Real.exp (-c*cubeHeight X)) (fun chi => hX q chi hq)
  have he : ‖(residuePsi a X:ℂ)-(X:ℂ)/(q.totient:ℂ)‖ =
      |residuePsi a X-X/(q.totient:ℝ)| := by
    rw [show (q.totient:ℂ) = ((q.totient:ℝ):ℂ) by simp,
      ← Complex.ofReal_div,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rwa [he] at h

theorem residueTheta_exponential :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a →
      (q:ℝ) ≤ Real.exp (cubeHeight X) →
      |residueTheta a X-X/(q.totient:ℝ)| ≤ K*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,K,hc,hc2,hK,hpsi⟩ := residuePsi_exponential
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C : ℝ := max D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨c,K+C,hc,hc2,by positivity,?_⟩
  filter_upwards [hpsi,eventually_sqrt_le_X_exp c] with X hX hsqrt
  intro q _ a ha hq
  have hgap := residuePsi_sub_theta_bounds a X
  have hb : residuePsi a X-residueTheta a X ≤ C*X*Real.exp (-c*cubeHeight X) := by
    calc
      _ ≤ D*Real.sqrt X := hgap.2.trans (hD X)
      _ ≤ C*Real.sqrt X := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ C*(X*Real.exp (-c*cubeHeight X)) := mul_le_mul_of_nonneg_left hsqrt hC.le
      _ = _ := by ring
  calc
    _ ≤ |residuePsi a X-X/(q.totient:ℝ)|+|residuePsi a X-residueTheta a X| := by
      have h := abs_sub_le (residueTheta a X) (residuePsi a X) (X/(q.totient:ℝ))
      rw [abs_sub_comm (residueTheta a X) (residuePsi a X),add_comm] at h
      exact h
    _ ≤ K*X*Real.exp (-c*cubeHeight X)+C*X*Real.exp (-c*cubeHeight X) := by
      rw [abs_of_nonneg hgap.1]
      exact add_le_add (hX q a ha hq) hb
    _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.MeasureTheory
open scoped Topology

lemma cubeHeight_above_sqrt {X t : ℝ} (hX : 3 ≤ Real.sqrt X) (ht : Real.sqrt X ≤ t) :
    cubeHeight X/2 ≤ cubeHeight t := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 < X := Real.sqrt_pos.mp hs
  have hx1 : 1 < X := by nlinarith [Real.sq_sqrt hx0.le]
  have ht1 : 1 < t := by linarith
  have hhX : 0 < cubeHeight X := cubeHeight_pos hx1
  have hht : 0 < cubeHeight t := cubeHeight_pos ht1
  have hcompare : Real.log X ≤ 2*Real.log t := by
    have he := Real.log_le_log hs ht
    rw [Real.log_sqrt hx0.le] at he
    linarith
  apply (pow_le_pow_iff_left₀ (show 0 ≤ cubeHeight X/2 by positivity) hht.le (by decide : (3:ℕ)≠0)).mp
  rw [show (cubeHeight X/2)^3=(cubeHeight X)^3/8 by ring,
    cubeHeight_pow_three hx1.le,cubeHeight_pow_three ht1.le]
  have hlog := Real.log_pos hx1
  linarith

lemma modulus_exponential_above_sqrt {c X t : ℝ} (hc : c ≤ 1/2)
    (hX : 3 ≤ Real.sqrt X) (ht : Real.sqrt X ≤ t) {q : ℕ}
    (hq : (q:ℝ) ≤ Real.exp (c*cubeHeight X)) :
    (q:ℝ) ≤ Real.exp (cubeHeight t) := by
  have hx0 : 0 < X := Real.sqrt_pos.mp (by linarith)
  have hhX : 0 < cubeHeight X := cubeHeight_pos (by nlinarith [Real.sq_sqrt hx0.le])
  apply hq.trans (Real.exp_le_exp.mpr ?_)
  calc
    _ ≤ cubeHeight X/2 := by nlinarith
    _ ≤ _ := cubeHeight_above_sqrt hX ht

lemma residueErrorKernel_exp_upper {q : ℕ} (a : ZMod q) {K d X t : ℝ}
    (hK : 0 ≤ K) (hd : 0 < d) (hX : 3 ≤ Real.sqrt X) (ht : Real.sqrt X ≤ t)
    (herror : |residueTheta a t-t/(q.totient:ℝ)| ≤ K*t*Real.exp (-d*cubeHeight t)) :
    |residueErrorKernel a t| ≤ K*Real.exp (-(d/2)*cubeHeight X) := by
  have ht3 : 3 ≤ t := hX.trans ht
  have ht0 : 0 < t := by linarith
  have hl1 : 1 ≤ Real.log t :=
    ((Real.lt_log_iff_exp_lt ht0).mpr (Real.exp_one_lt_three.trans_le ht3)).le
  have hcompare := cubeHeight_above_sqrt hX ht
  rw [residueErrorKernel_eq a ht0,abs_div,abs_of_pos (by positivity : 0<t*Real.log t^2)]
  calc
    _ ≤ (K*t*Real.exp (-d*cubeHeight t))/(t*Real.log t^2) :=
      div_le_div_of_nonneg_right herror (by positivity)
    _ = (K*Real.exp (-d*cubeHeight t))/(Real.log t)^2 := by field_simp
    _ ≤ K*Real.exp (-d*cubeHeight t) := div_le_self (by positivity) (by nlinarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hK

lemma residueErrorKernel_exp_high_integral {q : ℕ} (a : ZMod q) {K d X : ℝ}
    (hK : 0 ≤ K) (hd : 0 < d) (hX : 3 ≤ Real.sqrt X)
    (herror : ∀ t, Real.sqrt X ≤ t →
      |residueTheta a t-t/(q.totient:ℝ)| ≤ K*t*Real.exp (-d*cubeHeight t)) :
    |∫ t in Real.sqrt X..X, residueErrorKernel a t| ≤
      K*X*Real.exp (-(d/2)*cubeHeight X) := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 < X := Real.sqrt_pos.mp hs
  have hsX : Real.sqrt X ≤ X := by nlinarith [Real.sq_sqrt hx0.le]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a:=Real.sqrt X) (b:=X)
    (f:=residueErrorKernel a) (C:=K*Real.exp (-(d/2)*cubeHeight X)) (fun t ht => by
      rw [Set.uIoc_of_le hsX] at ht
      simpa only [Real.norm_eq_abs] using
        residueErrorKernel_exp_upper a hK hd hX ht.1.le (herror t ht.1.le))
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hsX)] at he
  calc
    _ ≤ K*Real.exp (-(d/2)*cubeHeight X)*(X-Real.sqrt X) := he
    _ ≤ K*Real.exp (-(d/2)*cubeHeight X)*X :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.MeasureTheory
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma large_modulus_siegel_walfisz_eventually :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (r : ℤ), IsUnit (r:ZMod q) →
      (q:ℝ) ≤ Real.exp (c*cubeHeight X) →
      |((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ)| ≤
        C*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨d,K,hd,hd2,hK,hθ⟩ := residueTheta_exponential
  obtain ⟨b,hb⟩ := eventually_atTop.mp hθ
  let c : ℝ := d/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : c ≤ 1/2 := by dsimp [c]; linarith
  let D : ℝ := (Real.log 4+1)/(Real.log 2)^2
  let E : ℝ := 2/Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨c,E+2*K+D,hc,hc2,by positivity,?_⟩
  filter_upwards [Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (max 3 b)),
    eventually_ge_atTop (3:ℝ),eventually_sqrt_le_X_exp c,
    eventually_polynomial_le_X_exp 1 0 c] with X hs hX hroot hscale
  intro q _ r hr hq
  have hs3 : 3 ≤ Real.sqrt X := (le_max_left _ _).trans hs
  have hsb : b ≤ Real.sqrt X := (le_max_right _ _).trans hs
  have hx0 : 0 < X := by linarith
  have hsX : Real.sqrt X ≤ X := by nlinarith [Real.sq_sqrt hx0.le]
  have hhX : 0 < cubeHeight X := cubeHeight_pos (by linarith)
  have hL1 : 1 ≤ Real.log X :=
    ((Real.lt_log_iff_exp_lt hx0).mpr (Real.exp_one_lt_three.trans_le hX)).le
  have hL : 0 < Real.log X := by linarith
  have hscale1 : 1 ≤ X*Real.exp (-c*cubeHeight X) := by simpa only [pow_zero,mul_one] using hscale
  have herror : ∀ t, Real.sqrt X ≤ t →
      |residueTheta (r:ZMod q) t-t/(q.totient:ℝ)| ≤ K*t*Real.exp (-d*cubeHeight t) := by
    intro t ht
    exact hb t (hsb.trans ht) q (r:ZMod q) hr
      (modulus_exponential_above_sqrt hc2 hs3 ht hq)
  have hdecay : Real.exp (-d*cubeHeight X) ≤ Real.exp (-c*cubeHeight X) :=
    Real.exp_le_exp.mpr (by dsimp [c]; nlinarith)
  have hend : |(residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X| ≤
      K*X*Real.exp (-c*cubeHeight X) := by
    rw [abs_div,abs_of_pos hL]
    calc
      _ ≤ (K*X*Real.exp (-d*cubeHeight X))/Real.log X :=
        div_le_div_of_nonneg_right (herror X hsX) hL.le
      _ ≤ K*X*Real.exp (-d*cubeHeight X) := div_le_self (by positivity) hL1
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)
  have hlo : |∫ t in 2..Real.sqrt X, residueErrorKernel (r:ZMod q) t| ≤
      D*X*Real.exp (-c*cubeHeight X) := by
    calc
      _ ≤ D*Real.sqrt X := residueErrorKernel_low_integral _ (by linarith)
      _ ≤ D*(X*Real.exp (-c*cubeHeight X)) := mul_le_mul_of_nonneg_left hroot hD.le
      _ = _ := by ring
  have hhi := residueErrorKernel_exp_high_integral (r:ZMod q) hK.le hd hs3 herror
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (residueErrorKernel_integrable (r:ZMod q) (by norm_num) (by linarith : (2:ℝ)≤Real.sqrt X))
    (residueErrorKernel_integrable (r:ZMod q) (by linarith : (2:ℝ)≤Real.sqrt X) hsX)
  have hint : |∫ t in 2..X, residueErrorKernel (r:ZMod q) t| ≤
      D*X*Real.exp (-c*cubeHeight X)+K*X*Real.exp (-c*cubeHeight X) := by
    rw [← hsplit]
    exact (abs_add_le _ _).trans (add_le_add hlo hhi)
  have hphi : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hconst : |2/((q.totient:ℝ)*Real.log 2)| ≤ E*X*Real.exp (-c*cubeHeight X) := by
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = E/(q.totient:ℝ) := by dsimp [E]; ring
      _ ≤ E := div_le_self hE.le hphi
      _ ≤ E*(X*Real.exp (-c*cubeHeight X)) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale1 hE.le
      _ = _ := by ring
  rw [intervalPrimes_error_eq (by linarith) q r]
  calc
    _ ≤ |2/((q.totient:ℝ)*Real.log 2)|+
        |(residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X|+
        |∫ t in 2..X, residueErrorKernel (r:ZMod q) t| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ E*X*Real.exp (-c*cubeHeight X)+K*X*Real.exp (-c*cubeHeight X)+
        (D*X*Real.exp (-c*cubeHeight X)+K*X*Real.exp (-c*cubeHeight X)) :=
      add_le_add (add_le_add hconst hend) hint
    _ = _ := by ring

theorem large_modulus_siegel_walfisz :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ (q : ℕ) (r : ℤ), 0 < q → IsCoprime r (q:ℤ) →
      (q:ℝ) ≤ Real.exp (c*(Real.log X)^((1:ℝ)/3)) →
      |((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ)| ≤
        C*X*Real.exp (-c*(Real.log X)^((1:ℝ)/3)) := by
  obtain ⟨c,C,hc,_hc2,hC,h⟩ := large_modulus_siegel_walfisz_eventually
  obtain ⟨b,hb⟩ := eventually_atTop.mp h
  refine ⟨c,C,max 3 b,hc,hC,le_max_left _ _,?_⟩
  intro X hX q r hq hr hbound
  let _ : NeZero q := ⟨hq.ne'⟩
  exact hb X ((le_max_right _ _).trans hX) q r (isUnit_intCast_of_isCoprime hr) hbound

end Erdos970Dependency.SiegelWalfisz


end Erdos970

end OAI
