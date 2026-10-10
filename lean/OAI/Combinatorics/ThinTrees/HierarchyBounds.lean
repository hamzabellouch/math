import OAI.Combinatorics.ThinTrees.MatrixDomain

namespace OAI

section

noncomputable section
open Finset Filter
open scoped Topology
namespace StrongThinTree.ShortcutNumeric
open MultiGraph.Hierarchy

lemma eventually_affine_log_lt_rpow (a b : ℝ) {z : ℝ} (hz : 0 < z) :
    ∀ᶠ x : ℝ in atTop, a+b*Real.log x < x^z := by
  have hc : Tendsto (fun x : ℝ => a/x^z) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using
      ((tendsto_rpow_atTop hz).inv_tendsto_atTop.const_mul a)
  have hl := (isLittleO_log_rpow_atTop hz).tendsto_div_nhds_zero.const_mul b
  have ht : Tendsto (fun x : ℝ => (a+b*Real.log x)/x^z) atTop (𝓝 0) := by
    convert hc.add hl using 1 <;> simp only [mul_zero,add_zero,add_div,mul_div_assoc]
  filter_upwards [ht.eventually_lt_const (show (0:ℝ)<1 by norm_num),eventually_gt_atTop (0:ℝ)] with x hx hxp
  exact (div_lt_one (Real.rpow_pos_of_pos hxp _)).mp hx

lemma eventually_const_mul_rpow_le_rpow (c : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, c*x^a ≤ x^b := by
  have hh := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually (eventually_ge_atTop c)
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with x hx hxp
  calc
    c*x^a ≤ x^(b-a)*x^a := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hxp.le _)
    _ = x^b := by rw [←Real.rpow_add hxp]; congr 1; ring

lemma eventually_logb_mul_rpow_lt (c a b : ℝ) (hc : 0 < c) {z : ℝ} (hz : 0 < z) :
    ∀ᶠ x : ℝ in atTop, Real.logb 2 (c*x^a)+b < x^z := by
  filter_upwards [eventually_affine_log_lt_rpow (Real.log c/Real.log 2+b) (a/Real.log 2) hz,
    eventually_gt_atTop (0:ℝ)] with x hx hxp
  rw [Real.logb,Real.log_mul hc.ne' (Real.rpow_pos_of_pos hxp a).ne',Real.log_rpow hxp]
  convert hx using 1; ring

def alpha (x : ℝ) : ℝ := x^(-4/5:ℝ)
def gamma (x : ℝ) : ℝ := truncationGain (alpha x)
def scale (x : ℝ) : ℝ := alpha x*gamma x/32
def rho (x : ℝ) : ℝ := 1/(2*x^2)
def count (x : ℝ) : ℕ := ⌈x^(1/100:ℝ)⌉₊

lemma bins_log (x : ℝ) (hx : 0 < x) :
    Real.logb 2 (256/(alpha x)^2) = Real.logb 2 256+(8/5:ℝ)/Real.log 2*Real.log x := by
  have ha : 0 < alpha x := Real.rpow_pos_of_pos hx _
  rw [Real.logb,Real.log_div (by norm_num) (pow_ne_zero _ ha.ne'),Real.log_pow,
    alpha,Real.log_rpow hx,Real.logb]
  ring

lemma eventually_bins_le :
    ∀ᶠ x : ℝ in atTop, (truncationBins (alpha x) : ℝ) ≤ x^(1/1000:ℝ) := by
  filter_upwards [eventually_affine_log_lt_rpow (Real.logb 2 256+2) ((8/5:ℝ)/Real.log 2)
    (show 0 < (1/1000:ℝ) by norm_num),eventually_ge_atTop (1:ℝ)] with x hh hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.logb 2 (256/alpha x^2) := by
    rw [bins_log x hxp]
    have hlogx := Real.log_nonneg hx
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog256 : 0 ≤ Real.logb 2 256 := Real.logb_nonneg (by norm_num) (by norm_num)
    positivity
  have hc := Nat.ceil_lt_add_one hlog
  dsimp [truncationBins]
  push_cast
  rw [bins_log x hxp] at hc ⊢
  linarith

lemma gamma_pos {x : ℝ} : 0 < gamma x := truncationGain_pos _
lemma scale_pos {x : ℝ} (hx : 0 < x) : 0 < scale x := by
  have ha : 0 < alpha x := Real.rpow_pos_of_pos hx _
  have hg : 0 < gamma x := gamma_pos
  dsimp [scale]; positivity

lemma gamma_le_one (x : ℝ) : gamma x ≤ 1 := by
  have hJ : 1 ≤ (truncationBins (alpha x) : ℝ) := by
    dsimp [truncationBins]
    push_cast
    have hh : (0:ℝ) ≤ ⌈Real.logb 2 (256/alpha x^2)⌉₊ := Nat.cast_nonneg _
    linarith
  have hp : 1 ≤ (truncationBins (alpha x) : ℝ)^4 := one_le_pow₀ hJ
  change 1/(4*(truncationBins (alpha x) : ℝ)^4) ≤ 1
  apply (div_le_one (by positivity : (0:ℝ)<4*(truncationBins (alpha x):ℝ)^4)).mpr
  linarith

lemma eventually_gamma_lower :
    ∀ᶠ x : ℝ in atTop, x^(-1/100:ℝ) ≤ gamma x := by
  filter_upwards [eventually_bins_le,
    eventually_const_mul_rpow_le_rpow 4 (show (1/250:ℝ)<1/100 by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hJ hc hx
  have hp : 4*(truncationBins (alpha x):ℝ)^4 ≤ x^(1/100:ℝ) := by
    calc
      _ ≤ 4*(x^(1/1000:ℝ))^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hJ 4) (by norm_num)
      _ = 4*x^(1/250:ℝ) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]
        norm_num
      _ ≤ _ := hc
  have hJp : 0 < (truncationBins (alpha x):ℝ) := by
    dsimp [truncationBins]
    positivity
  rw [show (-1/100:ℝ)=-(1/100) by ring,Real.rpow_neg hx.le]
  change (x^(1/100:ℝ))⁻¹ ≤ 1/(4*(truncationBins (alpha x):ℝ)^4)
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hp

lemma scale_le_alpha {x : ℝ} (hx : 0 < x) : scale x ≤ alpha x := by
  have ha : 0 < alpha x := Real.rpow_pos_of_pos hx _
  have hh := mul_le_mul_of_nonneg_left (gamma_le_one x) ha.le
  dsimp [scale]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<32)).mpr
  nlinarith

lemma eventually_scale_lower :
    ∀ᶠ x : ℝ in atTop, x^(-41/50:ℝ) ≤ scale x := by
  filter_upwards [eventually_gamma_lower,
    eventually_const_mul_rpow_le_rpow 32 (show (-41/50:ℝ) < -81/100 by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hg hc hx
  have ha : 0 < alpha x := Real.rpow_pos_of_pos hx _
  have hh := mul_le_mul_of_nonneg_left hg ha.le
  have heq : alpha x*x^(-1/100:ℝ)=x^(-81/100:ℝ) := by
    rw [alpha,←Real.rpow_add hx]
    norm_num
  rw [heq] at hh
  dsimp [scale]
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<32)).mpr
  nlinarith

lemma count_pos {x : ℝ} (hx : 0 < x) : 0 < count x :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx _)

lemma count_upper {x : ℝ} (hx : 1 ≤ x) : (count x : ℝ) ≤ 2*x^(1/100:ℝ) := by
  have hh : 1 ≤ x^(1/100:ℝ) := Real.one_le_rpow hx (by norm_num)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (zero_le_one.trans hx) (1/100:ℝ))
  change (⌈x^(1/100:ℝ)⌉₊:ℝ) ≤ _
  linarith

lemma eventually_small :
    ∀ᶠ x : ℝ in atTop, (scale x)^(1/10:ℝ) ≤ 1/(1728*(1024/(1/10:ℝ)^2)) := by
  have ht : Tendsto (fun x : ℝ => x^(-2/25:ℝ)) atTop (𝓝 0) := by
    convert tendsto_rpow_neg_atTop (show (0:ℝ)<2/25 by norm_num) using 1; norm_num
  filter_upwards [ht.eventually_lt_const (show (0:ℝ)<1/(1728*(1024/(1/10:ℝ)^2)) by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hh hx
  have hl := Real.rpow_le_rpow (scale_pos hx).le (scale_le_alpha hx) (by norm_num : (0:ℝ)≤1/10)
  have heq : (alpha x)^(1/10:ℝ)=x^(-2/25:ℝ) := by
    rw [alpha,←Real.rpow_mul hx.le]
    norm_num
  rw [heq] at hl
  exact hl.trans hh.le

lemma eventually_assignment :
    ∀ᶠ x : ℝ in atTop, 6144/x ≤ (scale x)^(1+2*(1/10:ℝ)) := by
  filter_upwards [eventually_scale_lower,
    eventually_const_mul_rpow_le_rpow 6144 (show (-1:ℝ) < -123/125 by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hs hc hx
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hs
    (by norm_num : (0:ℝ)≤1+2*(1/10:ℝ))
  rw [←Real.rpow_mul hx.le] at hh
  norm_num at hh
  norm_num only at hc ⊢
  simpa only [Real.rpow_neg_one,div_eq_mul_inv] using hc.trans hh

lemma eventually_log_count_left :
    ∀ᶠ x : ℝ in atTop, Real.logb 2 (16/(alpha x*gamma x))+1 < (count x:ℝ) := by
  filter_upwards [eventually_gamma_lower,
    eventually_logb_mul_rpow_lt 16 (81/100) 1 (by norm_num) (show (0:ℝ)<1/100 by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hg hh hx
  have hb : x^(-81/100:ℝ) ≤ alpha x*gamma x := by
    have h := mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hx.le (-4/5:ℝ))
    rw [←Real.rpow_add hx] at h
    norm_num at h
    norm_num [alpha] at ⊢
    exact h
  have harg : 16/(alpha x*gamma x) ≤ 16*x^(81/100:ℝ) := by
    calc
      _ ≤ 16/x^(-81/100:ℝ) := div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hx _) hb
      _ = _ := by rw [show (-81/100:ℝ)=-(81/100) by ring,Real.rpow_neg hx.le,div_inv_eq_mul]
  have hp : 0 < 16/(alpha x*gamma x) := by
    have ha : 0 < alpha x := Real.rpow_pos_of_pos hx _
    have hg : 0 < gamma x := gamma_pos
    positivity
  have hl := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hp (hp.trans_le harg)).mpr harg
  have hcount := Nat.le_ceil (x^(1/100:ℝ))
  dsimp [count]
  linarith

lemma eventually_log_count_right :
    ∀ᶠ x : ℝ in atTop, Real.logb 2 (24/(rho x*(scale x)^2)) < (count x:ℝ) := by
  filter_upwards [eventually_scale_lower,
    eventually_logb_mul_rpow_lt 48 (91/25) 0 (by norm_num) (show (0:ℝ)<1/100 by norm_num),
    eventually_gt_atTop (0:ℝ)] with x hs hh hx
  have hs2 : x^(-41/25:ℝ) ≤ (scale x)^2 := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hx.le _) hs 2
    rw [←Real.rpow_natCast,←Real.rpow_mul hx.le] at h
    norm_num at h
    norm_num at ⊢
    exact h
  have hr : 0 < rho x := by dsimp [rho]; positivity
  have hp : 0 < rho x*(scale x)^2 := mul_pos hr (sq_pos_of_pos (scale_pos hx))
  have harg : 24/(rho x*(scale x)^2) ≤ 48*x^(91/25:ℝ) := by
    apply (div_le_iff₀ hp).mpr
    calc
      24 = (48*x^(91/25:ℝ)*rho x)*x^(-41/25:ℝ) := by
        rw [rho]
        have heq : x^(91/25:ℝ)*x^(-41/25:ℝ)=x^2 := by
          rw [←Real.rpow_add hx]
          norm_num
        field_simp
        nlinarith only [heq]
      _ ≤ (48*x^(91/25:ℝ)*rho x)*(scale x)^2 :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = _ := by ring
  have hl := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (div_pos (by norm_num) hp)
    ((div_pos (by norm_num) hp).trans_le harg)).mpr harg
  exact hl.trans_lt (by simpa only [add_zero,count] using hh.trans_le (Nat.le_ceil _))

def coefficient (x : ℝ) : ℝ :=
  2*alpha x+2*(count x:ℝ)*(count x:ℝ)/
    ((x/8192)*((scale x)^(1/10:ℝ)/(6912*(1024/(1/10:ℝ)^2)))*gamma x)

def largeConstant : ℝ := 8*8192*6912*102400

lemma coefficient_eq {x : ℝ} (hx : 0 < x) :
    coefficient x = 2*alpha x+(2*8192*6912*102400)*((count x:ℝ)^2)/(x*(scale x)^(1/10:ℝ)*gamma x) := by
  unfold coefficient
  norm_num
  field_simp
  ring

lemma eventually_denominator_lower :
    ∀ᶠ x : ℝ in atTop, x^(227/250:ℝ) ≤ x*(scale x)^(1/10:ℝ)*gamma x := by
  filter_upwards [eventually_scale_lower,eventually_gamma_lower,eventually_gt_atTop (0:ℝ)] with x hs hg hx
  have hsp := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hs (by norm_num : (0:ℝ)≤1/10)
  rw [←Real.rpow_mul hx.le] at hsp
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hsp hx.le) hg (Real.rpow_nonneg hx.le _)
    (mul_nonneg hx.le (Real.rpow_nonneg (scale_pos hx).le _))
  have heq : x*x^((-41/50:ℝ)*(1/10))*x^(-1/100:ℝ)=x^(227/250:ℝ) := by
    calc
      _ = x^((1:ℝ)+(-41/50:ℝ)*(1/10))*x^(-1/100:ℝ) := by
        rw [Real.rpow_add hx,Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hx]; norm_num
  rwa [heq] at hh

lemma eventually_coefficient_bound :
    ∀ᶠ x : ℝ in atTop, coefficient x ≤ 2*x^(-4/5:ℝ)+largeConstant*x^(-111/125:ℝ) := by
  filter_upwards [eventually_denominator_lower,eventually_ge_atTop (1:ℝ)] with x hd hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hc : (count x:ℝ)^2 ≤ 4*x^(1/50:ℝ) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) (count_upper hx) 2
    rw [mul_pow,←Real.rpow_natCast (x^(1/100:ℝ)) 2,←Real.rpow_mul hxp.le] at hh
    norm_num at hh
    exact hh
  rw [coefficient_eq hxp]
  apply add_le_add (le_refl (2*alpha x))
  calc
    _ ≤ (2*8192*6912*102400)*(4*x^(1/50:ℝ))/x^(227/250:ℝ) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hc (by norm_num))
        (Real.rpow_pos_of_pos hxp _) hd
    _ = largeConstant*x^(-111/125:ℝ) := by
      calc
        _ = largeConstant*(x^(1/50:ℝ)/x^(227/250:ℝ)) := by unfold largeConstant; ring
        _ = _ := by rw [←Real.rpow_sub hxp]; norm_num

lemma eventually_coefficient_small :
    ∀ᶠ x : ℝ in atTop, coefficient x ≤ x^(-31/40:ℝ)/2 := by
  filter_upwards [eventually_coefficient_bound,
    eventually_const_mul_rpow_le_rpow 8 (show (-4/5:ℝ) < -31/40 by norm_num),
    eventually_const_mul_rpow_le_rpow (4*largeConstant) (show (-111/125:ℝ) < -31/40 by norm_num)]
    with x hb h1 h2
  nlinarith

lemma eventually_rho_small :
    ∀ᶠ x : ℝ in atTop, rho x ≤ 1/1536 := by
  filter_upwards [eventually_ge_atTop (100:ℝ)] with x hx
  have hp : 0 < 2*x^2 := by positivity
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (x-100)]

structure GoodParameters (x : ℝ) : Prop where
  large : 2 ≤ x
  small : (scale x)^(1/10:ℝ) ≤ 1/(1728*(1024/(1/10:ℝ)^2))
  assignment : 6144/x ≤ (scale x)^(1+2*(1/10:ℝ))
  rho_small : rho x ≤ 1/1536
  log_left : Real.logb 2 (16/(alpha x*gamma x))+1 < (count x:ℝ)
  log_right : Real.logb 2 (24/(rho x*(scale x)^2)) < (count x:ℝ)
  coefficient_small : coefficient x ≤ x^(-31/40:ℝ)/2

lemma eventually_good : ∀ᶠ x : ℝ in atTop, GoodParameters x := by
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_small,eventually_assignment,
    eventually_rho_small,eventually_log_count_left,eventually_log_count_right,
    eventually_coefficient_small] with x h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1,h2,h3,h4,h5,h6,h7⟩

lemma exists_cutoff : ∃qH : ℕ, 2 ≤ qH ∧ ∀q : ℕ, qH ≤ q → GoodParameters q := by
  have hh : ∀ᶠ q : ℕ in atTop, GoodParameters q :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop).eventually eventually_good
  obtain ⟨qH,hqH⟩ := hh.exists_forall_of_atTop
  exact ⟨max 2 qH,le_max_left _ _,fun q hq => hqH q ((le_max_right _ _).trans hq)⟩

end StrongThinTree.ShortcutNumeric

namespace StrongThinTree.MultiGraph.Hierarchy
open Matrix Finset ShortcutNumeric
open scoped Classical MatrixOrder
variable {n m : ℕ} {G : MultiGraph n m} {H : Hierarchy n}

lemma edgeConnected_of_locally {q : ℕ} (hconn : H.LocallyConnectedReal G q) : G.EdgeConnected q := by
  intro S hS hS'
  have hh := hconn univ H.root_mem S hS (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hS'⟩)
  have heq : G.inducedEdges univ=univ := by ext e; simp [MultiGraph.inducedEdges]
  rw [heq] at hh
  exact_mod_cast hh

theorem polynomial_shortcut :
    ∃qH : ℕ, 2 ≤ qH ∧ ∀q : ℕ, qH ≤ q →
      ∀(n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n),
      H.LocallyConnectedReal G q →
      ∀M : Finset (Finset (Fin n)), M ⊆ H.nodes →
      (∀t ∈ M, t ≠ univ) →
      (∀t ∈ M, ((G.cut univ t).card : ℝ)/q ≤ (H.parentBoundary G t).card) →
      ∃D : Matrix (Fin n) (Fin n) ℝ, D.PosDef ∧
        (∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
          cutIndicator S ⬝ᵥ (D *ᵥ cutIndicator S) ≤ ((G.cut univ S).card : ℝ)) ∧
        (∀t ∈ M, ShortcutDual.boundaryAverage G.incidence (H.parentBoundary G) t D ≤
          (q:ℝ)^(-31/40:ℝ)) := by
  obtain ⟨qH,hqH,hgood⟩ := exists_cutoff
  refine ⟨qH,hqH,?_⟩
  intro q hq n m G H hconn M hM hroot hratio
  have hg := hgood q hq
  have hqpos : 0 < q := lt_of_lt_of_le (by omega : 0 < qH) hq
  have hqp : (0:ℝ) < q := Nat.cast_pos.mpr hqpos
  have hq1 : (1:ℝ) ≤ q := le_trans (by norm_num) hg.large
  have hα : 0 < alpha q := Real.rpow_pos_of_pos hqp _
  have hα1 : alpha q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by norm_num)
  have hρ : 0 < rho q := by dsimp [rho]; positivity
  have hr : ∀t ∈ M, (q:ℝ)*rho q*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card := by
    intro t ht
    have heq : (q:ℝ)*rho q*((G.cut univ t).card : ℝ)=((G.cut univ t).card : ℝ)/q/2 := by
      unfold rho
      field_simp
    rw [heq]
    have hp : (0:ℝ) ≤ ((G.cut univ t).card : ℝ)/q := div_nonneg (Nat.cast_nonneg _) hqp.le
    exact (by linarith : ((G.cut univ t).card : ℝ)/q/2 ≤ ((G.cut univ t).card : ℝ)/q).trans (hratio t ht)
  have hη : 0 < (q:ℝ)^(-31/40:ℝ)/2 := by positivity
  obtain ⟨D,hD,hb,hc⟩ := exists_shortcut_explicit hqpos (count_pos hqp) (count_pos hqp)
    (edgeConnected_of_locally hconn) hconn M hM hroot hα hα1
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (1/10:ℝ)<1/3)
    hρ hg.rho_small hg.small hg.assignment hr hg.log_left hg.log_right hη
  refine ⟨D,hD,fun S hS hS' => (hc S hS hS').le,?_⟩
  intro t ht
  have hh := hb t ht
  have hcoef : shortcutCoefficient q (count q) (count q) (alpha q) (1/10)=coefficient q := rfl
  rw [hcoef] at hh
  linarith [hg.coefficient_small]

end StrongThinTree.MultiGraph.Hierarchy

end
end

end OAI
