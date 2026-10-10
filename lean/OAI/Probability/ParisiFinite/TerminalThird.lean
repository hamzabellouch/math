import Mathlib
import OAI.Probability.ParisiFinite.OrderPointIntegrable

namespace OAI

/-! Terminal Third. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ThirdJet

def terminalThird (β : ℝ≥0) (hβ : 0<β) : ThirdJet (terminalField β hβ) where
  d3 := fun x => -2*(β:ℝ)*(terminalField β hβ).d1 x*(terminalField β hβ).d2 x
  hasD3 := by
    intro x
    have hf : (terminalField β hβ).d2 = fun y => (β:ℝ)*(1-(terminalField β hβ).d1 y^2) :=
      funext (terminal_curvature_identity β hβ)
    rw [hf]
    convert (((terminalField β hβ).hasD2 x).pow 2 |>.const_sub 1 |>.const_mul (β:ℝ)) using 1
    first | rfl | (norm_num;rw [terminal_curvature_identity];ring)
  continuousD3 := by
    have h1 := (terminalField β hβ).continuousD1
    have h2 := (terminalField β hβ).continuousD2
    fun_prop
  bound3 := 2*β^2
  normD3 := by
    intro x
    have h1 := (terminalField β hβ).normD1 x
    have h2 := (terminalField β hβ).normD2 x
    change |(terminalField β hβ).d1 x|≤(1:ℝ) at h1
    change |(terminalField β hβ).d2 x|≤(β:ℝ) at h2
    norm_num only [abs_mul,abs_neg,abs_of_nonneg β.coe_nonneg,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow]
    nlinarith [mul_le_mul h1 h2 (abs_nonneg _) (show (0:ℝ)≤1 by norm_num),β.coe_nonneg]

lemma terminal_expThird (β : ℝ≥0) (hβ : 0<β) (x : ℝ) :
    (terminalThird β hβ).expThird β x=(β:ℝ)^2*(terminalField β hβ).d1 x := by
  dsimp only [ThirdJet.expThird,terminalThird]
  rw [terminal_curvature_identity]
  ring

lemma expThird_change_bound {β : ℝ≥0} {f : SmoothField} (hf : HasParisiCurvature β f)
    (j : ThirdJet f) {a r C : ℝ} (ha : 0≤a) (har : a≤r)
    (hC : ∀ x,|j.expThird r x|≤C) (x : ℝ) :
    |j.expThird a x|≤C+3*(r-a)*(β:ℝ)+(r^2-a^2) := by
  have h1 : |f.d1 x|≤(1:ℝ) := by simpa only [hf.1,NNReal.coe_one] using f.normD1 x
  have h2 := curvature_abs_d2 hf x
  have h12 : |f.d1 x*f.d2 x|≤(β:ℝ) := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul h1 h2 (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h3 : |f.d1 x^3|≤(1:ℝ) := by
    simpa only [abs_pow,one_pow] using pow_le_pow_left₀ (abs_nonneg _) h1 3
  have har2 : 0≤r^2-a^2 := by nlinarith
  have he : j.expThird a x=j.expThird r x-3*(r-a)*(f.d1 x*f.d2 x)-(r^2-a^2)*f.d1 x^3 := by
    unfold ThirdJet.expThird; ring
  rw [he]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_sub _ _) (le_refl _)).trans
  norm_num only [abs_mul,abs_of_nonneg (sub_nonneg.mpr har),abs_of_nonneg har2]
  calc
    _ ≤ C+3*(r-a)*(β:ℝ)+(r^2-a^2)*1 := by
      gcongr
      · exact hC x
      · simpa only [abs_mul] using h12
    _ = _ := by ring

lemma ordered_coefficient_bounds {β a : ℝ} {ls : Schedule}
    (h : ParisiGuerra.OrderedFrom β a ls) : a≤β ∧ ∀ l∈ls,(l.1:ℝ)≤β := by
  induction ls generalizing a with
  | nil => exact ⟨h,by simp⟩
  | cons l ls ih =>
    obtain ⟨hb,hls⟩ := ih h.2
    refine ⟨h.1.trans hb,?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl|hk
    · exact hb
    · exact hls k hk

def recursionThird (β : ℝ≥0) (hβ : 0<β) : (ls : Schedule) → ThirdJet (smoothRecursion β hβ ls)
  | [] => terminalThird β hβ
  | l::ls => (recursionThird β hβ ls).transform l.1 (Real.sqrt l.2)

lemma recursion_expThird_bound (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) {a : ℝ}
    (ha : 0≤a) (h : ParisiGuerra.OrderedFrom β a ls) (x : ℝ) :
    |(recursionThird β hβ ls).expThird a x|≤(β:ℝ)^2+3*((β:ℝ)-a)*β+((β:ℝ)^2-a^2) := by
  induction ls generalizing a x with
  | nil =>
    have hb : ∀ y,|(terminalThird β hβ).expThird β y|≤(β:ℝ)^2 := by
      intro y
      rw [terminal_expThird,abs_mul,abs_sq]
      exact mul_le_mul_of_nonneg_left (terminalField β hβ |>.normD1 y) (sq_nonneg _) |>.trans_eq (mul_one _)
    exact expThird_change_bound (terminal_hasParisiCurvature β hβ) (terminalThird β hβ) ha h hb x
  | cons l ls ih =>
    have hlb := ordered_coefficient_bounds h.2
    have hf := smoothRecursion_hasParisiCurvature β hβ (l::ls)
      (fun k hk => by exact_mod_cast (ordered_coefficient_bounds h).2 k hk)
    have ht : ∀ y,|(recursionThird β hβ (l::ls)).expThird l.1 y|≤
        (β:ℝ)^2+3*((β:ℝ)-l.1)*β+((β:ℝ)^2-(l.1:ℝ)^2) := by
      intro y
      change |((recursionThird β hβ ls).transform l.1 (Real.sqrt l.2)).expThird l.1 y|≤_
      rw [ThirdJet.expThird_transform]
      exact abs_tiltedMean_le (smoothRecursion β hβ ls).lipschitz
        ((recursionThird β hβ ls).continuous_expThird l.1) (fun z => ih l.1.coe_nonneg h.2 z) _ _ _
    have hh := expThird_change_bound hf (recursionThird β hβ (l::ls)) ha h.1 ht x
    convert hh using 1
    ring

lemma recursion_d3_bound (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (h : ParisiGuerra.OrderedFrom β 0 ls) (x : ℝ) :
    |(recursionThird β hβ ls).d3 x|≤5*(β:ℝ)^2 := by
  have hh := recursion_expThird_bound β hβ ls (by norm_num : (0:ℝ)≤0) h x
  simpa only [ThirdJet.expThird,mul_zero,zero_mul,zero_pow (by norm_num : 2≠0),
    add_zero,sub_zero,show (β:ℝ)^2+3*(β:ℝ)*β+(β:ℝ)^2=5*(β:ℝ)^2 by ring] using hh

lemma ordered_lower {β a r : ℝ} {ls : Schedule}
    (har : a≤r) (h : ParisiGuerra.OrderedFrom β r ls) : ParisiGuerra.OrderedFrom β a ls := by
  cases ls with
  | nil => exact har.trans h
  | cons l ls => exact ⟨har.trans h.1,h.2⟩

lemma ordered_upper {β b a : ℝ} {ls : Schedule}
    (hb : β≤b) (h : ParisiGuerra.OrderedFrom β a ls) : ParisiGuerra.OrderedFrom b a ls := by
  induction ls generalizing a with
  | nil => exact h.trans hb
  | cons l ls ih => exact ⟨h.1,ih h.2⟩

lemma ordered_append {β r a : ℝ} {ls ks : Schedule}
    (h1 : ParisiGuerra.OrderedFrom r a ls) (h2 : ParisiGuerra.OrderedFrom β r ks) :
    ParisiGuerra.OrderedFrom β a (ls++ks) := by
  induction ls generalizing a with
  | nil => exact ordered_lower h1 h2
  | cons l ls ih => exact ⟨h1.1,ih h1.2⟩

lemma dyadicSchedule_ordered {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ)
    (u : Bool) (t d : ℝ≥0) (n : ℕ) :
    ParisiGuerra.OrderedFrom (γ (t+d)) (γ t) (dyadicSchedule γ u t d n) := by
  induction n generalizing t d with
  | zero =>
    change (γ t:ℝ)≤γ (if u then t+d else t) ∧ (γ (if u then t+d else t):ℝ)≤γ (t+d)
    have hh : γ t≤γ (t+d) := hγ (le_add_of_nonneg_right d.coe_nonneg)
    cases u <;> simpa using hh
  | succ n ih =>
    have hn : t+d/2+d/2=t+d := by exact_mod_cast (by ring : (t:ℝ)+(d:ℝ)/2+(d:ℝ)/2=(t:ℝ)+d)
    have hh := ordered_append (ih t (d/2)) (ih (t+d/2) (d/2))
    simpa only [dyadicSchedule,hn] using hh

lemma dyadic_recursion_d3_bound (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (u : Bool) (t d : ℝ≥0) (n : ℕ) (x : ℝ) :
    |(recursionThird β hβ (dyadicSchedule γ u t d n)).d3 x|≤5*(β:ℝ)^2 :=
  recursion_d3_bound β hβ _ (ordered_lower (γ t).coe_nonneg
    (ordered_upper (show (γ (t+d):ℝ)≤β by exact_mod_cast hb _) (dyadicSchedule_ordered hγ u t d n))) x

lemma recursion_curvature_lipschitz (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (h : ParisiGuerra.OrderedFrom β 0 ls) :
    LipschitzWith (5*β^2) (smoothRecursion β hβ ls).d2 := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => ((recursionThird β hβ ls).hasD3 x).differentiableAt)
  intro x
  rw [((recursionThird β hβ ls).hasD3 x).deriv]
  exact_mod_cast recursion_d3_bound β hβ ls h x

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

lemma taylor_error_of_derivative_lipschitz {f g : ℝ → ℝ} {K : ℝ≥0}
    (hd : ∀ x,HasDerivAt f (g x) x) (hg : LipschitzWith K g)
    (x : ℝ) {h : ℝ} (hh : 0≤h) :
    |f (x+h)-f x-h*g x|≤(K:ℝ)*h^2 := by
  let r (y : ℝ) := f y-f x-(y-x)*g x
  have hder (y : ℝ) : HasDerivAt r (g y-g x) y := by
    convert (hd y |>.sub_const (f x)).sub
      (((hasDerivAt_id y).sub_const x).mul_const (g x)) using 1 <;>
      first | rfl | simp only [one_mul]
  have hb (y : ℝ) (hy : y∈Set.Ico x (x+h)) : ‖g y-g x‖≤(K:ℝ)*h := by
    have hl := hg.dist_le_mul y x
    rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hy.1)] at hl
    simpa only [Real.norm_eq_abs] using hl.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) K.coe_nonneg)
  have ht := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y (_ : y∈Set.Icc x (x+h)) => (hder y).hasDerivWithinAt) hb (x+h) ⟨by linarith,le_rfl⟩
  simpa only [r,sub_self,zero_mul,sub_zero,add_sub_cancel_left,Real.norm_eq_abs,pow_two,mul_assoc] using ht

lemma derivative_stability_lipschitz {f g f' g' : ℝ → ℝ} {K : ℝ≥0}
    (hf : ∀ x,HasDerivAt f (f' x) x) (hg : ∀ x,HasDerivAt g (g' x) x)
    (hf' : LipschitzWith K f') (hg' : LipschitzWith K g')
    {ε h : ℝ} (hh : 0≤h) (he : ∀ y,|f y-g y|≤ε) (x : ℝ) :
    h*|f' x-g' x|≤2*ε+2*(K:ℝ)*h^2 := by
  have hferr := abs_le.mp (taylor_error_of_derivative_lipschitz hf hf' x hh)
  have hgerr := abs_le.mp (taylor_error_of_derivative_lipschitz hg hg' x hh)
  have hx := abs_le.mp (he x)
  have hx' := abs_le.mp (he (x+h))
  have ha : h*|f' x-g' x|=|h*(f' x-g' x)| := by rw [abs_mul,abs_of_nonneg hh]
  rw [ha,abs_le]
  constructor <;> nlinarith

lemma exists_uniform_derivative_lipschitz_limit {K : ℝ≥0} {F G : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n x,HasDerivAt (F n) (G n x) x) (hG : ∀ n,LipschitzWith K (G n))
    (ht : TendstoUniformly F f atTop) :
    ∃ g : ℝ → ℝ,TendstoUniformly G g atTop ∧ (∀ x,HasDerivAt f (g x) x) ∧ LipschitzWith K g := by
  have hc : UniformCauchySeqOn G atTop Set.univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    let h := ε/(8*((K:ℝ)+1))
    have hh : 0<h := by dsimp [h];positivity
    have hsmall : 2*(K:ℝ)*h≤ε/4 := by
      dsimp [h]
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
      field_simp
      nlinarith [K.coe_nonneg]
    obtain ⟨N,hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp ht (ε*h/8) (by positivity))
    refine ⟨N,fun m hm n hn x _ => ?_⟩
    have hd : ∀ y,|F m y-F n y|≤2*(ε*h/8) := by
      intro y
      have h1 := hN m hm y
      have h2 := hN n hn y
      rw [Real.dist_eq] at h1 h2
      calc
        _ ≤ |F m y-f y|+|f y-F n y| := abs_sub_le _ _ _
        _ ≤ 2*(ε*h/8) := by rw [abs_sub_comm] at h1;linarith
    have hb := derivative_stability_lipschitz (hF m) (hF n) (hG m) (hG n) hh.le hd x
    rw [Real.dist_eq]
    have hm := mul_le_mul_of_nonneg_right hsmall hh.le
    nlinarith
  choose g hg using fun x : ℝ => cauchySeq_tendsto_of_complete (hc.cauchySeq (Set.mem_univ x))
  have hu : TendstoUniformly G g atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hc.tendstoUniformlyOn_of_tendsto (fun x _ => hg x)
  refine ⟨g,hu,fun x => hasDerivAt_of_tendstoUniformly hu (Eventually.of_forall hF) (fun y => ht.tendsto_at y) x,?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto ((hg x).dist (hg y))
  exact Eventually.of_forall fun n => (hG n).dist_le_mul x y

end ParisiFinite

end

end OAI
