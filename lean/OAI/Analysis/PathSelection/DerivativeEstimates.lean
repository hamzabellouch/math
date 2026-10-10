import Mathlib
import OAI.Analysis.PathSelection.ExponentialCharts

namespace OAI

/-! Strip derivative variation and equal-exponent error estimates. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
namespace DegeneratingTrees.Clock

theorem affine_strip_estimate {F : ℂ → ℂ}
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hz : ∀ᶠ z in stripInfinity,deriv F z≠0)
    (hd : Tendsto (fun z => deriv (deriv F) z/deriv F z) stripInfinity (𝓝 0))
    {R : ℝ} (hR : 0<R) {B : ℝ} (hB : 0<B) {ε : ℝ} (hε : 0<ε) :
    ∃ A : ℝ,∀ z∈horizontalTail A R,∀ w∈horizontalTail A R,‖z-w‖≤B →
      ‖F z-F w-deriv F w*(z-w)‖≤ε*‖deriv F w‖*‖z-w‖ := by
  obtain ⟨A₁,hA₁⟩ := relative_strip_pair_estimate (ha.mono (fun z hz => hz.deriv)) hz hd hR hB
    (show 0<ε/B by positivity)
  obtain ⟨A₂,hA₂⟩ := eventually_stripInfinity.mp ha R
  let A := max A₁ A₂
  have hsub₁ : horizontalTail A R ⊆ horizontalTail A₁ R :=
    fun z hz => ⟨(le_max_left _ _).trans_lt hz.1,hz.2⟩
  have hsub₂ : horizontalTail A R ⊆ horizontalTail A₂ R :=
    fun z hz => ⟨(le_max_right _ _).trans_lt hz.1,hz.2⟩
  refine ⟨A,?_⟩
  intro z hz w hw hdist
  let S := horizontalTail A R ∩ closedBall w B
  have hSw : w∈S := ⟨hw,mem_closedBall_self hB.le⟩
  have hSz : z∈S := ⟨hz,mem_closedBall_iff_norm.mpr hdist⟩
  have hDS (u : ℂ) (hu : u∈S) :
      ‖deriv F u-deriv F w‖≤ε*‖deriv F w‖ := by
    have hub : ‖u-w‖≤B := mem_closedBall_iff_norm.mp hu.2
    obtain ⟨hwn,hhh⟩ := hA₁ u (hsub₁ hu.1) w (hsub₁ hw) hub
    have hrel : ‖deriv F u/deriv F w-1‖≤ε := by
      have hm := mul_le_mul_of_nonneg_left hub (by positivity : 0≤ε/B)
      have he : ε/B*B=ε := div_mul_cancel₀ _ hB.ne'
      exact hhh.trans (hm.trans_eq he)
    have he : deriv F u-deriv F w=(deriv F u/deriv F w-1)*deriv F w := by
      field_simp [hwn]
    rw [he,norm_mul]
    exact mul_le_mul_of_nonneg_right hrel (norm_nonneg _)
  let G : ℂ → ℂ := fun u => F u-deriv F w*u
  have hGd (u : ℂ) (hu : u∈S) : HasDerivAt G (deriv F u-deriv F w) u := by
    simpa only [G,Pi.sub_def,id_eq,mul_one] using (hA₂ u (hsub₂ hu.1)).differentiableAt.hasDerivAt.sub
      (hasDerivAt_const_mul (deriv F w))
  have hcv : Convex ℝ S := (horizontalTail_convex A R).inter (convex_closedBall w B)
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hGd u hu).differentiableAt)
    (fun u hu => by rw [(hGd u hu).deriv]; exact hDS u hu) hcv hSw hSz
  convert hh using 1
  dsimp [G]
  congr 1
  ring

theorem strip_derivative_variation {F : ℂ → ℂ}
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hz : ∀ᶠ z in stripInfinity,deriv F z≠0)
    (hd : Tendsto (fun z => deriv (deriv F) z/deriv F z) stripInfinity (𝓝 0))
    {R : ℝ} (hR : 0<R) {B : ℝ} (hB : 0<B) :
    ∃ A : ℝ,∀ z∈horizontalTail A R,∀ w∈horizontalTail A R,‖z-w‖≤B →
      ‖F z-F w‖≤2*‖deriv F w‖*‖z-w‖ := by
  obtain ⟨A,hA⟩ := affine_strip_estimate ha hz hd hR hB (show (0:ℝ)<1 by norm_num)
  refine ⟨A,?_⟩
  intro z hz w hw hdist
  have hh := hA z hz w hw hdist
  calc
    ‖F z-F w‖ = ‖(F z-F w-deriv F w*(z-w))+deriv F w*(z-w)‖ := by congr 1; ring
    _ ≤ ‖F z-F w-deriv F w*(z-w)‖+‖deriv F w*(z-w)‖ := norm_add_le _ _
    _ ≤ 2*‖deriv F w‖*‖z-w‖ := by rw [norm_mul]; linarith

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

 theorem equal_exponent_ratio_error {F H J E x : ℂ → ℂ} {b ε C c T : ℝ}
    (hb : 0<b) (hε : 0<ε) (hC : 0≤C)
    (hxr : ∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0)
    (hxt : Tendsto (fun r : ℝ => (x (r:ℂ)).re) atTop atTop)
    (hxi : ∃ U : ℝ,∀ w : ℂ,0<w.re → U<‖w‖ →
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤|w.arg|)
    (hinv : ∀ w : ℂ,0<w.re → T<‖w‖ → H (x w)=w)
    (hJa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ J z)
    (hJ0 : ∀ᶠ z in stripInfinity,J z≠0)
    (hJd : Tendsto (fun z => deriv J z/J z) stripInfinity (𝓝 0))
    (hJr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0)
    (hJl : Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 c))
    (hJd0 : ∀ᶠ z in stripInfinity,deriv J z≠0)
    (hJdd : Tendsto (fun z => deriv (deriv J) z/deriv J z) stripInfinity (𝓝 0))
    (he : ∀ᶠ z in stripInfinity,‖E z‖≤C*Real.exp (-ε*z.re))
    (hfactor : ∀ᶠ z in stripInfinity,F z/H z=J z*(1+E z)) :
    ∃ K U : ℝ,0<K ∧ ∀ w : ℂ,0<w.re → U<‖w‖ →
      ‖F (x w)/w-((J ((x (‖w‖:ℂ)).re:ℂ)).re:ℂ)‖ ≤
        K*(‖deriv J ((x (‖w‖:ℂ)).re:ℂ)‖+Real.exp (-ε*(x (‖w‖:ℂ)).re)) := by
  obtain ⟨R,B,hR,hB,hmap⟩ := inverse_halfplane_strip hb hxr hxt hxi
  obtain ⟨A₁,hA₁⟩ := strip_derivative_variation hJa hJd0 hJdd hR hB
  obtain ⟨A₂,hA₂⟩ := relative_strip_pair_estimate hJa hJ0 hJd hR hB
    (show 0<1/B by positivity)
  obtain ⟨A₃,hA₃⟩ := eventually_stripInfinity.mp (he.and hfactor) R
  let M := |c|+1
  have hM : 0<M := by dsimp [M]; positivity
  have hrb : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0 ∧ ‖J (t:ℂ)‖≤M := by
    filter_upwards [hJr,(Metric.tendsto_nhds.mp hJl) 1 zero_lt_one] with t hr ht
    refine ⟨hr,?_⟩
    have hreal : J (t:ℂ)=((J (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hr)
    rw [hreal,Complex.norm_real,Real.norm_eq_abs]
    have hh : |(J (t:ℂ)).re-c|<1 := by simpa only [Real.dist_eq] using ht
    calc
      |(J (t:ℂ)).re| = |((J (t:ℂ)).re-c)+c| := by rw [sub_add_cancel]
      _ ≤ |(J (t:ℂ)).re-c|+|c| := abs_add_le _ _
      _ ≤ M := by dsimp [M]; linarith
  obtain ⟨A₄,hA₄⟩ := eventually_atTop.mp hrb
  let A := max A₁ (max A₂ (max A₃ A₄))
  have hAA₁ : A₁≤A := le_max_left _ _
  have hAA₂ : A₂≤A := (le_max_left _ _).trans (le_max_right _ _)
  have hAA₃ : A₃≤A := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAA₄ : A₄≤A := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨U,hU,hUf⟩ := hmap A
  let K := 1+2*B+2*M*C*Real.exp (ε*B)
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,max T U,hK,?_⟩
  intro w hw hwU
  let t := (x (‖w‖:ℂ)).re
  obtain ⟨ht,hx,hdist⟩ := hUf w hw ((le_max_right _ _).trans_lt hwU)
  have htstr : (t:ℂ)∈horizontalTail A R := ⟨ht,by simpa using hR⟩
  have hsub {A' : ℝ} (h : A'≤A) {z : ℂ} (hz : z∈horizontalTail A R) :
      z∈horizontalTail A' R := ⟨h.trans_lt hz.1,hz.2⟩
  obtain ⟨hJtn,hratio⟩ := hA₂ (x w) (hsub hAA₂ hx) (t:ℂ) (hsub hAA₂ htstr) hdist
  have hr₁ : ‖J (x w)/J (t:ℂ)-1‖≤1 := by
    calc
      _ ≤ 1/B*‖x w-(t:ℂ)‖ := hratio
      _ ≤ 1/B*B := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = 1 := by field_simp
  have hnormratio : ‖J (x w)/J (t:ℂ)‖≤2 := by
    have hh := norm_le_norm_sub_add (J (x w)/J (t:ℂ)) 1
    rw [norm_one] at hh
    linarith
  have htr := hA₄ t (hAA₄.trans ht.le)
  have hJx : ‖J (x w)‖≤2*M := by
    have heq : J (x w)=(J (x w)/J (t:ℂ))*J (t:ℂ) := by field_simp
    rw [heq,norm_mul]
    exact (mul_le_mul_of_nonneg_right hnormratio (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left htr.2 (by norm_num))
  have hvar := hA₁ (x w) (hsub hAA₁ hx) (t:ℂ) (hsub hAA₁ htstr) hdist
  have hv : ‖J (x w)-J (t:ℂ)‖≤2*B*‖deriv J (t:ℂ)‖ := by
    have hh := mul_le_mul_of_nonneg_left hdist (by positivity : 0≤2*‖deriv J (t:ℂ)‖)
    nlinarith
  obtain ⟨he',hf'⟩ := hA₃ (x w) (hsub hAA₃ hx)
  have hdre := (Complex.abs_re_le_norm (x w-(t:ℂ))).trans hdist
  simp only [Complex.sub_re,Complex.ofReal_re] at hdre
  have hexp : Real.exp (-ε*(x w).re)≤Real.exp (ε*B)*Real.exp (-ε*t) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := (abs_le.mp hdre).1
    nlinarith
  have he'' : ‖E (x w)‖≤C*Real.exp (ε*B)*Real.exp (-ε*t) := by
    exact he'.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hexp hC)
  have hJreal : J (t:ℂ)=((J (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using htr.1)
  rw [hinv w hw ((le_max_left _ _).trans_lt hwU)] at hf'
  change ‖F (x w)/w-((J (t:ℂ)).re:ℂ)‖ ≤ K*(‖deriv J (t:ℂ)‖+Real.exp (-ε*t))
  rw [hf',←hJreal]
  have heq : J (x w)*(1+E (x w))-J (t:ℂ)=
      (J (x w)-J (t:ℂ))+J (x w)*E (x w) := by ring
  rw [heq]
  calc
    _ ≤ ‖J (x w)-J (t:ℂ)‖+‖J (x w)*E (x w)‖ := norm_add_le _ _
    _ ≤ 2*B*‖deriv J (t:ℂ)‖+(2*M)*(C*Real.exp (ε*B)*Real.exp (-ε*t)) := by
      rw [norm_mul]
      exact add_le_add hv (mul_le_mul hJx he'' (norm_nonneg _) (by positivity))
    _ ≤ K*(‖deriv J (t:ℂ)‖+Real.exp (-ε*t)) := by
      have hCM : 0≤2*M*C*Real.exp (ε*B) := by positivity
      have hK₁ : 2*B≤K := by dsimp [K]; linarith
      have hK₂ : 2*M*C*Real.exp (ε*B)≤K := by dsimp [K]; linarith
      have hh := add_le_add
        (mul_le_mul_of_nonneg_right hK₁ (norm_nonneg (deriv J (t:ℂ))))
        (mul_le_mul_of_nonneg_right hK₂ (Real.exp_pos (-ε*t)).le)
      nlinarith only [hh]

end DegeneratingTrees.Clock
end

end OAI
