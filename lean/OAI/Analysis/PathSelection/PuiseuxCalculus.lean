import Mathlib

namespace OAI

/-! Puiseux expansions, differentiation and analytic Hardy properties. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

def rootCoord (n : ℕ) (x : ℝ) : ℝ := x ^ (-(n:ℝ)⁻¹)

def Puiseux (f : ℝ → ℂ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, ∃ F : ℂ → ℂ,
    AnalyticAt ℂ F 0 ∧ f =ᶠ[atTop] fun x => ((rootCoord n x)^m : ℝ) • F (rootCoord n x)

lemma rootCoord_pos {n : ℕ} {x : ℝ} (hx : 0 < x) : 0 < rootCoord n x :=
  Real.rpow_pos_of_pos hx _

lemma rootCoord_tendsto_zero {n : ℕ} (hn : 0 < n) :
    Tendsto (rootCoord n) atTop (𝓝 0) :=
  tendsto_rpow_neg_atTop (inv_pos.mpr (Nat.cast_pos.mpr hn))

lemma rootCoord_complex_tendsto_zero {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x => (rootCoord n x : ℂ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp (rootCoord_tendsto_zero hn)

lemma rootCoord_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {x : ℝ} (hx : 0 < x) :
    (rootCoord (n*m) x)^m = rootCoord n x := by
  rw [rootCoord,←Real.rpow_natCast,←Real.rpow_mul hx.le]
  congr 1
  push_cast
  field_simp

lemma rootCoord_zpow {n : ℕ} {x : ℝ} (hx : 0 < x) (m : ℤ) :
    (rootCoord n x)^m = x^(-(m:ℝ)/(n:ℝ)) := by
  rw [rootCoord,←Real.rpow_intCast,←Real.rpow_mul hx.le]
  congr 1
  ring

lemma Puiseux.congr {f g : ℝ → ℂ} (hf : Puiseux f) (hfg : f =ᶠ[atTop] g) : Puiseux g := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  exact ⟨n,hn,m,F,hF,hfg.symm.trans he⟩

lemma puiseux_const (c : ℂ) : Puiseux (fun _ : ℝ => c) := by
  refine ⟨1,by norm_num,0,fun _ => c,analyticAt_const,?_⟩
  exact Eventually.of_forall (fun x => by simp)

lemma Puiseux.normalize {f : ℝ → ℂ} (hf : Puiseux f)
    (hne : ¬ f =ᶠ[atTop] fun _ => 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, ∃ F : ℂ → ℂ,
      AnalyticAt ℂ F 0 ∧ F 0 ≠ 0 ∧
      f =ᶠ[atTop] fun x => ((rootCoord n x)^m : ℝ) • F (rootCoord n x) := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  have hFne : ¬ F =ᶠ[𝓝 0] fun _ => 0 := by
    intro h0
    apply hne
    filter_upwards [he,(rootCoord_complex_tendsto_zero hn).eventually h0] with x hx hz
    simp [hx,hz]
  obtain ⟨k,G,hG,hG0,hfac⟩ := hF.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hFne
  refine ⟨n,hn,m+(k:ℤ),G,hG,hG0,?_⟩
  filter_upwards [he,(rootCoord_complex_tendsto_zero hn).eventually hfac,
    eventually_gt_atTop (0:ℝ)] with x hx hfac hxpos
  rw [hx,hfac,sub_zero]
  rw [zpow_add₀ (rootCoord_pos hxpos).ne',zpow_natCast]
  simp only [←Complex.ofReal_pow,Complex.real_smul,Complex.ofReal_mul,smul_eq_mul,mul_assoc]

 

lemma Puiseux.leading {f : ℝ → ℂ} (hf : Puiseux f)
    (hne : ¬ f =ᶠ[atTop] fun _ => 0) :
    ∃ q : ℚ, ∃ C : ℂ, C ≠ 0 ∧
      Tendsto (fun x => ((x^(q:ℝ) : ℝ):ℂ)⁻¹ * f x) atTop (𝓝 C) := by
  obtain ⟨n,hn,m,F,hF,hF0,he⟩ := hf.normalize hne
  refine ⟨-(m:ℚ)/(n:ℚ),F 0,hF0,?_⟩
  apply (hF.continuousAt.tendsto.comp (rootCoord_complex_tendsto_zero hn)).congr'
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with x hx hxpos
  rw [hx,rootCoord_zpow hxpos]
  push_cast
  rw [Complex.real_smul]
  have hne : ((x^(-(m:ℝ)/(n:ℝ)) : ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hxpos (-(m:ℝ)/(n:ℝ))).ne'
  simp [hne]

lemma Puiseux.eventually_nonzero {f : ℝ → ℂ} (hf : Puiseux f)
    (hne : ¬ f =ᶠ[atTop] fun _ => 0) : ∀ᶠ x : ℝ in atTop, f x ≠ 0 := by
  obtain ⟨q,C,hC,ht⟩ := hf.leading hne
  filter_upwards [ht.eventually_ne hC] with x hx
  exact (mul_ne_zero_iff.mp hx).2

 
lemma Puiseux.eventually_sign {f : ℝ → ℝ} (hf : Puiseux (fun x => (f x : ℂ)))
    (hne : ¬ f =ᶠ[atTop] fun _ => 0) :
    (∀ᶠ x : ℝ in atTop, 0 < f x) ∨ (∀ᶠ x : ℝ in atTop, f x < 0) := by
  have hcne : ¬ (fun x => (f x:ℂ)) =ᶠ[atTop] fun _ => 0 := by
    intro h
    apply hne
    exact h.mono (fun x hx => Complex.ofReal_eq_zero.mp hx)
  obtain ⟨q,C,hC,ht⟩ := hf.leading hcne
  have ht' : Tendsto (fun x => (x^(q:ℝ))⁻¹*f x) atTop (𝓝 C.re) := by
    simpa only [Function.comp_def, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re] using Complex.continuous_re.continuousAt.tendsto.comp ht
  have hCim : C.im = 0 := by
    have h : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (𝓝 C.im) := by
      simpa only [Function.comp_def, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_im] using Complex.continuous_im.continuousAt.tendsto.comp ht
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hCre : C.re ≠ 0 := by
    intro h
    apply hC
    exact Complex.ext h hCim
  rcases lt_or_gt_of_ne hCre with hneg | hpos
  · right
    filter_upwards [ht'.eventually_lt_const hneg,eventually_gt_atTop (0:ℝ)] with x hx hxpos
    exact neg_of_mul_neg_right hx (inv_nonneg.mpr (Real.rpow_nonneg hxpos.le _))
  · left
    filter_upwards [ht'.eventually_const_lt hpos,eventually_gt_atTop (0:ℝ)] with x hx hxpos
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr (Real.rpow_pos_of_pos hxpos _))).mp hx

end DegeneratingTrees.Clock

 

 

open Filter Topology Complex
namespace DegeneratingTrees.Clock

 
lemma puiseux_refine {f : ℝ → ℂ} {n : ℕ} (hn : 0 < n) {m : ℤ} {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0)
    (he : f =ᶠ[atTop] fun x => ((rootCoord n x)^m : ℝ) • F (rootCoord n x))
    {r : ℕ} (hr : 0 < r) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      f =ᶠ[atTop] fun x => ((rootCoord (n*r) x)^(m*(r:ℤ)) : ℝ) • G (rootCoord (n*r) x) := by
  refine ⟨fun z => F (z^r), ?_, ?_⟩
  · have hF' : AnalyticAt ℂ F ((0:ℂ)^r) := by simpa [zero_pow hr.ne'] using hF
    exact hF'.comp (f := fun z : ℂ => z^r) (analyticAt_id.pow r)
  · filter_upwards [he,eventually_gt_atTop (0:ℝ)] with x hx hxpos
    rw [hx,←rootCoord_pow hn hr hxpos,Complex.ofReal_pow]
    congr 1
    rw [←zpow_natCast,←zpow_mul]
    congr 1
    ring

lemma Puiseux.mul {f g : ℝ → ℂ} (hf : Puiseux f) (hg : Puiseux g) :
    Puiseux (fun x => f x * g x) := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  obtain ⟨r,hr,k,G,hG,he'⟩ := hg
  obtain ⟨F',hF',hf'⟩ := puiseux_refine hn hF he hr
  obtain ⟨G',hG',hg'⟩ := puiseux_refine hr hG he' hn
  rw [Nat.mul_comm r n] at hg'
  refine ⟨n*r,Nat.mul_pos hn hr,m*(r:ℤ)+k*(n:ℤ),fun z => F' z * G' z,
    hF'.mul hG',?_⟩
  filter_upwards [hf',hg',eventually_gt_atTop (0:ℝ)] with x hx hy hxpos
  rw [hx,hy,zpow_add₀ (rootCoord_pos hxpos).ne']
  simp only [Complex.real_smul,Complex.ofReal_mul]
  ring

lemma Puiseux.neg {f : ℝ → ℂ} (hf : Puiseux f) : Puiseux (fun x => -f x) := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  refine ⟨n,hn,m,fun z => -F z,hF.neg,?_⟩
  filter_upwards [he] with x hx
  simp [hx]

lemma Puiseux.add {f g : ℝ → ℂ} (hf : Puiseux f) (hg : Puiseux g) :
    Puiseux (fun x => f x + g x) := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  obtain ⟨r,hr,k,G,hG,he'⟩ := hg
  obtain ⟨F',hF',hf'⟩ := puiseux_refine hn hF he hr
  obtain ⟨G',hG',hg'⟩ := puiseux_refine hr hG he' hn
  rw [Nat.mul_comm r n] at hg'
  let a := m*(r:ℤ)
  let b := k*(n:ℤ)
  let c := min a b
  have ha : 0 ≤ a-c := sub_nonneg.mpr (min_le_left _ _)
  have hb : 0 ≤ b-c := sub_nonneg.mpr (min_le_right _ _)
  refine ⟨n*r,Nat.mul_pos hn hr,c,fun z => z^(a-c).toNat*F' z+z^(b-c).toNat*G' z,
    ((analyticAt_id.pow _).mul hF').add ((analyticAt_id.pow _).mul hG'),?_⟩
  filter_upwards [hf',hg',eventually_gt_atTop (0:ℝ)] with x hx hy hxpos
  have ht : rootCoord (n*r) x ≠ 0 := (rootCoord_pos hxpos).ne'
  have hpa : (rootCoord (n*r) x)^c * (rootCoord (n*r) x)^(a-c).toNat =
      (rootCoord (n*r) x)^a := by
    rw [←zpow_natCast,Int.toNat_of_nonneg ha,←zpow_add₀ ht]
    congr 1
    ring
  have hpb : (rootCoord (n*r) x)^c * (rootCoord (n*r) x)^(b-c).toNat =
      (rootCoord (n*r) x)^b := by
    rw [←zpow_natCast,Int.toNat_of_nonneg hb,←zpow_add₀ ht]
    congr 1
    ring
  rw [hx,hy]
  simp only [Complex.real_smul,←Complex.ofReal_pow,mul_add,←mul_assoc,←Complex.ofReal_mul,
    hpa,hpb]
  rfl

lemma Puiseux.sub {f g : ℝ → ℂ} (hf : Puiseux f) (hg : Puiseux g) :
    Puiseux (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma Puiseux.inv {f : ℝ → ℂ} (hf : Puiseux f) : Puiseux (fun x => (f x)⁻¹) := by
  by_cases hz : f =ᶠ[atTop] fun _ => 0
  · apply (puiseux_const 0).congr
    exact hz.mono (fun x hx => by simp [hx])
  · obtain ⟨n,hn,m,F,hF,hF0,he⟩ := hf.normalize hz
    refine ⟨n,hn,-m,fun z => (F z)⁻¹,hF.inv hF0,?_⟩
    filter_upwards [he] with x hx
    simp [hx,Complex.real_smul,zpow_neg,Complex.ofReal_inv,mul_inv_rev,mul_comm]

lemma Puiseux.div {f g : ℝ → ℂ} (hf : Puiseux f) (hg : Puiseux g) :
    Puiseux (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

end DegeneratingTrees.Clock

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma analyticAt_conj_conj {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (fun z => star (F (star z))) 0 := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hc : Tendsto (star : ℂ → ℂ) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_star.continuousAt (x := (0:ℂ))).tendsto
  filter_upwards [hc.eventually hF.eventually_analyticAt] with z hz
  simpa only [Function.comp_def, Complex.star_def, Complex.conj_conj] using hz.differentiableAt.conj_conj

lemma Puiseux.conj {f : ℝ → ℂ} (hf : Puiseux f) : Puiseux (fun x => star (f x)) := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  refine ⟨n,hn,m,fun z => star (F (star z)),analyticAt_conj_conj hF,?_⟩
  filter_upwards [he] with x hx
  simp [hx,Complex.real_smul]

lemma puiseux_analytic_root {n : ℕ} (hn : 0 < n) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) : Puiseux (fun x => F (rootCoord n x)) := by
  refine ⟨n,hn,0,F,hF,?_⟩
  exact Eventually.of_forall (fun x => by simp)

lemma puiseux_ratPower (q : ℚ) : Puiseux (fun x : ℝ => ((x^(q:ℝ):ℝ):ℂ)) := by
  refine ⟨q.den,q.pos,-q.num,fun _ => 1,analyticAt_const,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  simp only [rootCoord_zpow hx,Int.cast_neg,neg_neg,Complex.real_smul,mul_one]
  congr 2
  exact_mod_cast q.num_div_den.symm

lemma eventuallyEq_deriv_atTop {f g : ℝ → ℂ} (he : f =ᶠ[atTop] g) :
    deriv f =ᶠ[atTop] deriv g := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  filter_upwards [eventually_gt_atTop T] with x hx
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact hT y hy.le

lemma Puiseux.deriv {f : ℝ → ℂ} (hf : Puiseux f) : Puiseux (deriv f) := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  let q : ℚ := -(m:ℚ)/(n:ℚ)
  let r : ℚ := -(n:ℚ)⁻¹
  have he' : f =ᶠ[atTop] fun x => ((x^(q:ℝ):ℝ):ℂ) * F (rootCoord n x) := by
    filter_upwards [he,eventually_gt_atTop (0:ℝ)] with x hx hxpos
    simp [hx,rootCoord_zpow hxpos,q,Complex.real_smul]
  let g : ℝ → ℂ := fun x =>
    ((q:ℂ)*((x^((q-1:ℚ):ℝ):ℝ):ℂ))*F (rootCoord n x) +
    ((x^(q:ℝ):ℝ):ℂ)*(_root_.deriv F (rootCoord n x)*((r:ℂ)*((x^((r-1:ℚ):ℝ):ℝ):ℂ)))
  have hg : Puiseux g :=
    (((puiseux_const (q:ℂ)).mul (puiseux_ratPower (q-1))).mul (puiseux_analytic_root hn hF)).add
      ((puiseux_ratPower q).mul ((puiseux_analytic_root hn hF.deriv).mul
        ((puiseux_const (r:ℂ)).mul (puiseux_ratPower (r-1)))))
  apply hg.congr
  have hd := eventuallyEq_deriv_atTop he'
  filter_upwards [hd,(rootCoord_complex_tendsto_zero hn).eventually hF.eventually_analyticAt,
    eventually_gt_atTop (0:ℝ)] with x hx hFx hxpos
  rw [hx]
  have hdF := hFx.differentiableAt.hasDerivAt.comp_ofReal
  have hdroot : HasDerivAt (rootCoord n) ((r:ℝ)*x^((r:ℝ)-1)) x := by
    convert! (Real.hasDerivAt_rpow_const (p := -(n:ℝ)⁻¹) (Or.inl hxpos.ne')) using 1
    simp [r]
  have hdFroot := hdF.scomp x hdroot
  have hdpow := (Real.hasDerivAt_rpow_const (p := (q:ℝ)) (Or.inl hxpos.ne')).ofReal_comp
  have hdprod := hdpow.mul hdFroot
  convert! hdprod.deriv.symm using 1
  first | rfl |
    (simp only [g,Rat.cast_sub,Rat.cast_one,Complex.ofReal_mul,Complex.ofReal_ratCast,
      Complex.real_smul,Function.comp_def]; ring)

end DegeneratingTrees.Clock

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma analyticAt_real_rpow {x : ℝ} (hx : 0 < x) (p : ℝ) :
    AnalyticAt ℝ (fun y : ℝ => y^p) x := by
  apply (((analyticAt_log hx).mul analyticAt_const).rexp).congr
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact (Real.rpow_def_of_pos hy p).symm

lemma Puiseux.eventually_analytic {f : ℝ → ℂ} (hf : Puiseux f) :
    ∀ᶠ x : ℝ in atTop, AnalyticAt ℝ f x := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  filter_upwards [eventually_gt_atTop T,eventually_gt_atTop (0:ℝ),
    (rootCoord_complex_tendsto_zero hn).eventually hF.eventually_analyticAt] with x hx hxpos hFx
  have ht : AnalyticAt ℝ (rootCoord n) x := analyticAt_real_rpow hxpos _
  have htc : AnalyticAt ℝ (fun y => (rootCoord n y:ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp ht
  have hP : AnalyticAt ℝ (fun y => ((y^(-(m:ℝ)/(n:ℝ)):ℝ):ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp (analyticAt_real_rpow hxpos _)
  have hmodel := hP.mul ((hFx.restrictScalars (𝕜 := ℝ)).comp (f := fun y:ℝ => (rootCoord n y:ℂ)) htc)
  apply hmodel.congr
  filter_upwards [eventually_gt_nhds hx,eventually_gt_nhds hxpos] with y hy hypos
  rw [hT y hy.le]
  dsimp
  rw [rootCoord_zpow hypos]

lemma Puiseux.real_eventually_analytic {f : ℝ → ℝ} (hf : Puiseux (fun x => (f x:ℂ))) :
    ∀ᶠ x : ℝ in atTop, AnalyticAt ℝ f x := by
  filter_upwards [hf.eventually_analytic] with x hx
  exact (Complex.reCLM.analyticAt _).comp hx

lemma Puiseux.real_deriv {f : ℝ → ℝ} (hf : Puiseux (fun x => (f x:ℂ))) :
    Puiseux (fun x => ((_root_.deriv f x : ℝ):ℂ)) := by
  apply hf.deriv.congr
  filter_upwards [hf.real_eventually_analytic] with x hx
  exact hx.differentiableAt.hasDerivAt.ofReal_comp.deriv

 

theorem Puiseux.eventually_monotone {f : ℝ → ℝ} (hf : Puiseux (fun x => (f x:ℂ))) :
    ∃ T : ℝ, MonotoneOn f (Ioi T) ∨ AntitoneOn f (Ioi T) := by
  have hder : (∀ᶠ x : ℝ in atTop, 0 ≤ _root_.deriv f x) ∨
      (∀ᶠ x : ℝ in atTop, _root_.deriv f x ≤ 0) := by
    by_cases hz : _root_.deriv f =ᶠ[atTop] fun _ => 0
    · exact Or.inl (hz.mono fun x hx => hx.ge)
    · rcases hf.real_deriv.eventually_sign hz with h | h
      · exact Or.inl (h.mono fun _ hx => hx.le)
      · exact Or.inr (h.mono fun _ hx => hx.le)
  rcases hder with h | h
  · obtain ⟨T,hT⟩ := eventually_atTop.mp (hf.real_eventually_analytic.and h)
    refine ⟨T,Or.inl ?_⟩
    apply monotoneOn_of_deriv_nonneg (convex_Ioi T)
    · exact fun x hx => (hT x hx.le).1.continuousAt.continuousWithinAt
    · exact fun x hx => (hT x (interior_subset hx).le).1.differentiableAt.differentiableWithinAt
    · exact fun x hx => (hT x (interior_subset hx).le).2
  · obtain ⟨T,hT⟩ := eventually_atTop.mp (hf.real_eventually_analytic.and h)
    refine ⟨T,Or.inr ?_⟩
    apply antitoneOn_of_deriv_nonpos (convex_Ioi T)
    · exact fun x hx => (hT x hx.le).1.continuousAt.continuousWithinAt
    · exact fun x hx => (hT x (interior_subset hx).le).1.differentiableAt.differentiableWithinAt
    · exact fun x hx => (hT x (interior_subset hx).le).2

end DegeneratingTrees.Clock
end

end OAI
