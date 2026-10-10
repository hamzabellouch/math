import Mathlib
import OAI.Probability.SKValue.Evolution.LogCoshTerminal
import OAI.Probability.SKValue.Equations.BackwardComparison
import OAI.Probability.SKValue.Equations.ForwardComparison

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue
namespace BackwardBurgers
variable {T : ℝ} (B : BackwardBurgers) (F : ForwardBurgers T) (b : ℝ)
noncomputable def ratioJ (t x : ℝ) : ℝ := B.jet 0 (b-t) x*F.jet 1 t x-F.jet 0 t x*B.jet 1 (b-t) x
noncomputable def ratioJx (t x : ℝ) : ℝ := B.jet 0 (b-t) x*F.jet 2 t x-F.jet 0 t x*B.jet 2 (b-t) x
noncomputable def ratioJxx (t x : ℝ) : ℝ := B.jet 1 (b-t) x*F.jet 2 t x+
  B.jet 0 (b-t) x*F.jet 3 t x-F.jet 1 t x*B.jet 2 (b-t) x-F.jet 0 t x*B.jet 3 (b-t) x
noncomputable def ratioJt (t x : ℝ) : ℝ := (1/2:ℝ)*B.ratioJxx F b t x-
  (B.jet 1 (b-t) x/B.jet 0 (b-t) x)*B.ratioJx F b t x-
  (B.jet 1 (b-t) x+F.jet 1 t x)*B.ratioJ F b t x+
  (F.jet 0 t x/B.jet 0 (b-t) x)*B.n (b-t) x-
  B.jet 0 (b-t) x*F.jet 0 t x*(B.jet 2 (b-t) x+F.jet 2 t x)
lemma ratioJ_space (t x : ℝ) : HasDerivAt (B.ratioJ F b t) (B.ratioJx F b t x) x := by
  have hh := ((B.space 0 (b-t) x).mul (F.space 1 t x)).sub
    ((F.space 0 t x).mul (B.space 1 (b-t) x))
  convert! hh using 1
  dsimp [ratioJ,ratioJx]
  ring
lemma ratioJx_space (t x : ℝ) : HasDerivAt (B.ratioJx F b t) (B.ratioJxx F b t x) x := by
  have hh := ((B.space 0 (b-t) x).mul (F.space 2 t x)).sub
    ((F.space 0 t x).mul (B.space 2 (b-t) x))
  convert! hh using 1
  dsimp [ratioJx,ratioJxx]
  ring
lemma ratioJ_time {t x : ℝ} (ht : t∈Ioc (0:ℝ) T) (hb : T<b) (hx : 0<x) :
    HasDerivAt (B.ratioJ F b · x) (B.ratioJt F b t x) t := by
  have hbt : 0<b-t := by linarith [ht.2]
  have hd : HasDerivAt (fun s : ℝ ↦ b-s) (-1) t := (hasDerivAt_id t).const_sub b
  have h0 := (B.time0 (b-t) hbt x).comp t hd
  have h1 := (B.time1 (b-t) hbt x).comp t hd
  have hh := (h0.mul (F.time1 t ht x)).sub ((F.time0 t ht x).mul h1)
  convert! hh using 1
  dsimp [ratioJt,ratioJxx,ratioJx,ratioJ,n]
  field_simp [(B.positive (b-t) x hx).ne']
  ring
lemma ratioJ_continuous : Continuous (fun p : ℝ×ℝ ↦ B.ratioJ F b p.1 p.2) := by
  have hb (n : ℕ) : Continuous (fun p : ℝ×ℝ ↦ B.jet n (b-p.1) p.2) :=
    (B.continuous n).comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  exact ((hb 0).mul (F.continuous 1)).sub ((F.continuous 0).mul (hb 1))

lemma ratioJ_nonneg {b a : ℝ} (ha : 0<a) (hT : 0≤T) (hb : T<b)
    (hinit : ∀ x,0≤x → 0≤B.ratioJ F b 0 x)
    (hslope : ∀ x,1/a≤F.jet 1 0 x)
    (hsconc : ∀ x,0≤x → F.jet 2 0 x≤0)
    (hw : ∀ t∈Icc (0:ℝ) T,∀ x,0≤x → B.jet 2 (b-t) x≤0)
    (hn : ∀ t∈Icc (0:ℝ) T,∀ x,0≤x → 0≤B.n (b-t) x) :
    ∀ t∈Icc (0:ℝ) T,∀ x,0≤x → 0≤B.ratioJ F b t x := by
  obtain ⟨R,hR,hr⟩ := B.bound 0
  obtain ⟨V,hV,hv⟩ := B.bound 1
  obtain ⟨A,hA,ha'⟩ := F.bound 0
  obtain ⟨S,hS,hs⟩ := F.growth
  apply halfline_parabolic_nonneg_linear (B := 0) (C := 0) (M := R*A+S*V) hT le_rfl (by positivity)
    (ut := B.ratioJt F b) (ux := B.ratioJx F b) (uxx := B.ratioJxx F b)
    (β := fun t x ↦ -(B.jet 1 (b-t) x/B.jet 0 (b-t) x))
    (c := fun t x ↦ -(B.jet 1 (b-t) x+F.jet 1 t x))
    (B.ratioJ_continuous F b).continuousOn
    (fun t ht x hx ↦ B.ratioJ_time F b ht hb hx)
    (fun t _ x ↦ B.ratioJ_space F b t x)
    (fun t _ x ↦ B.ratioJx_space F b t x) hinit
    (by intro t ht; simp [ratioJ,B.zero0,F.zero0])
    (by
      intro t ht x hx
      have h1 : |B.jet 0 (b-t) x*F.jet 1 t x|≤R*A := by
        rw [abs_mul]; exact mul_le_mul (hr _ _) (ha' t ht x) (abs_nonneg _) hR
      have h2 : |F.jet 0 t x*B.jet 1 (b-t) x|≤S*(1+x)*V := by
        rw [abs_mul]
        exact mul_le_mul (by simpa only [abs_of_nonneg hx] using hs t ht x) (hv _ _) (abs_nonneg _) (by positivity)
      have h3 := (abs_le.mp h1).1
      have h4 := (abs_le.mp h2).2
      dsimp [ratioJ]
      nlinarith [mul_nonneg (mul_nonneg hR hA) hx])
    (by intro t ht x hx; exact neg_nonpos.mpr (div_nonneg (B.slope_nonneg _ _) (B.positive _ _ hx).le))
    (by
      intro t ht x hx
      have h1 := F.preserve_slope ha hT hslope ⟨ht.1.le,ht.2⟩ x
      have h2 : 0<1/(a+t) := one_div_pos.mpr (by linarith [ht.1])
      linarith [B.slope_nonneg (b-t) x])
    (by
      intro t ht x hx
      have htc : t∈Icc (0:ℝ) T := ⟨ht.1.le,ht.2⟩
      have hrp := (B.positive (b-t) x hx).le
      have hsp := F.score_nonneg ha hT hslope htc hx.le
      have hnp := hn t htc x hx.le
      have hwp := hw t htc x hx.le
      have hscp := F.preserve_concavity ha hT hslope hsconc htc hx.le
      have hsrc1 := mul_nonneg (div_nonneg hsp hrp) hnp
      have hsrc2 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hrp hsp) (add_nonpos hwp hscp)
      dsimp [ratioJt]
      linarith)

end BackwardBurgers
end SKValue

end

section

open Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue

noncomputable def spatialJet (c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  c*iteratedDeriv n (deriv ψ) x
noncomputable def spatialK (c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  spatialJet c ψ 2 x+2*spatialJet c ψ 0 x*spatialJet c ψ 1 x
noncomputable def spatialN (c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  spatialJet c ψ 0 x*spatialJet c ψ 3 x-spatialJet c ψ 1 x*spatialJet c ψ 2 x+
    2*(spatialJet c ψ 0 x)^2*spatialJet c ψ 2 x

structure BackwardShape (c : ℝ) (ψ : ℝ → ℝ) : Prop where
  even : ∀ x,ψ (-x)=ψ x
  convex : ∀ x,0<deriv (deriv ψ) x
  w : ∀ x,0≤x → spatialJet c ψ 2 x≤0
  k : ∀ x,0≤x → spatialK c ψ x≤0
  n : ∀ x,0≤x → 0≤ spatialN c ψ x

lemma spatialJet_scale (a c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    spatialJet (a*c) ψ n x=a*spatialJet c ψ n x := by dsimp [spatialJet]; ring

lemma spatialK_scale (a c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) :
    spatialK (a*c) ψ x=a*spatialK c ψ x-
      2*a*(1-a)*spatialJet c ψ 0 x*spatialJet c ψ 1 x := by
  simp only [spatialK,spatialJet_scale]
  ring
lemma spatialN_scale (a c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) :
    spatialN (a*c) ψ x=a^2*spatialN c ψ x-
      2*a^2*(1-a)*(spatialJet c ψ 0 x)^2*spatialJet c ψ 2 x := by
  simp only [spatialN,spatialJet_scale]
  ring

lemma BackwardShape.scale {c a : ℝ} {ψ : ℝ → ℝ} (hs : BackwardShape c ψ)
    (hc : 0<c) (ha : 0≤a) (ha1 : a≤1) : BackwardShape (a*c) ψ := by
  have hr (x : ℝ) (hx : 0≤x) : 0≤ spatialJet c ψ 0 x := by
    have hm := (strictMono_of_deriv_pos hs.convex).monotone hx
    rw [deriv_even_zero hs.even] at hm
    exact mul_nonneg hc.le hm
  have hv (x : ℝ) : 0≤ spatialJet c ψ 1 x := by
    simpa only [spatialJet,iteratedDeriv_one] using (mul_pos hc (hs.convex x)).le
  refine ⟨hs.even,hs.convex,?_,?_,?_⟩
  · intro x hx
    rw [spatialJet_scale]
    exact mul_nonpos_of_nonneg_of_nonpos ha (hs.w x hx)
  · intro x hx
    rw [spatialK_scale]
    have hn := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) ha)
      (sub_nonneg.mpr ha1)) (hr x hx)) (hv x)
    exact sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos ha (hs.k x hx)).trans hn)
  · intro x hx
    rw [spatialN_scale]
    have hn := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg a))
        (sub_nonneg.mpr ha1)) (sq_nonneg (spatialJet c ψ 0 x))) (hs.w x hx)
    exact sub_nonneg.mpr (hn.trans (mul_nonneg (sq_nonneg a) (hs.n x hx)))

lemma BackwardShape.lower {c d : ℝ} {ψ : ℝ → ℝ} (hs : BackwardShape c ψ)
    (hc : 0<c) (hd : 0≤d) (hdc : d≤c) : BackwardShape d ψ := by
  have hh := hs.scale hc (div_nonneg hd hc.le) ((div_le_one hc).mpr hdc)
  rwa [div_mul_cancel₀ _ hc.ne'] at hh

lemma BackwardShape.evolve {c : ℝ} {ψ : ℝ → ℝ} (hs : BackwardShape c ψ)
    (hψ : SmoothTerminal ψ) (hc : 0<c) {t : ℝ} (ht : 0≤t) :
    BackwardShape c (coleHopf c t ψ) := by
  let F := hψ.backwardBurgers hs.even hs.convex hc
  have h0 : coleHopf c 0 ψ=ψ := by funext x; exact coleHopf_zero c ψ x
  have hw : ∀ x,0≤x → F.jet 2 0 x≤0 := by
    simpa only [F,SmoothTerminal.backwardBurgers,scaledHeatJet,h0,spatialJet] using hs.w
  have hk : ∀ x,0≤x → F.k 0 x≤0 := by
    simpa only [F,BackwardBurgers.k,SmoothTerminal.backwardBurgers,scaledHeatJet,h0,
      spatialK,spatialJet] using hs.k
  have hn : ∀ x,0≤x → 0≤F.n 0 x := by
    simpa only [F,BackwardBurgers.n,SmoothTerminal.backwardBurgers,scaledHeatJet,h0,
      spatialN,spatialJet] using hs.n
  exact ⟨coleHopf_even hs.even c t,hψ.coleHopf_curvature_pos hs.convex hc t,
    fun x hx ↦ F.preserve_w hw ht hx,fun x hx ↦ F.preserve_k hk ht hx,
    fun x hx ↦ F.preserve_n hw hk hn ht hx⟩

lemma logCoshTerminal_gradient_jet (M : ℝ) (hM : M≠0) (n : ℕ) :
    iteratedDeriv n (deriv (logCoshTerminal M)) =
    fun x ↦ JetExpr.eval (fun _ ↦ Real.tanh (M*x)) (JetExpr.fieldJet
      (fun _ ↦ .mul (.const M) (.add (.const 1) (.mul (.const (-1)) (.mul (.coord 0) (.coord 0)))))
      (.coord 0) n) := by
  have hder : deriv (logCoshTerminal M)=fun x ↦ Real.tanh (M*x) :=
    funext (fun x ↦ (logCoshTerminal_hasDerivAt hM x).deriv)
  rw [hder]
  apply JetExpr.iteratedDeriv_fieldJet (R := fun _ x ↦ Real.tanh (M*x)) (e := .coord 0)
  intro j x
  convert! tanh_scaled_hasDerivAt M x using 1
  dsimp [JetExpr.eval]
  ring

lemma logCoshTerminal_backwardShape {M c : ℝ} (hM : 0<M) (hc : 0<c) (hcM : c≤M) :
    BackwardShape c (logCoshTerminal M) := by
  have hq (x : ℝ) : 0<1-(Real.tanh (M*x))^2 := by
    have hh := Real.abs_tanh_lt_one (M*x)
    have hh2 := (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).mpr hh
    rw [sq_abs] at hh2
    nlinarith
  have htanh (x : ℝ) (hx : 0≤x) : 0≤Real.tanh (M*x) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hM.le hx)) (Real.cosh_pos _).le
  have he1 (x : ℝ) : spatialJet M (logCoshTerminal M) 1 x=M^2*(1-(Real.tanh (M*x))^2) := by
    rw [spatialJet,logCoshTerminal_gradient_jet M hM.ne' 1]
    dsimp [JetExpr.fieldJet,JetExpr.D,JetExpr.eval]
    ring
  have he2 (x : ℝ) : spatialJet M (logCoshTerminal M) 2 x=
      -2*M^3*Real.tanh (M*x)*(1-(Real.tanh (M*x))^2) := by
    rw [spatialJet,logCoshTerminal_gradient_jet M hM.ne' 2]
    dsimp [JetExpr.fieldJet,JetExpr.D,JetExpr.eval]
    ring
  have hk (x : ℝ) : spatialK M (logCoshTerminal M) x=0 := by
    dsimp only [spatialK,spatialJet]
    simp only [logCoshTerminal_gradient_jet M hM.ne']
    dsimp [JetExpr.fieldJet,JetExpr.D,JetExpr.eval]
    ring
  have hn (x : ℝ) : spatialN M (logCoshTerminal M) x=0 := by
    dsimp only [spatialN,spatialJet]
    simp only [logCoshTerminal_gradient_jet M hM.ne']
    dsimp [JetExpr.fieldJet,JetExpr.D,JetExpr.eval]
    ring
  have hs : BackwardShape M (logCoshTerminal M) := by
    refine ⟨logCoshTerminal_even M,?_,?_,fun x hx ↦ (hk x).le,fun x hx ↦ (hn x).ge⟩
    · intro x
      have hj := he1 x
      simp only [spatialJet,iteratedDeriv_one] at hj
      have hp := mul_pos (sq_pos_of_pos hM) (hq x)
      rw [←hj] at hp
      exact pos_of_mul_pos_right hp hM.le
    · intro x hx
      rw [he2]
      have hp := mul_nonneg (mul_nonneg (pow_nonneg hM.le 3) (htanh x hx)) (hq x).le
      nlinarith
  exact hs.lower hM hc.le hcM

end SKValue

end

end OAI
