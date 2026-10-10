import Mathlib
import OAI.Probability.SKValue.Gaussian.DensityJump

namespace OAI

section

namespace SKValue.Certificate
noncomputable def Q (R K v b : ℝ) : ℝ :=
  (1/13)*v*b+(53/24)*v^2+(19/16)*K*v-2*(19/16)*R*b+(73/48)*R*v
noncomputable def T (R v j : ℝ) : ℝ := (2331/10000)*R*v+(87/2500)*j*v
noncomputable def F₂ (R K v b j : ℝ) : ℝ :=
  (4663/5000)*v^2*j+(6853/10000)*v^3-(1051/400)*K*v^2-(1073/500)*R*v^2-
  (b^2*(2*R*(19/16)-(1/13)*v)+
    b*(-2*K*(19/16)*v-R*(2331/10000)*v-2*R*(73/48)*v-2*(53/24)*v^2-(87/2500)*j*v))
noncomputable def W₂ (R K v b j z L : ℝ) : ℝ :=
  (2*R*v)*(-(1073/500)*v^2-2*(19/16)*b^2+b*((2331/10000)*v+2*(73/48)*v))+
  (2*v*K+R*j)*(-(1051/400)*v^2+2*(19/16)*b*v)+
  (-R*b)*(2*(4663/5000)*v*j+3*(6853/10000)*v^2-2*(1051/400)*K*v-
    2*(1073/500)*R*v+(1/13)*b^2+
    b*(2*K*(19/16)+R*(2331/10000)+2*R*(73/48)+4*(53/24)*v+(87/2500)*j))+
  (-z-b*v)*(-2*b*(2*R*(19/16)-(1/13)*v)+2*K*(19/16)*v+
    R*(2331/10000)*v+2*R*(73/48)*v+2*(53/24)*v^2+(87/2500)*j*v)+
  (-j*v+K*b-L)*((4663/5000)*v^2+(87/2500)*b*v)+(v+R-K)*F₂ R K v b j
noncomputable def remainder (R K v B j : ℝ) : ℝ :=
  (223/160000)*R^2*v^2+(4007/240000)*R^2*v*B+(1097/120000)*R^2*B^2+
  (83/80000)*R*K*v^2+(3343/24000)*R*K*v*B+(16259/23400000)*R*v^3+
  (30179/5460000)*R*v^2*B+(26/625)*R*v^2*j+(107/15000)*R*v*B^2+
  (3/2500)*R*v*B*j+(121/32500)*R*B^3+(11/10000)*R*B^2*j+
  (579/20000)*K^2*v^2+(207/2500)*K^2*v*B+(911/975000)*K*v^3+
  (349/420000)*K*v^2*B+(5011/5000)*K*v^2*j+(133/130000)*K*v*B^2+
  (87/2500)*K*v*B*j+(1661507/1521000000)*v^4+
  (633799/621075000)*v^3*B+(10657/1690000)*v^2*B^2

theorem rational_identity (R K v B j z L : ℝ) :
    let b:=B+2*v
    z^2-12*R*v*b^2+6*v^4=
      (z+Q R K v b)^2+(z+b*v-2*R*b)*T R v j+
      (337/10000)*(R*j*(b-7*v)^2)+
      (183/2500)*(R*B*(b-(7/3)*v)^2)+
      (411/10000)*(K*v*(b-(9/2)*v)^2)+
      (11461/5000)*(v*B*(K+(1/4)*R-(1/7)*v)^2)+
      (647/10000)*(v*b-(14/5)*v^2-(13/4)*K*v+(4/3)*R*v)^2+
      W₂ R K v b j z L+L*((4663/5000)*v^2+(87/2500)*b*v)+remainder R K v B j := by
  dsimp only [Q,T,W₂,F₂,remainder]
  ring

theorem pointwise_coercivity {R K v B j z L : ℝ}
    (hR : 0≤R) (hK : 0≤K) (hv : 0≤v) (hB : 0≤B) (hj : 0≤j) (hL : 0≤L)
    (hS : 0≤z+(B+2*v)*v-2*R*(B+2*v)) :
    (1661507/1521000000)*v^4+W₂ R K v (B+2*v) j z L≤
      z^2-12*R*v*(B+2*v)^2+6*v^4 := by
  have he := rational_identity R K v B j z L
  dsimp only at he
  have hrem : (1661507/1521000000)*v^4≤remainder R K v B j := by
    unfold remainder
    have hrest : 0≤
      (223/160000)*R^2*v^2+(4007/240000)*R^2*v*B+(1097/120000)*R^2*B^2+
      (83/80000)*R*K*v^2+(3343/24000)*R*K*v*B+(16259/23400000)*R*v^3+
      (30179/5460000)*R*v^2*B+(26/625)*R*v^2*j+(107/15000)*R*v*B^2+
      (3/2500)*R*v*B*j+(121/32500)*R*B^3+(11/10000)*R*B^2*j+
      (579/20000)*K^2*v^2+(207/2500)*K^2*v*B+(911/975000)*K*v^3+
      (349/420000)*K*v^2*B+(5011/5000)*K*v^2*j+(133/130000)*K*v*B^2+
      (87/2500)*K*v*B*j+
      (633799/621075000)*v^3*B+(10657/1690000)*v^2*B^2 := by positivity
    linarith
  have hT : 0≤T R v j := by unfold T; positivity
  have hST := mul_nonneg hS hT
  have h0 : 0≤(337/10000 : ℝ)*(R*j*(B+2*v-7*v)^2) := by positivity
  have h1 : 0≤(183/2500 : ℝ)*(R*B*(B+2*v-(7/3)*v)^2) := by positivity
  have h2 : 0≤(411/10000 : ℝ)*(K*v*(B+2*v-(9/2)*v)^2) := by positivity
  have h3 : 0≤(11461/5000 : ℝ)*(v*B*(K+(1/4)*R-(1/7)*v)^2) := by positivity
  have h4 : 0≤(647/10000 : ℝ)*(v*(B+2*v)-(14/5)*v^2-(13/4)*K*v+(4/3)*R*v)^2 := by positivity
  have hLC : 0≤L*((4663/5000)*v^2+(87/2500)*(B+2*v)*v) := by positivity
  have hs := sq_nonneg (z+Q R K v (B+2*v))
  linarith only [he,hrem,hST,h0,h1,h2,h3,h4,hLC,hs]
end SKValue.Certificate

end

section
namespace SKValue.Certificate
lemma growth_F {R K v b j:ℝ → ℝ} (hR:ExpGrowth R) (hK:ExpGrowth K)
    (hv:ExpGrowth v) (hb:ExpGrowth b) (hj:ExpGrowth j) :
    ExpGrowth (fun x ↦ F₂ (R x) (K x) (v x) (b x) (j x)) := by
  have h := (((((((ExpGrowth.const (4663/5000:ℝ)).mul (hv.pow 2)).mul hj).add ((ExpGrowth.const (6853/10000:ℝ)).mul (hv.pow 3))).sub (((ExpGrowth.const (1051/400:ℝ)).mul hK).mul (hv.pow 2))).sub (((ExpGrowth.const (1073/500:ℝ)).mul hR).mul (hv.pow 2))).sub (((hb.pow 2).mul ((((ExpGrowth.const (2/1:ℝ)).mul hR).mul (ExpGrowth.const (19/16:ℝ))).sub ((ExpGrowth.const (1/13:ℝ)).mul hv))).add (hb.mul ((((((((ExpGrowth.const (-2/1:ℝ)).mul hK).mul (ExpGrowth.const (19/16:ℝ))).mul hv).sub ((hR.mul (ExpGrowth.const (2331/10000:ℝ))).mul hv)).sub ((((ExpGrowth.const (2/1:ℝ)).mul hR).mul (ExpGrowth.const (73/48:ℝ))).mul hv)).sub ((ExpGrowth.const (53/12:ℝ)).mul (hv.pow 2))).sub (((ExpGrowth.const (87/2500:ℝ)).mul hj).mul hv)))))
  convert! h using 1
  funext x
  dsimp [F₂]
  ring
lemma growth_W {R K v b j z L:ℝ → ℝ} (hR:ExpGrowth R) (hK:ExpGrowth K)
    (hv:ExpGrowth v) (hb:ExpGrowth b) (hj:ExpGrowth j) (hz:ExpGrowth z) (hL:ExpGrowth L) :
    ExpGrowth (fun x ↦ W₂ (R x) (K x) (v x) (b x) (j x) (z x) (L x)) := by
  have hF:=growth_F hR hK hv hb hj
  have h := (((((((((ExpGrowth.const (2/1:ℝ)).mul hR).mul hv).mul ((((ExpGrowth.const (-1073/500:ℝ)).mul (hv.pow 2)).sub ((ExpGrowth.const (19/8:ℝ)).mul (hb.pow 2))).add (hb.mul (((ExpGrowth.const (2331/10000:ℝ)).mul hv).add ((ExpGrowth.const (73/24:ℝ)).mul hv))))).add (((((ExpGrowth.const (2/1:ℝ)).mul hv).mul hK).add (hR.mul hj)).mul (((ExpGrowth.const (-1051/400:ℝ)).mul (hv.pow 2)).add (((ExpGrowth.const (19/8:ℝ)).mul hb).mul hv)))).add (((hR.neg).mul hb).mul ((((((((ExpGrowth.const (4663/2500:ℝ)).mul hv).mul hj).add ((ExpGrowth.const (20559/10000:ℝ)).mul (hv.pow 2))).sub (((ExpGrowth.const (1051/200:ℝ)).mul hK).mul hv)).sub (((ExpGrowth.const (1073/250:ℝ)).mul hR).mul hv)).add ((ExpGrowth.const (1/13:ℝ)).mul (hb.pow 2))).add (hb.mul (((((((ExpGrowth.const (2/1:ℝ)).mul hK).mul (ExpGrowth.const (19/16:ℝ))).add (hR.mul (ExpGrowth.const (2331/10000:ℝ)))).add (((ExpGrowth.const (2/1:ℝ)).mul hR).mul (ExpGrowth.const (73/48:ℝ)))).add ((ExpGrowth.const (53/6:ℝ)).mul hv)).add ((ExpGrowth.const (87/2500:ℝ)).mul hj)))))).add (((hz.neg).sub (hb.mul hv)).mul ((((((((ExpGrowth.const (-2/1:ℝ)).mul hb).mul ((((ExpGrowth.const (2/1:ℝ)).mul hR).mul (ExpGrowth.const (19/16:ℝ))).sub ((ExpGrowth.const (1/13:ℝ)).mul hv))).add ((((ExpGrowth.const (2/1:ℝ)).mul hK).mul (ExpGrowth.const (19/16:ℝ))).mul hv)).add ((hR.mul (ExpGrowth.const (2331/10000:ℝ))).mul hv)).add ((((ExpGrowth.const (2/1:ℝ)).mul hR).mul (ExpGrowth.const (73/48:ℝ))).mul hv)).add ((ExpGrowth.const (53/12:ℝ)).mul (hv.pow 2))).add (((ExpGrowth.const (87/2500:ℝ)).mul hj).mul hv)))).add (((((hj.neg).mul hv).add (hK.mul hb)).sub hL).mul (((ExpGrowth.const (4663/5000:ℝ)).mul (hv.pow 2)).add (((ExpGrowth.const (87/2500:ℝ)).mul hb).mul hv)))).add (((hv.add hR).sub hK).mul hF))
  convert! h using 1
  funext x
  dsimp [W₂]
  ring
end SKValue.Certificate

end

section
open MeasureTheory Set Filter
open scoped Topology
namespace SKValue.Certificate

lemma flux_derivative {r v w z s a d f:ℝ → ℝ} {x:ℝ}
    (hr:HasDerivAt r (v x) x) (hv:HasDerivAt v (w x) x)
    (hw:HasDerivAt w (z x) x) (hs:HasDerivAt s (a x) x)
    (ha:HasDerivAt a (d x) x) (hf:HasDerivAt f ((r x-s x)*f x) x)
    (hn:r x≠0) :
    HasDerivAt (fun y ↦ r y*F₂ (r y^2) (r y*s y) (v y) (-w y/r y)
      (a y-s y/r y*v y)*f y)
      (W₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)
        (z x) (-r x*d x)*f x) x := by
  have hR := hr.pow 2
  have hK := hr.mul hs
  have hb := hw.neg.div hr hn
  have hj := ha.sub ((hs.div hr hn).mul hv)
  have hF := (((((((hasDerivAt_const x (4663/5000:ℝ)).mul (hv.pow 2)).mul hj).add ((hasDerivAt_const x (6853/10000:ℝ)).mul (hv.pow 3))).sub (((hasDerivAt_const x (1051/400:ℝ)).mul hK).mul (hv.pow 2))).sub (((hasDerivAt_const x (1073/500:ℝ)).mul hR).mul (hv.pow 2))).sub (((hb.pow 2).mul ((((hasDerivAt_const x (2/1:ℝ)).mul hR).mul (hasDerivAt_const x (19/16:ℝ))).sub ((hasDerivAt_const x (1/13:ℝ)).mul hv))).add (hb.mul ((((((((hasDerivAt_const x (-2/1:ℝ)).mul hK).mul (hasDerivAt_const x (19/16:ℝ))).mul hv).sub ((hR.mul (hasDerivAt_const x (2331/10000:ℝ))).mul hv)).sub ((((hasDerivAt_const x (2/1:ℝ)).mul hR).mul (hasDerivAt_const x (73/48:ℝ))).mul hv)).sub ((hasDerivAt_const x (53/12:ℝ)).mul (hv.pow 2))).sub (((hasDerivAt_const x (87/2500:ℝ)).mul hj).mul hv)))))
  have hflux := (hr.mul hF).mul hf
  convert! hflux using 1
  · funext y
    dsimp [F₂]
    ring
  · dsimp [W₂,F₂]
    field_simp
    ring
end SKValue.Certificate

end

end OAI
