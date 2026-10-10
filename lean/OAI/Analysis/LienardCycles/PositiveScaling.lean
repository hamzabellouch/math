import OAI.Analysis.LienardCycles.OriginalProfile

namespace OAI

universe uP uQ

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveWidth
open ScalarArcs ArcFamilies
variable {P : Type uP} {Q : Type uQ} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    (Ψ : Q × ℝ → ℝ) (hΨ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Ψ q)
    (hlocal : ∀ x : State Q, 0<x.2.1 → ∃ f : State Q × ℝ → State Q,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Ψ (f q)) q.2)
include hΦ hloc hΨ hlocal
lemma fixed_width_scaling {p : P} {q : Q} {b H c C r : ℝ}
    (hb : 0<b) (hh : 0<H+c^2*b) (hc : 0<c) (hr : 0<r)
    (he : ∀ x, 0<x → Ψ (q,H+c^2*x)=C+c*Φ (p,x)) :
    midpointAtWidth Ψ ((q,H+c^2*b),c*r)=c*midpointAtWidth Φ ((p,b),r) := by
  let T := peakAtWidth Φ ((p,b),r)
  have hs := peak_spec Φ hΦ hloc (p:=p) hb hr
  have ha := chosen_arch (positive_arch_exists (profile_C1 Φ hΦ p) hb hs.1)
  have haf := ArchSymmetries.IsArch.affineOn ha (ψ:=fun x => Ψ (q,x)) (H:=H) (C:=C) hs.1 hc
    (fun x hx => he x (lt_of_lt_of_le hb hx.1))
  have hw : ((C+c*upper (fun x => Φ (p,x)) b T)-(C+c*lower (fun x => Φ (p,x)) b T))/2=c*r := by
    have hw := hs.2
    change (upper (fun x => Φ (p,x)) b T-lower (fun x => Φ (p,x)) b T)/2=r at hw
    calc
      _ = c*((upper (fun x => Φ (p,x)) b T-lower (fun x => Φ (p,x)) b T)/2) := by ring
      _ = c*r := by rw [hw]
  have hm := midpoint_of_arch Ψ hΨ hlocal haf hh (by nlinarith [sq_pos_of_pos hc,hs.1]) (mul_pos hc hr) hw
  rw [hm,he b hb]
  dsimp [midpointAtWidth,midpointFamily,ScalarArcs.midpoint,T]
  ring
lemma fixed_width_derivative_scaling {p : P} {q : Q} {b H c C r : ℝ}
    (hb : 0<b) (hh : 0<H+c^2*b) (hc : 0<c) (hr : 0<r)
    (he : ∀ x, 0<x → Ψ (q,H+c^2*x)=C+c*Φ (p,x)) :
    PositiveFit.n Ψ (H+c^2*b) (q,c*r)=PositiveFit.n Φ b (p,r) := by
  have hd := (PositiveFit.m_hasDerivAt Ψ hΨ hlocal (p:=q) hh (mul_pos hc hr)).comp r
    ((hasDerivAt_id r).const_mul c)
  have hs := (PositiveFit.m_hasDerivAt Φ hΦ hloc (p:=p) hb hr).const_mul c
  have hev : (fun s => PositiveFit.m Ψ (H+c^2*b) (q,c*s)) =ᶠ[𝓝 r]
      (fun s => c*PositiveFit.m Φ b (p,s)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact fixed_width_scaling Φ hΦ hloc Ψ hΨ hlocal hb hh hc hs he
  have hd' := hd.unique (hs.congr_of_eventuallyEq hev)
  apply mul_right_cancel₀ hc.ne'
  calc
    _ = c*PositiveFit.n Φ b (p,r) := by simpa only [mul_one] using hd'
    _ = PositiveFit.n Φ b (p,r)*c := mul_comm _ _
end QuinticLienard.PositiveWidth

end OAI
