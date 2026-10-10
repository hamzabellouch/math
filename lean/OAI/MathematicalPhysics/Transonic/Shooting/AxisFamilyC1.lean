import OAI.MathematicalPhysics.Transonic.Shooting.FamilyQuotient
import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyJets

namespace OAI

section
noncomputable section

namespace SepticProfile.NormalizedAxis
open Filter
open scoped Topology ContDiff

def A {K : Type*} [CommRing K] (sigma x g : K) : K := (1-sigma*x)*(1-x*g^2)
def A1 {K : Type*} [CommRing K] (sigma x g : K) : K := -sigma-g^2+sigma*x*g^2
def R {K : Type*} [CommRing K] (sigma kappa c x g : K) : K :=
  -kappa*g^2-c*g^2*(kappa+3-3*g)+c*kappa*x*g^4+sigma*g+g^3-sigma*x*g^3

theorem axis_identity {K : Type*} [CommRing K] (sigma kappa c a x g dg : K)
    (ha : 4*a=kappa+3) :
    A sigma x g*(g+2*x*dg)-(1-c*x*g^2)*(kappa*(1-x*g^2)+3*(1-g)) =
      2*A sigma x g*(x*dg+2*(g-a))-x*(R sigma kappa c x g+4*A1 sigma x g*(g-a)) := by
  simp only [A,A1,R]
  linear_combination ha

def H (sigma kappa c : ℝ) (v : ℂ × ℂ) : ℂ :=
  let a : ℂ := ((kappa : ℂ)+3)/4
  (R (sigma : ℂ) (kappa : ℂ) (c : ℂ) v.1 (a+v.2)+4*A1 (sigma : ℂ) v.1 (a+v.2)*v.2) /
    (2*A (sigma : ℂ) v.1 (a+v.2))

theorem H_analytic (sigma kappa c : ℝ) : AnalyticAt ℂ (H sigma kappa c) 0 := by
  have hf (a : ℂ × ℂ) : AnalyticAt ℂ (fun v : ℂ × ℂ => v.1) a := analyticAt_fst
  have hg (a : ℂ × ℂ) : AnalyticAt ℂ (fun v : ℂ × ℂ => v.2) a := analyticAt_snd
  unfold H
  apply AnalyticAt.div
  · dsimp only [R,A1]
    fun_prop
  · dsimp only [A]
    fun_prop
  · simp [A]

theorem H_real (sigma kappa c : ℝ) (v : ℂ × ℂ) (hx : v.1.im=0) (hy : v.2.im=0) :
    (H sigma kappa c v).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  have hx' := Complex.conj_eq_iff_im.mpr hx
  have hy' := Complex.conj_eq_iff_im.mpr hy
  simp only [H,R,A,A1,map_add,map_sub,map_mul,map_pow,map_neg,map_div₀,map_ofNat,map_one,
    Complex.conj_ofReal,hx',hy']

end SepticProfile.NormalizedAxis

namespace SepticProfile.AxisFamily
open Set Metric FamilyC1 SourceFamily
open scoped NNReal

def numerator (a : Parameter) (v : ℂ × ℂ) : ℂ :=
  let b : ℂ := ((kap a:ℂ)+3)/4
  NormalizedAxis.R (sig a:ℂ) (kap a:ℂ) (3/5:ℂ) v.1 (b+v.2)+
    4*NormalizedAxis.A1 (sig a:ℂ) v.1 (b+v.2)*v.2

def denominator (a : Parameter) (v : ℂ × ℂ) : ℂ :=
  2*NormalizedAxis.A (sig a:ℂ) v.1 (((kap a:ℂ)+3)/4+v.2)

def H (a : Parameter) (v : ℂ × ℂ) : ℂ := numerator a v/denominator a v

def numeratorC1 : Data numerator := by
  unfold numerator NormalizedAxis.R NormalizedAxis.A1
  repeat' first
    | exact Data.fst
    | exact Data.snd
    | exact Data.const _ (by fun_prop)
    | apply Data.neg
    | apply Data.add
    | apply Data.sub
    | apply Data.mul

def denominatorC1 : Data denominator := by
  unfold denominator NormalizedAxis.A
  repeat' first
    | exact Data.fst
    | exact Data.snd
    | exact Data.const _ (by fun_prop)
    | apply Data.neg
    | apply Data.add
    | apply Data.sub
    | apply Data.mul

lemma denominator_zero_ne (a : Parameter) : denominator a 0 ≠ 0 := by
  norm_num [denominator,NormalizedAxis.A]

lemma H_normalizedAxis (a : Parameter) : H a=NormalizedAxis.H (sig a) (kap a) (3/5) := by
  funext v
  simp [H,numerator,denominator,NormalizedAxis.H]

theorem uniform_bounds :
    ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ≥0, ∃ M : ℝ, 0 ≤ M ∧
      (∀ a v, v ∈ closedBall 0 R → denominator a v ≠ 0) ∧
      (∀ a, DifferentiableOn ℂ (H a) (closedBall 0 R)) ∧
      (∀ a, LipschitzOnWith K (H a) (closedBall 0 R)) ∧
      Continuous (fun p : Parameter × ↥(closedBall (0:V) R) => H p.1 p.2) ∧
      ∀ a, ‖H a 0‖ ≤ M :=
  exists_uniform_quotient_bounds numeratorC1 denominatorC1 denominator_zero_ne

end SepticProfile.AxisFamily

end
end

end OAI
