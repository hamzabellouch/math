import OAI.Geometry.Convex.GeneralMahler.MatrixDeriv

namespace OAI
/-! Fixed profiles supplementing Profile.d,v,g, exact constants
and layered profiles. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.Profile
def bb : ℝ := 602/1000
def cc : ℝ := 365/1000
def r : ℝ := 22/100
def omegaP : ℝ := 46/10
def sb : ℝ := 36/10
def eta : ℝ := 22/1000
def kk : ℝ := √(bb-cc)
def kar : ℝ := 116/100
def ar : ℝ := 75/10
def tc : ℝ := 21/1000
def tr : ℝ := 43/1000
def bm : ℝ := (1+tmax)*(bb-3*eta)/(3*(3*(bb+eta)-4*cc))
def e₀ : ℝ := 256/1000
def alpha : ℝ := 226/100
def h₀ : ℝ := 5/10

def rad (x:ℝ) := bb-r^2-d x
def qu (x:ℝ) := kk-√(rad x)
def angle (x:ℝ) := omegaP*Real.arsinh (x/sb)
def uc (x:ℝ) := r*Real.cos (angle x)
def us (x:ℝ) := r*Real.sin (angle x)
def FF (x:ℝ) := cc+2*kk*qu x
def Cp (x:ℝ) := -d x+(ar-1)*deriv (deriv g) x
def Kp (x:ℝ) := d x-2*g x

def HH (w:Plane) := 4*cc+4*kk*qu w.2+2*(kk-qu w.2)*N2 qu w.1 -
    2*(N2 uc w.1*uc w.2+N2 us w.1*us w.2)
def Hh (w:Plane) := HH w+deriv (deriv v) w.2-2*kar

lemma k_pos : 0<kk := by unfold kk; apply Real.sqrt_pos.2; norm_num [bb,cc]
lemma k_sq : kk^2=bb-cc := Real.sq_sqrt (by norm_num [bb,cc])
lemma u_eq (x:ℝ) (h:0≤rad x) :
    FF x=d x+(uc x^2+us x^2+qu x^2) := by
  have hh := Real.sin_sq_add_cos_sq (angle x)
  have hi := Real.sq_sqrt h
  unfold rad at hi
  unfold FF qu uc us rad r at *
  nlinarith [k_sq]

-- Properties proved later in the scalar estimates and used in abstract layer lemmas
structure LayerOK : Prop where
  rp : ∀ x, 0<rad x
  q_test : TestF qu
  c_test : TestF uc
  s_test : TestF us
  q_even : Function.Even qu
  sq_p : ∀ x,0<N2 qu x
  v_bound : ∀ x,|deriv v x-x|≤319/1000
  bh_contact : ∀ x y,0<4*cc+2*kk*(N2 qu x+N2 qu y)-
    N2 qu x*N2 qu y - (N2 uc x*N2 uc y+N2 us x*N2 us y)
  bh_layer : ∀ w:Plane, HH w + tc*Hh w-1/2*tr*(h₀+Hh w^2/h₀)>
    2*(bb+eta+(bb+eta-kar)*tmin)+2*bm*N2 qu w.1*N2 qu w.2+2*e₀*(2*tr)^2+Hh w^2/alpha

namespace LayerOK
variable (h:LayerOK)
include h
lemma f_test : TestF FF := (TestF.const _).add ((TestF.const _).mul h.q_test)
lemma fN (x) : N2 FF x=2*cc+2*kk*N2 qu x := by
  have hh (x:ℝ) : deriv FF x=2*kk*deriv qu x :=
    ((((h.q_test.diff x).hasDerivAt).const_mul (2*kk)).const_add cc).deriv
  have ht : deriv (deriv FF) x=2*kk*deriv (deriv qu) x := by
    rw [funext hh]
    exact ((((h.q_test.der.diff x).hasDerivAt).const_mul _)).deriv
  unfold N2 N; rw [ht,hh]
  unfold FF; ring
end LayerOK
end GeneralMahler.Profile

end

end OAI
