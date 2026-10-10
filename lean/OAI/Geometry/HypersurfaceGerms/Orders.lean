import Mathlib
import OAI.Geometry.HypersurfaceGerms.Jets
import OAI.Geometry.HypersurfaceGerms.Preparation

namespace OAI

/-! Exact orders four and five of the prepared holomorphic germs. -/

namespace AmbientMultiplicity.Preparation
noncomputable section
open Filter
open scoped Topology
open AmbientMultiplicity.Jets

lemma coordinate_vanishing (i : Fin 4) : Vanishing 1 (fun x : V 4 => x i) :=
  Vanishing.one ((proj i).analyticAt 0) rfl

lemma q1_vanishing {u w : V 4 → ℂ} (hu : Vanishing 1 u) (hw : Vanishing 1 w) :
    Vanishing 3 (fun x => q1 (u x) (w x)) := by
  have h8 : Vanishing 1 (fun x => (w x)^8) := (hw.pow 8).mono (by norm_num)
  have h2 : Vanishing 1 (fun x => (w x)^2) := (hw.pow 2).mono (by norm_num)
  convert! (((hu.sub hw).sub h8).mul ((hu.sub hw).sub (h8.const_mul 2))).mul
    (hu.sub h2) using 1

lemma psi_vanishing (s : ℂ) : Vanishing 4 (fun x : V 4 => psi (x 0) (x 3/s)) := by
  have hw : Vanishing 1 (fun x : V 4 => x 3/s) := by
    simpa only [div_eq_mul_inv] using (coordinate_vanishing 3).mul_const s⁻¹
  have hu := (coordinate_vanishing 0).add hw
  have hq : Vanishing 2 (fun x : V 4 => q2 (x 0+x 3/s) (x 3/s)) := by
    convert! ((q1_vanishing hu hw).mono (by norm_num : 2 ≤ 3)).sub (hu.pow 2) using 1
  convert! (hu.mul (hu.sub ((hw.pow 2).mono (by norm_num)))).mul hq using 1

def chartUnit0 (s : ℂ) (x : V 4) : ℂ := u0 (rescale s (chart0 s x))
def chartUnit1 (s : ℂ) (x : V 4) : ℂ := u1 (rescale s (chart1 s x))
lemma chartUnit0_analytic (s : ℂ) : AnalyticAt ℂ (chartUnit0 s) 0 := by
  have hc := ((rescale s).analyticAt _).comp (chart0_analytic s)
  have hu : AnalyticAt ℂ u0 (rescale s (chart0 s 0)) := by simpa [chart0_zero] using u0_analytic
  exact AnalyticAt.comp (f := fun x : V 4 => rescale s (chart0 s x)) hu hc
lemma chartUnit1_analytic (s : ℂ) : AnalyticAt ℂ (chartUnit1 s) 0 := by
  have hc := ((rescale s).analyticAt _).comp (chart1_analytic s)
  have hu : AnalyticAt ℂ u1 (rescale s (chart1 s 0)) := by simpa [chart1_zero] using u1_analytic
  exact AnalyticAt.comp (f := fun x : V 4 => rescale s (chart1 s x)) hu hc
lemma chartUnit0_one (s : ℂ) : chartUnit0 s 0 = 1 := by simp [chartUnit0, chart0_zero, u0_zero]
lemma chartUnit1_one (s : ℂ) : chartUnit1 s 0 = 1 := by simp [chartUnit1, chart1_zero, u1_zero]
lemma chartUnit0_remainder (s : ℂ) : Vanishing 1 (fun x => chartUnit0 s x-1) :=
  Vanishing.one ((chartUnit0_analytic s).sub analyticAt_const) (by simp [chartUnit0_one])
lemma chartUnit1_remainder (s : ℂ) : Vanishing 1 (fun x => chartUnit1 s x-1) :=
  Vanishing.one ((chartUnit1_analytic s).sub analyticAt_const) (by simp [chartUnit1_one])

def quadratic (s : ℂ) (x : V 4) : ℂ := (s^4)⁻¹*x 1*x 2
lemma quadratic_vanishing (s : ℂ) : Vanishing 2 (quadratic s) := by
  convert! ((coordinate_vanishing 1).const_mul (s^4)⁻¹).mul (coordinate_vanishing 2) using 1

def error0 (s : ℂ) (x : V 4) : ℂ := eliminated0 s x - ((x 0)^2+quadratic s x)
def error1 (s : ℂ) (x : V 4) : ℂ := eliminated1 s x - quadratic s x

lemma error0_vanishing (s : ℂ) : Vanishing 3 (error0 s) := by
  have hw : Vanishing 1 (fun x : V 4 => x 3/s) := by
    simpa only [div_eq_mul_inv] using (coordinate_vanishing 3).mul_const s⁻¹
  have hq := q1_vanishing (coordinate_vanishing 0) hw
  have hu := (quadratic_vanishing s).mul (chartUnit0_remainder s)
  apply (hq.add hu).congr
  filter_upwards [chart0_implicit s] with x hx
  dsimp only [error0, eliminated0, quadratic, chartUnit0]
  rw [hx]
  ring
lemma error1_vanishing (s : ℂ) : Vanishing 3 (error1 s) := by
  have hq := (psi_vanishing s).mono (by norm_num : 3 ≤ 4)
  have hu := (quadratic_vanishing s).mul (chartUnit1_remainder s)
  apply (hq.add hu).congr
  filter_upwards [chart1_implicit s] with x hx
  dsimp only [error1, eliminated1, quadratic, chartUnit1]
  rw [hx]
  ring

lemma eliminated0_vanishing (s : ℂ) : Vanishing 2 (eliminated0 s) := by
  apply (((coordinate_vanishing 0).pow 2).add (quadratic_vanishing s)).add
    ((error0_vanishing s).mono (by norm_num : 2 ≤ 3)) |>.congr
  exact Filter.Eventually.of_forall fun x => by dsimp [error0]; ring
lemma eliminated1_vanishing (s : ℂ) : Vanishing 2 (eliminated1 s) := by
  apply (quadratic_vanishing s).add
    ((error1_vanishing s).mono (by norm_num : 2 ≤ 3)) |>.congr
  exact Filter.Eventually.of_forall fun x => by dsimp [error1]; ring

lemma perturbation_vanishing {a b : ℕ} (ha : 4 < a) (hb : 4 < b) :
    Vanishing 6 (perturbation a b) := by
  have hya : Vanishing 5 (fun x : V 4 => (x 1)^a) :=
    ((coordinate_vanishing 1).pow a).mono (by omega)
  have hzb : Vanishing 5 (fun x : V 4 => (x 2)^b) :=
    ((coordinate_vanishing 2).pow b).mono (by omega)
  exact (coordinate_vanishing 3).mul (hya.add hzb)

 
def initial5 (s : ℂ) (x : V 4) : ℂ := x 0*quadratic s x*(quadratic s x-(x 0)^2)
def initial4 (s : ℂ) (x : V 4) : ℂ := quadratic s x*(x 0)^2
lemma initial5_vanishing (s : ℂ) : Vanishing 5 (initial5 s) := by
  exact ((coordinate_vanishing 0).mul (quadratic_vanishing s)).mul
    ((quadratic_vanishing s).sub ((coordinate_vanishing 0).pow 2))
lemma initial4_vanishing (s : ℂ) : Vanishing 4 (initial4 s) := by
  exact (quadratic_vanishing s).mul ((coordinate_vanishing 0).pow 2)

lemma f5_remainder (s : ℂ) {a b : ℕ} (ha : 4 < a) (hb : 4 < b) :
    Vanishing 6 (fun x => f5 s a b x-initial5 s x) := by
  have hmid : Vanishing 2 (fun x : V 4 => 2*quadratic s x-(x 0)^2+error0 s x) :=
    (((quadratic_vanishing s).const_mul 2).sub ((coordinate_vanishing 0).pow 2)).add
      ((error0_vanishing s).mono (by norm_num : 2 ≤ 3))
  have h := ((coordinate_vanishing 0).mul (error0_vanishing s)).mul hmid
  apply (h.add (perturbation_vanishing ha hb)).congr
  exact Filter.Eventually.of_forall fun x => by
    dsimp [f5, initial5, error0]
    ring
lemma f4_remainder (s : ℂ) {a b : ℕ} (ha : 4 < a) (hb : 4 < b) :
    Vanishing 5 (fun x => f4 s a b x-initial4 s x) := by
  have h1 := (error1_vanishing s).mul ((coordinate_vanishing 0).pow 2)
  have h2 : Vanishing 5 (fun x : V 4 => 3*x 0*(eliminated1 s x)^3) :=
    (((coordinate_vanishing 0).const_mul 3).mul ((eliminated1_vanishing s).pow 3)).mono (by norm_num)
  have h3 : Vanishing 5 (fun x : V 4 => 2*(eliminated1 s x)^5) :=
    (((eliminated1_vanishing s).pow 5).const_mul 2).mono (by norm_num)
  apply (((h1.sub h2).add h3).add
    ((perturbation_vanishing ha hb).mono (by norm_num : 5 ≤ 6))).congr
  exact Filter.Eventually.of_forall fun x => by
    dsimp [f4, initial4, error1]
    ring

lemma initial5_nonzero (s : ℂ) (hs : s ≠ 0) : iteratedFDeriv ℂ 5 (initial5 s) 0 ≠ 0 := by
  let I : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ
  let L : ℂ →L[ℂ] V 4 := ContinuousLinearMap.pi ![I, I, (2*s^4) • I, 0]
  apply nonzero_derivative_of_line (initial5_vanishing s).1 L 5 (c := 2) (by norm_num)
  intro t
  change t*((s^4)⁻¹*t*((2*s^4)*t))*((s^4)⁻¹*t*((2*s^4)*t)-t^2) = 2*t^5
  field_simp
  ring
lemma initial4_nonzero (s : ℂ) (hs : s ≠ 0) : iteratedFDeriv ℂ 4 (initial4 s) 0 ≠ 0 := by
  let I : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ
  let L : ℂ →L[ℂ] V 4 := ContinuousLinearMap.pi ![I, I, (s^4) • I, 0]
  apply nonzero_derivative_of_line (initial4_vanishing s).1 L 4 (c := 1) (by norm_num)
  intro t
  change (s^4)⁻¹*t*(s^4*t)*t^2 = 1*t^4
  field_simp

 
theorem order_five (s : ℂ) (hs : s ≠ 0) {a b : ℕ} (ha : 4 < a) (hb : 4 < b) :
    (∀ k < 5, iteratedFDeriv ℂ k (f5 s a b) 0 = 0) ∧
      iteratedFDeriv ℂ 5 (f5 s a b) 0 ≠ 0 := by
  have h := order_of_remainder (f5_analytic s a b) (initial5_vanishing s)
    (f5_remainder s ha hb) (initial5_nonzero s hs)
  exact ⟨h.1.2, h.2⟩
theorem order_four (s : ℂ) (hs : s ≠ 0) {a b : ℕ} (ha : 4 < a) (hb : 4 < b) :
    (∀ k < 4, iteratedFDeriv ℂ k (f4 s a b) 0 = 0) ∧
      iteratedFDeriv ℂ 4 (f4 s a b) 0 ≠ 0 := by
  have h := order_of_remainder (f4_analytic s a b) (initial4_vanishing s)
    (f4_remainder s ha hb) (initial4_nonzero s hs)
  exact ⟨h.1.2, h.2⟩

end
end AmbientMultiplicity.Preparation

end OAI
