import Mathlib
import OAI.Analysis.Conductivity.Geometry.UnitBoxAverage

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def unitSquareAverage (f : ℝ×ℝ → ℝ) : ℝ :=
  unitAverage (fun y => unitAverage (fun x => f (y,x)))

def squarePartial (f : ℝ×ℝ → ℝ) (v : ℝ×ℝ) (z : ℝ×ℝ) : ℝ := fderiv ℝ f z v

lemma continuous_squarePartial {f : ℝ×ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (v : ℝ×ℝ) : Continuous (squarePartial f v) :=
  (hf.fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const

lemma deriv_fiber_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (y : E) (x : ℝ) :
    deriv (fun t => f (y,t)) x=fderiv ℝ f (y,x) (0,1) := by
  exact (((hf.differentiable (by simp) (y,x)).hasFDerivAt).comp_hasDerivAt x
    ((hasDerivAt_const x y).prodMk (hasDerivAt_id x))).deriv

theorem smooth_unit_square_poincare {f : ℝ×ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    unitSquareAverage (fun z => (f z-unitSquareAverage f)^2) ≤
      2*unitSquareAverage (fun z => (squarePartial f (1,0) z)^2+
        (squarePartial f (0,1) z)^2) := by
  let m : ℝ → ℝ := fun y => unitAverage (fun x => f (y,x))
  let d₁ := squarePartial f (1,0)
  let d₂ := squarePartial f (0,1)
  have hm : ContDiff ℝ (↑(⊤ : ℕ∞)) m := contDiff_unitAverage hf
  have hd₁ : Continuous d₁ := continuous_squarePartial hf _
  have hd₂ : Continuous d₂ := continuous_squarePartial hf _
  have hd₁av : Continuous (fun y => unitAverage (fun x => (d₁ (y,x))^2)) :=
    continuous_unitAverage (hd₁.pow 2)
  have hd₂av : Continuous (fun y => unitAverage (fun x => (d₂ (y,x))^2)) :=
    continuous_unitAverage (hd₂.pow 2)
  have hd (y : ℝ) : deriv m y=unitAverage (fun x => d₁ (y,x)) := by
    exact fderiv_unitAverage hf y 1
  have hdm (y : ℝ) : (deriv m y)^2 ≤ unitAverage (fun x => (d₁ (y,x))^2) := by
    rw [hd]
    exact unitAverage_sq_le (hd₁.comp (continuous_const.prodMk continuous_id))
  have hvarm : unitAverage (fun y => (m y-unitAverage m)^2) ≤
      unitAverage (fun y => unitAverage (fun x => (d₁ (y,x))^2)) :=
    (unitAverage_mean_poincare hm).trans
      (unitAverage_mono ((hm.continuous_deriv (by simp)).pow 2) hd₁av (fun y _ => hdm y))
  have hvarf (y : ℝ) : unitAverage (fun x => (f (y,x)-m y)^2) ≤
      unitAverage (fun x => (d₂ (y,x))^2) := by
    have h := unitAverage_mean_poincare
      (hf.comp (contDiff_const.prodMk contDiff_id) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => f (y,x)))
    change unitAverage (fun x => (f (y,x)-m y)^2) ≤
      unitAverage (fun x => (deriv (fun t => f (y,t)) x)^2) at h
    simpa only [deriv_fiber_right hf, d₂,squarePartial] using h
  have hp (y : ℝ) : unitAverage (fun x => (f (y,x)-unitAverage m)^2) ≤
      2*unitAverage (fun x => (d₂ (y,x))^2)+2*(m y-unitAverage m)^2 := by
    have hc := hf.continuous.comp (continuous_const.prodMk continuous_id : Continuous (fun x : ℝ => (y,x)))
    have h := unitAverage_mono ((hc.sub continuous_const).pow 2)
      (((continuous_const.mul ((hc.sub continuous_const).pow 2))).add continuous_const)
      (fun x _ => show (f (y,x)-unitAverage m)^2 ≤
        2*(f (y,x)-m y)^2+2*(m y-unitAverage m)^2 by nlinarith [sq_nonneg (f (y,x)-2*m y+unitAverage m)])
    change unitAverage (fun x => (f (y,x)-unitAverage m)^2) ≤
      unitAverage (fun x => 2*(f (y,x)-m y)^2+2*(m y-unitAverage m)^2) at h
    rw [unitAverage_add (f := fun x => 2*(f (y,x)-m y)^2)
      (g := fun _ => 2*(m y-unitAverage m)^2)
      (continuous_const.mul ((hc.sub continuous_const).pow 2)) continuous_const,
      unitAverage_mul,unitAverage_const] at h
    exact h.trans (by linarith [hvarf y])
  have hi := unitAverage_mono
    (continuous_unitAverage ((hf.continuous.sub continuous_const).pow 2))
    ((continuous_const.mul hd₂av).add (continuous_const.mul ((hm.continuous.sub continuous_const).pow 2)))
    (fun y _ => hp y)
  change unitAverage (fun y => unitAverage (fun x => (f (y,x)-unitAverage m)^2)) ≤
    unitAverage (fun y => 2*unitAverage (fun x => (d₂ (y,x))^2)+2*(m y-unitAverage m)^2) at hi
  rw [unitAverage_add (f := fun y => 2*unitAverage (fun x => (d₂ (y,x))^2))
      (g := fun y => 2*(m y-unitAverage m)^2) (continuous_const.mul hd₂av)
      (continuous_const.mul ((hm.continuous.sub continuous_const).pow 2)),
    unitAverage_mul,unitAverage_mul] at hi
  have he : unitSquareAverage (fun z => (d₁ z)^2+(d₂ z)^2)=
      unitAverage (fun y => unitAverage (fun x => (d₁ (y,x))^2))+
      unitAverage (fun y => unitAverage (fun x => (d₂ (y,x))^2)) := by
    dsimp [unitSquareAverage]
    have hh (y : ℝ) := unitAverage_add
      (f := fun x => (d₁ (y,x))^2) (g := fun x => (d₂ (y,x))^2)
      (hd₁.comp (continuous_const.prodMk continuous_id) |>.pow 2)
      (hd₂.comp (continuous_const.prodMk continuous_id) |>.pow 2)
    simp_rw [hh]
    exact unitAverage_add hd₁av hd₂av
  change unitAverage (fun y => unitAverage (fun x => (f (y,x)-unitAverage m)^2)) ≤
    2*unitSquareAverage (fun z => (d₁ z)^2+(d₂ z)^2)
  rw [he]
  linarith

lemma unitSquareAverage_add {f g : ℝ×ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    unitSquareAverage (fun z => f z+g z)=unitSquareAverage f+unitSquareAverage g := by
  dsimp [unitSquareAverage]
  have hh (y : ℝ) := unitAverage_add (f := fun x => f (y,x)) (g := fun x => g (y,x))
    (hf.comp (continuous_const.prodMk continuous_id)) (hg.comp (continuous_const.prodMk continuous_id))
  simp_rw [hh]
  exact unitAverage_add (continuous_unitAverage hf) (continuous_unitAverage hg)

lemma unitSquareAverage_mul (c : ℝ) (f : ℝ×ℝ → ℝ) :
    unitSquareAverage (fun z => c*f z)=c*unitSquareAverage f := by
  simp only [unitSquareAverage,unitAverage_mul]

lemma unitSquareAverage_const (c : ℝ) : unitSquareAverage (fun _ => c)=c := by
  simp only [unitSquareAverage,unitAverage_const]

lemma unitSquareAverage_mono {f g : ℝ×ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ y∈Icc (0:ℝ) 1, ∀ x∈Icc (0:ℝ) 1, f (y,x) ≤ g (y,x)) :
    unitSquareAverage f ≤ unitSquareAverage g := by
  apply unitAverage_mono (continuous_unitAverage hf) (continuous_unitAverage hg)
  intro y hy
  exact unitAverage_mono (hf.comp (continuous_const.prodMk continuous_id))
    (hg.comp (continuous_const.prodMk continuous_id)) (fun x hx => h y hy x hx)

lemma unitSquareAverage_nonneg {f : ℝ×ℝ → ℝ}
    (h : ∀ y∈Icc (0:ℝ) 1, ∀ x∈Icc (0:ℝ) 1, 0 ≤ f (y,x)) :
    0 ≤ unitSquareAverage f :=
  unitAverage_nonneg (fun y hy => unitAverage_nonneg (fun x hx => h y hy x hx))

abbrev Box3 := (ℝ×ℝ)×ℝ

def unitCubeAverage (f : Box3 → ℝ) : ℝ :=
  unitSquareAverage (fun y => unitAverage (fun x => f (y,x)))

def cubePartial (f : Box3 → ℝ) (v : Box3) (z : Box3) : ℝ := fderiv ℝ f z v

lemma continuous_cubePartial {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (v : Box3) : Continuous (cubePartial f v) :=
  (hf.fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const

theorem smooth_unit_cube_poincare {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    unitCubeAverage (fun z => (f z-unitCubeAverage f)^2) ≤
      4*unitCubeAverage (fun z =>
        (cubePartial f ((1,0),0) z)^2+(cubePartial f ((0,1),0) z)^2+
        (cubePartial f ((0,0),1) z)^2) := by
  let m : ℝ×ℝ → ℝ := fun y => unitAverage (fun x => f (y,x))
  let d₁ := cubePartial f ((1,0),0)
  let d₂ := cubePartial f ((0,1),0)
  let d₃ := cubePartial f ((0,0),1)
  have hm : ContDiff ℝ (↑(⊤ : ℕ∞)) m := contDiff_unitAverage hf
  have hd₁ : Continuous d₁ := continuous_cubePartial hf _
  have hd₂ : Continuous d₂ := continuous_cubePartial hf _
  have hd₃ : Continuous d₃ := continuous_cubePartial hf _
  have ha₁ := continuous_unitAverage (hd₁.pow 2)
  have ha₂ := continuous_unitAverage (hd₂.pow 2)
  have ha₃ := continuous_unitAverage (hd₃.pow 2)
  have hdm₁ (y : ℝ×ℝ) : (squarePartial m (1,0) y)^2 ≤
      unitAverage (fun x => (d₁ (y,x))^2) := by
    change (fderiv ℝ m y (1,0))^2 ≤ _
    rw [fderiv_unitAverage hf]
    exact unitAverage_sq_le (hd₁.comp (continuous_const.prodMk continuous_id))
  have hdm₂ (y : ℝ×ℝ) : (squarePartial m (0,1) y)^2 ≤
      unitAverage (fun x => (d₂ (y,x))^2) := by
    change (fderiv ℝ m y (0,1))^2 ≤ _
    rw [fderiv_unitAverage hf]
    exact unitAverage_sq_le (hd₂.comp (continuous_const.prodMk continuous_id))
  have hvarm : unitSquareAverage (fun y => (m y-unitSquareAverage m)^2) ≤
      2*(unitCubeAverage (fun z => (d₁ z)^2)+unitCubeAverage (fun z => (d₂ z)^2)) := by
    have hi := unitSquareAverage_mono
      (((continuous_squarePartial hm (1,0)).pow 2).add ((continuous_squarePartial hm (0,1)).pow 2))
      (ha₁.add ha₂) (fun y _ x _ => add_le_add (hdm₁ (y,x)) (hdm₂ (y,x)))
    change unitSquareAverage (fun y => (squarePartial m (1,0) y)^2+(squarePartial m (0,1) y)^2) ≤
      unitSquareAverage (fun y => unitAverage (fun x => (d₁ (y,x))^2)+unitAverage (fun x => (d₂ (y,x))^2)) at hi
    rw [unitSquareAverage_add (f := fun y => unitAverage (fun x => (d₁ (y,x))^2))
      (g := fun y => unitAverage (fun x => (d₂ (y,x))^2)) ha₁ ha₂] at hi
    exact (smooth_unit_square_poincare hm).trans (mul_le_mul_of_nonneg_left hi (by norm_num))
  have hvarf (y : ℝ×ℝ) : unitAverage (fun x => (f (y,x)-m y)^2) ≤
      unitAverage (fun x => (d₃ (y,x))^2) := by
    have hi := unitAverage_mean_poincare
      (hf.comp (contDiff_const.prodMk contDiff_id) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => f (y,x)))
    change unitAverage (fun x => (f (y,x)-m y)^2) ≤ unitAverage (fun x => (deriv (fun t => f (y,t)) x)^2) at hi
    simpa only [deriv_fiber_right hf,d₃,cubePartial,Prod.zero_eq_mk] using hi
  have hp (y : ℝ×ℝ) : unitAverage (fun x => (f (y,x)-unitSquareAverage m)^2) ≤
      2*unitAverage (fun x => (d₃ (y,x))^2)+2*(m y-unitSquareAverage m)^2 := by
    have hc := hf.continuous.comp (continuous_const.prodMk continuous_id : Continuous (fun x : ℝ => (y,x)))
    have hi := unitAverage_mono ((hc.sub continuous_const).pow 2)
      ((continuous_const.mul ((hc.sub continuous_const).pow 2)).add continuous_const)
      (fun x _ => show (f (y,x)-unitSquareAverage m)^2 ≤
        2*(f (y,x)-m y)^2+2*(m y-unitSquareAverage m)^2 by
          nlinarith [sq_nonneg (f (y,x)-2*m y+unitSquareAverage m)])
    change unitAverage (fun x => (f (y,x)-unitSquareAverage m)^2) ≤
      unitAverage (fun x => 2*(f (y,x)-m y)^2+2*(m y-unitSquareAverage m)^2) at hi
    rw [unitAverage_add (f := fun x => 2*(f (y,x)-m y)^2)
      (g := fun _ => 2*(m y-unitSquareAverage m)^2)
      (continuous_const.mul ((hc.sub continuous_const).pow 2)) continuous_const,
      unitAverage_mul,unitAverage_const] at hi
    exact hi.trans (by linarith [hvarf y])
  have hi := unitSquareAverage_mono
    (continuous_unitAverage ((hf.continuous.sub continuous_const).pow 2))
    ((continuous_const.mul ha₃).add (continuous_const.mul ((hm.continuous.sub continuous_const).pow 2)))
    (fun y _ x _ => hp (y,x))
  change unitSquareAverage (fun y => unitAverage (fun x => (f (y,x)-unitSquareAverage m)^2)) ≤
    unitSquareAverage (fun y => 2*unitAverage (fun x => (d₃ (y,x))^2)+2*(m y-unitSquareAverage m)^2) at hi
  rw [unitSquareAverage_add (f := fun y => 2*unitAverage (fun x => (d₃ (y,x))^2))
    (g := fun y => 2*(m y-unitSquareAverage m)^2) (continuous_const.mul ha₃)
    (continuous_const.mul ((hm.continuous.sub continuous_const).pow 2)),
    unitSquareAverage_mul,unitSquareAverage_mul] at hi
  have he : unitCubeAverage (fun z => (d₁ z)^2+(d₂ z)^2+(d₃ z)^2)=
      unitCubeAverage (fun z => (d₁ z)^2)+unitCubeAverage (fun z => (d₂ z)^2)+
      unitCubeAverage (fun z => (d₃ z)^2) := by
    dsimp [unitCubeAverage]
    have hh (y : ℝ×ℝ) := unitAverage_add (f := fun x => (d₁ (y,x))^2+(d₂ (y,x))^2)
      (g := fun x => (d₃ (y,x))^2)
      ((hd₁.comp (continuous_const.prodMk continuous_id) |>.pow 2).add
        (hd₂.comp (continuous_const.prodMk continuous_id) |>.pow 2))
      (hd₃.comp (continuous_const.prodMk continuous_id) |>.pow 2)
    have hh' (y : ℝ×ℝ) := unitAverage_add (f := fun x => (d₁ (y,x))^2)
      (g := fun x => (d₂ (y,x))^2)
      (hd₁.comp (continuous_const.prodMk continuous_id) |>.pow 2)
      (hd₂.comp (continuous_const.prodMk continuous_id) |>.pow 2)
    simp_rw [hh,hh']
    rw [unitSquareAverage_add (f := fun y => unitAverage (fun x => (d₁ (y,x))^2)+unitAverage (fun x => (d₂ (y,x))^2))
      (g := fun y => unitAverage (fun x => (d₃ (y,x))^2)) (ha₁.add ha₂) ha₃,
      unitSquareAverage_add (f := fun y => unitAverage (fun x => (d₁ (y,x))^2))
      (g := fun y => unitAverage (fun x => (d₂ (y,x))^2)) ha₁ ha₂]
  have hnonneg : 0 ≤ unitCubeAverage (fun z => (d₃ z)^2) :=
    unitSquareAverage_nonneg (fun y _ x _ => unitAverage_nonneg (fun t _ => sq_nonneg _))
  change unitSquareAverage (fun y => unitAverage (fun x => (f (y,x)-unitSquareAverage m)^2)) ≤
    4*unitCubeAverage (fun z => (d₁ z)^2+(d₂ z)^2+(d₃ z)^2)
  rw [he]
  change unitSquareAverage (fun y => unitAverage (fun x => (f (y,x)-unitSquareAverage m)^2)) ≤
    2*unitCubeAverage (fun z => (d₃ z)^2)+2*unitSquareAverage (fun y => (m y-unitSquareAverage m)^2) at hi
  linarith

end ScalarConductivity

end

end OAI
