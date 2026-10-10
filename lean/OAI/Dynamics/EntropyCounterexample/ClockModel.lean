import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section

namespace Problem340.ClockModel

def circleHomeomorph : Circle ≃ₜ StandardClock :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype (by
    intro z
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere (0 : ClockAmbient) 1
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map])

@[simp] theorem circleHomeomorph_val (z : Circle) :
    (circleHomeomorph z).val = Complex.orthonormalBasisOneI.repr (z : ℂ) := rfl

@[simp] theorem circleHomeomorph_coord_zero (z : Circle) :
    (circleHomeomorph z).val 0 = (z : ℂ).re := by
  simp [circleHomeomorph_val, Complex.orthonormalBasisOneI_repr_apply]

@[simp] theorem circleHomeomorph_coord_one (z : Circle) :
    (circleHomeomorph z).val 1 = (z : ℂ).im := by
  simp [circleHomeomorph_val, Complex.orthonormalBasisOneI_repr_apply]

def clockHomeomorph : AddCircle (100 : ℝ) ≃ₜ StandardClock :=
  (AddCircle.homeomorphCircle (T := (100 : ℝ)) (by norm_num)).trans circleHomeomorph

def rotationAmbient (p : ℝ × ClockAmbient) : ClockAmbient :=
  Complex.orthonormalBasisOneI.repr
    ((Circle.exp (2 * Real.pi / 100 * p.1) : ℂ) *
      Complex.orthonormalBasisOneI.repr.symm p.2)

theorem contDiff_rotationAmbient : ContDiff ℝ ⊤ rotationAmbient := by
  unfold rotationAmbient
  apply Complex.orthonormalBasisOneI.repr.contDiff.comp
  apply ContDiff.mul
  · simp only [Circle.coe_exp]
    exact Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)).mul contDiff_const)
  · exact Complex.orthonormalBasisOneI.repr.symm.contDiff.comp contDiff_snd

def clockRotation (s : ℝ) (z : StandardClock) : StandardClock :=
  circleHomeomorph
    (Circle.exp (2 * Real.pi / 100 * s) * circleHomeomorph.symm z)

@[simp] theorem clockRotation_val (s : ℝ) (z : StandardClock) :
    (clockRotation s z).val = rotationAmbient (s, z.val) := rfl

theorem clockHomeomorph_add (t : AddCircle (100 : ℝ)) (s : ℝ) :
    clockHomeomorph (t + (s : AddCircle (100 : ℝ))) =
      clockRotation s (clockHomeomorph t) := by
  simp [clockHomeomorph, clockRotation, Homeomorph.trans_apply,
    AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add,
    AddCircle.toCircle_apply_mk, mul_comm]

theorem contDiff_rotationAmbient_comp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {h : E → ℝ} {x : E → ClockAmbient}
    (hh : ContDiff ℝ n h) (hx : ContDiff ℝ n x) :
    ContDiff ℝ n (fun y => rotationAmbient (h y, x y)) :=
  (contDiff_rotationAmbient.of_le le_top).comp (hh.prodMk hx)

def prependHomeomorph (q : ℕ) (S : Type*) [TopologicalSpace S] :
    S × (Fin q → S) ≃ₜ (Fin (q + 1) → S) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, fun i => x i.succ)
  left_inv p := by cases p; rfl
  right_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  continuous_invFun :=
    (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)

@[simp] theorem prependHomeomorph_zero (q : ℕ) {S : Type*} [TopologicalSpace S]
    (p : S × (Fin q → S)) : prependHomeomorph q S p 0 = p.1 := rfl

@[simp] theorem prependHomeomorph_succ (q : ℕ) {S : Type*} [TopologicalSpace S]
    (p : S × (Fin q → S)) (i : Fin q) :
    prependHomeomorph q S p i.succ = p.2 i := rfl

def productHomeomorph (q : ℕ) {S : Type*} [TopologicalSpace S]
    (eSphere : S ≃ₜ StandardSphere2) :
    (AddCircle (100 : ℝ) × (S × (Fin q → S))) ≃ₜ CounterexampleManifold q :=
  clockHomeomorph.prodCongr
    ((prependHomeomorph q S).trans (Homeomorph.piCongrRight fun _ => eSphere))

@[simp] theorem productHomeomorph_clock (q : ℕ) {S : Type*} [TopologicalSpace S]
    (eSphere : S ≃ₜ StandardSphere2)
    (x : AddCircle (100 : ℝ) × (S × (Fin q → S))) :
    (productHomeomorph q eSphere x).1 = clockHomeomorph x.1 := rfl

@[simp] theorem productHomeomorph_main (q : ℕ) {S : Type*} [TopologicalSpace S]
    (eSphere : S ≃ₜ StandardSphere2)
    (x : AddCircle (100 : ℝ) × (S × (Fin q → S))) :
    (productHomeomorph q eSphere x).2 0 = eSphere x.2.1 := rfl

@[simp] theorem productHomeomorph_register (q : ℕ) {S : Type*} [TopologicalSpace S]
    (eSphere : S ≃ₜ StandardSphere2)
    (x : AddCircle (100 : ℝ) × (S × (Fin q → S))) (i : Fin q) :
    (productHomeomorph q eSphere x).2 i.succ = eSphere (x.2.2 i) := rfl

end Problem340.ClockModel

end

end OAI
