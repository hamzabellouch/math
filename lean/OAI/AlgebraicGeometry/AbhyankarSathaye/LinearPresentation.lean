import OAI.AlgebraicGeometry.AbhyankarSathaye.Lifting
import OAI.AlgebraicGeometry.AbhyankarSathaye.LinearElimination

namespace OAI

/-!
# The intermediate linear presentation

The relation `h * G - y * U = x` has parameter `α * U + β * G`.
The remaining compatible equations generate the principal ideal `(W - W₀)`.
-/

noncomputable section
namespace AbhyankarSathaye.LinearPresentation
open MvPolynomial

variable {B : Type*} [CommRing B]

def relation (h x y : B) : MvPolynomial (Fin 2) B := C h*X 1-C y*X 0-C x
def ideal (h x y : B) : Ideal (MvPolynomial (Fin 2) B) := Ideal.span {relation h x y}
abbrev A (h x y : B) := MvPolynomial (Fin 2) B ⧸ ideal h x y
def qmap (h x y : B) : MvPolynomial (Fin 2) B →ₐ[B] A h x y :=
  Ideal.Quotient.mkₐ B (ideal h x y)
def qvar (h x y : B) (i : Fin 2) : A h x y := qmap h x y (X i)
def coeff (h x y : B) : B →+* A h x y := algebraMap B _

theorem linear_relation (h x y : B) :
    coeff h x y h*qvar h x y 1-coeff h x y y*qvar h x y 0 = coeff h x y x := by
  have hz : qmap h x y (relation h x y) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  apply sub_eq_zero.mp
  simpa [relation, qvar, coeff] using hz

def values (h x y α β : B) : Fin 2 → Polynomial B :=
  ![Lifting.polyU h x β, Lifting.polyG x y α]

def forward (h x y α β : B) (hb : α*h+β*y = 1) : A h x y →ₐ[B] Polynomial B := by
  let ev : MvPolynomial (Fin 2) B →ₐ[B] Polynomial B := aeval (values h x y α β)
  have hb' : Polynomial.C α*Polynomial.C h+Polynomial.C β*Polynomial.C y = 1 := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hb
  have he : ev (relation h x y) = 0 := by
    simpa [ev, values, relation, Lifting.polyU, Lifting.polyG,
      Polynomial.algebraMap_eq, inverseU, inverseG] using
      sub_eq_zero.mpr (linear_parameter_relation (Polynomial.C h) (Polynomial.C x)
        (Polynomial.C y) (Polynomial.C α) (Polynomial.C β) Polynomial.X hb')
  have hi : ideal h x y ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact he
  exact Ideal.Quotient.liftₐ _ ev (fun z hz => hi hz)

@[simp] theorem forward_qvar (h x y α β : B) (hb) (i : Fin 2) :
    forward h x y α β hb (qvar h x y i) = values h x y α β i := by
  change (aeval (values h x y α β) : MvPolynomial (Fin 2) B →ₐ[B] Polynomial B) (X i) = _
  exact aeval_X _ _

def backward (h x y α β : B) : Polynomial B →ₐ[B] A h x y :=
  Polynomial.aeval (coeff h x y α*qvar h x y 0+coeff h x y β*qvar h x y 1)

theorem forward_backward (h x y α β : B) (hb) :
    (forward h x y α β hb).comp (backward h x y α β) = AlgHom.id B _ := by
  apply Polynomial.algHom_ext
  have hb' : Polynomial.C α*Polynomial.C h+Polynomial.C β*Polynomial.C y = 1 := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hb
  simpa [backward, coeff, values, Lifting.polyU, Lifting.polyG, inverseU, inverseG,
    Polynomial.algebraMap_eq] using
    linear_parameter_inverse (Polynomial.C h) (Polynomial.C x) (Polynomial.C y)
      (Polynomial.C α) (Polynomial.C β) Polynomial.X hb'

theorem backward_forward (h x y α β : B) (hb) :
    (backward h x y α β).comp (forward h x y α β hb) = AlgHom.id B _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hb' : coeff h x y α*coeff h x y h+coeff h x y β*coeff h x y y = 1 := by
    simpa using congrArg (coeff h x y) hb
  change backward h x y α β (forward h x y α β hb (qvar h x y i)) = qvar h x y i
  rw [forward_qvar]
  fin_cases i
  · simpa [backward, values, Lifting.polyU, inverseU, coeff] using
      recover_U (coeff h x y h) (coeff h x y x) (coeff h x y y)
        (coeff h x y α) (coeff h x y β) (qvar h x y 0) (qvar h x y 1)
        hb' (linear_relation h x y)
  · simpa [backward, values, Lifting.polyG, inverseG, coeff] using
      recover_G (coeff h x y h) (coeff h x y x) (coeff h x y y)
        (coeff h x y α) (coeff h x y β) (qvar h x y 0) (qvar h x y 1)
        hb' (linear_relation h x y)

def equivalence (h x y α β : B) (hb : α*h+β*y = 1) : A h x y ≃ₐ[B] Polynomial B :=
  AlgEquiv.ofAlgHom (forward h x y α β hb) (backward h x y α β)
    (forward_backward h x y α β hb) (backward_forward h x y α β hb)

def a (h x y : B) : A h x y := coeff h x y y+(qvar h x y 0)^2
def b (h x y s : B) : A h x y := coeff h x y s-coeff h x y h*(qvar h x y 1)^2+
  2*qvar h x y 0*coeff h x y y*qvar h x y 1
def r (h x y α β : B) : A h x y := coeff h x y α*(1+coeff h x y β*coeff h x y y)
def q (h x y β : B) : A h x y := (coeff h x y β)^2
def W0 (h x y s α β : B) : A h x y := r h x y α β*a h x y+q h x y β*b h x y s

theorem compatible (h x y s : B) (hc : x^2+y^3 = h*s) :
    (coeff h x y y)^2*a h x y = coeff h x y h*b h x y s := by
  have hc' : (coeff h x y x)^2+(coeff h x y y)^3 = coeff h x y h*coeff h x y s := by
    simpa using congrArg (coeff h x y) hc
  exact compatibility _ _ _ _ _ _ hc' (linear_relation h x y)

theorem bezout_squared (h x y α β : B) (hb : α*h+β*y = 1) :
    r h x y α β*coeff h x y h+q h x y β*(coeff h x y y)^2 = 1 := by
  have hb' : coeff h x y α*coeff h x y h+coeff h x y β*coeff h x y y = 1 := by
    simpa using congrArg (coeff h x y) hb
  exact squared_bezout _ _ _ _ hb'

theorem W_ideal (h x y s α β : B) (hc : x^2+y^3 = h*s) (hb : α*h+β*y = 1) :
    Ideal.span ({Polynomial.C (coeff h x y h)*Polynomial.X-Polynomial.C (a h x y),
      Polynomial.C ((coeff h x y y)^2)*Polynomial.X-Polynomial.C (b h x y s)} :
      Set (Polynomial (A h x y))) = Ideal.span {Polynomial.X-Polynomial.C (W0 h x y s α β)} := by
  have hc' := congrArg (Polynomial.C : A h x y →+* Polynomial (A h x y)) (compatible h x y s hc)
  have hb' := congrArg (Polynomial.C : A h x y →+* Polynomial (A h x y)) (bezout_squared h x y α β hb)
  simp only [map_mul, map_add, map_one] at hc' hb'
  simpa only [W0, map_add, map_mul] using
    linear_ideal (Polynomial.C (coeff h x y h)) (Polynomial.C ((coeff h x y y)^2))
      (Polynomial.C (a h x y)) (Polynomial.C (b h x y s))
      (Polynomial.C (r h x y α β)) (Polynomial.C (q h x y β)) Polynomial.X hc' hb'

end AbhyankarSathaye.LinearPresentation

end

end OAI
