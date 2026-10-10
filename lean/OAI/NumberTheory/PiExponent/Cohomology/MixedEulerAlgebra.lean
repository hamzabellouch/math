import OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws
import OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

def LineIsoInvariant (f : LineBundle X → ℤ) : Prop :=
  ∀ L M, (L.sheaf ≅ M.sheaf) → f L = f M

def tensorDifference (L : LineBundle X) (f : LineBundle X → ℤ) : LineBundle X → ℤ :=
  fun M => f (L.tensor M) - f M

def mixedDifference : List (LineBundle X) → (LineBundle X → ℤ) → (LineBundle X → ℤ)
  | [], f => f
  | L :: ls, f => tensorDifference L (mixedDifference ls f)

@[simp] theorem mixedDifference_nil (f : LineBundle X → ℤ) : mixedDifference [] f = f := rfl
@[simp] theorem mixedDifference_cons (L : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) :
    mixedDifference (L :: ls) f = tensorDifference L (mixedDifference ls f) := rfl

def tensorTwistSwapIso (L B M : LineBundle X) :
    (L.tensor (B.tensor M)).sheaf ≅ (B.tensor (L.tensor M)).sheaf :=
  (lineTensorAssoc L B M).symm ≪≫
    moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc B L M

theorem tensorDifference_sub (L : LineBundle X) (f g : LineBundle X → ℤ) :
    tensorDifference L (f - g) = tensorDifference L f - tensorDifference L g := by
  funext M
  simp only [tensorDifference, Pi.sub_apply]
  ring

theorem mixedDifference_sub (ls : List (LineBundle X)) (f g : LineBundle X → ℤ) :
    mixedDifference ls (f - g) = mixedDifference ls f - mixedDifference ls g := by
  induction ls with
  | nil => rfl
  | cons L ls ih => rw [mixedDifference_cons, ih, tensorDifference_sub]; rfl

theorem tensorDifference_add (L : LineBundle X) (f g : LineBundle X → ℤ) :
    tensorDifference L (f + g) = tensorDifference L f + tensorDifference L g := by
  funext M
  simp only [tensorDifference, Pi.add_apply]
  ring

theorem mixedDifference_add (ls : List (LineBundle X)) (f g : LineBundle X → ℤ) :
    mixedDifference ls (f + g) = mixedDifference ls f + mixedDifference ls g := by
  induction ls with
  | nil => rfl
  | cons L ls ih => rw [mixedDifference_cons, ih, tensorDifference_add]; rfl

@[simp] theorem mixedDifference_zero (ls : List (LineBundle X)) :
    mixedDifference ls (0 : LineBundle X → ℤ) = 0 := by
  induction ls with
  | nil => rfl
  | cons L ls ih =>
      rw [mixedDifference_cons, ih]
      funext M
      exact sub_self _

theorem LineIsoInvariant.tensorDifference {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (L : LineBundle X) : LineIsoInvariant (tensorDifference L f) := by
  intro M N e
  change f (L.tensor M) - f M = f (L.tensor N) - f N
  rw [hf (L.tensor M) (L.tensor N) (moduleTensorIso (Iso.refl L.sheaf) e), hf M N e]

theorem LineIsoInvariant.mixedDifference {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (ls : List (LineBundle X)) : LineIsoInvariant (mixedDifference ls f) := by
  induction ls with
  | nil => exact hf
  | cons L ls ih => exact ih.tensorDifference L

theorem LineIsoInvariant.tensorShift {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (B : LineBundle X) : LineIsoInvariant (fun M => f (B.tensor M)) := by
  intro M N e
  exact hf _ _ (moduleTensorIso (Iso.refl B.sheaf) e)

theorem LineIsoInvariant.pullback {g : LineBundle Y → ℤ} (hg : LineIsoInvariant g)
    (i : Y ⟶ X) : LineIsoInvariant (fun M => g (M.pullback i)) := by
  intro M N e
  exact hg _ _ ((Scheme.Modules.pullback i).mapIso e)

theorem tensorDifference_commute (L B : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) :
    tensorDifference L (tensorDifference B f) = tensorDifference B (tensorDifference L f) := by
  funext M
  simp only [tensorDifference]
  rw [hf _ _ (tensorTwistSwapIso B L M)]
  ring

theorem mixedDifference_cons_commute (L : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (L :: ls) f = mixedDifference ls (tensorDifference L f) := by
  induction ls with
  | nil => rfl
  | cons B ls ih =>
      change tensorDifference L (tensorDifference B (mixedDifference ls f)) =
        tensorDifference B (mixedDifference ls (tensorDifference L f))
      rw [tensorDifference_commute L B _ (hf.mixedDifference ls)]
      exact congrArg (tensorDifference B) ih

theorem mixedDifference_tensorShift (ls : List (LineBundle X))
    (g : LineBundle X → ℤ) (hg : LineIsoInvariant g) (B M : LineBundle X) :
    mixedDifference ls (fun N => g (B.tensor N)) M = mixedDifference ls g (B.tensor M) := by
  induction ls generalizing M with
  | nil => rfl
  | cons L ls ih =>
      change mixedDifference ls (fun N => g (B.tensor N)) (L.tensor M) -
        mixedDifference ls (fun N => g (B.tensor N)) M =
          mixedDifference ls g (L.tensor (B.tensor M)) - mixedDifference ls g (B.tensor M)
      rw [ih, ih, (hg.mixedDifference ls) _ _ (tensorTwistSwapIso B L M)]

theorem mixedDifference_pullback (ls : List (LineBundle X)) (i : Y ⟶ X)
    (g : LineBundle Y → ℤ) (hg : LineIsoInvariant g) (M : LineBundle X) :
    mixedDifference ls (fun N => g (N.pullback i)) M =
      mixedDifference (ls.map (fun L => L.pullback i)) g (M.pullback i) := by
  induction ls generalizing M with
  | nil => rfl
  | cons L ls ih =>
      change mixedDifference ls (fun N => g (N.pullback i)) (L.tensor M) -
        mixedDifference ls (fun N => g (N.pullback i)) M =
          mixedDifference (ls.map (fun N => N.pullback i)) g
            ((L.pullback i).tensor (M.pullback i)) -
          mixedDifference (ls.map (fun N => N.pullback i)) g (M.pullback i)
      rw [ih, ih, (hg.mixedDifference _) _ _ (PiExponentSeshadri.PullbackTensor.iso i L M)]

theorem mixedDifference_append (ls ks : List (LineBundle X)) (f : LineBundle X → ℤ) :
    mixedDifference (ls ++ ks) f = mixedDifference ls (mixedDifference ks f) := by
  induction ls with
  | nil => rfl
  | cons L ls ih => simp only [List.cons_append, mixedDifference_cons, ih]

theorem tensorDifference_tensor (A B : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) :
    tensorDifference (A.tensor B) f =
      tensorDifference A f + tensorDifference B f + mixedDifference [A,B] f := by
  funext M
  simp only [tensorDifference, mixedDifference, Pi.add_apply]
  rw [hf ((A.tensor B).tensor M) (A.tensor (B.tensor M)) (lineTensorAssoc A B M),
    hf _ _ (tensorTwistSwapIso A B M)]
  ring

theorem mixedDifference_tensor_cons (A B : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (A.tensor B :: ls) f =
      mixedDifference (A :: ls) f + mixedDifference (B :: ls) f +
        mixedDifference (A :: B :: ls) f :=
  tensorDifference_tensor A B (mixedDifference ls f) (hf.mixedDifference ls)

theorem mixedDifference_tensor_cons_of_next_eq_zero (A B : LineBundle X)
    (ls : List (LineBundle X)) (f : LineBundle X → ℤ) (hf : LineIsoInvariant f)
    (hzero : mixedDifference (A :: B :: ls) f = 0) :
    mixedDifference (A.tensor B :: ls) f =
      mixedDifference (A :: ls) f + mixedDifference (B :: ls) f := by
  rw [mixedDifference_tensor_cons A B ls f hf, hzero, add_zero]

end
end PiExponent.NumericalAmpleness

end OAI
