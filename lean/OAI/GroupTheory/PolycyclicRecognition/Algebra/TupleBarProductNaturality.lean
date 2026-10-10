import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleBarInsertion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianMultilinearNaturality

namespace OAI

/-! # Naturality of the integral higher bar product -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A B : Type}

def tupleBarMap (f : A → B) (n : ℕ) :
    ((Fin n → A) →₀ ℤ) →ₗ[ℤ] ((Fin n → B) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun v => f ∘ v)

@[simp] theorem tupleBarMap_single (f : A → B) (n : ℕ) (v : Fin n → A) (c : ℤ) :
    tupleBarMap f n (Finsupp.single v c) = Finsupp.single (f ∘ v) c := by
  simp [tupleBarMap]

theorem tupleBarMap_insert (f : A → B) (n : ℕ) (a : A) (z : (Fin n → A) →₀ ℤ) :
    tupleBarMap f (n + 1) (tupleBarInsert n a z) =
      tupleBarInsert n (f a) (tupleBarMap f n z) := by
  have hi (i : Fin (n + 1)) (v : Fin n → A) :
      f ∘ (i.insertNth a v) = i.insertNth (f a) (f ∘ v) := by
    funext k
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩ <;> simp
  have hs (v : Fin n → A) : tupleBarMap f (n + 1) (tupleBarInsert n a (Finsupp.single v 1)) =
      tupleBarInsert n (f a) (tupleBarMap f n (Finsupp.single v 1)) := by
    simp only [tupleBarInsert, LinearMap.sum_apply, LinearMap.smul_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, map_sum, map_smul,
      tupleBarMap_single, hi]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v c =>
    rw [← Finsupp.smul_single_one v c]
    simpa only [map_smul] using congrArg (c • ·) (hs v)

theorem tupleBarProduct_natural (f : A → B) {n : ℕ} (v : Fin n → A) :
    tupleBarMap f n (tupleBarProduct v) = tupleBarProduct (f ∘ v) := by
  induction n with
  | zero =>
    have hz {X : Type} (w : Fin 0 → X) : tupleBarProduct w = Finsupp.single w 1 := by
      apply tupleBarToList_injective 0
      simp only [tupleBarProduct_toList, tupleBarToList_single, List.ofFn_zero, listBarProduct]
    rw [hz, tupleBarMap_single, hz]
  | succ n ih =>
    obtain ⟨a, w, rfl⟩ := Fin.exists_cons v
    have hc : f ∘ Fin.cons a w = Fin.cons (f a) (f ∘ w) := by
      ext i; cases i using Fin.cases <;> rfl
    rw [hc, tupleBarProduct_cons, tupleBarMap_insert, ih, tupleBarProduct_cons]

variable [CommGroup A] [CommGroup B]

theorem trivialBar_chainsMap_eq (f : A →* B) (n : ℕ) (z : (Fin n → A) →₀ ℤ) :
    (groupHomology.chainsMap f (integralTrivialCoefficientMap f)).f n z =
      tupleBarMap f n z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v c =>
    rw [groupHomology.chainsMap_f_single, tupleBarMap_single]
    rfl

theorem tupleBarProductClass_natural (f : A →* B) {n : ℕ} (v : Fin (n + 1) → A) :
    groupHomology.map f (integralTrivialCoefficientMap f) (n + 1) (tupleBarProductClass v) =
      tupleBarProductClass (f ∘ v) := by
  have hp := congrArg (fun E => E.hom (tupleBarProductCycle v))
    (groupHomology.π_map f (integralTrivialCoefficientMap f) (n + 1))
  change groupHomology.map f (integralTrivialCoefficientMap f) (n + 1)
      (tupleBarProductClass v) =
    groupHomology.π (integralTrivialCoefficient B) (n + 1)
      (groupHomology.cyclesMap f (integralTrivialCoefficientMap f) (n + 1)
        (tupleBarProductCycle v)) at hp
  rw [hp, tupleBarProductClass]
  apply congrArg (groupHomology.π (integralTrivialCoefficient B) (n + 1))
  apply (ModuleCat.mono_iff_injective
    (groupHomology.iCycles (integralTrivialCoefficient B) (n + 1))).mp inferInstance
  have hc := congrArg (fun E => E.hom (tupleBarProductCycle v))
    (HomologicalComplex.cyclesMap_i
      (groupHomology.chainsMap f (integralTrivialCoefficientMap f)) (n + 1))
  change groupHomology.iCycles (integralTrivialCoefficient B) (n + 1)
      (groupHomology.cyclesMap f (integralTrivialCoefficientMap f) (n + 1)
        (tupleBarProductCycle v)) =
    (groupHomology.chainsMap f (integralTrivialCoefficientMap f)).f (n + 1)
      (groupHomology.iCycles (integralTrivialCoefficient A) (n + 1)
        (tupleBarProductCycle v)) at hc
  rw [hc, tupleBarProductCycle_val, tupleBarProductCycle_val, trivialBar_chainsMap_eq]
  exact tupleBarProduct_natural f v

end PolycyclicRecognition

end

end OAI
