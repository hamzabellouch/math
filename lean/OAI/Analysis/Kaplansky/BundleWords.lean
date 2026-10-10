import OAI.Analysis.Kaplansky.Words
import OAI.Geometry.ComplexBundle.LineStage

namespace OAI

noncomputable section

/-! Continuous bundle words and their finite-tower Hilbert realization. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ}

section WordValues

/-- One monomial restricted to the bottom level, as an actual continuous
bundle map into its single output level. -/
structure BundleWordValue (a : ℕ → LineStage K) where
  level : ℕ
  map : ∀ y, (a 0).Fiber y →ₗ[ℂ] (a level).Fiber y
  continuous_map : Continuous (fun z : TotalSpace (a 0).Model (a 0).Fiber =>
    TotalSpace.mk' (a level).Model z.proj (map z.proj z.2))

namespace BundleWordValue
variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

def identity : BundleWordValue a := ⟨0,fun _ => LinearMap.id,continuous_id⟩

def raise (W : BundleWordValue a) (i : Fin 24) : BundleWordValue a where
  level := W.level+1
  map y := ((X W.level).tuple y).forward i |>.comp (W.map y)
  continuous_map := ((X W.level).continuous_forward i).comp W.continuous_map

def lower (W : BundleWordValue a) (i : Fin 24) : BundleWordValue a := by
  obtain ⟨k,T,hT⟩ := W
  cases k with
  | zero =>
    refine ⟨0,fun _ => 0,?_⟩
    exact (Bundle.Trivialization.continuous_zeroSection ℂ (F := (a 0).Model) (E := (a 0).Fiber)).comp
      (FiberBundle.continuous_proj (a 0).Model (a 0).Fiber)
  | succ k =>
    exact ⟨k,fun y => ((X k).tuple y).reverse i |>.comp (T y),
      ((X k).continuous_reverse i).comp hT⟩

@[simp] theorem raise_level (W : BundleWordValue a) (i : Fin 24) : (raise X W i).level = W.level+1 := rfl
@[simp] theorem lower_level (W : BundleWordValue a) (i : Fin 24) : (lower X W i).level = W.level-1 := by
  obtain ⟨k,T,hT⟩ := W
  cases k <;> rfl
end BundleWordValue

def bundleWordValue {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1))) :
    List (Bool × Fin 24) → BundleWordValue a
  | [] => BundleWordValue.identity
  | (false,i)::w => (bundleWordValue X w).raise X i
  | (true,i)::w => (bundleWordValue X w).lower X i

theorem bundleWordValue_level_le {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))
    (w : List (Bool × Fin 24)) : (bundleWordValue X w).level ≤ w.length := by
  induction w with
  | nil => exact Nat.zero_le _
  | cons l w ih =>
    obtain ⟨b,i⟩ := l
    cases b <;> simp only [bundleWordValue,BundleWordValue.raise_level,
      BundleWordValue.lower_level,List.length_cons] <;> omega

end WordValues

section Evaluation

variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

def towerOperator (i : Fin 24) (y : ProjectiveProduct K) (j : ℕ) :
    EuclideanSpace ℂ (a j).Slot →L[ℂ] EuclideanSpace ℂ (a (j+1)).Slot := by
  let T : NormalizedHermitianTuple (EuclideanSpace ℂ (a j).Slot)
      (EuclideanSpace ℂ (a (j+1)).Slot) := (X j).tuple y
  exact T.operator i

theorem towerOperator_norm (i : Fin 24) (y : ProjectiveProduct K) (j : ℕ) :
    ‖towerOperator X i y j‖ ≤ 1 := by
  let T : NormalizedHermitianTuple (EuclideanSpace ℂ (a j).Slot)
      (EuclideanSpace ℂ (a (j+1)).Slot) := (X j).tuple y
  have h := T.operator_norm_le i
  exact h

theorem bundleWordValue_raise_single (W : BundleWordValue a) (i : Fin 24)
    (y : ProjectiveProduct K) (v : (a 0).Fiber y) :
    forwardShift (towerOperator X i y) (towerOperator_norm X i y)
      (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 W.level (W.map y v)) =
      lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 (W.raise X i).level ((W.raise X i).map y v) := by
  exact forwardShift_single (towerOperator X i y) (towerOperator_norm X i y) W.level (W.map y v)

theorem bundleWordValue_lower_single (W : BundleWordValue a) (i : Fin 24)
    (y : ProjectiveProduct K) (v : (a 0).Fiber y) :
    (forwardShift (towerOperator X i y) (towerOperator_norm X i y)).adjoint
      (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 W.level (W.map y v)) =
      lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 (W.lower X i).level ((W.lower X i).map y v) := by
  obtain ⟨k,T,hT⟩ := W
  cases k with
  | zero =>
    exact (forwardShift_adjoint_single_zero (towerOperator X i y)
      (towerOperator_norm X i y) (T y v)).trans
      (lp.single_zero (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 0).symm
  | succ k =>
    have hs := forwardShift_adjoint_single_succ (towerOperator X i y)
      (towerOperator_norm X i y) k (T y v)
    let U : NormalizedHermitianTuple (EuclideanSpace ℂ (a k).Slot)
      (EuclideanSpace ℂ (a (k+1)).Slot) := (X k).tuple y
    have hAdj := U.operator_adjoint i
    have hval := congrArg (fun f : EuclideanSpace ℂ (a (k+1)).Slot →L[ℂ]
      EuclideanSpace ℂ (a k).Slot => f (T y v)) hAdj
    exact hs.trans (congrArg (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 k) hval)

/-- The continuous intrinsic monomial is exactly the Hilbert-shift word
restricted to level zero, including adjoints at zero and constant words. -/
theorem bundleWordValue_shift_eval (w : List (Bool × Fin 24))
    (y : ProjectiveProduct K) (v : (a 0).Fiber y) :
    applyWord (shiftLetter (fun i j => towerOperator X i y j)
      (fun i j => towerOperator_norm X i y j)) w (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 0 v) =
      lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 (bundleWordValue X w).level ((bundleWordValue X w).map y v) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨b,i⟩ := l
    cases b with
    | false =>
      change forwardShift (towerOperator X i y) (towerOperator_norm X i y)
        (applyWord _ w (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 0 v)) = _
      rw [ih]
      exact bundleWordValue_raise_single X _ i y v
    | true =>
      change (forwardShift (towerOperator X i y) (towerOperator_norm X i y)).adjoint
        (applyWord _ w (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 0 v)) = _
      rw [ih]
      exact bundleWordValue_lower_single X _ i y v

end Evaluation

open scoped BigOperators

/-- The finite retained tower embeds into the actual Hilbert direct sum. -/
def finiteTowerHilbert (a : ℕ → LineStage K) (R : ℕ) (y : ProjectiveProduct K) :
    (LineStage.sum (fun j : Fin (R+1) => a j.val)).Fiber y →ₗ[ℂ]
      lp (fun j => (a j).Fiber y) 2 where
  toFun v := ∑ j : Fin (R+1), lp.single (E := fun j => (a j).Fiber y) 2 j.val
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y v)
  map_add' v w := by
    simp only [map_add]
    exact (Finset.sum_congr rfl (fun j _ =>
      lp.single_add (E := fun j => (a j).Fiber y) 2 j.val _ _)).trans
      (Finset.sum_add_distrib)
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ =>
      lp.single_smul (E := fun j => (a j).Fiber y) 2 j.val c _)

@[simp] theorem finiteTowerHilbert_inj (a : ℕ → LineStage K) (R : ℕ)
    (y : ProjectiveProduct K) (j : Fin (R+1)) (v : (a j.val).Fiber y) :
    finiteTowerHilbert a R y (LineStage.sumInj (fun k : Fin (R+1) => a k.val) j y v) =
      lp.single (E := fun j => (a j).Fiber y) 2 j.val v := by
  classical
  change (∑ k : Fin (R+1), lp.single (E := fun j => (a j).Fiber y) 2 k.val
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) k y
      (LineStage.sumInj (fun k : Fin (R+1) => a k.val) j y v))) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have he := LineStage.sumProj_sumInj_ne (fun k : Fin (R+1) => a k.val) hkj y v
    exact (congrArg (lp.single (E := fun j => (a j).Fiber y) 2 k.val) he).trans
      (lp.single_zero (E := fun j => (a j).Fiber y) 2 k.val)
  · simp

/-- No information is lost by embedding the finite bundle in the Hilbert tower. -/
theorem finiteTowerHilbert_injective (a : ℕ → LineStage K) (R : ℕ)
    (y : ProjectiveProduct K) : Function.Injective (finiteTowerHilbert a R y) := by
  intro v w h
  apply LineStage.sumProj_ext
  intro j
  have he (u : (LineStage.sum (fun k : Fin (R+1) => a k.val)).Fiber y) :
      finiteTowerHilbert a R y u j.val = LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y u := by
    classical
    change (∑ k : Fin (R+1), lp.single (E := fun j => (a j).Fiber y) 2 k.val
      (LineStage.sumProj (fun k : Fin (R+1) => a k.val) k y u)) j.val = _
    rw [lp.coeFn_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · exact lp.single_apply_self _ _ _
    · intro k _ hkj
      exact lp.single_apply_ne _ _ _ (fun h => hkj (Fin.ext h.symm))
    · simp
  exact (he v).symm.trans ((congrArg (fun u : lp (fun j => (a j).Fiber y) 2 => u j.val) h).trans (he w))

/-- The coordinate at every retained level is the original bundle vector. -/
theorem finiteTowerHilbert_apply (a : ℕ → LineStage K) (R : ℕ)
    (y : ProjectiveProduct K) (v : (LineStage.sum (fun k : Fin (R+1) => a k.val)).Fiber y)
    (j : Fin (R+1)) :
    finiteTowerHilbert a R y v j.val = LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y v := by
  classical
  change (∑ k : Fin (R+1), lp.single (E := fun j => (a j).Fiber y) 2 k.val
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) k y v)) j.val = _
  rw [lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · exact lp.single_apply_self _ _ _
  · intro k _ hkj
    exact lp.single_apply_ne _ _ _ (fun h => hkj (Fin.ext h.symm))
  · simp

/-- This inclusion preserves the actual Hermitian metrics, which is needed
when the operator lower bound is restricted to the finite bundle. -/
theorem finiteTowerHilbert_inner (a : ℕ → LineStage K) (R : ℕ)
    (y : ProjectiveProduct K)
    (v w : (LineStage.sum (fun k : Fin (R+1) => a k.val)).Fiber y) :
    inner ℂ (finiteTowerHilbert a R y v) (finiteTowerHilbert a R y w) = inner ℂ v w := by
  change inner ℂ (∑ j : Fin (R+1), lp.single (E := fun j => (a j).Fiber y) 2 j.val
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y v))
    (finiteTowerHilbert a R y w) = _
  simp only [sum_inner,
    lp.inner_single_left,finiteTowerHilbert_apply]
  change (∑ j : Fin (R+1), inner ℂ
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y v)
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y w)) = _
  exact (LineStage.sum_inner _ y v w).symm

def finiteTowerHilbertIsometry (a : ℕ → LineStage K) (R : ℕ) (y : ProjectiveProduct K) :
    (LineStage.sum (fun j : Fin (R+1) => a j.val)).Fiber y →ₗᵢ[ℂ]
      lp (fun j => (a j).Fiber y) 2 where
  toLinearMap := finiteTowerHilbert a R y
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (finiteTowerHilbert_inner a R y)

end Kaplansky

end

end OAI
