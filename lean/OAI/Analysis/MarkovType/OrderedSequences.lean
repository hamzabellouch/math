import Mathlib.Data.Finsupp.SMul
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

abbrev C00 := ℕ →₀ ℝ

namespace C00

def basis (i : ℕ) : C00 := Finsupp.single i 1

def place {m : ℕ} (ι : Fin m → ℕ) (a : Fin m → ℝ) : C00 :=
  ∑ i, Finsupp.single (ι i) (a i)

def ofArray {m : ℕ} (a : Fin m → ℝ) : C00 := place Fin.val a

def placeLinear {m : ℕ} (ι : Fin m → ℕ) : (Fin m → ℝ) →ₗ[ℝ] C00 where
  toFun := place ι
  map_add' a b := by
    simp only [place, Pi.add_apply, Finsupp.single_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [place, Pi.smul_apply, Finset.smul_sum, Finsupp.smul_single, RingHom.id_apply]

def arrayLinear (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] C00 := placeLinear Fin.val

@[simp] theorem placeLinear_apply {m : ℕ} (ι : Fin m → ℕ) (a : Fin m → ℝ) :
    placeLinear ι a = place ι a := rfl

@[simp] theorem arrayLinear_apply {m : ℕ} (a : Fin m → ℝ) :
    arrayLinear m a = ofArray a := rfl

@[simp] theorem ofArray_apply {m : ℕ} (a : Fin m → ℝ) (i : Fin m) :
    ofArray a i.val = a i := by
  classical
  simp only [ofArray, place, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [hval]
  · simp

theorem ofArray_injective (m : ℕ) : Function.Injective (@ofArray m) := by
  intro a b h
  funext i
  simpa only [ofArray_apply] using congrArg (fun x : C00 => x i.val) h

def mergeIndex (i j : ℕ) : ℕ := if j ≤ i then j else j - 1

def mergeAt (i : ℕ) (x : C00) : C00 := Finsupp.mapDomain (mergeIndex i) x

@[simp] theorem mergeAt_zero (i : ℕ) : mergeAt i 0 = 0 := by
  simp [mergeAt]

@[simp] theorem mergeAt_single (i j : ℕ) (a : ℝ) :
    mergeAt i (Finsupp.single j a) = Finsupp.single (mergeIndex i j) a := by
  exact Finsupp.mapDomain_single

end C00

def prefixCut (x : C00) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, x i

@[simp] theorem prefixCut_zero (x : C00) : prefixCut x 0 = 0 := by
  simp [prefixCut]

theorem prefixCut_succ (x : C00) (k : ℕ) :
    prefixCut x (k + 1) = prefixCut x k + x k := by
  exact Finset.sum_range_succ (fun i => x i) k

end MarkovSuperreflexivity

end

end OAI
