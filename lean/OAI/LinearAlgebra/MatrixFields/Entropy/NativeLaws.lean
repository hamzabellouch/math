import Mathlib
import OAI.LinearAlgebra.MatrixFields.Extraction.ComplexRationalTypes
import OAI.LinearAlgebra.MatrixFields.Parameters.NativeCapacity

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldNativeCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators

def indexedRationalLaw (support : List Shape) (p : Shape → ℚ)
    (hpos : ∀ u ∈ support, 0 ≤ p u) (htotal : (support.map p).sum = 1) :
    RationalLaw (Fin support.length) where
  mass j := p (support.get j)
  nonneg j := hpos _ (List.get_mem _ _)
  total := by
    simp only [List.get_eq_getElem]
    rw [Fin.sum_univ_fun_getElem]
    exact htotal

def stageASplitLaw (g : Shape) (hg : g ∈ positiveInitial) :
    FiniteLaw (Fin (below g).length) :=
  (indexedRationalLaw (below g) (stageALaw g)
    (fun u hu => (stageALaw_positive g u hu).le) (stageALaw_normalized g hg)).toFiniteLaw

def stageBSplitLaw (t : Shape) (ht : t ∈ positiveSecond) :
    FiniteLaw (Fin (below t).length) :=
  (indexedRationalLaw (below t) (stageBLaw t)
    (fun u hu => (stageBLaw_positive t u hu).le) (stageBLaw_normalized t ht)).toFiniteLaw

def indexedMarginalLaw (support : List Shape) (p : Shape → ℚ)
    (hpos : ∀ u ∈ support, 0 ≤ p u) (htotal : (support.map p).sum = 1)
    (side : Fin 3) (hbound : ∀ u ∈ support, u side < 17) : FiniteLaw (Fin 17) :=
  (indexedRationalLaw support p hpos htotal).toFiniteLaw.map
    (fun j => ⟨support.get j side, hbound _ (List.get_mem _ _)⟩)

theorem indexedMarginalLaw_mass (support : List Shape) (p : Shape → ℚ)
    (hpos : ∀ u ∈ support, 0 ≤ p u) (htotal : (support.map p).sum = 1)
    (side : Fin 3) (hbound : ∀ u ∈ support, u side < 17) (k : Fin 17) :
    (indexedMarginalLaw support p hpos htotal side hbound).mass k =
      marginal support (fun u => (p u : ℝ)) side k := by
  simp only [indexedMarginalLaw, FiniteLaw.map_mass, RationalLaw.toFiniteLaw_mass,
    indexedRationalLaw, Fin.ext_iff, marginal, List.get_eq_getElem]
  exact Fin.sum_univ_fun_getElem support (fun u : Shape => if u side = k.val then (p u : ℝ) else 0)

def stageAMarginalLaw (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) :
    FiniteLaw (Fin 17) :=
  indexedMarginalLaw (below g) (stageALaw g)
    (fun u hu => (stageALaw_positive g u hu).le) (stageALaw_normalized g hg) side
    (fun _ hu => Nat.lt_succ_of_le ((below_le hu side).trans
      ((positiveInitial_shape_spec g hg).1 side)))

def stageBMarginalLaw (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) :
    FiniteLaw (Fin 17) :=
  indexedMarginalLaw (below t) (stageBLaw t)
    (fun u hu => (stageBLaw_positive t u hu).le) (stageBLaw_normalized t ht) side
    (fun _ hu => Nat.lt_succ_of_le ((below_le hu side).trans
      ((positiveSecond_shape_spec t ht).1 side)))

theorem stageACapacity_first_entropy (g : Shape) (hg : g ∈ positiveInitial) :
    stageACapacity g 0 = finiteEntropy (stageAMarginalLaw g hg 0).mass := by
  rw [stageACapacity, nativeCapacity_first]
  simp only [Equiv.refl_apply]
  have hm : (stageAMarginalLaw g hg 0).mass =
      marginal (below g) (fun u => (stageALaw g u : ℝ)) 0 := by
    funext k
    exact indexedMarginalLaw_mass _ _ _ _ _ _ k
  rw [← hm]
  exact homogeneousEntropy_normalized _ (stageAMarginalLaw g hg 0).total

theorem stageBCapacity_first_entropy (t : Shape) (ht : t ∈ positiveSecond) :
    stageBCapacity t 0 =
      finiteEntropy (stageBMarginalLaw t ht (stageBPriority t 0)).mass := by
  rw [stageBCapacity, nativeCapacity_first]
  have hm : (stageBMarginalLaw t ht (stageBPriority t 0)).mass =
      marginal (below t) (fun u => (stageBLaw t u : ℝ)) (stageBPriority t 0) := by
    funext k
    exact indexedMarginalLaw_mass _ _ _ _ _ _ k
  rw [← hm]
  exact homogeneousEntropy_normalized _ (stageBMarginalLaw t ht (stageBPriority t 0)).total

def halfFiniteLaw (t : Shape) (ht : t ∈ shapes 8) (side : Fin 3) : FiniteLaw PairSlot where
  mass a := (halfLaw t side a : ℝ)
  nonneg a := by exact_mod_cast halfLaw_nonnegative t side a
  total := by exact_mod_cast halfLaw_normalized t ht side

def littleFiniteLaw (t u : Shape) (side : Fin 3) : FiniteLaw (Fin 6) where
  mass a := (littleLaw t u side a : ℝ)
  nonneg a := by exact_mod_cast littleLaw_nonnegative t u side a
  total := by exact_mod_cast littleLaw_normalized t u side

private theorem list_rat_cast_inline_MatrixMultiplication_AllFieldNativeLaws {I : Type*} (xs : List I) (f : I → ℚ) :
    ((xs.map f).sum : ℝ) = (xs.map fun i => (f i : ℝ)).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih => simp [ih]

theorem pairLaw_total {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (q : Shape → A → ℝ)
    (hleft : ∀ u ∈ support, ∑ a, q u a = 1)
    (hright : ∀ u ∈ support, ∑ a, q (complement s u) a = 1) :
    (∑ ij : A × A, pairLaw support s p q ij) = (support.map p).sum := by
  unfold pairLaw
  induction support with
  | nil => simp
  | cons u us ih =>
      have hl := hleft u (by simp)
      have hr := hright u (by simp)
      have hh : (∑ ij : A × A, p u * q u ij.1 * q (complement s u) ij.2) = p u := by
        simp [Fintype.sum_prod_type, ← Finset.mul_sum, hl, hr]
      have ht := ih (fun v hv => hleft v (by simp [hv]))
        (fun v hv => hright v (by simp [hv]))
      simpa only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, hh] using
        congrArg (fun x => p u + x) ht

def pairFiniteLaw {A : Type*} [Fintype A] (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (q : Shape → A → ℝ)
    (hpos : ∀ u ∈ support, 0 ≤ p u) (htotal : (support.map p).sum = 1)
    (hqpos : ∀ u a, 0 ≤ q u a)
    (hleft : ∀ u ∈ support, ∑ a, q u a = 1)
    (hright : ∀ u ∈ support, ∑ a, q (complement s u) a = 1) : FiniteLaw (A × A) where
  mass := pairLaw support s p q
  nonneg ij := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (mul_nonneg (hpos u hu) (hqpos u ij.1))
      (hqpos (complement s u) ij.2)
  total := (pairLaw_total support s p q hleft hright).trans htotal

def stageAPairLaw (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) :
    FiniteLaw (PairSlot × PairSlot) :=
  pairFiniteLaw (below g) g (fun u => (stageALaw g u : ℝ))
    (fun u a => (halfLaw u side a : ℝ))
    (fun u hu => Rat.cast_nonneg.mpr (stageALaw_positive g u hu).le)
    (by rw [← list_rat_cast_inline_MatrixMultiplication_AllFieldNativeLaws, stageALaw_normalized g hg]; norm_num)
    (fun u a => Rat.cast_nonneg.mpr (halfLaw_nonnegative u side a))
    (fun u hu => (halfFiniteLaw u (stageA_children_size g hg u hu) side).total)
    (fun u hu => (halfFiniteLaw (complement g u)
      (stageA_children_size g hg _ (stageA_support_complement g hg u hu).1) side).total)

def stageBPairLaw (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) :
    FiniteLaw (Fin 6 × Fin 6) :=
  pairFiniteLaw (below t) t (fun u => (stageBLaw t u : ℝ))
    (fun u a => (littleLaw t u side a : ℝ))
    (fun u hu => Rat.cast_nonneg.mpr (stageBLaw_positive t u hu).le)
    (by rw [← list_rat_cast_inline_MatrixMultiplication_AllFieldNativeLaws, stageBLaw_normalized t ht]; norm_num)
    (fun u a => Rat.cast_nonneg.mpr (littleLaw_nonnegative t u side a))
    (fun u _ => (littleFiniteLaw t u side).total)
    (fun u _ => (littleFiniteLaw t (complement t u) side).total)

theorem stageACapacity_sharing (g : Shape) (hg : g ∈ positiveInitial)
    (i : Fin 3) (hi : i ≠ 0) :
    stageACapacity g i = finiteEntropy (stageAPairLaw g hg i).mass -
      2 * groupedEntropy (below g) (fun u => (stageALaw g u : ℝ))
        (Equiv.refl (Fin 3)) i (fun u a => (halfLaw u i a : ℝ)) := by
  rw [stageACapacity, nativeCapacity_sharing _ _ _ _ _ i hi]
  congr 1
  exact homogeneousEntropy_normalized _ (stageAPairLaw g hg i).total

theorem stageBCapacity_sharing (t : Shape) (ht : t ∈ positiveSecond)
    (i : Fin 3) (hi : i ≠ 0) :
    stageBCapacity t i = finiteEntropy (stageBPairLaw t ht (stageBPriority t i)).mass -
      2 * groupedEntropy (below t) (fun u => (stageBLaw t u : ℝ))
        (stageBPriority t) i (fun u a => (littleLaw t u (stageBPriority t i) a : ℝ)) := by
  rw [stageBCapacity, nativeCapacity_sharing _ _ _ _ _ i hi]
  congr 1
  exact homogeneousEntropy_normalized _ (stageBPairLaw t ht (stageBPriority t i)).total

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
