import Mathlib
import OAI.Analysis.CoulombIonization.Variational.RootCoulomb
import OAI.Analysis.CoulombIonization.FormDomain.WeakChangeVariables

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

def electronProjection {N : ℕ} (i : Fin N) : Configuration N →L[ℝ] Space :=
  ContinuousLinearMap.proj i

def graphComponent {N : ℕ} (s : Spins N) (k : Option (Fin N × Fin 3)) :
    fermionGraph N →L[ℂ] Lp ℂ 2 (volume : Measure (Configuration N)) :=
  (PiLp.proj 2 (fun _ : Option (Fin N × Fin 3) => Lp ℂ 2 (volume : Measure (Configuration N))) k
    ).comp ((weakGraph (sectorDirections N)).subtypeL.comp
      ((PiLp.proj 2 (fun _ : Spins N => weakGraph (sectorDirections N)) s).comp
        (fermionGraph N).subtypeL))

@[simp] lemma graphComponent_apply {N : ℕ} (s : Spins N) (k : Option (Fin N × Fin 3))
    (F : fermionGraph N) : graphComponent s k F = (F.val s).val k := rfl

def graphNuclear {N : ℕ} (s : Spins N) (i : Fin N) :
    fermionGraph N →L[ℂ] Lp ℂ 2 (volume : Measure (Configuration N)) :=
  (rootCoulombMap (sectorDirections N) (ContinuousLinearMap.proj i) (fun a => (i, a))
    (by intro a; simp [sectorDirections, direction])).comp
    ((PiLp.proj 2 (fun _ : Spins N => weakGraph (sectorDirections N)) s).comp
      (fermionGraph N).subtypeL)

def graphPair {N : ℕ} (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    fermionGraph N →L[ℂ] Lp ℂ 2 (volume : Measure (Configuration N)) :=
  (rootCoulombMap (sectorDirections N) (electronProjection i - electronProjection j)
    (fun a => (i, a)) (by
      intro a
      change direction i a i - direction i a j = EuclideanSpace.single a 1
      simp [direction, Ne.symm hij])).comp
    ((PiLp.proj 2 (fun _ : Spins N => weakGraph (sectorDirections N)) s).comp
      (fermionGraph N).subtypeL)

def coulombFormOperator (Z : ℝ) (N : ℕ) : fermionGraph N →L[ℂ] fermionGraph N :=
  (1 / 2 : ℂ) • (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
    (graphComponent s (some (i, a))).adjoint.comp (graphComponent s (some (i, a)))) -
  (Z : ℂ) • (∑ s : Spins N, ∑ i : Fin N, (graphNuclear s i).adjoint.comp (graphNuclear s i)) +
  (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
    if h : i < j then (graphPair s i j (ne_of_lt h)).adjoint.comp (graphPair s i j (ne_of_lt h)) else 0)

lemma gram_selfAdjoint {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : V →L[ℂ] H) : IsSelfAdjoint (T.adjoint.comp T) :=
  T.isPositive_adjoint_comp_self.isSelfAdjoint

lemma gram_inner {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : V →L[ℂ] H) (u : V) : (⟪u, T.adjoint.comp T u⟫_ℂ).re = ‖T u‖ ^ 2 := by
  rw [ContinuousLinearMap.comp_apply, T.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

def graphFormVector {N : ℕ} (F : fermionGraph N) : FormVector N where
  value := fun s x => (F.val s).val none x
  gradient := fun s i a x => (F.val s).val (some (i, a)) x

lemma graphNuclear_norm_sq {N : ℕ} (s : Spins N) (i : Fin N) (F : fermionGraph N) :
    ‖graphNuclear s i F‖ ^ 2 = ∫ x, ‖(graphFormVector F).value s x‖ ^ 2 / ‖x i‖ :=
  rootCoulombLp_norm_sq (sectorDirections N) (ContinuousLinearMap.proj i) (fun a => (i, a))
    (by intro a; simp [sectorDirections, direction]) (F.val s)

lemma graphPair_norm_sq {N : ℕ} (s : Spins N) (i j : Fin N) (hij : i ≠ j) (F : fermionGraph N) :
    ‖graphPair s i j hij F‖ ^ 2 = ∫ x, ‖(graphFormVector F).value s x‖ ^ 2 / ‖x i - x j‖ :=
  rootCoulombLp_norm_sq (sectorDirections N) (electronProjection i - electronProjection j)
    (fun a => (i, a)) (by
      intro a
      change direction i a i - direction i a j = EuclideanSpace.single a 1
      simp [direction, Ne.symm hij]) (F.val s)

attribute [local irreducible] graphComponent graphNuclear graphPair

lemma coulombFormOperator_selfAdjoint (Z : ℝ) (N : ℕ) : IsSelfAdjoint (coulombFormOperator Z N) := by
  unfold coulombFormOperator
  apply IsSelfAdjoint.add (R := fermionGraph N →L[ℂ] fermionGraph N)
  · apply IsSelfAdjoint.sub (R := fermionGraph N →L[ℂ] fermionGraph N)
    · apply IsSelfAdjoint.smul (R := ℂ) (A := fermionGraph N →L[ℂ] fermionGraph N)
      · norm_num [IsSelfAdjoint]
      · apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
        intro s _
        apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
        intro i _
        apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
        intro a _
        exact gram_selfAdjoint _
    · apply IsSelfAdjoint.smul (R := ℂ) (A := fermionGraph N →L[ℂ] fermionGraph N)
      · exact Complex.conj_ofReal Z
      · apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
        intro s _
        apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
        intro i _
        exact gram_selfAdjoint _
  · apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
    intro s _
    apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
    intro i _
    apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
    intro j _
    split_ifs
    · exact gram_selfAdjoint _
    · exact IsSelfAdjoint.zero _

lemma coulombFormOperator_inner (Z : ℝ) (N : ℕ) (F : fermionGraph N) :
    (⟪F, coulombFormOperator Z N F⟫_ℂ).re = formEnergy Z (graphFormVector F) := by
  have ht : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  unfold coulombFormOperator formEnergy
  simp only [ht, add_apply, sub_apply, smul_apply, sum_apply, inner_add_right, inner_sub_right,
    inner_smul_right, inner_sum, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]
  simp only [gram_inner, graphNuclear_norm_sq]
  congr 1
  · congr 1
    congr 1
    simp only [lp_norm_sq, graphComponent_apply, graphFormVector]
  · apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · rw [gram_inner, graphPair_norm_sq]
    · simp

end CoulombAtom

end

end OAI
