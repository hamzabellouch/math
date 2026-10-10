import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.Sandwich2
import OAI.Analysis.MatrixSigning.Potential.Coordinates
import OAI.Analysis.MatrixSigning.Matrices.SandwichShiftInverse
import OAI.Analysis.MatrixSigning.Matrices.OperatorNorm

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def varianceH (A : Fin N → H d) : H d := ∑ i,sandwich (A i) (Hermitian.one : H d)

lemma varianceH_psd (A : Fin N → H d) : varianceH A ∈ psdCone d :=
  psd_sum Finset.univ _ fun index _ => sandwich_psd (A index) _ one_mem_psdCone

lemma trace_each_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i) = 1) (i : Fin N) : Hermitian.realTrace (A i) ≤ 1 := by
  rw [← htr]
  exact Finset.single_le_sum (fun j _ => realTrace_nonneg (hA j)) (Finset.mem_univ i)

lemma varianceH_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (htr : ∑ i,Hermitian.realTrace (A i) = 1) :
    varianceH A ≤ (Hermitian.one : H d) := by
  apply le_trans _ (sum_le_one A hA htr)
  apply Finset.sum_le_sum
  intro i _
  rw [sandwich_rank_one (A i) _ (hA i) (hrank i),inner_one']
  simpa only [one_smul] using scalar_mono_psd (hA i) (trace_each_le_one A hA htr i)

lemma varianceH_pos [NeZero d] (A : Fin N → H d) (_hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i) = 1) : 0 < operatorNorm (varianceH A) := by
  apply lt_of_le_of_ne (operatorNorm_nonneg _)
  intro heq
  have hzero : varianceH A = 0 := (operatorNorm_eq_zero_iff _).mp heq.symm
  have hz (i : Fin N) : A i = 0 := by
    have hle : sandwich (A i) (Hermitian.one : H d) ≤ varianceH A :=
      Finset.single_le_sum (fun j _ => psd_nonneg (sandwich_psd (A j) _ one_mem_psdCone)) (Finset.mem_univ i)
    rw [hzero] at hle
    have hh : sandwich (A i) (Hermitian.one : H d) = 0 :=
      le_antisymm hle (psd_nonneg (sandwich_psd _ _ one_mem_psdCone))
    exact (sandwich_eq_zero_iff (A i) (Hermitian.one : H d) Matrix.PosDef.one).mp hh
  have ht : (∑ i,Hermitian.realTrace (A i)) = 0 := by simp only [hz,realTrace_zero,Finset.sum_const_zero]
  linarith

lemma S_bounds_hundred (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i) = 1) {x : Coordinates N} (hx : Cube x) :
    -(100 : ℝ) • (Hermitian.one : H d) ≤ S A x ∧ S A x ≤ (100 : ℝ) • (Hermitian.one : H d) := by
  have hb := S_bounds A hA htr hx
  have hl : -(100 : ℝ) • (Hermitian.one : H d) ≤ -(Hermitian.one : H d) := by
    convert scalar_one_mono (d := d) (show (-100 : ℝ) ≤ -1 by norm_num) using 1
    first | rfl | module
  have hh : (Hermitian.one : H d) ≤ (100 : ℝ) • (Hermitian.one : H d) := by
    simpa only [one_smul] using scalar_one_mono (show (1 : ℝ) ≤ 100 by norm_num)
  exact ⟨hl.trans hb.1,hb.2.trans hh⟩

lemma feasible_norm_le_objective [NeZero d] (ε : ℝ) (hε : 0 ≤ ε) (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ Z ∈ psdCone d, η Z ∈ psdCone d) (z : Point d) (hz : z ∈ feasible S η) :
    operatorNorm S ≤ objective ε z := by
  obtain ⟨hX,hY,h₁,h₂⟩ := (feasible_iff S η z).mp hz
  obtain ⟨ht,htrX,htrY⟩ := trace_bounds_of_feasible S η hη hz
  have hiX : 0 ≤ invH z.2.1 := psd_nonneg (A := invH z.2.1) hX.inv.posSemidef
  have hiY : 0 ≤ invH z.2.2 := psd_nonneg (A := invH z.2.2) hY.inv.posSemidef
  have heX : 0 ≤ η z.2.1 := psd_nonneg (hη _ hX.posSemidef)
  have heY : 0 ≤ η z.2.2 := psd_nonneg (hη _ hY.posSemidef)
  have hu : S ≤ z.1 • (Hermitian.one : H d) := by
    apply le_trans _ h₁
    exact (le_add_of_nonneg_left hiX).trans
      (le_add_of_nonneg_right heY)
  have hl : -z.1 • (Hermitian.one : H d) ≤ S := by
    have hn : -S ≤ z.1 • (Hermitian.one : H d) := by
      apply le_trans _ h₂
      change -S ≤ invH z.2.2+(-S)+η z.2.1
      exact (le_add_of_nonneg_left hiY).trans
        (le_add_of_nonneg_right heX)
    calc
      -z.1 • (Hermitian.one : H d) = -(z.1 • Hermitian.one) := neg_smul z.1 (Hermitian.one : H d)
      _ ≤ S := by simpa only [neg_neg] using neg_le_neg hn
  have hb := operatorNorm_le_of_bounds ht hl hu
  apply hb.trans
  change z.1 ≤ z.1+ε*Hermitian.realTrace (z.2.1+z.2.2)
  rw [realTrace_add]
  exact le_add_of_nonneg_right (mul_nonneg hε (add_nonneg htrX htrY))

def jointObjective (ε lam : ℝ) (w : Coordinates N × Point d) : ℝ :=
  objective ε w.2+lam*(∑ i,psi (w.1 i))

lemma cube_zero : Cube (0 : Coordinates N) := fun _ => by norm_num

lemma S_zero (A : Fin N → H d) : S A (0 : Coordinates N) = 0 := by simp [S]

lemma initial_scalar_point [NeZero d] [NeZero N] (A : Fin N → H d) {ν : ℝ} (hν : 0 < ν)
    (hvar : varianceH A ≤ ν • (Hermitian.one : H d)) :
    ∃ z : Point d, z ∈ feasible (S A 0) (eta 384 A 0) ∧
      jointObjective (ν/d) (Real.sqrt ν/(100*N)) ((0 : Coordinates N),z) = (3931/100 : ℝ)*Real.sqrt ν := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  let a : ℝ := (20*Real.sqrt ν)⁻¹
  have ha : 0 < a := inv_pos.mpr (mul_pos (by norm_num) hs)
  have hh : -(0 : ℝ) • (Hermitian.one : H d) ≤ S A 0 := by rw [S_zero]; simp
  have hh' : S A 0 ≤ (0 : ℝ) • (Hermitian.one : H d) := by rw [S_zero]; simp
  have hb := eta_one_bound (show (0 : ℝ) ≤ 384 by norm_num) A hvar cube_zero
  refine ⟨(0+a⁻¹+(384*ν)*a,a • Hermitian.one,a • Hermitian.one),scalar_feasible _ _ hh hh' hb ha,?_⟩
  change objective (ν/d) (0+a⁻¹+(384*ν)*a,a • Hermitian.one,a • Hermitian.one)+
    (Real.sqrt ν/(100*N))*(∑ i : Fin N,psi ((0 : Coordinates N) i)) = _
  rw [scalar_objective]
  have hpsi : (∑ i : Fin N,psi ((0 : Coordinates N) i)) = N := by simp [psi]
  rw [hpsi]
  dsimp [a]
  rw [inv_inv]
  field_simp [hd,hN,ne_of_gt hs]
  nlinarith [Real.sq_sqrt hν.le]

end CurrentKS.State

end

end OAI
