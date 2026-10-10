import Mathlib
import OAI.Probability.LogConcave.Sampling.MatrixArrayAdjoint

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma arrayComponent_polySmooth {d : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (hS : 2≤Fintype.card S) {g : Point d → (S → Fin d) → ℝ}
    (hg : ContDiff ℝ (⊤:ℕ∞) g) (M : ℕ → ℝ) (hM : ∀n,0≤M n)
    (hB : ∀n y,AllSplitBound (arrayTensor (iteratedFDeriv ℝ n g y)) (M n))
    (c : S → Fin d) : PolySmooth (fun y => g y c) := by
  apply PolySmooth.of_basis_growth ((ContinuousLinearMap.proj c).contDiff.comp hg)
  intro l
  apply growth_of_bounded (hM l.length)
  intro y
  have hh := (hB l.length y).reindex (Equiv.sumComm S (Fin l.length))
  rw [←spatialTensor_eq_arrayTensor hg y] at hh
  have hb := hh.entry_le (hM _) (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
    (Sum.elim l.get c)
  change |JetCalculus.jet ((EuclideanSpace.basisFun (Fin d) ℝ) ∘ l.get)
    (List.finRange l.length) (fun y => g y c) y|≤_ at hb
  rw [←JetCalculus.jet_map,List.map_get_finRange] at hb
  exact hb

lemma centeringKernel_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hT0 : 0≤T) (hT1 : T<1) (c : Unit ⊕ Unit → Fin d) :
    PolySmooth (fun y => matrixArray d (centeringKernel hF x hr hl hT0 hT1 y) c) := by
  let R := Real.sqrt (1-T^2)
  have hR : 0<R := Real.sqrt_pos.mpr (by nlinarith)
  have hRT : R^2≤1-T^2 := (Real.sq_sqrt (by nlinarith)).le
  exact arrayComponent_polySmooth (by simp)
    ((matrixArray d).contDiff.comp (centeringKernel_smooth hF x hr hlam hl hT0 hT1))
    (fun n => ((lam:ℝ)*r)*kernelMajorant n/R^n)
    (fun n => div_nonneg (mul_nonneg (mul_nonneg lam.2 hr.le) (kernelMajorant_nonneg _)) (pow_nonneg hR.le _))
    (fun _ y => centeringKernel_iterated_split hF x hr hlam hl hR hRT hT0 hT1 y) c

end LogConcaveSampling

end

end

end

end OAI
