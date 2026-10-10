import OAI.Analysis.KadisonKastler.TwoStateCornerCocycle
import OAI.Analysis.KadisonKastler.ModularActionVector

namespace OAI

/-! # Strong-star continuity of the two-state corner cocycle -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (m : ModularSpectralResolution (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ))

def twoStateFirstColumnVector (j : Fin 2) (x : H) : TwoStateMatrixHilbert H H :=
  WithLp.toLp 2 (tupleSingle j x, 0)

theorem twoStateMatrixEquiv_firstEntry (a : CStarMatrix (Fin 2) (Fin 2) (Algebra M))
    (i j : Fin 2) (x : H) :
    ((twoStateMatrixEquiv M a).val (twoStateFirstColumnVector j x)).fst i =
      (a i j).val x := by
  rw [twoStateMatrixEquiv_coe]
  change matrixOperatorHom M a (tupleSingle j x) i = _
  fin_cases j <;> simp [matrixOperatorHom_apply, hilbertMatrix_apply, tupleSingle_apply,
    CStarMatrix.map_apply, Fin.sum_univ_two]

theorem twoStateMatrixAut_entry_continuous (a : CStarMatrix (Fin 2) (Fin 2) (Algebra M))
    (i j : Fin 2) (x : H) :
    Continuous (fun t : ℝ => (twoStateMatrixAut M Ω ξ m (Multiplicative.ofAdd t) a i j).val x) := by
  have he (t : Multiplicative ℝ) : twoStateMatrixEquiv M (twoStateMatrixAut M Ω ξ m t a) =
      modularAlgebraAut m t (twoStateMatrixEquiv M a) := by
    change (twoStateMatrixEquiv M) ((twoStateMatrixEquiv M).symm _) = _
    exact (twoStateMatrixEquiv M).apply_symm_apply _
  have hp : Continuous (fun v : TwoStateMatrixHilbert H H => v.fst i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => H) i).comp (by fun_prop)
  have h := hp.comp (modularAlgebraAut_strongContinuous m (twoStateMatrixEquiv M a)
    (twoStateFirstColumnVector j x))
  convert h using 1
  funext t
  change (twoStateMatrixAut M Ω ξ m (Multiplicative.ofAdd t) a i j).val x =
    ((modularAlgebraAut m (Multiplicative.ofAdd t) (twoStateMatrixEquiv M a)).val
      (twoStateFirstColumnVector j x)).fst i
  rw [← he, twoStateMatrixEquiv_firstEntry]

theorem twoStateCornerCocycle_continuous (x : H) :
    Continuous (fun t : ℝ => (twoStateCornerCocycle M Ω ξ m (Multiplicative.ofAdd t) :
      Algebra M).val x) :=
  twoStateMatrixAut_entry_continuous M Ω ξ m (matrixSlot 1 0 1) 1 0 x

theorem twoStateCornerCocycle_star_continuous (x : H) :
    Continuous (fun t : ℝ => (star (twoStateCornerCocycle M Ω ξ m (Multiplicative.ofAdd t) :
      Algebra M)).val x) := by
  have he (t : Multiplicative ℝ) :
      star (twoStateCornerCocycle M Ω ξ m t : Algebra M) =
        twoStateMatrixAut M Ω ξ m t (matrixSlot 0 1 1) 0 1 := by
    change star (twoStateMatrixAut M Ω ξ m t (matrixSlot 1 0 1) 1 0) = _
    have h := congrArg (fun a : CStarMatrix (Fin 2) (Fin 2) (Algebra M) => a 0 1)
      (map_star (twoStateMatrixAut M Ω ξ m t) (matrixSlot 1 0 1))
    rw [matrixSlot_star, star_one] at h
    exact h.symm
  simp_rw [he]
  exact twoStateMatrixAut_entry_continuous M Ω ξ m (matrixSlot 0 1 1) 0 1 x

end

end KadisonKastler

end OAI
