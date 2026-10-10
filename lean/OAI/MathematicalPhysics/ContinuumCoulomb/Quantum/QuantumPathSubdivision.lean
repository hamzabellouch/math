import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSingletStarSpectrum

namespace OAI

/-! Rational two-edge and three-edge exchange subdivision, including the
pendant singlet partner needed by an even-length lattice path. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPathMember (even : Bool) : Fin 2 → Fin 2 := if even then ![0,0] else ![0,1]
def qmaPathAmplitude (even : Bool) (R J : ℝ) : Fin 2 → ℝ := ![R,if even then -2*R*J else 2*R*J]
def qmaPathCorrection (_R J : ℝ) {n : ℕ} : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ((3/4+3*J^2:ℝ):ℂ) • 1

theorem qmaPathSubdivision_effective {n r : ℕ} (e : Fin r) (site : Fin 2 → Fin n)
    (hsite : Function.Injective site) (even : Bool) (R J : ℝ) (hR : R ≠ 0) :
    qmaPathCorrection R J - mediatorCompression n r
      (qmaSingletStar n r e site (qmaPathMember even) (qmaPathAmplitude even R J) *
        liftedMediatorInverse n r (R^2) *
          qmaSingletStar n r e site (qmaPathMember even) (qmaPathAmplitude even R J)) =
      (J:ℂ) • sourceHeisenbergMatrix n (site 0) (site 1) := by
  have hk (a b : Fin 2) : qmaPauliKernel n (site a) (site b) =
      if a = b then (3:ℂ) • 1 else sourceHeisenbergMatrix n (site a) (site b) := by
    by_cases hab : a = b
    · subst b
      simp only [ite_true,qmaPauliKernel_self]
    · rw [ite_eq_right hab]
      exact qmaPauliKernel_eq n _ _ (fun h => hab (hsite h))
  rw [qmaSingletStar_compression]
  simp only [hk,qmaPathCorrection]
  cases even <;>
    simp [qmaPathMember,qmaPathAmplitude,Fin.sum_univ_succ] <;>
    rw [qmaHeisenberg_symm n (site 1) (site 0)] <;>
    ext s t <;>
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,Matrix.smul_apply,
      smul_eq_mul,RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal] <;>
    have hRC : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  all_goals field_simp [hRC]; ring

end ContinuumCoulomb

end

end OAI
