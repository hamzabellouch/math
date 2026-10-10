import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSingletStar

namespace OAI

/-! Exact four-terminal crossing gadget and its perimeter counterterms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaCrossingMember : Fin 4 → Fin 2 := ![0,0,1,1]

def qmaCrossingAmplitude (R J K : ℝ) : Fin 4 → ℝ := ![R,R,2*R*J,2*R*K]

def qmaCrossingCorrection {n : ℕ} (site : Fin 4 → Fin n) (J K : ℝ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ((3/2+3*J^2+3*K^2:ℝ):ℂ) • 1 +
    (1/2:ℂ) • sourceHeisenbergMatrix n (site 0) (site 1) -
    (K:ℂ) • sourceHeisenbergMatrix n (site 0) (site 3) -
    (J:ℂ) • sourceHeisenbergMatrix n (site 1) (site 2) +
    ((2*J*K:ℝ):ℂ) • sourceHeisenbergMatrix n (site 2) (site 3)

theorem qmaCrossing_effective {n r : ℕ} (e : Fin r) (site : Fin 4 → Fin n)
    (hsite : Function.Injective site) (R J K : ℝ) (hR : R ≠ 0) :
    qmaCrossingCorrection site J K -
      mediatorCompression n r
        (qmaSingletStar n r e site qmaCrossingMember (qmaCrossingAmplitude R J K) *
          liftedMediatorInverse n r (R^2) *
            qmaSingletStar n r e site qmaCrossingMember (qmaCrossingAmplitude R J K)) =
      (J:ℂ) • sourceHeisenbergMatrix n (site 0) (site 2) +
        (K:ℂ) • sourceHeisenbergMatrix n (site 1) (site 3) := by
  have hk (a b : Fin 4) : qmaPauliKernel n (site a) (site b) =
      if a = b then (3:ℂ) • 1 else sourceHeisenbergMatrix n (site a) (site b) := by
    by_cases hab : a = b
    · subst b
      simp only [ite_true,qmaPauliKernel_self]
    · rw [ite_eq_right hab]
      exact qmaPauliKernel_eq n _ _ (fun h => hab (hsite h))
  rw [qmaSingletStar_compression]
  simp only [hk,qmaCrossingCorrection]
  simp [qmaCrossingMember,qmaCrossingAmplitude,Fin.sum_univ_succ]
  rw [qmaHeisenberg_symm n (site 1) (site 0),qmaHeisenberg_symm n (site 2) (site 0),
    qmaHeisenberg_symm n (site 2) (site 1),qmaHeisenberg_symm n (site 3) (site 0),
    qmaHeisenberg_symm n (site 3) (site 1),qmaHeisenberg_symm n (site 3) (site 2)]
  ext s t
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,Matrix.smul_apply,
    smul_eq_mul,RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal]
  have hRC : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  field_simp [hRC]
  ring

end ContinuumCoulomb

end

end OAI
