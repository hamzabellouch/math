import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreePhysicalBasis
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinPlane

namespace OAI

/-! Propagation of the outer outgoing Robin plane through the free radial equation. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFreePhysicalPairField_smul (b ζ η : ℂ) (r : ℝ) (c : ℂ) (X : E₄) :
    spectralFreePhysicalPairField b ζ η r (c • X)=c • spectralFreePhysicalPairField b ζ η r X := by
  apply Prod.ext <;> apply Prod.ext
  · rfl
  · change -(11/(r : ℂ)+1*Complex.I*(r : ℂ)/2)*(c*X.1.2)-
        (b+1*Complex.I*ζ-η/(r : ℂ)^2)*(c*X.1.1)=
      c*(-(11/(r : ℂ)+1*Complex.I*(r : ℂ)/2)*X.1.2-
        (b+1*Complex.I*ζ-η/(r : ℂ)^2)*X.1.1)
    ring
  · rfl
  · change -(11/(r : ℂ)+(-1)*Complex.I*(r : ℂ)/2)*(c*X.2.2)-
        (b+(-1)*Complex.I*ζ-η/(r : ℂ)^2)*(c*X.2.1)=
      c*(-(11/(r : ℂ)+(-1)*Complex.I*(r : ℂ)/2)*X.2.2-
        (b+(-1)*Complex.I*ζ-η/(r : ℂ)^2)*X.2.1)
    ring

theorem spectralFreePhysicalPairField_add (b ζ η : ℂ) (r : ℝ) (X Y : E₄) :
    spectralFreePhysicalPairField b ζ η r (X+Y)=
      spectralFreePhysicalPairField b ζ η r X+spectralFreePhysicalPairField b ζ η r Y := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralFreePhysicalPairField,spectralFreePhysicalField,Prod.fst_add,Prod.snd_add] <;> ring

theorem spectralFreeCombination_hasDerivAt (b ζ η : ℂ) (P N : ℝ → E₄)
    (a c : ℂ) (r : ℝ)
    (hP : HasDerivAt P (spectralFreePhysicalPairField b ζ η r (P r)) r)
    (hN : HasDerivAt N (spectralFreePhysicalPairField b ζ η r (N r)) r) :
    HasDerivAt (fun s => a • P s+c • N s)
      (spectralFreePhysicalPairField b ζ η r (a • P r+c • N r)) r := by
  have hd : HasDerivAt (fun s => a • P s+c • N s)
      (a • spectralFreePhysicalPairField b ζ η r (P r)+
        c • spectralFreePhysicalPairField b ζ η r (N r)) r :=
    (hP.const_smul a).add (hN.const_smul c)
  apply hd.congr_deriv
  rw [spectralFreePhysicalPairField_add,spectralFreePhysicalPairField_smul,spectralFreePhysicalPairField_smul]

theorem spectralFreeRobin_propagation_general (b ζ η : ℂ) (P N X : ℝ → E₄)
    (L R : ℝ) (hL : 0 < L) (hLR : L < R)
    (hP : ∀ r ∈ Icc L R, HasDerivAt P (spectralFreePhysicalPairField b ζ η r (P r)) r)
    (hN : ∀ r ∈ Icc L R, HasDerivAt N (spectralFreePhysicalPairField b ζ η r (N r)) r)
    (hX : ContinuousOn X (Icc L R))
    (hD : ∀ r ∈ Ioo L R, HasDerivAt X (spectralFreePhysicalPairField b ζ η r (X r)) r)
    (hdet : spectralValueDet (spectralPhysicalValueMap (P R)) (spectralPhysicalValueMap (N R)) ≠ 0)
    (hB : spectralPhysicalDerivativeMap (X R)=
      spectralJetRobin (P R) (N R) (spectralPhysicalValueMap (X R))) :
    ∃ c : ℂ × ℂ, EqOn X (fun r => c.1 • P r+c.2 • N r) (Icc L R) := by
  obtain ⟨c,hc⟩ := (spectralJetRobin_plane (P R) (N R) (X R) hdet).mp hB
  have hpc : ContinuousOn P (Icc L R) := fun r hr => (hP r hr).continuousAt.continuousWithinAt
  have hnc : ContinuousOn N (Icc L R) := fun r hr => (hN r hr).continuousAt.continuousWithinAt
  have hY : ContinuousOn (fun r => c.1 • P r+c.2 • N r) (Icc L R) :=
    (hpc.const_smul c.1).add (hnc.const_smul c.2)
  have hDY : ∀ r ∈ Ioo L R, HasDerivAt (fun s => c.1 • P s+c.2 • N s)
      (spectralFreePhysicalPairField b ζ η r (c.1 • P r+c.2 • N r)) r :=
    fun r hr => spectralFreeCombination_hasDerivAt b ζ η P N c.1 c.2 r
      (hP r ⟨hr.1.le,hr.2.le⟩) (hN r ⟨hr.1.le,hr.2.le⟩)
  exact ⟨c,spectralFree_eq_on_annulus b ζ η X _ L R hL hLR hX hY hD hDY hc⟩

theorem spectralFreeRobin_propagation (ell : ℕ) (b : ℝ) (ζ : ℂ)
    (hζ : -(1/32 : ℝ) ≤ ζ.re) (X : ℝ → E₄) (L R : ℝ) (hL : 0 < L) (hLR : L < R)
    (hX : ContinuousOn X (Icc L R))
    (hD : ∀ r ∈ Ioo L R,
      HasDerivAt X (spectralFreePhysicalPairField b ζ ((ell : ℂ)*((ell : ℂ)+10)) r (X r)) r)
    (hdet : spectralValueDet (spectralPhysicalValueMap (spectralFreePositivePhysical ell b ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell b ζ R)) ≠ 0)
    (hB : spectralPhysicalDerivativeMap (X R)=
      spectralJetRobin (spectralFreePositivePhysical ell b ζ R)
        (spectralFreeNegativePhysical ell b ζ R) (spectralPhysicalValueMap (X R))) :
    ∃ c : ℂ × ℂ, EqOn X (fun r => c.1 • spectralFreePositivePhysical ell b ζ r+
      c.2 • spectralFreeNegativePhysical ell b ζ r) (Icc L R) := by
  exact spectralFreeRobin_propagation_general b ζ ((ell : ℂ)*((ell : ℂ)+10))
    (spectralFreePositivePhysical ell b ζ) (spectralFreeNegativePhysical ell b ζ) X L R hL hLR
    (fun r hr => spectralFreePositivePhysical_hasDerivAt ell b ζ hζ r (hL.trans_le hr.1))
    (fun r hr => spectralFreeNegativePhysical_hasDerivAt ell b ζ hζ r (hL.trans_le hr.1)) hX hD hdet hB

theorem spectralFreeCoreBoundary_linear (ell : ℕ) (r : ℝ) (a b : ℂ) (X Y : E₄) :
    spectralFreeCoreBoundary ell r (a • X+b • Y)=
      a • spectralFreeCoreBoundary ell r X+b • spectralFreeCoreBoundary ell r Y := by
  funext j
  fin_cases j <;>
    simp [spectralFreeCoreBoundary,smul_eq_mul] <;> ring

theorem matchingColumn_coefficients_zero (u v : Fin 2 → ℂ) (a b : ℂ)
    (hd : matchingColumnDeterminant u v ≠ 0) (hz : a • u+b • v=0) : a=0 ∧ b=0 := by
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  change a*u 0+b*v 0=0 at h0
  change a*u 1+b*v 1=0 at h1
  have ha : a*matchingColumnDeterminant u v=0 := by
    unfold matchingColumnDeterminant
    linear_combination v 1*h0-v 0*h1
  have hb : b*matchingColumnDeterminant u v=0 := by
    unfold matchingColumnDeterminant
    linear_combination u 0*h1-u 1*h0
  exact ⟨(mul_eq_zero.mp ha).resolve_right hd,(mul_eq_zero.mp hb).resolve_right hd⟩

end DefocusingNLS

end OAI
