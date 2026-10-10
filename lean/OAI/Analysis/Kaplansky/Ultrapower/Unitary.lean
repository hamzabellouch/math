import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.QuasiValue
import OAI.Analysis.Kaplansky.Ultrapower.PartialIsometry
import OAI.Analysis.Kaplansky.Ultrapower.PartialCorners
import OAI.Analysis.Kaplansky.Ultrapower.Maximal
import OAI.Analysis.Kaplansky.Ultrapower.Polar
import OAI.Analysis.Kaplansky.Ultrapower.Wandering

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

include hu in
lemma ultra_unitary_extension {v : V.UltraQuotient u} (hv : IsPartialIsometry v) :
    ∃ w : V.UltraQuotient u, star w*w=1 ∧ w*star w=1 ∧ w*(star v*v)=v := by
  let W := V.ultra u
  obtain ⟨w,hw,hwv,hmax⟩ := V.ultra_maximal_extension u hu hv
  have hcorner (a : V.UltraQuotient u) : (1-w*star w)*a*(1-star w*w)=0 := by
    let p := 1-star w*w
    let q := 1-w*star w
    let b := q*a*p
    have hp : IsStarProjection p := hw.initial.one_sub
    have hq : IsStarProjection q := hw.final.one_sub
    have hbp : b*p=b := by dsimp [b]; rw [mul_assoc,hp.isIdempotentElem.eq]
    have hqb : q*b=b := by dsimp [b]; rw [← mul_assoc,← mul_assoc,hq.isIdempotentElem.eq]
    obtain ⟨z,hz,hzb,hqz,hzp⟩ := V.ultra_polar_corner u hu b p q hp hbp hqb
    obtain ⟨h₁,h₂⟩ := hw.orthogonal_of_corners hqz hzp
    have hzw : IsPartialIsometry (w+z) := hw.add_orthogonal hz h₁ h₂
    have hzv : z*(star v*v)=0 := hv.corner_annihilates_extension hw hwv hzp
    have he : (w+z)*(star v*v)=v := by rw [add_mul,hwv,hzv,add_zero]
    have hsize := hmax (w+z) hzw he
    change W.quotQ (w+z) ≤ W.quotQ w at hsize
    rw [W.quotQ_partial_add hw hz h₁ h₂] at hsize
    have hzero : W.quotQ z=0 := by linarith [W.quotQ_nonneg z]
    have hz0 := (W.quotQ_eq_zero z).mp hzero
    rw [hz0,zero_mul] at hzb
    exact hzb.symm
  obtain ⟨hi,hf⟩ := W.unitary_of_residual_corner_zero hw hcorner
  exact ⟨w,hi,hf,hwv⟩

private local instance ultraRealSMulComm :
    SMulCommClass ℝ (V.UltraQuotient u) (V.UltraQuotient u) := Algebra.to_smulCommClass

private local instance ultraRealTower :
    IsScalarTower ℝ (V.UltraQuotient u) (V.UltraQuotient u) := IsScalarTower.right

private local instance ultraRealCFC :
    NonUnitalContinuousFunctionalCalculus ℝ (V.UltraQuotient u) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

private local instance ultraNonnegSpectrum : NonnegSpectrumClass ℝ (V.UltraQuotient u) :=
  CStarAlgebra.instNonnegSpectrumClass

include hu in
lemma ultra_unitary_polar (x : V.UltraQuotient u) :
    ∃ w : V.UltraQuotient u, star w*w=1 ∧ w*star w=1 ∧
      w*CFC.sqrt (star x*x)=x := by
  obtain ⟨v,hv,hvx⟩ := V.ultra_polar u hu x
  obtain ⟨w,hi,hf,hwv⟩ := V.ultra_unitary_extension u hu hv
  refine ⟨w,hi,hf,?_⟩
  calc _ = w*((star v*v)*CFC.sqrt (star x*x)) :=
          (congrArg (fun a : V.UltraQuotient u => w * a) (hv.initial_of_factor hvx)).symm
       _ = (w*(star v*v))*CFC.sqrt (star x*x) := by noncomm_ring
       _ = x := by rw [hwv,hvx]


end KaplanskyConsequences.QuasiValue

end

end OAI
