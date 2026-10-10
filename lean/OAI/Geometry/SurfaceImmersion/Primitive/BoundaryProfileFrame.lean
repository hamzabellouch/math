import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileGeometry

namespace OAI

/-! Identification of the five-profile coefficient map with the genuine
second fundamental form of a smooth immersion. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def realBoundaryProfile (F : RField 4) (z : ℝ) (p : Base) : BoundaryProfile :=
  ![coordDeriv dx F p,coordDeriv dy F p,coordDeriv dy (coordDeriv dy F) p,
    coordDeriv dx (coordDeriv dy F) p,z • coordDeriv dx (coordDeriv dx F) p]

lemma realNormalPart_dot_of_normal (X Y W n : Vec)
    (hX : X ⬝ᵥ n = 0) (hY : Y ⬝ᵥ n = 0) :
    realNormalPart X Y W ⬝ᵥ n = W ⬝ᵥ n := by
  simp only [realNormalPart,sub_dotProduct,smul_dotProduct,hX,hY,
    smul_eq_mul,mul_zero,sub_zero]

lemma realBoundaryProfile_regular {F : RField 4} {p : Base} (z : ℝ)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : realSecondForm F dy dy p ≠ 0) :
    realBoundaryProfile F z p ∈ regularBoundaryProfiles := by
  exact ⟨hD,hB⟩

/-- The scaled longitudinal coefficient is read from `z Fxx`, so this
identification is uniform even when `Fxx` itself diverges. -/
theorem exists_profile_secondFormFrame {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (z : ℝ) (p : Base) (hJ : realBoundaryProfile F z p ∈ regularBoundaryProfiles) :
    ∃ d : SecondFormFrame F p
      (coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p),
      d.n = profilePreferred (realBoundaryProfile F z p) ∧
      d.m = profileComplement (realBoundaryProfile F z p) ∧
      profileCoefficients (realBoundaryProfile F z p) = ![d.S,d.D,d.N,z*d.L] := by
  obtain ⟨d,hn,hm,hS,hD,hN,hL⟩ := exists_secondFormFrame_with_coordinates hF p hJ.1 hJ.2
  have hn' : d.n = profilePreferred (realBoundaryProfile F z p) := hn
  have hm' : d.m = profileComplement (realBoundaryProfile F z p) := by
    simpa only [profileComplement,realBoundaryProfile,Matrix.cons_val_zero,
      Matrix.cons_val_one,hn'] using hm
  refine ⟨d,hn',hm',?_⟩
  have hdn := realNormalPart_dot_of_normal (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dx (coordDeriv dy F) p) d.n d.tangent_n.1 d.tangent_n.2
  have hnm := realNormalPart_dot_of_normal (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dx (coordDeriv dy F) p) d.m d.tangent_m.1 d.tangent_m.2
  have hlm := realNormalPart_dot_of_normal (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dx (coordDeriv dx F) p) d.m d.tangent_m.1 d.tangent_m.2
  ext j
  fin_cases j
  · exact hS.symm
  · change coordDeriv dx (coordDeriv dy F) p ⬝ᵥ
      profilePreferred (realBoundaryProfile F z p) = d.D
    rw [← hn',hD]
    exact hdn.symm
  · change coordDeriv dx (coordDeriv dy F) p ⬝ᵥ
      profileComplement (realBoundaryProfile F z p) = d.N
    rw [← hm',hN]
    exact hnm.symm
  · change (z • coordDeriv dx (coordDeriv dx F) p) ⬝ᵥ
      profileComplement (realBoundaryProfile F z p) = z*d.L
    rw [← hm',hL,smul_dotProduct]
    exact congrArg (fun a => z*a) hlm.symm

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
