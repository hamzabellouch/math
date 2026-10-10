import OAI.Geometry.SurfaceImmersion.Primitive.FiniteCrossingNormals
import OAI.Geometry.SurfaceImmersion.Primitive.FiniteCrossingNeighborhoods
import OAI.Geometry.SurfaceImmersion.Geometry.SecondFormNormalFields

namespace OAI

/-! The finite crossing construction applied to the actual second form of
one immersion, with its canonical transverse preferred normal. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem actual_finite_crossing_normal {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ)
    {U V : Set Base} (hV : IsOpen V)
    (hreg : ∀ y ∈ U, realBoundaryProfile F z y ∈ regularBoundaryProfiles)
    (Y : κ → Base → Base) (hY : ∀ k, ContDiffOn ℝ ∞ (Y k) U)
    (left right : ι → κ) (x : ι → Base) (hxinj : Function.Injective x)
    (hxU : ∀ i, x i ∈ U) (hxV : ∀ i, x i ∈ V)
    (C : κ → Set Base) (hC : ∀ k, IsClosed (C k))
    (honly : ∀ i k, x i ∈ C k → k = left i ∨ k = right i)
    (hchoice : ∀ i,
      (0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ
          profilePreferred (realBoundaryProfile F z (x i)) ∧
       0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ
          profilePreferred (realBoundaryProfile F z (x i))) ∨
      (0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ
          realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ∧
        ∃ w : Vec, profilePreferred (realBoundaryProfile F z (x i)) ⬝ᵥ w = 0 ∧
          0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ w ∧
          0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ w))
    (hU : IsOpen U) :
    ∃ g : Base → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ y ∈ U, g y ⬝ᵥ g y = 1) ∧
      (∀ y ∈ U, ∀ w : Base, coordDeriv w F y ⬝ᵥ g y = 0) ∧
      (∀ y ∈ U, y ∉ V → g y = profilePreferred (realBoundaryProfile F z y)) ∧
      (∀ k y, y ∈ U → y ∈ C k →
        profilePreferred (realBoundaryProfile F z y) ≠
          -normalize (realSecondForm F (Y k y) (Y k y) y) →
        g y ≠ -normalize (realSecondForm F (Y k y) (Y k y) y)) ∧
      ∀ i, 0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ g (x i) ∧
        0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ g (x i) := by
  let n : Base → Vec := fun y => profilePreferred (realBoundaryProfile F z y)
  let P : κ → Base → Vec := fun k y => realSecondForm F (Y k y) (Y k y) y
  have hD : ∀ y ∈ U, gramDet (coordDeriv dx F y) (coordDeriv dy F y) ≠ 0 :=
    fun y hy => (hreg y hy).1
  have hPs : ∀ k, ContDiffOn ℝ ∞ (P k) U :=
    fun k => realSecondForm_variable_smoothOn hF hD (hY k)
  have hns : ContDiffOn ℝ ∞ n U := profilePreferred_field_smoothOn hF z hreg
  have hnu : ∀ y ∈ U, n y ⬝ᵥ n y = 1 := fun y hy => profilePreferred_unit (hreg y hy)
  obtain ⟨O,hO,hxo,hOV,hdisj,hcurve⟩ := finite_crossing_neighborhoods x hxinj left right C hC honly
    (fun _ => V) (fun _ => hV) hxV
  obtain ⟨g,hg,hgu,hge,hga,hgn,hgp⟩ := finite_crossing_normals hU hns hnu P hPs left right x hxU
    O hO hxo hdisj C hcurve hchoice
  refine ⟨g,hg,hgu,?_,?_,hga,hgp⟩
  · intro y hy w
    have hnperp := profilePreferred_perp (hreg y hy)
    have hperp (d : Base) (hd : coordDeriv d F y ⬝ᵥ n y = 0)
        (hsecond : ∀ k, coordDeriv d F y ⬝ᵥ P k y = 0) : coordDeriv d F y ⬝ᵥ g y = 0 :=
      hgn y hy _ hd hsecond
    have hxg := hperp dx hnperp.1
      (fun k => (realSecondForm_field_perp (hD y hy) (Y k y) (Y k y)).1)
    have hyg := hperp dy hnperp.2
      (fun k => (realSecondForm_field_perp (hD y hy) (Y k y) (Y k y)).2)
    rw [coordDeriv_eq_basis F w y]
    simp only [add_dotProduct,smul_dotProduct,smul_eq_mul,hxg,hyg,mul_zero,add_zero]
  · intro y hy hyV
    exact hge y hy (fun i h => hyV (hOV i h))

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
