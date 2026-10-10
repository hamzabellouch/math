import OAI.Geometry.RCD.Coordinates.MatrixTransverseDefect
import OAI.Geometry.RCD.Coordinates.TransverseCoordinateEnergy

namespace OAI

/-! # Quantitative transverse energy for actual bounded coordinate functions -/

open Set Filter MeasureTheory Finset
open scoped InnerProductSpace NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localGamma_transverse_defect {n : ℕ} (u : Fin n → SobolevSpace μ Q)
    (A : Fin n → ℝ≥0) (hA : ∀ i, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (u i) x|≤A i)
    (Ω : Set X) (v : X → Euclidean n)
    (hu : ∀ i, SobolevSpace.toLp μ Q (u i) =ᵐ[μ.restrict Ω] fun x => v x i)
    (a : Euclidean n) (ha : ‖a‖=1) (B : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (sobolevColumnMap μ Q u a) x|≤B) :
    ∀ᵐ x ∂μ.restrict Ω,
      |localGamma μ Q
        ((∑ i, SobolevSpace.square μ Q (u i) (A i))-
          SobolevSpace.square μ Q (sobolevColumnMap μ Q u a) B)
        (sobolevColumnMap μ Q u a) x|≤
          2*((n:ℝ)+1)*‖v x‖*gramDefect μ Q u x := by
  let w := sobolevColumnMap μ Q u a
  have hwrep := sobolevColumnMap_representative μ Q u Ω v hu a
  filter_upwards [ae_restrict_of_ae (localGamma_sub_left μ Q
      (∑ i, SobolevSpace.square μ Q (u i) (A i)) (SobolevSpace.square μ Q w B) w),
    ae_restrict_of_ae (localGamma_finset_sum_left μ Q univ
      (fun i => SobolevSpace.square μ Q (u i) (A i)) w),
    ae_all_iff.mpr (fun i => ae_restrict_of_ae (localGamma_square μ Q (u i) w (A i) (hA i))),
    ae_restrict_of_ae (localGamma_square μ Q w w B hB),
    ae_all_iff.mpr (fun i => ae_restrict_of_ae (localGamma_column_right μ Q (u i) u a)),
    ae_restrict_of_ae (localGamma_column_pair μ Q u a a),ae_all_iff.mpr hu,hwrep]
    with x hs hsum hsq hw hrows hww hux hwr
  change |localGamma μ Q ((∑ i, SobolevSpace.square μ Q (u i) (A i))-
    SobolevSpace.square μ Q w B) w x|≤_
  rw [hs,hsum,hw,hww,hwr]
  change ∀ i, localGamma μ Q (u i) w x=∑ j, a j*localGamma μ Q (u i) (u j) x at hrows
  simp_rw [hsq,hrows,hux]
  have hh := matrix_transverse_defect (fun i j => localGamma μ Q (u i) (u j) x)
    a (v x) ha (le_refl ‖v x‖)
  have he : (∑ i, 2*(v x) i*(∑ j, a j*localGamma μ Q (u i) (u j) x))=
      2*(∑ i, (v x) i*(∑ j, a j*localGamma μ Q (u i) (u j) x)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  exact hh

end RegularPointCoordinates

end

end OAI
