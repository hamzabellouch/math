import OAI.Geometry.RCD.Coordinates.FrameResidualEnergy
import OAI.Geometry.RCD.Coordinates.GammaCoordinateForm

namespace OAI

/-! # Squared transverse coordinates have zero derivative in the axial direction -/

open Set Filter MeasureTheory Finset
open scoped InnerProductSpace NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localGamma_transverse_coordinate {n : ℕ} (u : Fin n → SobolevSpace μ Q)
    (A : Fin n → ℝ≥0) (hA : ∀ i, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (u i) x|≤A i)
    (Ω : Set X)
    (hgram : ∀ i j, localGamma μ Q (u i) (u j) =ᵐ[μ.restrict Ω]
      fun _ => if i=j then 1 else 0)
    (a : Euclidean n) (ha : ‖a‖=1) (B : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (sobolevColumnMap μ Q u a) x|≤B) :
    localGamma μ Q
      ((∑ i, SobolevSpace.square μ Q (u i) (A i))-
        SobolevSpace.square μ Q (sobolevColumnMap μ Q u a) B)
      (sobolevColumnMap μ Q u a) =ᵐ[μ.restrict Ω] fun _ => 0 := by
  let w := sobolevColumnMap μ Q u a
  have hrow (i : Fin n) : localGamma μ Q (u i) w =ᵐ[μ.restrict Ω] fun _ => a i := by
    filter_upwards [ae_restrict_of_ae (localGamma_column_right μ Q (u i) u a),
      ae_all_iff.mpr (fun j => hgram i j)] with x hx hg
    rw [hx]
    simp_rw [hg]
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hcol : SobolevSpace.toLp μ Q w =ᵐ[μ.restrict Ω]
      fun x => ∑ i, a i*SobolevSpace.toLp μ Q (u i) x := by
    have hc := sobolevColumnMap_representative μ Q u Ω
      (fun x => WithLp.toLp 2 (fun i => SobolevSpace.toLp μ Q (u i) x))
      (fun _ => EventuallyEq.rfl) a
    simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial] using hc
  have hww : localGamma μ Q w w =ᵐ[μ.restrict Ω] fun _ => (1:ℝ) := by
    simpa only [ha,one_pow] using localGamma_column_orthonormal μ Q u Ω hgram a
  filter_upwards [ae_restrict_of_ae (localGamma_sub_left μ Q
      (∑ i, SobolevSpace.square μ Q (u i) (A i)) (SobolevSpace.square μ Q w B) w),
    ae_restrict_of_ae (localGamma_finset_sum_left μ Q univ
      (fun i => SobolevSpace.square μ Q (u i) (A i)) w),
    ae_all_iff.mpr (fun i => ae_restrict_of_ae (localGamma_square μ Q (u i) w (A i) (hA i))),
    ae_restrict_of_ae (localGamma_square μ Q w w B hB),ae_all_iff.mpr hrow,hcol,hww]
    with x hs hsum hsq hw hrows hc hwwx
  change localGamma μ Q ((∑ i, SobolevSpace.square μ Q (u i) (A i))-
    SobolevSpace.square μ Q w B) w x=0
  rw [hs,hsum,hw,hwwx,hc]
  simp_rw [hsq,hrows]
  rw [Finset.mul_sum,mul_one]
  apply sub_eq_zero.mpr
  apply sum_congr rfl
  intro i _
  ring

end RegularPointCoordinates

end

end OAI
