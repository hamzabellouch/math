import OAI.Geometry.RCD.Coordinates.TransverseCoordinateEnergy

namespace OAI

/-! # Actual bounded axial and transverse functions of an orthonormal frame -/

open Set Filter MeasureTheory Finset
open scoped NNReal InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem bounded_transverse_frame_data {n : ℕ} (u : Fin n → SobolevSpace μ Q)
    (A : Fin n → ℝ≥0) (hA : ∀ i, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (u i) x|≤A i)
    (Ω : Set X) (v : X → Euclidean n)
    (hu : ∀ i, SobolevSpace.toLp μ Q (u i) =ᵐ[μ.restrict Ω] fun x => v x i)
    (hH : ∀ i, IsSobolevHarmonicOn μ Q Ω (u i))
    (hgram : ∀ i j, localGamma μ Q (u i) (u j) =ᵐ[μ.restrict Ω]
      fun _ => if i=j then 1 else 0) (a : Euclidean n) (ha : ‖a‖=1) :
    ∃ (w s : SobolevSpace μ Q) (B D : ℝ≥0),
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q w x|≤B) ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q s x|≤D) ∧
      (SobolevSpace.toLp μ Q w =ᵐ[μ.restrict Ω] fun x => ⟪v x,a⟫_ℝ) ∧
      (SobolevSpace.toLp μ Q s =ᵐ[μ.restrict Ω] fun x => ‖v x‖^2-⟪v x,a⟫_ℝ^2) ∧
      (localGamma μ Q w w =ᵐ[μ.restrict Ω] fun _ => (1:ℝ)) ∧
      (localGamma μ Q s w =ᵐ[μ.restrict Ω] fun _ => (0:ℝ)) ∧
      IsSobolevHarmonicOn μ Q Ω w := by
  let w := sobolevColumnMap μ Q u a
  let B : ℝ≥0 := ∑ i, ‖a i‖₊*A i
  have hwglobal : SobolevSpace.toLp μ Q w =ᵐ[μ]
      fun x => ∑ i, a i*SobolevSpace.toLp μ Q (u i) x := by
    have h := sobolevColumnMap_representative μ Q u univ
      (fun x => WithLp.toLp 2 (fun i => SobolevSpace.toLp μ Q (u i) x))
      (fun _ => EventuallyEq.rfl) a
    simpa only [Measure.restrict_univ,PiLp.inner_apply,RCLike.inner_apply,conj_trivial] using h
  have hwB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q w x|≤B := by
    filter_upwards [hwglobal,ae_all_iff.mpr hA] with x hx hb
    rw [hx]
    calc
      _ ≤ ∑ i, |a i*SobolevSpace.toLp μ Q (u i) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |a i| * (A i:ℝ) := sum_le_sum (fun i _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _))
      _ = B := by simp [B,Real.norm_eq_abs]
  let z := ∑ i, SobolevSpace.square μ Q (u i) (A i)
  have hz : SobolevSpace.toLp μ Q z =ᵐ[μ]
      fun x => ∑ i, (SobolevSpace.toLp μ Q (u i) x)^2 := by
    change SobolevSpace.toLpCLM μ Q (∑ i, SobolevSpace.square μ Q (u i) (A i)) =ᵐ[μ] _
    rw [map_sum]
    change (∑ i, SobolevSpace.toLp μ Q (SobolevSpace.square μ Q (u i) (A i))) =ᵐ[μ] _
    filter_upwards [Lp.coeFn_finsetSum univ (fun i => SobolevSpace.toLp μ Q
      (SobolevSpace.square μ Q (u i) (A i))),ae_all_iff.mpr
      (fun i => SobolevSpace.square_coe μ Q (u i) (A i) (hA i))] with x hx hs
    rw [hx]
    simp only [Finset.sum_apply,hs]
  let s := z-SobolevSpace.square μ Q w B
  have hs : SobolevSpace.toLp μ Q s =ᵐ[μ]
      fun x => (∑ i, (SobolevSpace.toLp μ Q (u i) x)^2)-(SobolevSpace.toLp μ Q w x)^2 := by
    filter_upwards [hz,SobolevSpace.square_coe μ Q w B hwB,
      Lp.coeFn_sub (SobolevSpace.toLp μ Q z) (SobolevSpace.toLp μ Q (SobolevSpace.square μ Q w B))]
      with x hx hy hsub
    change (SobolevSpace.toLp μ Q z-SobolevSpace.toLp μ Q (SobolevSpace.square μ Q w B)) x=_
    simp only [hsub,Pi.sub_apply,hx,hy]
  let D : ℝ≥0 := (∑ i, A i^2)+B^2
  have hsD : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q s x|≤D := by
    filter_upwards [hs,ae_all_iff.mpr hA,hwB] with x hx hb hw
    rw [hx]
    calc
      _ ≤ |∑ i, (SobolevSpace.toLp μ Q (u i) x)^2|+|(SobolevSpace.toLp μ Q w x)^2| := abs_sub _ _
      _ = (∑ i, |SobolevSpace.toLp μ Q (u i) x|^2)+|SobolevSpace.toLp μ Q w x|^2 := by
        rw [abs_of_nonneg (sum_nonneg (fun _ _ => sq_nonneg _))]
        simp only [abs_pow,sq_abs]
      _ ≤ (∑ i, (A i:ℝ)^2)+(B:ℝ)^2 := add_le_add
        (sum_le_sum (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hb i) 2))
        (pow_le_pow_left₀ (abs_nonneg _) hw 2)
      _ = D := by simp [D]
  have hw := sobolevColumnMap_representative μ Q u Ω v hu a
  refine ⟨w,s,B,D,hwB,hsD,hw,?_,?_,?_,IsSobolevHarmonicOn.linearCombination μ Q hH a⟩
  · filter_upwards [ae_restrict_of_ae hs,ae_all_iff.mpr hu,hw] with x hx hux hwx
    rw [hx,hwx,EuclideanSpace.real_norm_sq_eq]
    simp only [hux]
  · simpa only [ha,one_pow] using localGamma_column_orthonormal μ Q u Ω hgram a
  · exact localGamma_transverse_coordinate μ Q u A hA Ω hgram a ha B hwB

end RegularPointCoordinates

end

end OAI
