import OAI.Analysis.SphereIsometry.ChordSecant
import OAI.Analysis.SphereIsometry.RadialPerturbation

namespace OAI

/-!
# Excluding large aligned-chord ratios

The secant estimate holds for every support. Reusing a support in the equality
case makes the sign strict, and the literal inverse configuration gives the
opposite image sign. A small radial perturbation then violates the actual defect
bound. No compactness assumption on either ambient space is used here.
-/

noncomputable section

namespace Tingley
namespace AlignedConfiguration

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}
variable (C : AlignedConfiguration f y t M)

/-- The large-ratio secant bound controls both the product and the size of the
support perturbation. All quantities come from the given configuration. -/
theorem largeB_product_bounds (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hlarge : 1 - t < C.B) :
    1 - t ≤ C.A * C.u ∧ C.secantTheta ≤ 1 - C.B := by
  obtain ⟨φ, hφ⟩ := exists_support ((C.v : X) + C.secantTheta • (y : X))
  have hs := C.secant_bounds hM ht hb φ hφ
  have hle : (1 - t) / C.p ≤ C.B :=
    hs.1.trans (hs.2.1.trans (hs.2.2.2 hlarge))
  have hproduct : 1 - t ≤ C.A * C.u := by
    calc
      1 - t ≤ C.B * C.p := (div_le_iff₀ C.p_pos).mp hle
      _ = C.A * C.u := by unfold A B; ring
  refine ⟨hproduct, ?_⟩
  rw [secantTheta, C.secantStep_eq_largeB ht hlarge, C.one_sub_B]
  apply (div_le_iff₀ C.p_pos).mpr
  calc
    ((1 - t) / C.u) * C.s ≤ C.A * C.s :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ C.u_pos).mpr hproduct) C.s_pos.le
    _ = (C.s / C.d) * C.p := by unfold A; ring

/-- A large `B` makes every support at the original chord direction strictly
negative on the base vector, and forces `A` into the same large regime. -/
theorem largeB_forces_largeA_and_negative_support
    (hM : 0 < M) (ht : 0 < t ∧ t < 1) (hb : HasDefectBound f M)
    (hlarge : 1 - t < C.B) :
    1 - t < C.A ∧
      ∀ L : X →L[ℝ] ℝ, SupportAt L (C.v : X) → L (y : X) < 0 := by
  obtain ⟨hproduct, hθB⟩ := C.largeB_product_bounds hM ht hb hlarge
  have hθ : 0 < C.secantTheta := C.secantTheta_pos ht
  have hnegative : ∀ L : X →L[ℝ] ℝ,
      SupportAt L (C.v : X) → L (y : X) < 0 := by
    intro L hL
    have hLv : L (C.v : X) = 1 := hL.2.trans C.v.property
    obtain ⟨φ, hφ⟩ := exists_support ((C.v : X) + C.secantTheta • (y : X))
    have hs := C.secant_bounds hM ht hb φ hφ
    have hφv : φ (C.v : X) ≤ C.B := hs.2.1.trans (hs.2.2.2 hlarge)
    have hφy : φ (y : X) ≤ 1 := by
      simpa only [UnitSphere.norm_coe] using apply_le_norm hφ.1 (y : X)
    have hφeval : φ (C.v : X) + C.secantTheta * φ (y : X) =
        ‖(C.v : X) + C.secantTheta • (y : X)‖ := by
      simpa only [map_add, map_smul, smul_eq_mul] using hφ.2
    have hleft : 1 + C.secantTheta * L (y : X) ≤
        ‖(C.v : X) + C.secantTheta • (y : X)‖ := by
      simpa only [map_add, map_smul, smul_eq_mul, hLv] using
        apply_le_norm hL.1 ((C.v : X) + C.secantTheta • (y : X))
    have hφterm : C.secantTheta * φ (y : X) ≤ C.secantTheta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hφy hθ.le
    have hnorm : ‖(C.v : X) + C.secantTheta • (y : X)‖ ≤
        C.B + C.secantTheta := by
      linarith only [hφeval, hφv, hφterm]
    have hstrict : 1 + C.secantTheta * L (y : X) - C.secantTheta < C.B := by
      by_contra hnot
      have hLperturbed : SupportAt L ((C.v : X) + C.secantTheta • (y : X)) := by
        refine ⟨hL.1, ?_⟩
        simp only [map_add, map_smul, smul_eq_mul, hLv]
        have hreverse := le_of_not_gt hnot
        linarith only [hleft, hnorm, hreverse]
      have hsL := C.secant_bounds hM ht hb L hLperturbed
      have hbad : 1 ≤ C.B := by
        simpa only [hLv] using hsL.2.1.trans (hsL.2.2.2 hlarge)
      exact (not_le_of_gt C.B_lt_one) hbad
    have hmul : C.secantTheta * L (y : X) < C.secantTheta * 0 := by
      linarith only [hstrict, hθB]
    exact (mul_lt_mul_iff_right₀ hθ).mp hmul
  refine ⟨?_, hnegative⟩
  obtain ⟨L, hL⟩ := exists_support (C.v : X)
  have hj : L (y : X) < 0 := hnegative L hL
  have hLv : L (C.v : X) = 1 := hL.2.trans C.v.property
  have hz : C.r • (C.v : X) - t • (y : X) = -(C.z : X) := by
    rw [C.z_eq]
    abel
  have hznorm : ‖C.r • (C.v : X) - t • (y : X)‖ = 1 := by
    rw [hz, norm_neg, UnitSphere.norm_coe]
  have hr : C.r - t * L (y : X) ≤ 1 := by
    simpa only [map_sub, map_smul, smul_eq_mul, hLv, mul_one, hznorm] using
      apply_le_norm hL.1 (C.r • (C.v : X) - t • (y : X))
  have htj : t * L (y : X) < 0 := mul_neg_of_pos_of_neg ht.1 hj
  have hr1 : C.r < 1 := by linarith only [hr, htj]
  have hu1 : C.u < 1 := by linarith only [hr1, C.r_sub_u, hM]
  have hproduct_lt : C.A * C.u < C.A := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hu1 C.A_pos
  exact hproduct.trans_lt hproduct_lt

/-- The inverse uses literal negated directions. In particular, obtaining the
positive image sign does not assume that the sphere map preserves antipodes. -/
theorem largeB_support_signs (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hlarge : 1 - t < C.B) :
    (∀ L : X →L[ℝ] ℝ, SupportAt L (C.v : X) → L (y : X) < 0) ∧
      (∀ K : Y →L[ℝ] ℝ, SupportAt K (C.w : Y) → 0 < K (f y : Y)) := by
  obtain ⟨hA, hnegative⟩ :=
    C.largeB_forces_largeA_and_negative_support hM ht hb hlarge
  have hlarge_inverse : 1 - t < C.inverse.B := by
    simpa only [inverse_B] using hA
  have hinverse :=
    (C.inverse.largeB_forces_largeA_and_negative_support hM ht hb.symm
      hlarge_inverse).2
  refine ⟨hnegative, ?_⟩
  intro K hK
  have hKneg : SupportAt (-K) (C.inverse.v : Y) := by
    simpa only [inverse_v_coe] using hK.neg
  have h := hinverse (-K) hKneg
  change -(K (f y : Y)) < 0 at h
  linarith only [h]

/-- A small decrease of the radius strictly increases both contributions to the
signed defect, contradicting its global bound. -/
theorem largeB_impossible (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hlarge : 1 - t < C.B) : False := by
  obtain ⟨hnegative, hpositive⟩ := C.largeB_support_signs hM ht hb hlarge
  obtain ⟨η, hη, hηt, hshort⟩ :=
    exists_radial_perturbation_lt_with_cap C.v.property C.p_pos ht.1 hnegative
  obtain ⟨K, hK⟩ := exists_support (C.w : Y)
  have hKw : K (C.w : Y) = 1 := hK.2.trans C.w.property
  have hKb : 0 < K (f y : Y) := hpositive K hK
  have hlong : C.s < ‖C.s • (C.w : Y) + η • (f y : Y)‖ := by
    have hle := apply_le_norm hK.1 (C.s • (C.w : Y) + η • (f y : Y))
    simp only [map_add, map_smul, smul_eq_mul, hKw, mul_one] at hle
    have hterm : 0 < η * K (f y : Y) := mul_pos hη hKb
    linarith only [hle, hterm]
  have hq : t - η ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact (sub_pos.mpr hηt).le
    · linarith only [ht.2, hη]
  have hx : (C.x : X) - (t - η) • (y : X) =
      C.p • (C.v : X) + η • (y : X) := by
    rw [C.x_eq, sub_smul]
    abel
  have hfx : (f C.x : Y) - (t - η) • (f y : Y) =
      C.s • (C.w : Y) + η • (f y : Y) := by
    rw [C.fx_eq, sub_smul]
    abel
  have hbound := (abs_le.mp (hb (t - η) hq C.x y)).2
  rw [signedDefect, hfx, hx] at hbound
  linarith only [hbound, hshort, hlong, C.s_sub_p]

/-- Both ratios lie in the small regime. The first component is obtained by
applying the already-proved contradiction to the exact inverse configuration. -/
theorem small_ratios (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) : C.A ≤ 1 - t ∧ C.B ≤ 1 - t := by
  constructor
  · have h : C.inverse.B ≤ 1 - t :=
      le_of_not_gt (C.inverse.largeB_impossible hM ht hb.symm)
    simpa only [inverse_B] using h
  · exact le_of_not_gt (C.largeB_impossible hM ht hb)

end AlignedConfiguration
end Tingley

end

end OAI
