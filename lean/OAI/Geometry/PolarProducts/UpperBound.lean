import OAI.Geometry.PolarProducts.CanonicalCoordinates

namespace OAI

section
namespace CylinderNonsqueezing
noncomputable section
open Set
open scoped ContDiff
open FourierPolynomial
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem radius_le_of_map (j₀ : κ) {L R M : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (f : Vector κ → Vector κ) (hf : ContDiffOn ℝ ∞ f (PushedBall.domain L))
    (hi : InjOn f (PushedBall.domain L))
    (hω : ∀ z ∈ PushedBall.domain L, ComplexSymplectic.Preserves (fderiv ℝ f z))
    (hbounded : ∀ z ∈ PushedBall.domain L, ‖f z‖^2 ≤ M)
    (hcylinder : ∀ z ∈ PushedBall.domain L, ‖f z j₀‖^2 ≤ R) : L ≤ R := by
  let hU := PushedBall.isOpen_domain (κ := κ) L
  have hD (z) (hz : z ∈ PushedBall.domain L) := ComplexSymplectic.invertible (hω z hz)
  let e := EmbeddingInverse.localEquiv hU f hf hi hD
  exact radius_le_of_embedding j₀ hL hR hM e hf rfl hω
    (by rintro _ ⟨z,hz,rfl⟩; exact hbounded z hz)
    (by rintro _ ⟨z,hz,rfl⟩; exact hcylinder z hz)

end
end CylinderNonsqueezing
end

section
namespace SymmetricPolar
noncomputable section
open Set Filter
open scoped ContDiff Topology ENNReal
open ComplexCoordinates UpperCoordinates
variable {n : ℕ}

theorem capacity_le_four_of_embedding {K : Set (Position n)} (hK : IsSymmetricConvexBody K)
    (hn : 0 < n) {c : ℝ} (hc : 0 < c)
    (hemb : HasSymplecticEmbedding (capacityBall n c) (polarProduct K)) : c ≤ 4 := by
  obtain ⟨u,v,hvu,hcyl⟩ := exists_squareCylinder hK hn
  have hu : u ≠ 0 := by intro h; simp [h] at hvu
  obtain ⟨j,huj⟩ : ∃ j : Fin n, u j ≠ 0 := by
    by_contra h
    apply hu
    ext j
    exact not_not.mp ((not_exists.mp h) j)
  let A := CanonicalLinear.adapted j huj hvu
  let T := targetCoordinates A
  obtain ⟨e,he,hei,heK,heω⟩ := hemb
  let f : C (Fin n) → C (Fin n) := fun z => PlanarCylinder.map j (T (e (parts z)))
  have hball {z : C (Fin n)} (hz : z ∈ PushedBall.domain (c/Real.pi)) :
      parts z ∈ capacityBall n c := by
    change Real.pi*(‖re z‖^2+‖im z‖^2) < c
    rw [← norm_sq_parts]
    exact (lt_div_iff₀ Real.pi_pos).mp hz |> fun h => by simpa [mul_comm] using h
  have hfirst (z : C (Fin n)) (hz : z ∈ PushedBall.domain (c/Real.pi)) :
      T (e (parts z)) ∈ PlanarCylinder.domain j := by
    have hh := hcyl (heK (hball hz))
    have hi := targetCoordinates_first j huj hvu (e (parts z))
    change |(T (e (parts z)) j).re| < 1 ∧ |(T (e (parts z)) j).im| < 1
    rw [hi.1, hi.2]
    exact hh
  have hsm (z : C (Fin n)) (hz : z ∈ PushedBall.domain (c/Real.pi)) : ContDiffAt ℝ ∞ f z := by
    have hez := he.contDiffAt ((isOpen_lt (by fun_prop) continuous_const).mem_nhds (hball hz))
    have hP : ContDiffAt ℝ ∞ (parts : C (Fin n) → Phase n) z :=
      (parts (ι := Fin n)).contDiff.contDiffAt
    have hT : ContDiffAt ℝ ∞ (fun w => T (e (parts w))) z :=
      T.contDiff.contDiffAt.comp z (hez.comp z hP)
    have hout := (PlanarCylinder.contDiffAt_map j (abs_lt.mp (hfirst z hz).2).1).comp z hT
    exact hout
  have hfi : InjOn f (PushedBall.domain (c/Real.pi)) := by
    intro z hz w hw hzw
    apply parts.injective
    apply HasSymplecticEmbedding.injOn hei (hball hz) (hball hw)
    apply targetCoordinates_injective A
    exact PlanarCylinder.map_injOn j (hfirst z hz) (hfirst w hw) hzw
  have hfω (z : C (Fin n)) (hz : z ∈ PushedBall.domain (c/Real.pi)) :
      ComplexSymplectic.Preserves (fderiv ℝ f z) := by
    have hez := he.contDiffAt ((isOpen_lt (by fun_prop) continuous_const).mem_nhds (hball hz))
    have hed := (hez.differentiableAt (by simp)).hasFDerivAt
    have hd := (PlanarCylinder.hasFDerivAt_map j (abs_lt.mp (hfirst z hz).2).1).comp z
      (T.hasFDerivAt.comp z (hed.comp z (parts (ι := Fin n)).hasFDerivAt))
    have hfd : fderiv ℝ f z = (PlanarCylinder.derivative j (T (e (parts z)))).comp
        (T.comp ((fderiv ℝ e (parts z)).comp parts.toContinuousLinearMap)) := hd.fderiv
    intro a b
    change inner (𝕜 := ℝ) (Complex.I • fderiv ℝ f z a) (fderiv ℝ f z b) =
      inner (𝕜 := ℝ) (Complex.I • a) b
    rw [← PlanarCylinder.form_eq_inner, ← PlanarCylinder.form_eq_inner, hfd]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [PlanarCylinder.derivative_preserves j (abs_lt.mp (hfirst z hz).2).1,
      targetCoordinates_preserves, form_parts]
    exact heω _ (hball hz) (parts a) (parts b)
  have hpK : IsCompact (polar K) := ConvexPolar.isCompact_polar
    (ConvexPolar.zero_mem_interior_of_symmetric hK.2.1 hK.2.2.1 hK.2.2.2)
  obtain ⟨B,hB,hTB⟩ := ((hK.1.prod hpK).image T.continuous).isBounded.exists_pos_norm_le
  have hbnd (z : C (Fin n)) (hz : z ∈ PushedBall.domain (c/Real.pi)) :
      ‖f z‖^2 ≤ B^2 + 4/Real.pi := by
    have hh := heK (hball hz)
    have hT := hTB _ ⟨e (parts z), ⟨interior_subset hh.1,interior_subset hh.2⟩, rfl⟩
    have hsq := (sq_le_sq₀ (norm_nonneg _) hB.le).mpr hT
    have hnorm := PlanarCylinder.norm_bound j (hfirst z hz)
    change ‖PlanarCylinder.map j (T (e (parts z)))‖^2 ≤ _
    linarith
  have hle := CylinderNonsqueezing.radius_le_of_map j (div_pos hc Real.pi_pos)
    (by positivity : (0:ℝ) ≤ 4/Real.pi) (by positivity : (0:ℝ) ≤ B^2+4/Real.pi)
    f (fun z hz => (hsm z hz).contDiffWithinAt) hfi hfω hbnd
    (fun z hz => (PlanarCylinder.first_bound j (hfirst z hz)).le)
  exact (div_le_div_iff_of_pos_right Real.pi_pos).mp hle

theorem gromovWidth_polarProduct_le_four {K : Set (Position n)}
    (hK : IsSymmetricConvexBody K) (hn : 0 < n) : gromovWidth (polarProduct K) ≤ 4 := by
  apply sSup_le
  rintro _ ⟨c,⟨hc,he⟩,rfl⟩
  exact (ENNReal.ofReal_le_ofReal (capacity_le_four_of_embedding hK hn hc he)).trans_eq (by norm_num)

end
end SymmetricPolar
end

end OAI
