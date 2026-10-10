import OAI.Analysis.KadisonSimilarity.FreeProduct.ArcFourier
import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralPositiveDensity
import OAI.Analysis.KadisonSimilarity.Tracial.TracialCornerExpectations

namespace OAI

/-! The bounded Borel spectral calculus input, specialized to the centered
arc of a Haar rotation in a finite dihedral von Neumann algebra. Blackadar,
Operator Algebras, I.6.2.4 and I.6.2.8, supply the calculus and commutation;
integration against its Haar spectral measure gives the stated moments.

The interface is local to the specified trace and algebra. Its intended
application has the normal finite trace and the von Neumann algebra generated
by the two symmetries. No existence assertion is made for an arbitrary C-star
subalgebra or an arbitrary linear functional. The corner estimates below are
proved from the spectral data, rather than included in the published input. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- The half projection of a selfadjoint involution. -/
theorem isStarProjection_dihedralHalfProjection (d : Pˣ)
    (hd : star (d : P) = (d : P)) (hdd : d * d = 1) :
    IsStarProjection (dihedralHalfProjection d) := by
  have hdd' : (d : P) * (d : P) = 1 := by
    rw [← Units.val_mul, hdd, Units.val_one]
  apply isStarProjection_iff'.2
  constructor
  · simp only [dihedralHalfProjection, smul_mul_assoc, mul_smul_comm,
      add_mul, mul_add, one_mul, mul_one, hdd']
    module
  · simp only [dihedralHalfProjection, star_smul, star_add, star_one, hd]
    norm_num

/-- Centering the reflection fixes the trace of its half projection. -/
theorem trace_dihedralHalfProjection (τ : P →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (d : Pˣ) (hd : τ (d : P) = 0) : τ (dihedralHalfProjection d) = (1 / 2 : ℂ) := by
  simp only [dihedralHalfProjection, map_smul, map_add, hτ, hd, add_zero, smul_eq_mul,
    mul_one]

/-- Exactly the spectral data of the centered arc used in the argument. -/
structure DihedralSpectralArc (τ : P →ₗ[ℂ] ℂ) (C : StarSubalgebra ℂ P)
    (w d : Pˣ) (θ : ℝ) where
  element : P
  mem : element ∈ C
  selfAdjoint : star element = element
  norm_le : ‖element‖ ≤ 1
  commute_rotation : Commute element (w : P)
  commute_reflection : Commute element (d : P)
  rotation_moment : ∀ l : ℤ, τ (element * (↑(w ^ l) : P)) = arcFourierIntegral θ l
  reflection_moment : ∀ l : ℤ, τ ((element * (↑(w ^ l) : P)) * (d : P)) = 0
  square_moment : τ (element * element) = ((θ / Real.pi) * (1 - θ / Real.pi) : ℝ)
  square_reflection_moment : τ ((element * element) * (d : P)) = 0

/-- The local bounded Borel functional calculus specialization. In its
application `C` is the dihedral von Neumann algebra and `τ` its normal trace. -/
def DihedralSpectralArcInput (τ : P →ₗ[ℂ] ℂ) (C : StarSubalgebra ℂ P)
    (w d : Pˣ) : Prop :=
  ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi → Nonempty (DihedralSpectralArc τ C w d θ)

namespace DihedralSpectralArc

variable {τ : P →ₗ[ℂ] ℂ} {C : StarSubalgebra ℂ P} {w d : Pˣ} {θ : ℝ}
  (F : DihedralSpectralArc τ C w d θ)

theorem trace_zero (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) : τ F.element = 0 := by
  have h := F.rotation_moment 0
  simpa only [zpow_zero, Units.val_one, mul_one, arcFourierIntegral_zero hθ hπ] using h

theorem rotation_commutes (l : ℤ) :
    (↑(w ^ l) : P) * F.element = F.element * (↑(w ^ l) : P) :=
  (F.commute_rotation.units_zpow_right l).eq.symm

/-- The reflection used in the Hankel term is `w⁻¹d`, rather than `d`.
Traciality shifts the Fourier index and supplies its zero mixed moment. -/
theorem shifted_reflection_moment (htr : ∀ x y, τ (x * y) = τ (y * x)) (l : ℤ) :
    τ ((↑(w⁻¹ * d) : P) * (F.element * (↑(w ^ l) : P))) = 0 := by
  have hpow : w ^ l * w⁻¹ = w ^ (l - 1) := by
    rw [← zpow_neg_one, ← zpow_add]
    congr 1
  rw [htr]
  have hid : (F.element * (↑(w ^ l) : P)) * (↑(w⁻¹ * d) : P) =
      (F.element * (↑(w ^ (l - 1)) : P)) * (d : P) := by
    have hval : (↑(w ^ l) : P) * (↑w⁻¹ : P) = (↑(w ^ (l - 1)) : P) := by
      rw [← Units.val_mul, hpow]
    calc
      _ = F.element * ((↑(w ^ l) : P) * (↑w⁻¹ : P)) * (d : P) := by
        simp only [Units.val_mul, mul_assoc]
      _ = _ := by rw [hval]
  rw [hid, F.reflection_moment]

theorem halfProjection_commutes :
    Commute F.element (dihedralHalfProjection d) := by
  change F.element * ((1 / 2 : ℂ) • (1 + (d : P))) =
    ((1 / 2 : ℂ) • (1 + (d : P))) * F.element
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
    F.commute_reflection.eq]

/-- The actual arc element in the normalized half corner. -/
def corner (hp : IsStarProjection (dihedralHalfProjection d)) :
    CStarCorner (dihedralHalfProjection d) hp :=
  ⟨F.element * dihedralHalfProjection d, by
    constructor
    · rw [← mul_assoc, ← F.halfProjection_commutes.eq, mul_assoc,
        hp.isIdempotentElem.eq]
    · rw [mul_assoc, hp.isIdempotentElem.eq]⟩

@[simp] theorem corner_coe (hp : IsStarProjection (dihedralHalfProjection d)) :
    (F.corner hp : P) = F.element * dihedralHalfProjection d := rfl

theorem corner_mem (hp : IsStarProjection (dihedralHalfProjection d))
    (hdC : (d : P) ∈ C) : (F.corner hp : P) ∈ C :=
  C.mul_mem F.mem (C.smul_mem (C.add_mem C.one_mem hdC) _)

theorem corner_selfAdjoint (hp : IsStarProjection (dihedralHalfProjection d)) :
    star (F.corner hp) = F.corner hp := by
  apply Subtype.ext
  change star (F.element * dihedralHalfProjection d) = _
  rw [star_mul, hp.isSelfAdjoint.star_eq, F.selfAdjoint,
    ← F.halfProjection_commutes.eq]
  rfl

theorem corner_norm_le (hp : IsStarProjection (dihedralHalfProjection d)) :
    ‖F.corner hp‖ ≤ 1 := by
  change ‖F.element * dihedralHalfProjection d‖ ≤ 1
  exact (norm_mul_le _ _).trans
    ((mul_le_mul F.norm_le hp.norm_le (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))

theorem corner_trace_zero (hp : IsStarProjection (dihedralHalfProjection d))
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) : τ (F.corner hp : P) = 0 := by
  have hd0 : τ (F.element * (d : P)) = 0 := by
    simpa only [zpow_zero, Units.val_one, mul_one] using F.reflection_moment 0
  simp only [corner_coe, dihedralHalfProjection, mul_smul_comm, mul_add, mul_one,
    map_smul, map_add, F.trace_zero hθ hπ, hd0, add_zero, smul_zero]

theorem corner_square (hp : IsStarProjection (dihedralHalfProjection d)) :
    ((F.corner hp * F.corner hp : CStarCorner (dihedralHalfProjection d) hp) : P) =
      (F.element * F.element) * dihedralHalfProjection d := by
  change (F.element * dihedralHalfProjection d) *
    (F.element * dihedralHalfProjection d) = _
  calc
    _ = F.element * (dihedralHalfProjection d * F.element) *
        dihedralHalfProjection d := by simp only [mul_assoc]
    _ = F.element * (F.element * dihedralHalfProjection d) *
        dihedralHalfProjection d := by rw [← F.halfProjection_commutes.eq]
    _ = _ := by simp only [mul_assoc, hp.isIdempotentElem.eq]

/-- Normalization cancels the half-corner trace, leaving the arc variance. -/
theorem corner_second_moment (hp : IsStarProjection (dihedralHalfProjection d))
    (ht : τ (dihedralHalfProjection d) = (1 / 2 : ℂ)) :
    CStarCorner.normalizedTrace (dihedralHalfProjection d) hp τ
      (star (F.corner hp) * F.corner hp) = ((θ / Real.pi) * (1 - θ / Real.pi) : ℝ) := by
  rw [F.corner_selfAdjoint hp, CStarCorner.normalizedTrace_apply, F.corner_square hp, ht]
  simp only [dihedralHalfProjection, mul_smul_comm, mul_add, mul_one,
    map_smul, map_add, F.square_moment, F.square_reflection_moment, add_zero,
    smul_eq_mul]
  ring

theorem corner_second_moment_le (hp : IsStarProjection (dihedralHalfProjection d))
    (ht : τ (dihedralHalfProjection d) = (1 / 2 : ℂ))
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp τ
      (star (F.corner hp) * F.corner hp)).re ≤ 4 * θ := by
  rw [F.corner_second_moment hp ht, Complex.ofReal_re,
    ← centeredArc_second_moment hθ hπ]
  exact centeredArc_second_moment_le hθ hπ

/-- The trace-pairing expectation of the actual compressed arc is derived
from normalized corner freeness. The factor `2t` is not an extra hypothesis. -/
theorem compressed_expectation
    (E : TracialExpectation τ C)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (htr : ∀ x y, τ (x * y) = τ (y * x))
    (hp : IsStarProjection (dihedralHalfProjection d))
    (hpC : dihedralHalfProjection d ∈ C)
    (D : StarSubalgebra ℂ P) (hpD : dihedralHalfProjection d ∈ D)
    (htp : τ (dihedralHalfProjection d) = (1 / 2 : ℂ))
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp τ)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC))
    (e : CStarCorner (dihedralHalfProjection d) hp) (heD : (e : P) ∈ D)
    (hdC : (d : P) ∈ C) {t : ℝ} (hte : τ (e : P) = (t : ℂ))
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    E.map ((e : P) * (F.element * dihedralHalfProjection d) * (e : P)) =
      (2 * (t : ℂ)) ^ 2 • (F.element * dihedralHalfProjection d) := by
  have htne : τ (dihedralHalfProjection d) ≠ 0 := by rw [htp]; norm_num
  have h := E.free_corner_compression hfaithful htr (dihedralHalfProjection d) hp hpC
    htne D hpD hfree e (F.corner hp) heD (F.corner_mem hp hdC)
    (F.corner_trace_zero hp hθ hπ)
  simpa only [F.corner_coe, htp, hte, one_div, inv_inv] using h

end DihedralSpectralArc
end KadisonSimilarity

end

end OAI
