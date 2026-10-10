import OAI.Analysis.KadisonSimilarity.Tracial.TracialHeadCoordinates
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialPropagation

namespace OAI

/-! Realize the abstract propagation data by actual tracial left multipliers.
The remaining word data are elementary reduced-word multiplication and
isometry identities; the scaled support and vanishing coefficient are proved. -/

noncomputable section
namespace KadisonSimilarity

variable {D P E H F B V : Type*} [CStarAlgebra D] [CStarAlgebra P]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

namespace TracialCornerGeometry

/-- A scaled initial projection in the algebra gives the corresponding
operator identity in any represented tracial Hilbert space. -/
theorem embedded_left_scaled_initial (G : TracialCornerGeometry P H)
    (ι : D →⋆ₐ[ℂ] P) (x q : D) (c : ℂ) (hx : star x * x = c • q) :
    (G.left (ι x)).adjoint.comp (G.left (ι x)) = c • G.left (ι q) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  change G.left (star (ι x)) * G.left (ι x) = _
  rw [← map_mul, ← map_star, ← map_mul, hx, map_smul, map_smul]

end TracialCornerGeometry

variable {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)
  [W.vacuum.HasOrthogonalProjection]
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq)) (a : ℝ)
  (Y : H →L[ℂ] H) (B₀ : B →L[ℂ] B) (Bₖ : V →L[ℂ] V)

/-- The remaining raw reduced-word geometry for a fixed positive degree.
All operators acting on the ambient space are specified as left multipliers.
There is no approximation estimate among these fields. -/
structure TracialRepeatedWordRealization where
  repeatVector : B →ₗᵢ[ℂ] V
  word : ℕ → V →ₗᵢ[ℂ] H
  small : B →L[ℂ] H
  small_norm : ∀ v, ‖small v‖ = Real.sqrt a * ‖v‖
  level_zero : ∀ v, Y (small v) = small (B₀ v)
  level_repeated : ∀ n v, Y (word n (repeatVector v)) = word n (Bₖ (repeatVector v))
  support_small : ∀ v, G.left (ι q) (small v) = small v
  prefixElement : ℕ → P
  word_factor : ∀ n v, word n (repeatVector v) =
    G.left (prefixElement n) (G.left (ι (haarCornerLetter z a n)) (small v))
  prefix_isometry : ∀ n, ∀ y ∈ W.vacuumᗮ, ‖G.left (prefixElement n) y‖ = ‖y‖
  prefix_bound : ℝ
  prefix_bound_le : ∀ n, ‖G.left (prefixElement n)‖ ≤ prefix_bound

namespace TracialRepeatedWordRealization

variable {W z a Y B₀ Bₖ}
  (R : TracialRepeatedWordRealization W z a Y B₀ Bₖ)

/-- The full abstract propagation data are derived from the raw word
realization and the actual corner Haar unitary. -/
def propagationData (hτ : GD.trace 1 = 1) (ha : 0 < a)
    (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a) :
    RepeatedLetterWords (E := E) (F := F) Y B₀ Bₖ W.vacuum a where
  repeatVector := R.repeatVector
  word := R.word
  small := R.small
  small_norm := R.small_norm
  level_zero := R.level_zero
  level_repeated := R.level_repeated
  support := G.left (ι q)
  support_small := R.support_small
  letter n := G.left (ι (haarCornerLetter z a n))
  letter_scale n := G.embedded_left_scaled_initial ι _ q _
    (star_haarCornerLetter_mul_self z ha.le n)
  wordPrefix n := G.left (R.prefixElement n)
  word_factor := R.word_factor
  prefix_isometry := R.prefix_isometry
  prefix_bound := R.prefix_bound
  prefix_bound_le := R.prefix_bound_le
  tensor_coordinates := W.unitary.toContinuousLinearEquiv.toContinuousLinearMap
  vacuum_insert := W.unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (hilbertTensorInsert (GD.vector 1))
  adjoint_letters n := GD.vector (star (haarCornerLetter z a n))
  adjoint_letters_orthonormal := GD.haarCornerLetter_adjoint_orthonormal z ha htrace hhaar
  vacuum_slice _ y := W.vacuum_slice hτ _ y

/-- Every fixed error vector has a vanishing exceptional coefficient; this
is a conclusion of Haar orthogonality and the head tensor representation. -/
theorem exceptional_coefficient_tendsto_zero (hτ : GD.trace 1 = 1) (ha : 0 < a)
    (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a) (y : H) :
    Filter.Tendsto (fun n => W.vacuum.starProjection
      (G.left (ι (haarCornerLetter z a n)) y)) Filter.atTop (nhds 0) :=
  W.haar_vacuum_tendsto_zero hτ z ha htrace hhaar y

/-- A supported column approximation propagates to the repeated word with
factor two. All action-commutation and exceptional-limit requirements have
been discharged in the tracial model. -/
theorem propagation (hτ : GD.trace 1 = 1) (ha : 0 < a)
    (htrace : GD.trace q = (a : ℂ)) (hhaar : HaarCornerMoments GD.trace z a)
    (r b : P) {η : ℝ}
    (hcolumn : ‖(Y - G.right b).comp (G.corner 1 r).toSubmodule.subtypeL‖ ≤ η)
    (v : B) (hv : R.small v ∈ (G.corner 1 r).toSubmodule) :
    ‖Bₖ (R.repeatVector v) - R.repeatVector (B₀ v)‖ ≤ 2 * η * ‖v‖ := by
  let Q := R.propagationData hτ ha htrace hhaar
  exact Q.propagation_of_tracial_column G ha (ι q) r
    (fun n => ι (haarCornerLetter z a n)) R.prefixElement rfl (fun _ => rfl) (fun _ => rfl)
    b hcolumn v hv

end TracialRepeatedWordRealization
end KadisonSimilarity

end

end OAI
