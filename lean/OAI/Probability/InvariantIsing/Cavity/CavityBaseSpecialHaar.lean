import OAI.Probability.InvariantIsing.Cavity.CavityConcreteHaar
import OAI.Probability.InvariantIsing.Cavity.CavityConcreteFrameOrbit

namespace OAI

/-! The joint Haar law of the actual base interaction and its special
axes is independent of the cavity compression matrices. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

def cavityBaseSpecialAction {N d : ℕ} (V : Orthogonal N)
    (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin d) ℝ) :
    Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin d) ℝ :=
  (cavityConjugate V p.1, (V : Matrix (Fin N) (Fin N) ℝ) * p.2)

lemma continuous_cavityBaseSpecialAction (N d : ℕ) :
    Continuous (Function.uncurry (cavityBaseSpecialAction (N := N) (d := d))) := by
  exact (((continuous_subtype_val.comp continuous_fst).matrix_mul
    (continuous_fst.comp continuous_snd)).matrix_mul
      (continuous_subtype_val.comp continuous_fst).matrix_transpose).prodMk
    ((continuous_subtype_val.comp continuous_fst).matrix_mul (continuous_snd.comp continuous_snd))

lemma cavityBaseSpecialAction_mul {N d : ℕ} (U V : Orthogonal N)
    (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin d) ℝ) :
    cavityBaseSpecialAction (U * V) p =
      cavityBaseSpecialAction U (cavityBaseSpecialAction V p) := by
  apply Prod.ext
  · exact cavityConjugate_mul U V p.1
  · change ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) * p.2 =
      (U : Matrix (Fin N) (Fin N) ℝ) * ((V : Matrix (Fin N) (Fin N) ℝ) * p.2)
    exact Matrix.mul_assoc _ _ _

theorem cavityConcreteBaseSpecial_haar_factorization {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N + n) // g i = a} ≃ Fin (k a + n))
    (e : ((a : Fin m) × Fin (k a)) ⊕ Fin d ≃ Fin N)
    (e₀ : Fin (m * n) ≃ Fin (d + n))
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (l u : Fin m → ℕ)
    (hg : ∀ a i, g i = a ↔ l a ≤ i.val ∧ i.val < u a)
    (hln : ∀ a, l a + n ≤ u a) (hu : ∀ a, u a ≤ N + n)
    (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (μ : Measure (Orthogonal (N + n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (f : (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin d) ℝ) → ℝ)
    (q : (Fin m → Matrix (Fin n) (Fin n) ℝ) → ℝ)
    (hf : Measurable f) (hq : Measurable q)
    (Cf Cq : ℝ) (hCq : 0 ≤ Cq)
    (hfb : ∀ J, ‖f J‖ ≤ Cf) (hqb : ∀ M, ‖q M‖ ≤ Cq) :
    (∫ U, q (cavityCompressionGrams g U) *
      f (cavityPhysicalBase g lam (cavityConcreteComplement e₀ B₀) (Matrix.diagonal lam₀) U,
        cavityPhysicalSpecial g (cavityConcreteComplement e₀ B₀) U) ∂μ) =
      (∫ U, q (cavityCompressionGrams g U) ∂μ) *
        ∫ V, f (cavityBaseSpecialAction V
          (Matrix.diagonal (fun j => Sum.elim (fun a => lam a.1) lam₀ (e.symm j)),
            cavityCanonicalSpecial e)) ∂ν := by
  let : BorelSpace (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin d) ℝ) :=
    inferInstanceAs (BorelSpace ((Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ)))
  let : OpensMeasurableSpace (Orthogonal N ×
      (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin d) ℝ)) := inferInstanceAs
    (OpensMeasurableSpace (Orthogonal N × ((Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ))))
  let B := cavityConcreteComplement e₀ B₀
  have hBm : Measurable B := measurable_cavityConcreteComplement e₀ B₀
  apply cavity_orbit_factorization_right_ae μ ν
    (fun V => cavityReservoirRotation (n := n) V⁻¹)
    (fun U => (cavityPhysicalBase g lam B (Matrix.diagonal lam₀) U, cavityPhysicalSpecial g B U))
    (cavityCompressionGrams g)
    ((measurable_cavityPhysicalBase g lam B hBm _).prodMk (measurable_cavityPhysicalSpecial g B hBm))
    (measurable_cavityCompressionGrams g) cavityBaseSpecialAction
    (continuous_cavityBaseSpecialAction N d).measurable cavityBaseSpecialAction_mul
    _ _ _ _ f q hf hq Cf Cq hCq hfb hqb
  · intro V
    apply ae_of_all
    intro U
    apply Prod.ext
    · exact cavityPhysicalBase_reservoir_inv g lam B _ U V
    · have h := cavityPhysicalSpecial_reservoir g B U V⁻¹
      have hV : (V⁻¹ : Orthogonal N).val = (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
        ext i j
        rfl
      simpa only [hV, Matrix.transpose_transpose, cavityBaseSpecialAction] using h
  · intro V
    exact ae_of_all _ (fun U => cavityCompressionGrams_reservoir g U V⁻¹)
  · filter_upwards [cavityCompressionGrams_posDef_ae g l u hg hln hu μ] with U hU
    obtain ⟨V, hJ, hS⟩ := cavityPhysicalBaseSpecial_mem_orbit g k ek e U lam lam₀ B
      (cavityConcreteComplement_gram g e₀ B₀ U) (cavityConcreteComplement_perp g e₀ B₀ U) hU
    exact ⟨V, Prod.ext hJ hS⟩

end InvariantIsing

end

end OAI
