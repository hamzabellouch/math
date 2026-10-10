import OAI.NumberTheory.DukePrimeDegree.Geometry.GoodSetFiberCorrection
import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockMatrixProjection

namespace OAI

/-!
# Simultaneous generic representatives of a transverse pair

A correction in a block-preserving subgroup may depend on the pair.
The Haar-fiber selection puts both corrected points back in the same
generic set, and simultaneous block conjugation preserves the scalar
within-block normalization.  The subgroup is contained in the actual
measure stabilizer in the application; that inclusion is explicit here.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma measurable_rightAction_subgroup_uncurry {n : ℕ} (H : Subgroup (G n)) :
    Measurable (fun p : X n × H => rightAction p.1 (p.2 : G n)) := by
  exact ((continuous_rightAction_uncurry n).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).measurable

/-- The finite-patch enlargement uses invariance of the ambient measure
under its actual stabilizer, without selecting an ergodic time-one map. -/
theorem exists_actual_stabilizer_fiber_good_set {n : ℕ}
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (H : Subgroup (G n)) (hH : H ≤ invariantRightSubgroup μ)
    (ρ : Measure H) [SFinite ρ] (K : Set H)
    (G₀ : Set (X n)) (hG₀ : MeasurableSet G₀)
    (a : ℝ≥0∞) (ha : a ≠ 0) (hatop : a ≠ ⊤) :
    ∃ E : Set (X n), MeasurableSet E ∧
      μ Eᶜ ≤ (ρ K * μ G₀ᶜ) / a ∧
      ∀ x ∈ E,
        badOrbitFiberMass ρ (fun y h => rightAction y (h : G n)) K G₀ x < a := by
  apply exists_goodOrbitFiber_set μ ρ (fun y h => rightAction y (h : G n))
    (measurable_rightAction_subgroup_uncurry H) _ K G₀ hG₀ a ha hatop
  intro h
  exact ⟨(continuous_rightAction (h : G n)).measurable, hH h.property⟩

/-- Algebraic and generic-set properties hold for the very same common
translation.  The selected translation lies in the prescribed bounded
patch; it is not an extra independent limit or invariance hypothesis. -/
theorem exists_corrected_generic_pair {n : ℕ}
    (L H : Subgroup (G n)) (hHL : H ≤ L)
    (r : Setoid (Fin n)) (hblock : H ≤ blockMatrixGroup r)
    (ρ : Measure H) [ρ.IsMulLeftInvariant]
    (K₀ K₁ : Set H) (hK : K₀ ⊆ K₁)
    (G₀ : Set (X n)) (hG₀ : MeasurableSet G₀)
    (x : X n) (a : G n) (ha : a ∉ L) (b : H)
    (hb : ∀ h ∈ K₀, b * h ∈ K₁)
    (c : ℝ)
    (hpart : withinBlockPart r (a * (b : G n)).val = Matrix.diagonal (fun _ => c))
    (hsmall :
      badOrbitFiberMass ρ (fun y h => rightAction y (h : G n)) K₁ G₀ x +
      badOrbitFiberMass ρ (fun y h => rightAction y (h : G n)) K₁ G₀
        (rightAction x a) < ρ K₀) :
    ∃ h ∈ K₀,
      rightAction x (h : G n) ∈ G₀ ∧
      rightAction (rightAction x (h : G n))
        ((h : G n)⁻¹ * (a * (b : G n)) * (h : G n)) ∈ G₀ ∧
      (h : G n)⁻¹ * (a * (b : G n)) * (h : G n) ∉ L ∧
      withinBlockPart r ((h : G n)⁻¹ * (a * (b : G n)) * (h : G n)).val =
        Matrix.diagonal (fun _ => c) := by
  obtain ⟨h, hh, hx, hy⟩ := exists_common_goodOrbit_correction ρ
    (fun y h => rightAction y (h : G n))
    (fun y => ((continuous_rightAction_uncurry n).comp
      (continuous_const.prodMk continuous_subtype_val)).measurable)
    K₀ K₁ hK G₀ hG₀ x (rightAction x a) b hb hsmall
  refine ⟨h, hh, hx, ?_, ?_, ?_⟩
  · have heq : rightAction (rightAction x (h : G n))
        ((h : G n)⁻¹ * (a * (b : G n)) * (h : G n)) =
        rightAction (rightAction x a) ((b * h : H) : G n) := by
      simp only [rightAction_mul, Subgroup.coe_mul]
      congr 1
      group
    exact heq.symm ▸ hy
  · intro hmem
    have hhL := hHL h.property
    have hbL := hHL b.property
    have hab : a * (b : G n) ∈ L := by
      have ht := L.mul_mem (L.mul_mem hhL hmem) (L.inv_mem hhL)
      convert ht using 1
      group
    have ht := L.mul_mem hab (L.inv_mem hbL)
    apply ha
    simpa only [mul_inv_cancel_right] using ht
  · have heq : (h : G n)⁻¹ * (a * (b : G n)) * (h : G n) =
        (h : G n)⁻¹ * (a * (b : G n)) * ((h : G n)⁻¹)⁻¹ := by simp
    rw [heq]
    exact withinBlockPart_conjugate_scalar r (a * (b : G n)) (h : G n)⁻¹
      ((blockMatrixGroup r).inv_mem (hblock h.property)) c hpart

end DukePrimeDegree

end

end OAI
