import OAI.Probability.InvariantIsing.Cavity.CavitySimultaneousFrame
import OAI.Probability.InvariantIsing.Cavity.CavityBaseSpecialHaar

namespace OAI

/-! Joint labeled spectral projectors and special axes of the physical
base model. Labels are retained even for repeated spectral values. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

abbrev CavityProjectorFrame (N m d : ℕ) :=
  (Fin m → Matrix (Fin N) (Fin N) ℝ) × Matrix (Fin N) (Fin d) ℝ

def cavityLabeledProjectorAction {N m d : ℕ} (V : Orthogonal N)
    (p : CavityProjectorFrame N m d) : CavityProjectorFrame N m d :=
  (fun a => cavityConjugate V (p.1 a), (V : Matrix (Fin N) (Fin N) ℝ) * p.2)

lemma continuous_cavityLabeledProjectorAction (N m d : ℕ) :
    Continuous (Function.uncurry (cavityLabeledProjectorAction (N := N) (m := m) (d := d))) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro a
    exact (continuous_cavityConjugate N).comp (continuous_fst.prodMk
      ((continuous_apply a).comp (continuous_fst.comp continuous_snd)))
  · exact (continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_snd.comp continuous_snd)

lemma cavityLabeledProjectorAction_mul {N m d : ℕ} (U V : Orthogonal N)
    (p : CavityProjectorFrame N m d) :
    cavityLabeledProjectorAction (U*V) p =
      cavityLabeledProjectorAction U (cavityLabeledProjectorAction V p) := by
  apply Prod.ext
  · funext a
    exact cavityConjugate_mul U V (p.1 a)
  · exact Matrix.mul_assoc _ _ _

def cavityPhysicalLabeledProjectors {N n m d : ℕ}
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (U : Orthogonal (N+n)) : CavityProjectorFrame N m d :=
  (fun a => cavityPhysicalBase g (fun b => if b=a then 1 else 0) B
      (Matrix.diagonal (fun j => if a₀ j=a then 1 else 0)) U,
    cavityPhysicalSpecial g B U)

def cavityCanonicalProjectorFrame {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) : CavityProjectorFrame N m d :=
  (fun a => Matrix.diagonal (fun j => Sum.elim
      (fun w => if w.1=a then 1 else 0) (fun j => if a₀ j=a then 1 else 0) (e.symm j)),
    cavityCanonicalSpecial e)

lemma measurable_cavityPhysicalLabeledProjectors {N n m d : ℕ}
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : Measurable B) (a₀ : Fin d → Fin m) :
    Measurable (cavityPhysicalLabeledProjectors g B a₀) := by
  unfold cavityPhysicalLabeledProjectors
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro a
    exact measurable_cavityPhysicalBase g (fun b => if b=a then 1 else 0) B hB
      (Matrix.diagonal (fun j => if a₀ j=a then 1 else 0))
  · exact measurable_cavityPhysicalSpecial g B hB

lemma cavityPhysicalLabeledProjectors_reservoir {N n m d : ℕ}
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (U : Orthogonal (N+n)) (V : Orthogonal N) :
    cavityPhysicalLabeledProjectors g B a₀ (U*cavityReservoirRotation (n := n) V⁻¹) =
      cavityLabeledProjectorAction V (cavityPhysicalLabeledProjectors g B a₀ U) := by
  apply Prod.ext
  · funext a
    exact cavityPhysicalBase_reservoir_inv g (fun b => if b=a then 1 else 0) B
      (Matrix.diagonal (fun j => if a₀ j=a then 1 else 0)) U V
  · have h := cavityPhysicalSpecial_reservoir g B U V⁻¹
    have hV : (V⁻¹ : Orthogonal N).val = (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
      ext i j
      rfl
    simpa only [hV, Matrix.transpose_transpose, cavityPhysicalLabeledProjectors,
      cavityLabeledProjectorAction] using h

theorem cavityPhysicalLabeledProjectors_mem_orbit {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (U : Orthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g U)).transpose * B (cavityCompressionGrams g U) = 1)
    (hBT : (B (cavityCompressionGrams g U)).transpose *
      cavitySpectralStack (cavityCompressionGrams g U) = 0)
    (hA : ∀ a, (cavityCompressionGrams g U a).PosDef) :
    ∃ V : Orthogonal N, cavityPhysicalLabeledProjectors g B a₀ U =
      cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) := by
  obtain ⟨V,hV,hS⟩ := cavityPhysicalBaseSpecial_simultaneous g k ek e U B hB hBT hA
  refine ⟨V, Prod.ext ?_ hS⟩
  funext a
  exact hV (fun b => if b=a then 1 else 0) (fun j => if a₀ j=a then 1 else 0)

end InvariantIsing

end

end OAI
