import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockErgodicity
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ReverseRootFlow
import OAI.NumberTheory.DukePrimeDegree.Geometry.RightObservableUniformity
import OAI.NumberTheory.DukePrimeDegree.Dynamics.TerminalGenericWindows

namespace OAI

/-!
# One generic set for all roots of the selected block

The shearing root and its limiting displacement are chosen after the
initial pair. Finiteness of the roots and compactness of the possible
displacements give a single good set and one terminal-time threshold
that work for every possible choice. Full real-root ergodicity comes
from the actual single-block component and the Mautner argument.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_singleBlock_terminal_generic_set {n : ℕ}
    (S : Set (Fin n)) (μ : Measure (X n)) [IsProbabilityMeasure μ]
    [ErgodicSMul (singleBlockRootGroup S) (X n) μ]
    (F : Finset (CompactlySupportedContinuousMap (X n) ℝ))
    (K : Set (G n)) (hK : IsCompact K)
    (ε δ η : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) :
    ∃ E : Set (X n), MeasurableSet E ∧ μ Eᶜ ≤ ENNReal.ofReal η ∧
      ∃ R : ℝ, 0 < R ∧
        ∀ x ∈ E, ∀ i ∈ S, ∀ j ∈ S, ∀ (hij : i ≠ j), ∀ f ∈ F, ∀ T ≥ R,
          |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
            f (rightAction x (Matrix.SpecialLinearGroup.transvection hij (-t)))) -
              ∫ y, f y ∂μ| ≤ ε ∧
          ∀ h ∈ K,
            |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
              f (rightAction (rightAction x
                (Matrix.SpecialLinearGroup.transvection hij (-t))) h)) -
                  ∫ y, f (rightAction y h) ∂μ| ≤ ε := by
  classical
  let A := {p : Fin n × Fin n // p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2}
  let D : Set (X n →ᵇ ℝ) := ⋃ f : F,
    insert f.val.toBoundedContinuousFunction (rightCompactObservable f.val '' K)
  have hD : IsCompact D := isCompact_iUnion fun f : F =>
    (hK.image (continuous_rightCompactObservable f.val)).insert _
  let η₀ := η / (Fintype.card A + 1)
  have hη₀ : 0 < η₀ := div_pos hη (by positivity)
  have hper (p : A) : ∃ E : Set (X n), MeasurableSet E ∧
      μ Eᶜ ≤ ENNReal.ofReal η₀ ∧ ∃ R : ℝ, 0 < R ∧
        ∀ x ∈ E, ∀ f ∈ D, ∀ T ≥ R,
          |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
            f (rightAction x (Matrix.SpecialLinearGroup.transvection p.property.2.2 (-t)))) -
              ∫ y, f y ∂μ| ≤ ε := by
    let := reverseRootTranslationAction p.property.2.2
    let : ContinuousSMul (Multiplicative ℝ) (X n) :=
      reverseRootTranslationAction_continuous p.property.2.2
    let : ErgodicSMul (Multiplicative ℝ) (X n) μ :=
      reverseRootTranslationAction_ergodic p.property.2.2 μ
        (root_ergodic_of_single_block_ergodic S p.property.2.2 p.property.1
          p.property.2.1 μ)
    obtain ⟨E, hE, hEμ, R, hR, hgood⟩ := exists_compact_family_real_flow_generic_set
      μ D hD (ε * δ / 2) η₀ (by positivity) hη₀
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    refine ⟨E, hE, hEμ, R / (1 - δ), div_pos hRpos (sub_pos.mpr hδ1), ?_⟩
    intro x hx f hf T hT
    have hc := terminal_window_control_of_prefix_control realActionTime f
      (fun y a b => ((continuous_flow_observable f).comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
      E (∫ y, f y ∂μ) (ε * δ / 2) δ R (by positivity) hδ hδ1 hRpos
      (fun y hy t ht => hgood y hy f hf t ht) x hx T hT
    convert hc using 1
    · rfl
    · field_simp
  choose E hE hEμ R hR hgood using hper
  let N := Finset.univ.sup (fun p : A => ⌈R p⌉₊)
  let R₀ : ℝ := max 1 N
  have hRR (p : A) : R p ≤ R₀ := by
    have hp : ⌈R p⌉₊ ≤ N := Finset.le_sup (f := fun p => ⌈R p⌉₊) (Finset.mem_univ p)
    have hp' : (⌈R p⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp
    exact (Nat.le_ceil (R p)).trans (hp'.trans (le_max_right _ _))
  refine ⟨⋂ p, E p, MeasurableSet.iInter hE, ?_, R₀,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  · rw [compl_iInter]
    calc
      μ (⋃ p, (E p)ᶜ) ≤ ∑ p, μ (E p)ᶜ := measure_iUnion_fintype_le μ _
      _ ≤ ∑ _p : A, ENNReal.ofReal η₀ := Finset.sum_le_sum (fun p _ => hEμ p)
      _ = ENNReal.ofReal ((Fintype.card A : ℝ) * η₀) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hη₀.le)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal η := by
        apply ENNReal.ofReal_le_ofReal
        dsimp only [η₀]
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < Fintype.card A + 1)]
        nlinarith
  · intro x hx i hi j hj hij f hf T hT
    let p : A := ⟨(i, j), hi, hj, hij⟩
    have hxE : x ∈ E p := mem_iInter.mp hx p
    have hTf : R p ≤ T := (hRR p).trans hT
    constructor
    · exact hgood p x hxE f.toBoundedContinuousFunction
        (mem_iUnion.mpr ⟨⟨f, hf⟩, Or.inl rfl⟩) T hTf
    · intro h hh
      exact hgood p x hxE (rightCompactObservable f h)
        (mem_iUnion.mpr ⟨⟨f, hf⟩, Or.inr ⟨h, hh, rfl⟩⟩) T hTf

end DukePrimeDegree

end

end OAI
