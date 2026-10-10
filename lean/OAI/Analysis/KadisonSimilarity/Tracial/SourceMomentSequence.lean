import OAI.Analysis.KadisonSimilarity.Tracial.SourceUnitaryMoments

namespace OAI

/-! A diagonal sequence of source unitaries annihilates every fixed finite
mixed word in a countable family of ambient coefficient sequences. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison HochschildPatching BoundedHochschild
open Filter Topology
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

include hfactor hdiff hirr in
theorem exists_source_small_moment_sequence
    (F : ℕ → ℕ → M.toStarSubalgebra)
    (hF : ∀ n i, ‖F n i‖ ≤ 1) (hFτ : ∀ n i, υ.trace (F n i) = 0) :
    ∃ u : ℕ → unitary R.toStarSubalgebra, ∀ m K N : ℕ,
      ∀ a : BoundedWord (Fin m) K N, admissibleTail a.2.val →
      Tendsto (fun n => υ.trace (mixedEval (fun i : Fin m => F n i.val)
        (SourcePartialUnitary.map (coordinateInclusion hRM) (asPartialUnitary (u n)))
        a.1 a.2.val)) atTop (𝓝 0) := by
  classical
  have hex (n : ℕ) := exists_source_unitary_small_moments υ hRM hfactor hdiff hirr
    (fun i : Fin n => F n i.val) (fun i => hF n i.val) (fun i => hFτ n i.val)
    (Nat.zero_lt_succ n) (N := n) (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose u hu using hex
  refine ⟨u, fun m K N a ha => ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨b, hb⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop (max b (max m (max K N)))] with n hn
  have hbn : b ≤ n := (le_max_left _ _).trans hn
  have hmn : m ≤ n := (le_max_left m (max K N)).trans ((le_max_right b _).trans hn)
  have hKn : K ≤ n := (le_max_left K N).trans ((le_max_right m _).trans ((le_max_right b _).trans hn))
  have hNn : N ≤ n := (le_max_right K N).trans ((le_max_right m _).trans ((le_max_right b _).trans hn))
  let f : Fin m → Fin n := fun i => ⟨i.val, i.isLt.trans_le hmn⟩
  let g : Fin K → Fin (n + 1) := fun i => ⟨i.val, i.isLt.trans_le (hKn.trans (Nat.le_succ n))⟩
  let a' : BoundedWord (Fin n) (n + 1) n :=
    (a.1.map f, ⟨a.2.val.map (mapAtom f g), by simpa using a.2.property.trans hNn⟩)
  have htest := hu n a' (admissibleTail_map f g a.2.val ha)
  change ‖υ.trace (mixedEval (fun i : Fin n => F n i.val)
    (SourcePartialUnitary.map (coordinateInclusion hRM) (asPartialUnitary (u n)))
    (a.1.map f) (a.2.val.map (mapAtom f g)))‖ < _ at htest
  rw [mixedEval_map _ f g (fun _ => rfl)] at htest
  have hFcomp : (fun i : Fin n => F n i.val) ∘ f = (fun i : Fin m => F n i.val) := rfl
  rw [hFcomp] at htest
  have hne : 1 / ((n : ℝ) + 1) < ε := by
    have hbR : (b : ℝ) ≤ n := by exact_mod_cast hbn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    apply (div_lt_iff₀ hpos).mpr
    have hh := (div_lt_iff₀ hε).mp hb
    nlinarith
  simpa only [dist_zero_right] using htest.trans hne

end KadisonSimilarity

end

end OAI
