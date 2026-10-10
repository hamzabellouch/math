import OAI.NumberTheory.DukePrimeDegree.Geometry.IndexedLinearShear

namespace OAI

/-! # Each remaining-root shear preserves the actual intrinsic product -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_intrinsic_indexedLinearShear_preserves
    (d : ℕ) (S : Finset (Fin (d+1) × Fin (d+1)))
    (hpos : ∀ p ∈ S, p.1 < p.2) {a b c : Fin (d+1)} (hab : a ≠ b)
    (hbc : (b,c) ∈ S) (hac : (a,c) ∈ S)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hna : ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hab μ x)) :
    ∀ᵐ x ∂μ, ∀ r : ℝ,
      MeasurePreserving (indexedLinearShear (⟨(a,c),hac⟩ : S) ⟨(b,c),hbc⟩ r)
        (Measure.pi fun p : S => intrinsicRootLeaf (ne_of_lt (hpos p.val p.prop)) μ x)
        (Measure.pi fun p : S => intrinsicRootLeaf (ne_of_lt (hpos p.val p.prop)) μ x) := by
  classical
  have hbc' : b ≠ c := ne_of_lt (hpos _ hbc)
  have hac' : a ≠ c := ne_of_lt (hpos _ hac)
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree (p : S) : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection
        (ne_of_lt (hpos p.val p.prop)) t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _
  have hs := ae_all_iff.mpr fun p : S =>
    ae_intrinsicRootLeaf_spec (ne_of_lt (hpos p.val p.prop)) μ (hfree p)
  have halt : ∀ᵐ x ∂μ,
      intrinsicRootLeaf hbc' μ x = Measure.dirac 0 ∨
      ∀ r : ℝ, (intrinsicRootLeaf hac' μ x).map (fun t => t+r) = intrinsicRootLeaf hac' μ x := by
    rcases intrinsicRootLeaf_ergodic_alternative d hbc' μ with hb | hb
    · have hinv := root_invariant_of_adjacent_nonatomic_leaves d hab hbc' hac' μ hna hb
      exact (ae_rootLeaf_invariant_of_root_invariant d hac' μ hA hinv).mono
        fun _ hx => Or.inr hx
    · exact hb.mono fun _ hx => Or.inl hx
  filter_upwards [hs,halt] with x hx ha
  let ν (p : S) := intrinsicRootLeaf (ne_of_lt (hpos p.val p.prop)) μ x
  let : ∀ p : S, IsLocallyFiniteMeasure (ν p) := fun p => (hx p).1
  have hne : (⟨(b,c),hbc⟩ : S) ≠ ⟨(a,c),hac⟩ := by
    intro he
    exact hab (congrArg (fun p : S => p.val.1) he).symm
  intro r
  exact indexedLinearShear_preserves _ _ hne r ν ha

end DukePrimeDegree

end

end OAI
