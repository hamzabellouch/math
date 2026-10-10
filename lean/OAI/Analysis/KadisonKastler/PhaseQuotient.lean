import OAI.Analysis.KadisonKastler.FreeHaar
import OAI.Analysis.KadisonKastler.UltrapowerExpectation

namespace OAI

/-! # Phase coefficients in a tracial sequence quotient

The multiset coefficients are finite noncommutative polynomials. Their
bounded-sequence versions therefore descend exactly to the coefficients
of the constant partition and the quotient unitary. The free-word estimate
therefore applies to those quotient coefficients.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive phase coefficients commute with star algebra homomorphisms. -/
theorem map_positivePhaseCoefficient (φ : A →⋆ₐ[ℂ] B) (e : ι → A) (w : A)
    (r : ℕ) (s : Sym ι r) :
    φ (positivePhaseCoefficient e w r s) =
      positivePhaseCoefficient (fun a => φ (e a)) (φ w) r s := by
  induction r with
  | zero => simp only [positivePhaseCoefficient, map_one]
  | succ r ih =>
    simp only [positivePhaseCoefficient, map_sum, map_mul, ih]
    by_cases hr : r = 0 <;> simp only [hr, ite_true, ite_false, map_one]

/-- Negative phase coefficients have the same functoriality. -/
theorem map_negativePhaseCoefficient (φ : A →⋆ₐ[ℂ] B) (e : ι → A) (w : A)
    (r : ℕ) (s : Sym ι r) :
    φ (negativePhaseCoefficient e w r s) =
      negativePhaseCoefficient (fun a => φ (e a)) (φ w) r s := by
  simp only [negativePhaseCoefficient, map_mul, map_star, map_positivePhaseCoefficient]

/-- The actual positive coefficient bounded sequence. -/
def positivePhaseCoefficientSequence (e : ι → A) (w : BoundedSequence A)
    (r : ℕ) (s : Sym ι r) : BoundedSequence A :=
  positivePhaseCoefficient (fun a => boundedSequenceConst (e a)) w r s

/-- The actual negative coefficient bounded sequence. -/
def negativePhaseCoefficientSequence (e : ι → A) (w : BoundedSequence A)
    (r : ℕ) (s : Sym ι r) : BoundedSequence A :=
  negativePhaseCoefficient (fun a => boundedSequenceConst (e a)) w r s

@[simp]
theorem positivePhaseCoefficientSequence_apply (e : ι → A) (w : BoundedSequence A)
    (r : ℕ) (s : Sym ι r) (j : ℕ) :
    positivePhaseCoefficientSequence e w r s j = positivePhaseCoefficient e (w j) r s :=
  map_positivePhaseCoefficient (boundedSequenceEval j)
    (fun a => boundedSequenceConst (e a)) w r s

@[simp]
theorem negativePhaseCoefficientSequence_apply (e : ι → A) (w : BoundedSequence A)
    (r : ℕ) (s : Sym ι r) (j : ℕ) :
    negativePhaseCoefficientSequence e w r s j = negativePhaseCoefficient e (w j) r s :=
  map_negativePhaseCoefficient (boundedSequenceEval j)
    (fun a => boundedSequenceConst (e a)) w r s

/-- Quotients preserve the actual positive coefficient sequence exactly. -/
theorem quotient_positivePhaseCoefficientSequence (π : BoundedSequence A →⋆ₐ[ℂ] B)
    (e : ι → A) (w : BoundedSequence A) (r : ℕ) (s : Sym ι r) :
    π (positivePhaseCoefficientSequence e w r s) =
      positivePhaseCoefficient (fun a => π (boundedSequenceConst (e a))) (π w) r s :=
  map_positivePhaseCoefficient π (fun a => boundedSequenceConst (e a)) w r s

/-- Quotients preserve the actual negative coefficient sequence exactly. -/
theorem quotient_negativePhaseCoefficientSequence (π : BoundedSequence A →⋆ₐ[ℂ] B)
    (e : ι → A) (w : BoundedSequence A) (r : ℕ) (s : Sym ι r) :
    π (negativePhaseCoefficientSequence e w r s) =
      negativePhaseCoefficient (fun a => π (boundedSequenceConst (e a))) (π w) r s :=
  map_negativePhaseCoefficient π (fun a => boundedSequenceConst (e a)) w r s

omit [Fintype ι] in
/-- The support sum is also preserved by a star algebra homomorphism. -/
theorem map_phaseSupport (φ : A →⋆ₐ[ℂ] B) (e : ι → A) (s : Multiset ι) :
    φ (phaseSupport e s) = phaseSupport (fun a => φ (e a)) s := by
  simp only [phaseSupport, map_sum]

/-- Coordinate coefficients retain their actual right support. -/
theorem phaseCoefficientSequence_right_support
    (e : ι → A) (w : BoundedSequence A)
    (he : ∀ a, star (e a) = e a)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (r : ℕ) (s : Sym ι (r + 1)) (j : ℕ) :
    positivePhaseCoefficientSequence e w (r + 1) s j * phaseSupport e (s : Multiset ι) =
        positivePhaseCoefficientSequence e w (r + 1) s j ∧
      negativePhaseCoefficientSequence e w (r + 1) s j * phaseSupport e (s : Multiset ι) =
        negativePhaseCoefficientSequence e w (r + 1) s j := by
  rw [positivePhaseCoefficientSequence_apply, negativePhaseCoefficientSequence_apply]
  exact ⟨positivePhaseCoefficient_right_support e (w j) hmul r s,
    negativePhaseCoefficient_right_support e (w j) he hmul r s⟩

section RepresentedColumn

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Both signs of the actual coordinate coefficient family are isometric
columns after applying any Hilbert-space star representation. -/
theorem phaseCoefficientSequence_column_norm
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : ι → A)
    (w : unitary (BoundedSequence A))
    (he : ∀ a, star (e a) = e a)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (hsum : ∑ a, e a = 1) (r : ℕ) (j : ℕ) (ξ : H) :
    ‖WithLp.toLp 2 (fun s : Sym ι (r + 1) =>
      ρ (positivePhaseCoefficientSequence e (w : BoundedSequence A) (r + 1) s j) ξ)‖ = ‖ξ‖ ∧
    ‖WithLp.toLp 2 (fun s : Sym ι (r + 1) =>
      ρ (negativePhaseCoefficientSequence e (w : BoundedSequence A) (r + 1) s j) ξ)‖ = ‖ξ‖ := by
  let pe : ι → (H →L[ℂ] H) := fun a => ρ (e a)
  have hpe (a : ι) : star (pe a) = pe a := by
    change star (ρ (e a)) = ρ (e a)
    rw [← map_star, he a]
  have hpmul (a b : ι) : pe a * pe b = if a = b then pe a else 0 := by
    change ρ (e a) * ρ (e b) = _
    rw [← map_mul, hmul]
    split_ifs
    · rfl
    · exact map_zero ρ
  have hpsum : ∑ a, pe a = 1 := by
    change ∑ a, ρ (e a) = 1
    rw [← map_sum, hsum, map_one]
  let u : unitary (H →L[ℂ] H) :=
    Unitary.map (StarMonoidHom.ofClass (ρ.comp (boundedSequenceEval j))) w
  have hu : ρ ((w : BoundedSequence A) j) ∈ unitary (H →L[ℂ] H) := u.property
  let : NeZero (r + 2) := ⟨by omega⟩
  have hp := positivePhaseCoefficient_column_norm (q := r + 2) pe hpe hpmul hpsum
    (ρ ((w : BoundedSequence A) j)) hu r (by omega) ξ
  have hn := negativePhaseCoefficient_column_norm (q := r + 2) pe hpe hpmul hpsum
    (ρ ((w : BoundedSequence A) j)) hu r (by omega) ξ
  simpa only [positivePhaseCoefficientSequence_apply, negativePhaseCoefficientSequence_apply,
    map_positivePhaseCoefficient, map_negativePhaseCoefficient] using And.intro hp hn

end RepresentedColumn

variable {τ : FaithfulTracialState A} {σ : FaithfulTracialState B} {ω : Ultrafilter ℕ}

/-- Constant traces are preserved for arbitrary source C⋆-algebras. -/
theorem TraceQuotientMap.trace_boundedSequenceConst (Q : TraceQuotientMap τ σ ω) (a : A) :
    σ.toLinearMap (Q.quotient (boundedSequenceConst a)) = τ.toLinearMap a :=
  tendsto_nhds_unique (Q.trace_limit (boundedSequenceConst a)) tendsto_const_nhds

/-- The free-word estimates bound both signs of the actual sequence
coefficients after quotienting; no coefficient norm estimate is assumed. -/
theorem phaseCoefficientSequence_quotient_norm_bounds
    (hFock : PublishedDiagonalFockRepresentation.{v})
    (Q : TraceQuotientMap τ σ ω) {d r : ℕ} [NeZero d]
    (e : Fin d → A) (w : unitary (BoundedSequence A))
    (hprojection : ∀ a, IsStarProjection (e a))
    (horthogonal : ∀ a b, a ≠ b → e a * e b = 0)
    (hsum : ∑ a, e a = 1)
    (htrace : ∀ a, τ.toLinearMap (e a) = (d : ℂ)⁻¹)
    (hfree : FreeHaarMoments σ (Q.quotient.comp boundedSequenceConst).range
      (Unitary.map (StarMonoidHom.ofClass Q.quotient) w))
    (hr : 1 ≤ r) (hd : freeWordThreshold r ≤ d) :
    (∀ s : Sym (Fin d) r,
      ‖Q.quotient (positivePhaseCoefficientSequence e (w : BoundedSequence A) r s)‖ ≤
        projectionWordWeight (freeWordC r) s) ∧
    (∀ s : Sym (Fin d) r,
      ‖Q.quotient (negativePhaseCoefficientSequence e (w : BoundedSequence A) r s)‖ ≤
        projectionWordWeight (freeWordC r) s) := by
  let φ : A →⋆ₐ[ℂ] B := Q.quotient.comp boundedSequenceConst
  let ebar : Fin d → B := fun a => φ (e a)
  let ubar : unitary B := Unitary.map (StarMonoidHom.ofClass Q.quotient) w
  have hp (a : Fin d) : IsStarProjection (ebar a) := (hprojection a).map φ
  have ho (a b : Fin d) (hab : a ≠ b) : ebar a * ebar b = 0 := by
    change φ (e a) * φ (e b) = 0
    rw [← map_mul, horthogonal a b hab, map_zero]
  have ht : ∑ a, ebar a = 1 := by
    change ∑ a, φ (e a) = 1
    rw [← map_sum, hsum, map_one]
  have htr (a : Fin d) : σ.toLinearMap (ebar a) = (d : ℂ)⁻¹ :=
    (Q.trace_boundedSequenceConst (e a)).trans (htrace a)
  have hf : ScalarFreeDiagonal σ (conjugatedDiagonal ebar (ubar : B) r) :=
    hfree.scalarFree_conjugatedDiagonal ebar (fun a => ⟨e a, rfl⟩) htr
  constructor
  · intro s
    rw [quotient_positivePhaseCoefficientSequence]
    exact norm_positivePhaseCoefficient_le_of_published hFock σ ebar (ubar : B)
      ubar.property hp ho ht htr hf hr hd s
  · intro s
    rw [quotient_negativePhaseCoefficientSequence]
    exact norm_negativePhaseCoefficient_le_of_published hFock σ ebar (ubar : B)
      ubar.property hp ho ht htr hf hr hd s

end

end KadisonKastler

end OAI
