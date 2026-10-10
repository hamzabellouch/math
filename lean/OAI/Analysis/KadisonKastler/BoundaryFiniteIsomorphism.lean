import OAI.Analysis.KadisonKastler.BoundaryErgodicReduction
import OAI.Analysis.KadisonKastler.TraceUnitaryIsomorphism

namespace OAI

/-! # From a normalized boundary field to a finite-factor isomorphism

This joins the measurable simultaneous-point argument to the algebraic
unitary-image construction. The boundary comparison unitaries are required
to take values in the neighboring algebra, as supplied by the restricted
operator-field mean and the diagonal trace construction.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Evaluating the represented algebra at its trace vector. -/
def algebraVectorMap (M : VonNeumannAlgebra H) (Ω : H) : Algebra M →ₗ[ℂ] H where
  toFun a := a.val Ω
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The unitary in the ambient operator algebra. -/
def ambientAlgebraUnitary {M : VonNeumannAlgebra H} (u : unitary (Algebra M)) :
    unitary (H →L[ℂ] H) :=
  Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) u

/-- A unitary with value in the algebra is a unitary of that algebra. -/
def algebraUnitaryOfMem {M : VonNeumannAlgebra H} (u : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ M) : unitary (Algebra M) :=
  ⟨⟨u, hu⟩, by
    constructor
    · apply Subtype.ext
      exact u.property.1
    · apply Subtype.ext
      exact u.property.2⟩

variable {G D : Type*} [Group G] [Countable G] [MeasurableSpace D]
  {μ : Measure D} [SFinite μ] [NeZero (μ.prod μ)]
  {M N : VonNeumannAlgebra H}

/-- Once the scalar boundary relation has been obtained, the actual
algebra-valued comparison fields yield a nearby star isomorphism. -/
theorem exists_starEquiv_of_boundary_normalization
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (hτM : FiniteVectorTrace τM) (hτN : FiniteVectorTrace τN)
    (Ω : H)
    (hMΩ : ∀ a, ‖algebraVectorMap M Ω a‖ = traceTwoNorm τM a)
    (hNΩ : ∀ a, ‖algebraVectorMap N Ω a‖ = traceTwoNorm τN a)
    (ρ : G → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ g, traceTwoNorm τM ((u : Algebra M) - ρ g) < ε)
    (α : NonsingularAction G D μ)
    (L a : D × D → unitary (H →L[ℂ] H))
    (W : G → D → unitary (H →L[ℂ] H))
    (haN : ∀ p, (a p : H →L[ℂ] H) ∈ N)
    (hWN : ∀ g d, (W g d : H →L[ℂ] H) ∈ N)
    (z : ℂ) (hz : ‖z‖ = 1)
    (hvec : ∀ᵐ p ∂μ.prod μ,
      star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) = z • Ω)
    (hL : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (L p : H →L[ℂ] H) * ambientAlgebraUnitary (ρ g) =
        (W g p.1 : H →L[ℂ] H) * L (α.toPerm g⁻¹ p.1, p.2))
    {εL εa εW : ℝ} (hC : 0 ≤ 2 * εa + εW)
    (hznear : ‖z - 1‖ ≤ εL + εa)
    (hLn : ∀ᵐ p ∂μ.prod μ, ‖(L p : H →L[ℂ] H) - 1‖ ≤ εL)
    (han : ∀ᵐ p ∂μ.prod μ, ‖(a p : H →L[ℂ] H) - 1‖ ≤ εa)
    (hWn : ∀ g, ∀ᵐ p ∂μ.prod μ,
      ‖(W g p.1 : H →L[ℂ] H) - ambientAlgebraUnitary (ρ g)‖ ≤ εW)
    (hsmall : 3 * (2 * (2 * εa + εW)) + (2 * (2 * εa + εW)) ^ 2 < 2)
    (hgap : kkDistance M N + 2 * (2 * εa + εW) < 1) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      ∀ x, ‖(θ x : H →L[ℂ] H) - (x : H →L[ℂ] H)‖ ≤
        2 * (2 * εa + εW) * ‖x‖ := by
  obtain ⟨p, S, hSΩ, _, hS⟩ := exists_simultaneous_boundary_normalization
    α Ω L a (fun g => ambientAlgebraUnitary (ρ g)) W z hz hvec hL hznear hLn han hWn
  have hS1 : (S : H →L[ℂ] H) (algebraVectorMap M Ω 1) =
      algebraVectorMap N Ω 1 := by
    change (S : H →L[ℂ] H) ((1 : H →L[ℂ] H) Ω) = (1 : H →L[ℂ] H) Ω
    simpa only [one_apply_eq_self] using hSΩ
  have himages (g : G) : ∃ v : unitary (Algebra N),
      algebraVectorMap N Ω v = (S : H →L[ℂ] H) (algebraVectorMap M Ω (ρ g)) ∧
      ‖(v : H →L[ℂ] H) - (ρ g : Algebra M)‖ ≤ 2 * εa + εW := by
    let q : D × D := (α.toPerm g⁻¹ p.1, p.2)
    let v : unitary (H →L[ℂ] H) := star (a p) * W g p.1 * a q
    have hvN : (v : H →L[ℂ] H) ∈ N := by
      exact N.toStarSubalgebra.mul_mem
        (N.toStarSubalgebra.mul_mem (N.toStarSubalgebra.star_mem' (haN p)) (hWN g p.1))
        (haN q)
    exact ⟨algebraUnitaryOfMem v hvN, (hS g).1.symm, (hS g).2⟩
  obtain ⟨θ, _, hθ⟩ := exists_near_starEquiv_of_traceDense_unitary_images hM hN
    τM τN hτM hτN (algebraVectorMap M Ω) (algebraVectorMap N Ω) hMΩ hNΩ
    ρ hρ S hS1 hC himages hsmall hgap
  exact ⟨θ, hθ⟩

end

end KadisonKastler

end OAI
