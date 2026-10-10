import OAI.Analysis.KadisonKastler.PublishedIncreasingMatrixInjectivity
import OAI.Analysis.FactorGeneration.TraceTransport

namespace OAI

/-! # Pulling the increasing matrix construction to the original representation

The original representation need not possess a tracial vector. We construct
the matrix stages on the canonical separable trace Hilbert space, pull each
finite stage back algebraically, and take its actual original weak closure.
Commutation with that closure implies commutation with every pulled-back
stage and hence with the irreducible algebra in the trace representation.
Injectivity of the closure of the increasing matrix algebras is a hypothesis.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

section MatrixTransport

variable {A B : Type*} [Ring A] [StarRing A] [_root_.Algebra ℂ A] [StarModule ℂ A]
  [Ring B] [StarRing B] [_root_.Algebra ℂ B] [StarModule ℂ B]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mapped_matrixUnits_hom (E : MatrixUnitSystem ι A) (f : A →⋆ₐ[ℂ] B)
    (a : Matrix ι ι ℂ) : (E.map f).hom a = f (E.hom a) := by
  simp only [MatrixUnitSystem.hom_apply, MatrixUnitSystem.map_entry,
    map_sum, map_smul]

theorem mem_inverse_mapped_matrixUnits (E : MatrixUnitSystem ι B)
    (e : A ≃⋆ₐ[ℂ] B) (x : A) :
    x ∈ (E.map e.symm.toStarAlgHom).algebra ↔ e x ∈ E.algebra := by
  constructor
  · rintro ⟨a, ha⟩
    change (E.map e.symm.toStarAlgHom).hom a = x at ha
    refine ⟨a, ?_⟩
    change E.hom a = e x
    rw [mapped_matrixUnits_hom] at ha
    change e.symm (E.hom a) = x at ha
    simpa only [e.apply_symm_apply] using congrArg e ha
  · rintro ⟨a, ha⟩
    change E.hom a = e x at ha
    refine ⟨a, ?_⟩
    change (E.map e.symm.toStarAlgHom).hom a = x
    rw [mapped_matrixUnits_hom]
    change e.symm (E.hom a) = x
    rw [ha, e.symm_apply_apply]

end MatrixTransport

section Commutation

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra K}

/-- Membership in the commutant of every increasing stage gives commutation
with the actual generated von Neumann algebra. -/
theorem commutes_generated_of_commutes_stages (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun j => (A j).units.concreteAlgebra)) (c : K →L[ℂ] K)
    (hc : ∀ j x, x ∈ (A j).units.concreteAlgebra → x * c = c * x)
    (x : Algebra (FiniteMatrixStage.generatedVonNeumann A)) :
    (x : K →L[ℂ] K) * c = c * (x : K →L[ℂ] K) := by
  have hc' : c ∈ Set.centralizer
      (FiniteMatrixStage.stageUnion A : Set (K →L[ℂ] K)) := by
    intro a ha
    rw [FiniteMatrixStage.stageUnion_coe A hA] at ha
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ha
    exact hc j a hj
  have hx : (x : K →L[ℂ] K) ∈ Set.centralizer (Set.centralizer
      (FiniteMatrixStage.stageUnion A : Set (K →L[ℂ] K))) := by
    rw [← bicommutantVonNeumann_coe]
    change (x : K →L[ℂ] K) ∈
      (bicommutantVonNeumann (FiniteMatrixStage.stageUnion A)).toStarSubalgebra
    rw [← wstar_starAlgebra_eq_bicommutant,
      ← FiniteMatrixStage.generated_eq_wstar_union A hA]
    exact x.property
  exact (hx c hc').symm

end Commutation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

/-- An irreducible, increasing matrix-generated subalgebra in the original
representation. No tracial vector in that representation is assumed. -/
theorem exists_original_irreducible_matrix_algebra
    (hM : IsII1Factor M.toStarSubalgebra) :
    ∃ A : ℕ → FiniteMatrixStage M,
      Monotone (fun j => (A j).units.concreteAlgebra) ∧
      (∀ j, FiniteDimensional ℂ (A j).units.concreteAlgebra) ∧
      (∀ b : Algebra M,
        (∀ r : Algebra (FiniteMatrixStage.generatedVonNeumann A),
          coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) r * b =
            b * coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) r) →
        ∃ c : ℂ, b = c • (1 : Algebra M)) := by
  let K := ConcreteTraceHilbert hM
  let T : VonNeumannAlgebra K := traceFreeHilbertClosure (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)
  let e : Algebra M ≃⋆ₐ[ℂ] Algebra T := traceFreeHilbertEquiv (traceHilbert_factor hM)
    hM.diffuse hM.finite (traceHilbert_nonzero hM)
  let τ : UltrapowerBridge.TracialRepresentation T :=
    traceFreeHilbertClosureTrace (traceHilbert_factor hM)
      hM.diffuse hM.finite (traceHilbert_nonzero hM)
  have hT : IsII1Factor T.toStarSubalgebra :=
    traceFreeHilbertClosure_isII1Factor (traceHilbert_factor hM)
      hM.diffuse hM.finite (traceHilbert_nonzero hM)
  obtain ⟨P, hPT, _, hirr, A, rfl, hA, _⟩ :=
    exists_irreducible_matrix_subfactor τ hT
  let B : ℕ → FiniteMatrixStage M := fun j => {
    size := (A j).size
    positive := (A j).positive
    units := (A j).units.map e.symm.toStarAlgHom }
  have hmem (j : ℕ) (x : Algebra M) :
      x.val ∈ (B j).units.concreteAlgebra ↔ (e x).val ∈ (A j).units.concreteAlgebra := by
    rw [(B j).units.mem_concreteAlgebra, (A j).units.mem_concreteAlgebra]
    exact mem_inverse_mapped_matrixUnits (A j).units e x
  have hB : Monotone (fun j => (B j).units.concreteAlgebra) := by
    intro i j hij x hx
    let xM : Algebra M := ⟨x, (B i).units.concreteAlgebra_le hx⟩
    exact (hmem j xM).mpr (hA hij ((hmem i xM).mp hx))
  refine ⟨B, hB, fun j => (B j).units.concrete_finiteDimensional, ?_⟩
  intro b hb
  have hstage (j : ℕ) (x : K →L[ℂ] K) (hx : x ∈ (A j).units.concreteAlgebra) :
      x * (e b).val = (e b).val * x := by
    let xT : Algebra T := ⟨x, (A j).units.concreteAlgebra_le hx⟩
    let xM : Algebra M := e.symm xT
    have hxM : xM.val ∈ (B j).units.concreteAlgebra := by
      apply (hmem j xM).mpr
      simpa only [xM, e.apply_symm_apply] using hx
    let xR : Algebra (FiniteMatrixStage.generatedVonNeumann B) :=
      ⟨xM.val, FiniteMatrixStage.stage_le_generated B j hxM⟩
    have hc : xM * b = b * xM := hb xR
    have he := congrArg e hc
    rw [map_mul, map_mul] at he
    have he' : e xM = xT := e.apply_symm_apply xT
    rw [he'] at he
    exact congrArg Subtype.val he
  obtain ⟨c, hc⟩ := hirr (e b) (fun r => Subtype.ext
    (commutes_generated_of_commutes_stages A hA (e b).val hstage r))
  refine ⟨c, e.injective ?_⟩
  calc
    e b = c • (1 : Algebra T) := hc
    _ = e (c • (1 : Algebra M)) := by
      have hs : e (c • (1 : Algebra M)) = c • e 1 :=
        e.toAlgEquiv.toLinearEquiv.map_smul c 1
      have h1 : e (1 : Algebra M) = 1 := e.map_one
      rw [hs, h1]

/-- The injective common subalgebra needed in the finite-factor perturbation
proof exists in the original Hilbert representation. -/
theorem exists_original_irreducible_injective_subalgebra
    (hpub : PublishedIncreasingMatrixInjectivity (H := H))
    (hM : IsII1Factor M.toStarSubalgebra) :
    ∃ (R : VonNeumannAlgebra H) (hRM : R ≤ M), IsInjective R ∧
      (∀ b : Algebra M,
        (∀ r : Algebra R, coordinateInclusion hRM r * b = b * coordinateInclusion hRM r) →
        ∃ c : ℂ, b = c • (1 : Algebra M)) := by
  obtain ⟨A, hA, hfd, hirr⟩ := exists_original_irreducible_matrix_algebra hM
  exact ⟨FiniteMatrixStage.generatedVonNeumann A,
    FiniteMatrixStage.generatedVonNeumann_le A, hpub M A hA hfd, hirr⟩

end

end KadisonKastler

end OAI
