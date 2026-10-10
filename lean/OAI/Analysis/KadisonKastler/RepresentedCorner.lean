import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.FactorGeneration.MatrixSequence
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # Concrete compression to a common closed subspace

The corner acts on the subspace itself. Its operators are characterized by
membership of their extension by zero in the original von Neumann algebra.
This constructs the actual corner and proves that a common compression does
not increase Kadison--Kastler distance.
-/

namespace KadisonKastler

open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [CompleteSpace E]

/-- Extension by zero on the orthogonal complement. -/
def cornerExtension : (E →L[ℂ] E) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun T := E.subtypeL.comp (T.comp E.orthogonalProjectionOnto)
  map_add' T S := by ext x; rfl
  map_smul' c T := by ext x; rfl

/-- Compression of an arbitrary ambient operator. -/
def cornerCompression : (H →L[ℂ] H) →ₗ[ℂ] (E →L[ℂ] E) where
  toFun T := E.orthogonalProjectionOnto.comp (T.comp E.subtypeL)
  map_add' T S := by ext x; simp
  map_smul' c T := by ext x; simp

@[simp] theorem cornerExtension_apply (T : E →L[ℂ] E) (x : H) :
    cornerExtension E T x = (T (E.orthogonalProjectionOnto x) : H) := rfl

@[simp] theorem cornerCompression_apply (T : H →L[ℂ] H) (x : E) :
    cornerCompression E T x = E.orthogonalProjectionOnto (T x) := rfl

@[simp] theorem cornerCompression_extension (T : E →L[ℂ] E) :
    cornerCompression E (cornerExtension E T) = T := by
  ext x
  simp only [cornerCompression_apply, cornerExtension_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem cornerExtension_compression (T : H →L[ℂ] H) :
    cornerExtension E (cornerCompression E T) = E.starProjection * T * E.starProjection := by
  ext x
  rfl

@[simp] theorem cornerExtension_one : cornerExtension E 1 = E.starProjection := by
  ext x
  rfl

theorem cornerExtension_mul (T S : E →L[ℂ] E) :
    cornerExtension E (T * S) = cornerExtension E T * cornerExtension E S := by
  ext x
  simp only [mul_apply_eq_comp, cornerExtension_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

section Star

variable [CompleteSpace H]

theorem cornerExtension_star (T : E →L[ℂ] E) :
    cornerExtension E (star T) = star (cornerExtension E T) := by
  simp only [cornerExtension, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
    ContinuousLinearMap.comp_assoc]

end Star

theorem norm_cornerCompression_le (T : H →L[ℂ] H) : ‖cornerCompression E T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  exact (E.norm_orthogonalProjectionOnto_apply_le (T x)).trans (T.le_opNorm x)

theorem norm_cornerExtension_le (T : E →L[ℂ] E) : ‖cornerExtension E T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  change ‖T (E.orthogonalProjectionOnto x)‖ ≤ _
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (E.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg T))

@[simp] theorem norm_cornerExtension (T : E →L[ℂ] E) : ‖cornerExtension E T‖ = ‖T‖ := by
  apply le_antisymm (norm_cornerExtension_le E T)
  simpa only [cornerCompression_extension] using
    norm_cornerCompression_le E (cornerExtension E T)

/-- Coefficients of extension are coefficients on the projected vectors. -/
theorem inner_cornerExtension (T : E →L[ℂ] E) (x y : H) :
    inner ℂ y (cornerExtension E T x) =
      inner ℂ (E.orthogonalProjectionOnto y) (T (E.orthogonalProjectionOnto x)) := by
  exact (E.inner_orthogonalProjectionOnto_eq_of_mem_right
    (T (E.orthogonalProjectionOnto x)) y).symm

def cornerExtensionWOT (T : E →WOT[ℂ] E) : H →WOT[ℂ] H :=
  ContinuousLinearMapWOT.ofCLM (cornerExtension E T.toCLM)

variable [CompleteSpace H]

theorem continuous_cornerExtensionWOT : Continuous (cornerExtensionWOT E) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  change Continuous (fun T : E →WOT[ℂ] E => inner ℂ y (cornerExtension E T.toCLM x))
  simp only [inner_cornerExtension]
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id _ _

/-- The algebra of the concrete corner; its identity extends to the given
orthogonal projection in the ambient algebra. -/
def representedCornerAlgebra (M : VonNeumannAlgebra H) (hp : E.starProjection ∈ M) :
    StarSubalgebra ℂ (E →L[ℂ] E) where
  carrier := {T | cornerExtension E T ∈ M}
  zero_mem' := by change cornerExtension E 0 ∈ M; simp
  one_mem' := by
    change cornerExtension E 1 ∈ M
    simpa only [cornerExtension_one] using hp
  add_mem' {T S} hT hS := by
    change cornerExtension E (T + S) ∈ M
    rw [map_add]
    exact M.add_mem hT hS
  mul_mem' {T S} hT hS := by
    change cornerExtension E (T * S) ∈ M
    rw [cornerExtension_mul]
    exact M.mul_mem hT hS
  algebraMap_mem' c := by
    change cornerExtension E (algebraMap ℂ (E →L[ℂ] E) c) ∈ M
    rw [Algebra.algebraMap_eq_smul_one, map_smul, cornerExtension_one]
    exact M.smul_mem hp c
  star_mem' {T} hT := by
    change cornerExtension E (star T) ∈ M
    rw [cornerExtension_star]
    exact star_mem hT

theorem representedCornerAlgebra_wotClosed (M : VonNeumannAlgebra H)
    (hp : E.starProjection ∈ M) :
    Generator.WOTClosed (representedCornerAlgebra E M hp) := by
  exact (Generator.Tracial.vonNeumann_wotClosed M).preimage
    (continuous_cornerExtensionWOT E)

/-- Compression of a von Neumann algebra to the range of one of its
projections, represented on that range. -/
def representedCorner (M : VonNeumannAlgebra H) (hp : E.starProjection ∈ M) :
    VonNeumannAlgebra E :=
  Generator.vonNeumannOfWOTClosed (representedCornerAlgebra E M hp)
    (representedCornerAlgebra_wotClosed E M hp)

@[simp] theorem mem_representedCorner (M : VonNeumannAlgebra H)
    (hp : E.starProjection ∈ M) (T : E →L[ℂ] E) :
    T ∈ representedCorner E M hp ↔ cornerExtension E T ∈ M := Iff.rfl

theorem cornerCompression_mem {M : VonNeumannAlgebra H} (hp : E.starProjection ∈ M)
    {T : H →L[ℂ] H} (hT : T ∈ M) :
    cornerCompression E T ∈ representedCorner E M hp := by
  rw [mem_representedCorner, cornerExtension_compression]
  exact M.mul_mem (M.mul_mem hp hT) hp

/-- Every corner contraction extends to an ambient contraction. -/
theorem cornerExtension_mem_unitBall {M : VonNeumannAlgebra H}
    (hp : E.starProjection ∈ M) {T : E →L[ℂ] E}
    (hT : T ∈ unitBall (representedCorner E M hp)) :
    cornerExtension E T ∈ unitBall M :=
  ⟨hT.1, (norm_cornerExtension E T).le.trans hT.2⟩

/-- Compressing the same projection in both algebras does not increase
their ordinary Kadison--Kastler distance. -/
theorem kkDistance_representedCorner_le (M N : VonNeumannAlgebra H)
    (hM : E.starProjection ∈ M) (hN : E.starProjection ∈ N) :
    kkDistance (representedCorner E M hM) (representedCorner E N hN) ≤ kkDistance M N := by
  have happrox (P Q : VonNeumannAlgebra H)
      (hP : E.starProjection ∈ P) (hQ : E.starProjection ∈ Q)
      {r : ℝ} (hr : kkDistance P Q < r)
      (T : E →L[ℂ] E) (hT : T ∈ unitBall (representedCorner E P hP)) :
      ∃ S ∈ unitBall (representedCorner E Q hQ), ‖T - S‖ ≤ r := by
    obtain ⟨S, hS, hTS⟩ := exists_unitBall_approx (cornerExtension_mem_unitBall E hP hT) hr
    refine ⟨cornerCompression E S,
      ⟨cornerCompression_mem E hQ hS.1, (norm_cornerCompression_le E S).trans hS.2⟩, ?_⟩
    have hn := norm_cornerCompression_le E (cornerExtension E T - S)
    rw [map_sub, cornerCompression_extension] at hn
    exact hn.trans hTS.le
  apply le_of_forall_pos_le_add
  intro ε hε
  apply Metric.hausdorffDist_le_of_mem_dist
    (add_nonneg (kkDistance_nonneg M N) hε.le)
  · intro T hT
    obtain ⟨S, hS, hTS⟩ := happrox M N hM hN (lt_add_of_pos_right _ hε) T hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hTS⟩
  · intro S hS
    obtain ⟨T, hT, hST⟩ := happrox N M hN hM
      (by rw [kkDistance_comm]; exact lt_add_of_pos_right _ hε) S hS
    exact ⟨T, hT, by simpa only [dist_eq_norm] using hST⟩

end

end KadisonKastler

end OAI
