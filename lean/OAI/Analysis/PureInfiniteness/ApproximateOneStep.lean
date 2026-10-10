import Mathlib

namespace OAI

/-!
Finite specializations of the one-step-inner calculus in Kirchberg--Rørdam,
`Infinite non-simple C*-algebras: absorbing the Cuntz algebra O_infinity`,
Adv. Math. 167 (2002), Lemmas 7.19--7.20 (author preprint pp. 58--59).

These lemmas only perform the finite coefficient and closure steps. They do not
assert that a nuclear algebra supplies the abelian-range maps used in that paper.
-/

noncomputable section

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Point-norm approximation by a single inner compression. -/
def ApproximatelyOneStepInner (T : A → A) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ d : A, ∀ b ∈ F, ‖T b - star d * b * d‖ < ε

/-- Finite coefficient enlargement of a map, as in KR02, equation (7.10). -/
def coefficientEnlargement {ι : Type*} [Fintype ι]
    (T : A → A) (a c : ι → A) (b : A) : A :=
  ∑ i, ∑ j, star (a i) * T (star (c i) * b * c j) * a j

lemma coefficientEnlargement_inner {ι : Type*} [Fintype ι]
    (a c : ι → A) (d b : A) :
    coefficientEnlargement (fun x => star d * x * d) a c b =
      star (∑ i, c i * d * a i) * b * (∑ i, c i * d * a i) := by
  simp only [coefficientEnlargement, star_sum, Finset.sum_mul, Finset.mul_sum,
    star_mul, mul_assoc]
  exact Finset.sum_comm

lemma coefficientEnlargement_error_le {ι : Type*} [Fintype ι]
    (S T : A → A) (a c : ι → A) (b : A) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hST : ∀ i j, ‖S (star (c i) * b * c j) -
      T (star (c i) * b * c j)‖ ≤ δ) :
    ‖coefficientEnlargement S a c b - coefficientEnlargement T a c b‖ ≤
      δ * ∑ i, ∑ j, ‖a i‖ * ‖a j‖ := by
  have he : coefficientEnlargement S a c b - coefficientEnlargement T a c b =
      ∑ i, ∑ j, star (a i) *
        (S (star (c i) * b * c j) - T (star (c i) * b * c j)) * a j := by
    simp only [coefficientEnlargement, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, ‖∑ j, star (a i) *
        (S (star (c i) * b * c j) - T (star (c i) * b * c j)) * a j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖star (a i) *
        (S (star (c i) * b * c j) - T (star (c i) * b * c j)) * a j‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖a i‖ * δ * ‖a j‖ := by
      gcongr with i j
      calc
        _ ≤ (‖star (a i)‖ * ‖S (star (c i) * b * c j) -
            T (star (c i) * b * c j)‖) * ‖a j‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ _ := by rw [norm_star]; gcongr; exact hST i j
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The finite coefficient step of KR02 Lemma 7.20. No norm bound on the
approximating compression is asserted. -/
lemma ApproximatelyOneStepInner.coefficientEnlargement
    {T : A → A} (hT : ApproximatelyOneStepInner T)
    {ι : Type*} [Fintype ι] (a c : ι → A) :
    ApproximatelyOneStepInner (coefficientEnlargement T a c) := by
  classical
  intro F ε hε
  let K : ℝ := 1 + ∑ i, ∑ j, ‖a i‖ * ‖a j‖
  have hsum : 0 ≤ ∑ i, ∑ j, ‖a i‖ * ‖a j‖ := by positivity
  have hK : 0 < K := by dsimp only [K]; linarith
  let δ := ε / K
  have hδ : 0 < δ := div_pos hε hK
  let G : Finset A := F.biUnion fun b => Finset.univ.biUnion fun i =>
    Finset.univ.image fun j => star (c i) * b * c j
  obtain ⟨d, hd⟩ := hT G δ hδ
  refine ⟨∑ i, c i * d * a i, ?_⟩
  intro b hb
  rw [← coefficientEnlargement_inner a c d b]
  have hpoint (i j : ι) : ‖T (star (c i) * b * c j) -
      star d * (star (c i) * b * c j) * d‖ ≤ δ := by
    apply (hd _ ?_).le
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩⟩
  have hbound := coefficientEnlargement_error_le T (fun x => star d * x * d)
    a c b δ hδ.le hpoint
  apply hbound.trans_lt
  have heq : δ * K = ε := div_mul_cancel₀ ε (ne_of_gt hK)
  dsimp only [K] at heq
  nlinarith

lemma ApproximatelyOneStepInner.of_pointNorm_approximation (T : A → A)
    (hT : ∀ (F : Finset A) (ε : ℝ), 0 < ε →
      ∃ S : A → A, ApproximatelyOneStepInner S ∧ ∀ b ∈ F, ‖T b - S b‖ < ε) :
    ApproximatelyOneStepInner T := by
  intro F ε hε
  obtain ⟨S, hS, hTS⟩ := hT F (ε / 2) (by positivity)
  obtain ⟨d, hd⟩ := hS F (ε / 2) (by positivity)
  refine ⟨d, fun b hb => ?_⟩
  calc
    _ ≤ ‖T b - S b‖ + ‖S b - star d * b * d‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hTS b hb) (hd b hb)
    _ = ε := by ring

end WeakPureInfiniteness

end

end OAI
