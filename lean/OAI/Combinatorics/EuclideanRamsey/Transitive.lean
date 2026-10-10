import OAI.Combinatorics.EuclideanRamsey.Main

namespace OAI

/-! Finite transitive Euclidean configurations and their subsets are Ramsey. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace EuclideanRamsey
namespace TransitiveConsequence

def distancePermutationGroup {t D : ℕ} (y : Fin t → Space D) :
    Subgroup (Equiv.Perm (Fin t)) where
  carrier := {σ | ∀ i j, dist (y (σ i)) (y (σ j)) = dist (y i) (y j)}
  one_mem' := by intro i j; rfl
  mul_mem' := by
    intro σ τ hσ hτ i j
    change dist (y (σ (τ i))) (y (σ (τ j))) = dist (y i) (y j)
    rw [hσ, hτ]
  inv_mem' := by
    intro σ hσ i j
    have h := hσ (σ.symm i) (σ.symm j)
    simpa using h.symm

noncomputable instance distancePermutationFintype {t D : ℕ} (y : Fin t → Space D) :
    Fintype (distancePermutationGroup y) := Fintype.ofFinite _

def IsTransitive {t D : ℕ} (y : Fin t → Space D) : Prop :=
  ∀ i j : Fin t, ∃ σ : distancePermutationGroup y, σ.val i = j

theorem orbit_sum_eq {t D : ℕ} (y : Fin t → Space D) (hy : IsTransitive y)
    {M : Type*} [AddCommMonoid M] (f : Space D → M) (i j : Fin t) :
    (∑ σ : distancePermutationGroup y, f (y (σ.val i))) =
      ∑ σ : distancePermutationGroup y, f (y (σ.val j)) := by
  classical
  obtain ⟨τ, hτ⟩ := hy i j
  calc
    (∑ σ : distancePermutationGroup y, f (y (σ.val i))) =
        ∑ σ : distancePermutationGroup y, f (y ((σ * τ).val i)) :=
      (Equiv.sum_comp (Equiv.mulRight τ)
        (fun σ : distancePermutationGroup y => f (y (σ.val i)))).symm
    _ = ∑ σ : distancePermutationGroup y, f (y (σ.val j)) := by
      apply Finset.sum_congr rfl
      intro σ _
      change f (y (σ.val (τ.val i))) = f (y (σ.val j))
      rw [hτ]

theorem averaged_realCriterion {s d t D : ℕ}
    (a : Fin s → Space d) (hs : 0 < s)
    (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (y : Fin t → Space D) (hy : IsTransitive y)
    (e : Fin s → Fin t) (he : Congruent a (fun i => y (e i))) :
    RealCriterion a := by
  classical
  let H := distancePermutationGroup y
  let i₀ : Fin s := ⟨0, hs⟩
  have hcopies (σ : H) :
      ∃ Q : Space d →ₗᵢ[ℝ] Space D, ∃ z : Space D,
        ∀ i, y (σ.val (e i)) = z + Q (a i) := by
    apply congruent_linearIsometry a (fun i => y (σ.val (e i))) i₀ hspan
    intro i j
    exact (σ.property (e i) (e j)).trans (he i j)
  choose Q z hz using hcopies
  let S : RealArray d := ∑ σ : H, ∑ j : Fin D,
    (diagonalArray (z σ j) (isometryRows (Q σ) j) -
      diagonalArray (y (σ.val (e i₀)) j) 0)
  let q : ℚ := (Fintype.card H : ℚ)⁻¹
  have hcard : (Fintype.card H : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card H ≠ 0)
  have haff (σ : H) (i : Fin s) (j : Fin D) :
      affineEvaluation a i (z σ j) (isometryRows (Q σ) j) =
        y (σ.val (e i)) j := by
    calc
      affineEvaluation a i (z σ j) (isometryRows (Q σ) j) =
          z σ j + Q σ (a i) j := by
        rw [isometryRows_apply]
        rfl
      _ = y (σ.val (e i)) j := by
        simpa only [PiLp.add_apply] using
          (congrArg (fun v : Space D => v j) (hz σ i)).symm
  have heval (i : Fin s) :
      (∑ σ : H, ∑ j : Fin D,
        ((y (σ.val (e i)) j ⊗ₜ[ℚ] y (σ.val (e i)) j) -
          (y (σ.val (e i₀)) j ⊗ₜ[ℚ] y (σ.val (e i₀)) j))) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    exact orbit_sum_eq y hy (fun x => x j ⊗ₜ[ℚ] x j) (e i) (e i₀)
  have hS_eval (i : Fin s) : arrayEvaluation a i S = 0 := by
    dsimp only [S]
    simp only [map_sum, map_sub, arrayEvaluation_diagonal, haff]
    simpa [affineEvaluation] using heval i
  have hgram (σ : H) :
      (∑ j : Fin D,
        (gradientRankOne (isometryRows (Q σ) j) - gradientRankOne (0 : Space d))) =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext α β
    simpa only [Matrix.sum_apply, Matrix.sub_apply, gradientRankOne, PiLp.zero_apply,
      zero_mul, sub_zero, Matrix.one_apply] using
      isometryRows_gram (Q σ) α β
  have hS_spatial : spatialMultiply S =
      (Fintype.card H : ℚ) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    dsimp only [S]
    simp only [map_sum, map_sub, spatialMultiply_diagonal]
    simp_rw [hgram]
    ext α β
    simp [Matrix.one_apply, Rat.smul_def]
  refine ⟨q • S, ?_, ?_⟩
  · intro i
    rw [map_smul, hS_eval i, smul_zero]
  · rw [map_smul, hS_spatial, smul_smul]
    dsimp only [q]
    rw [inv_mul_cancel₀ hcard, one_smul]

theorem isometric_subconfiguration_ramsey {s d t D : ℕ}
    (a : Fin s → Space d) (hs : 0 < s) (ha : Function.Injective a)
    (y : Fin t → Space D) (hy : IsTransitive y)
    (e : Fin s → Fin t) (he : Congruent a (fun i => y (e i))) : Ramsey a := by
  classical
  by_cases hs1 : s = 1
  · subst s
    exact singleton_ramsey a
  have hs2 : 2 ≤ s := by omega
  obtain ⟨d', hd', b, hb, hab, hspan⟩ := full_affine_representative a hs2 ha
  have hbe : Congruent b (fun i => y (e i)) := by
    intro i j
    exact (he i j).trans (hab i j).symm
  have hreal : RealCriterion b :=
    averaged_realCriterion b hs hspan y hy e hbe
  have hrb : Ramsey b := fieldCriterion_ramsey b hs2 hd' hb
    (realCriterion_fieldCriterion b hreal)
  exact (ramsey_congruent_iff hab).mpr hrb

theorem subset_of_finite_transitive_ramsey {s t D : ℕ}
    (a : Fin s → Space D) (y : Fin t → Space D)
    (hs : 0 < s) (ha : Function.Injective a) (_hy : Function.Injective y)
    (htrans : ∀ i j : Fin t, ∃ σ : Equiv.Perm (Fin t),
      (∀ k l : Fin t, dist (y (σ k)) (y (σ l)) = dist (y k) (y l)) ∧ σ i = j)
    (hsub : Set.range a ⊆ Set.range y) : Ramsey a := by
  classical
  have htrans' : IsTransitive y := by
    intro i j
    obtain ⟨σ, hσ, hij⟩ := htrans i j
    exact ⟨⟨σ, hσ⟩, hij⟩
  have hex (i : Fin s) : ∃ j : Fin t, y j = a i :=
    hsub (Set.mem_range_self i)
  choose e he using hex
  apply isometric_subconfiguration_ramsey a hs ha y htrans' e
  intro i j
  change dist (y (e i)) (y (e j)) = dist (a i) (a j)
  rw [he i, he j]

end TransitiveConsequence
end EuclideanRamsey

end

end OAI
