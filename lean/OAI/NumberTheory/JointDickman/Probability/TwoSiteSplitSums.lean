import OAI.NumberTheory.JointDickman.Probability.TwoSiteSplitModel

namespace OAI

/-! # Expanding the two-site configuration sum -/

namespace JointDickman

open Finset

def twoSiteCoordinates (P : Finset ℕ) : TwoSiteSplit P ≃
    (P.powerset × P.powerset × P.powerset) × (P.powerset × P.powerset × P.powerset) where
  toFun x := ((x.site₁, x.first₁, x.second₁), (x.site₂, x.first₂, x.second₂))
  invFun x := ⟨x.1.1, x.2.1, x.1.2.1, x.2.2.1, x.1.2.2, x.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨⟨s, a, d⟩, ⟨t, b, e⟩⟩; rfl

theorem twoSiteSplit_sum (P : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ x : TwoSiteSplit P, F x.site₁.val x.first₁.val x.second₁.val x.site₂.val x.first₂.val x.second₂.val) =
      ∑ S ∈ P.powerset, ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
      ∑ T ∈ P.powerset, ∑ C ∈ P.powerset, ∑ E ∈ P.powerset, F S A D T C E := by
  classical
  have he := (twoSiteCoordinates P).symm.sum_comp
    (fun x => F x.site₁.val x.first₁.val x.second₁.val x.site₂.val x.first₂.val x.second₂.val)
  simp only [twoSiteCoordinates, Equiv.coe_fn_symm_mk, Fintype.sum_prod_type] at he
  have h3 (G : Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
      (∑ A : P.powerset, ∑ D : P.powerset, ∑ E : P.powerset, G A.val D.val E.val) =
        ∑ A ∈ P.powerset, ∑ D ∈ P.powerset, ∑ E ∈ P.powerset, G A D E := by
    calc
      _ = ∑ A ∈ P.powerset, ∑ D : P.powerset, ∑ E : P.powerset, G A D.val E.val :=
        sum_coe_sort P.powerset (fun A => ∑ D : P.powerset, ∑ E : P.powerset, G A D.val E.val)
      _ = _ := by
        apply sum_congr rfl
        intro A _
        exact (sum_coe_sort P.powerset (fun D => ∑ E : P.powerset, G A D E.val)).trans
          (sum_congr rfl (fun D _ => sum_coe_sort P.powerset (fun E => G A D E)))
  calc
    _ = ∑ S : P.powerset, ∑ A : P.powerset, ∑ D : P.powerset,
        ∑ T : P.powerset, ∑ C : P.powerset, ∑ E : P.powerset,
          F S.val A.val D.val T.val C.val E.val := he.symm
    _ = ∑ S ∈ P.powerset, ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        ∑ T : P.powerset, ∑ C : P.powerset, ∑ E : P.powerset, F S A D T.val C.val E.val :=
      h3 (fun S A D => ∑ T : P.powerset, ∑ C : P.powerset, ∑ E : P.powerset, F S A D T.val C.val E.val)
    _ = _ := by
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro A _
      apply sum_congr rfl
      intro D _
      exact h3 (F S A D)

/-- The two-site probability is the corresponding pair of one-site
expectations. The function sees each coefficient and remaining subset. -/
theorem twoSiteSplit_expectation (P : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ →
      Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ x : TwoSiteSplit P, twoSiteSplitMass P x *
      F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
        x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val)) =
      twoSplitSiteAverage P (fun A R D Q => twoSplitSiteAverage P (fun C T E U => F A R D Q C T E U)) := by
  classical
  unfold twoSiteSplitMass
  rw [twoSiteSplit_sum P (fun S A D T C E =>
    bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
      bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
      subsetRetentionMass S A * subsetRetentionMass T C *
      subsetRetentionMass S D * subsetRetentionMass T E *
        F A (S \ A) D (S \ D) C (T \ C) E (T \ E))]
  unfold twoSplitSiteAverage
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  simp only [mul_sum]
  apply sum_congr rfl
  intro T _
  apply sum_congr rfl
  intro C _
  apply sum_congr rfl
  intro E _
  ring

end JointDickman

end OAI
