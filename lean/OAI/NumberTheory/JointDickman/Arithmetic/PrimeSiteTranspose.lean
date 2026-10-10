import OAI.NumberTheory.JointDickman.Counting.BlockSiteComparison

namespace OAI

/-! # Reindexing independent prime hits as independent endpoint sets -/

namespace JointDickman
open Finset

noncomputable def primeSiteTranspose {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : Finset ℕ) : (P → I.powerset) ≃ (I → P.powerset) :=
  (Equiv.piCongrRight (fun _ : P => subsetHitEquiv I)).trans
    ((Equiv.piComm (fun (_ : P) (_ : I) => Bool)).trans
      (Equiv.piCongrRight (fun _ : I => (subsetHitEquiv P).symm)))

theorem primeSiteTranspose_hit {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : Finset ℕ) (x : P → I.powerset) (i : I) (p : P) :
    subsetHitEquiv P (primeSiteTranspose I P x i) p = subsetHitEquiv I (x p) i := by
  simp [primeSiteTranspose]
  rfl

theorem primeSiteTranspose_mem {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : Finset ℕ) (x : P → I.powerset) (i : I) (p : P) :
    p.val ∈ (primeSiteTranspose I P x i).val ↔ i.val ∈ (x p).val := by
  have h := primeSiteTranspose_hit I P x i p
  by_cases hp : p.val ∈ (primeSiteTranspose I P x i).val <;>
    by_cases hi : i.val ∈ (x p).val <;> simp_all [subsetHitEquiv]

theorem primeSiteTranspose_mass {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : Finset ℕ) (q : ℕ → ℝ) (x : P → I.powerset) :
    bernoulliProductMass I (fun p : P => fun _ => q p.val) x =
      finiteProductMass (fun _ : I => fun S : P.powerset => bernoulliSubsetMass P q S.val)
        (primeSiteTranspose I P x) := by
  classical
  have hl (p : P) : bernoulliSubsetMass I (fun _ : ι => q p.val) (x p).val =
      ∏ i : I, bernoulliBitMass (q p.val) (subsetHitEquiv I (x p) i) :=
    (bernoulliSubsetMass_eq_product I (fun _ : ι => q p.val) (x p)).symm
  have hr (i : I) : bernoulliSubsetMass P q (primeSiteTranspose I P x i).val =
      ∏ p : P, bernoulliBitMass (q p.val) (subsetHitEquiv I (x p) i) := by
    rw [← bernoulliSubsetMass_eq_product P q (primeSiteTranspose I P x i)]
    simp only [finiteProductMass,primeSiteTranspose_hit]
  change (∏ p : P, bernoulliSubsetMass I (fun _ : ι => q p.val) (x p).val) =
    ∏ i : I, bernoulliSubsetMass P q (primeSiteTranspose I P x i).val
  simp_rw [hl,hr]
  exact prod_comm

theorem primeSiteTranspose_sum {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : Finset ℕ) (q : ℕ → ℝ) (F : (I → P.powerset) → ℝ) :
    (∑ x, bernoulliProductMass I (fun p : P => fun _ => q p.val) x *
      F (primeSiteTranspose I P x)) =
      ∑ S, finiteProductMass
        (fun _ : I => fun R : P.powerset => bernoulliSubsetMass P q R.val) S * F S := by
  rw [← (primeSiteTranspose I P).sum_comp]
  apply sum_congr rfl
  intro x _
  rw [primeSiteTranspose_mass]

end JointDickman

end OAI
