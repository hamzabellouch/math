import OAI.NumberTheory.JointDickman.Counting.SamplingTransfer

namespace OAI

/-! # Conditional row variance gives a common degree event -/

namespace JointDickman
open Finset Classical
open PublishedInputs

/-- Markov's inequality for the finite nonnegative weights used here. -/
theorem finiteProbability_markov {Ω : Type*} [Fintype Ω]
    (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x)
    {t : ℝ} (ht : 0 < t) :
    finiteProbability w (fun x => t < f x) ≤ finiteExpectation w f/t := by
  unfold finiteProbability finiteExpectation
  rw [sum_div]
  apply sum_le_sum
  intro x _
  split_ifs with hx
  · have hh : 1 ≤ f x/t := (le_div_iff₀ ht).mpr (by linarith)
    simpa only [mul_one,mul_div_assoc] using mul_le_mul_of_nonneg_left hh (hw x)
  · exact div_nonneg (mul_nonneg (hw x) (hf x)) ht.le

/-- The mean is bounded for every row type, but the variance bound is
integrated over that type. This is sufficient for the degree tail. -/
theorem siteRow_degree_tail {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0)
    (i : ι) {C d : ℝ} (hgap : C < d)
    (hmean : ∀ a, |siteRowMean p K i a| ≤ C) :
    finiteProbability (siteProductMass p) (fun x => d < siteRowSum K i x) ≤
      siteRowSquareMass p K i/(d-C)^2 := by
  have hden : 0 < (d-C)^2 := sq_pos_of_pos (sub_pos.mpr hgap)
  let g := fun x => siteRowSum K i x-siteRowMean p K i (x i)
  have hsub : finiteProbability (siteProductMass p) (fun x => d < siteRowSum K i x) ≤
      finiteProbability (siteProductMass p) (fun x => (d-C)^2 < (g x)^2) := by
    apply finiteProbability_mono _ (siteProductMass_nonneg p hp)
    intro x hx
    have hm : siteRowMean p K i (x i) ≤ C := (le_abs_self _).trans (hmean _)
    have hg : d-C < g x := by dsimp only [g]; linarith
    nlinarith [sub_pos.mpr hgap]
  refine hsub.trans ((finiteProbability_markov (siteProductMass p) (fun x => (g x)^2)
    (siteProductMass_nonneg p hp) (fun _ => sq_nonneg _) hden).trans ?_)
  exact div_le_div_of_nonneg_right (siteRow_centered_sq_le p hp hpone K hdiag i) hden.le

/-- Union over all rows pays only the number of positions. -/
theorem siteDegree_bad_probability {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0)
    {C d q : ℝ} (hgap : C < d)
    (hmean : ∀ i a, |siteRowMean p K i a| ≤ C)
    (hsquare : ∀ i, siteRowSquareMass p K i ≤ q) :
    finiteProbability (siteProductMass p) (fun x => ¬ ∀ i, siteRowSum K i x ≤ d) ≤
      (Fintype.card ι : ℝ)*q/(d-C)^2 := by
  have hden : 0 ≤ (d-C)^2 := sq_nonneg _
  have he : (fun x : ι → A => ¬ ∀ i, siteRowSum K i x ≤ d) =
      (fun x => ∃ i, d < siteRowSum K i x) := by funext x; simp only [not_forall,not_le]
  rw [he]
  calc
    _ ≤ ∑ i, finiteProbability (siteProductMass p) (fun x => d < siteRowSum K i x) :=
      finiteProbability_union_le _ (siteProductMass_nonneg p hp) _
    _ ≤ ∑ _i : ι, q/(d-C)^2 := sum_le_sum (fun i _ =>
      (siteRow_degree_tail p hp hpone K hdiag i hgap (hmean i)).trans
        (div_le_div_of_nonneg_right (hsquare i) hden))
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring

end JointDickman

end OAI
