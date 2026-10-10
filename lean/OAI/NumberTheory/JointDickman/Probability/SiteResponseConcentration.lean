import OAI.NumberTheory.JointDickman.Amplification.ColumnResponseMean

namespace OAI

/-! # Exponential concentration of each fixed column response -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype A] [DecidableEq A]

theorem siteColumnResponse_concentration (hMC : FiniteMcDiarmidInput ι A)
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ)
    (hEsym : ∀ i j a b, E i j a b = E j i b a)
    (hHsym : ∀ i j a b, H i j a b = H j i b a)
    (hEdiag : ∀ i a, E i i a a = 0) (hHdiag : ∀ i a, H i i a a = 0)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    (g : ι → A → ℝ) (hg : ∀ i a, |g i a| ≤ 1)
    {C q d Ctest L u a : ℝ} (hd : 0 < d) (hgap : C < d)
    (hL : 0 ≤ L) (ha : 0 < a)
    (hmean : ∀ i b, |siteRowMean p H i b| ≤ C)
    (hsquareH : ∀ i, siteRowSquareMass p H i ≤ q)
    (hsquareE : ∀ i, siteRowSquareMass p E i ≤ q)
    (htest : ∀ h : ι → A → ℝ, (∀ i b, |h i b| ≤ 1) → siteTestMean p E g h ≤ Ctest)
    (hbad : (Fintype.card ι : ℝ)*q/(d-C)^2 < 1)
    (hbound : Ctest/Fintype.card ι + Real.sqrt q +
      L*((Fintype.card ι : ℝ)*q/(d-C)^2) ≤ u)
    (hcut : u+a < L) :
    finiteProbability (siteProductMass p)
      (fun x => (∀ i, siteRowSum H i x ≤ d) ∧
        u+a < siteColumnResponse E g x/Fintype.card ι) ≤
      Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2)) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  let G : Finset (ι → A) := univ.filter (fun x => ∀ i, siteRowSum H i x ≤ d)
  have hGmem (x : ι → A) : x ∈ G ↔ ∀ i, siteRowSum H i x ≤ d := by simp [G]
  have hprob := siteDegree_bad_probability p hp hpone H hHdiag hgap hmean hsquareH
  have hG : G.Nonempty := by
    by_contra hne
    have hb (x : ι → A) : ¬ ∀ i, siteRowSum H i x ≤ d := by
      intro hx
      exact hne ⟨x,(hGmem x).mpr hx⟩
    have he : finiteProbability (siteProductMass p)
        (fun x => ¬ ∀ i, siteRowSum H i x ≤ d) = 1 := by
      simp only [finiteProbability,hb]
      exact siteProductMass_sum p hpone
    rw [he] at hprob
    linarith
  have hresp := siteColumnResponse_mean_le p hp hpone E hEsym hEdiag g hg Ctest q htest hsquareE
  have hmeanZ : finiteExpectation (siteProductMass p)
      (fun x => siteColumnResponse E g x/Fintype.card ι) +
      L*finiteProbability (siteProductMass p) (fun x => x ∉ G) ≤ u := by
    rw [finiteExpectation_div]
    have hpg : finiteProbability (siteProductMass p) (fun x => x ∉ G) ≤
        (Fintype.card ι : ℝ)*q/(d-C)^2 := by
      simpa only [hGmem] using hprob
    have hr := div_le_div_of_nonneg_right hresp hN.le
    rw [add_div,mul_div_cancel_left₀ _ hN.ne'] at hr
    exact (add_le_add hr (mul_le_mul_of_nonneg_left hpg hL)).trans hbound
  have hlip : ∀ x ∈ G, ∀ y ∈ G,
      |siteColumnResponse E g x/Fintype.card ι - siteColumnResponse E g y/Fintype.card ι| ≤
        (4*d/Fintype.card ι)*hammingDist x y := by
    intro x hx y hy
    rw [← sub_div,abs_div,abs_of_pos hN]
    have hh := div_le_div_of_nonneg_right
      (siteColumnResponse_lipschitz_on_good E H g hHsym hdom hg d x y
        ((hGmem x).mp hx) ((hGmem y).mp hy)) hN.le
    convert hh using 1
    ring
  have hh := goodSet_concentration hMC p hp hpone G hG
    (fun x => siteColumnResponse E g x/Fintype.card ι)
    (div_nonneg (by positivity) hN.le) hL ha
    (fun x => div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) hN.le) hlip hmeanZ hcut
  have hexp : -2*a^2/((Fintype.card ι : ℝ)*(4*d/Fintype.card ι)^2) =
      -(a^2*(Fintype.card ι : ℝ))/(8*d^2) := by
    field_simp
    ring
  simpa only [hGmem,hexp] using hh

end JointDickman

end OAI
