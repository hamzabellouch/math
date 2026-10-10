import OAI.NumberTheory.TwoPoint.Bounds.PrimeRowSecondMoment
import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale

namespace OAI

/-! Group the disjoint prime bands before taking their row moments. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace FiniteLaw

lemma independent_average_grouped {ι A : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [Fintype A]
    (μ : (i : ι) → κ i → FiniteLaw A) (F : ((i : ι) → κ i → A) → ℝ) :
    (independent (fun p : Sigma κ => μ p.1 p.2)).average
      (fun x => F (fun i k => x ⟨i, k⟩)) =
        (dependentIndependent (fun i => independent (μ i))).average F := by
  let e := Equiv.piCurry (fun (i : ι) (_ : κ i) => A)
  calc
    _ = ∑ x : (i : ι) → κ i → A,
        (independent (fun p : Sigma κ => μ p.1 p.2)).weight (e.symm x) * F x :=
      (e.symm.sum_comp (fun x : Sigma κ → A =>
        (independent (fun p : Sigma κ => μ p.1 p.2)).weight x *
          F (fun i k => x ⟨i, k⟩))).symm
    _ = _ := by
      simp only [average, dependentIndependent, independent, Fintype.prod_sigma]
      rfl

lemma independent_average_disjoint_products {ι I A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    {κ : I → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [Fintype A]
    (μ : ι → FiniteLaw A) (e : (i : I) → κ i → ι)
    (he : Function.Injective (fun p : Sigma κ => e p.1 p.2))
    (f : (i : I) → (κ i → A) → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (fun k => x (e i k))) =
      ∏ i, (independent (fun k => μ (e i k))).average (f i) := by
  have hb := independent_average_embedding (fun p : Sigma κ => e p.1 p.2) he μ
    (fun x : Sigma κ → A => ∏ i, f i (fun k => x ⟨i, k⟩))
  rw [independent_average_grouped (fun i k => μ (e i k))
    (fun x => ∏ i, f i (x i)), dependentIndependent_average_product] at hb
  exact hb

end FiniteLaw

lemma prime_band_row_second_moment {J : ℕ} (P : Fin J → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → 2 ≤ p) (ambient : Finset ℕ)
    (hambient : ∀ p ∈ ambient, 2 ≤ p) (hsub : ∀ j, P j ⊆ ambient)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (paddingOriginalLaw ambient hambient).average (fun x =>
      ∏ j : Fin J, (booleanCount (fun p : P j => x ⟨p.val, hsub j p.property⟩) +
        primeHarmonicMass (P j)) ^ 2) ≤
      ∏ j : Fin J, (4 * (primeHarmonicMass (P j)) ^ 2 + primeHarmonicMass (P j)) := by
  let e : (j : Fin J) → P j → ambient := fun j p => ⟨p.val, hsub j p.property⟩
  have he : Function.Injective (fun p : Sigma (fun j => P j) => e p.1 p.2) := by
    rintro ⟨j, p⟩ ⟨l, q⟩ hpq
    have hv : p.val = q.val := congrArg Subtype.val hpq
    have hjl : j = l := by
      by_contra hne
      exact disjoint_left.mp (hdisjoint j l (Ne.symm hne)) p.property (hv.symm ▸ q.property)
    subst l
    exact congrArg (Sigma.mk j) (Subtype.ext hv)
  rw [paddingOriginalLaw,
    FiniteLaw.independent_average_disjoint_products
      (fun p : ambient => paddingOriginalPrimeLaw p (hambient p p.property)) e he
      (fun j a => (booleanCount a + primeHarmonicMass (P j)) ^ 2)]
  apply prod_le_prod₀
  · intro j _
    exact FiniteLaw.average_nonneg _ (fun _ => sq_nonneg _)
  · intro j _
    have hm : (∑ p : P j, 1 / (p.val : ℝ)) = primeHarmonicMass (P j) := by
      simp only [primeHarmonicMass, one_div]
    simpa only [paddingOriginalPrimeLaw, e, hm] using
      independent_boolean_shifted_count_square
        (fun p : P j => 1 / (p.val : ℝ)) (fun _ => by positivity)
        (fun p => by
          apply (div_le_one (by exact_mod_cast (show 0 < p.val by have := hP j p p.property; omega))).mpr
          exact_mod_cast (show 1 ≤ p.val by have := hP j p p.property; omega))

noncomputable def primeRowMajorant {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (n : ℤ) : ℝ :=
  actualPaddingWeight Q n *
    ∏ j : Fin J, ((actualPaddingDegree (P j) n : ℝ) + primeHarmonicMass (P j))

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

theorem prime_row_second_moment (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (P : Fin J → Finset ℕ) (hsub : ∀ j, P j ⊆ data.P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      (primeRowMajorant P data.Q (data.residueOrigin x + site)) ^ 2) ≤
      (∏ q : data.Q, (1 + 24 / (q.val : ℝ))) *
        ∏ j : Fin J, (4 * (primeHarmonicMass (P j)) ^ 2 + primeHarmonicMass (P j)) := by
  let F := fun x : data.P → Bool =>
    ∏ j : Fin J, (booleanCount (fun p : P j => x ⟨p.val, hsub j p.property⟩) +
      primeHarmonicMass (P j)) ^ 2
  let g := fun n : ℤ => (actualPaddingWeight data.Q n) ^ 2
  have he (x : ↥(data.P ∪ data.Q) → Fin B) :
      (primeRowMajorant P data.Q (data.residueOrigin x + site)) ^ 2 =
        F (fun p => decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) *
          g (data.residueOrigin x + site) := by
    simp only [primeRowMajorant, mul_pow, prod_pow, F, g, actualPrimeDegree_eq_count]
    ring
  simp_rw [he]
  rw [data.residue_average_prime_boolean_padding hB site F g
    (fun n m hnm => congrArg (fun t : ℝ => t ^ 2)
      (actualPaddingWeight_residue_congr data.Q n m hnm))]
  have hq : (data.paddingResidueLaw B hB).average
      (fun z => g (data.paddingResidueOrigin z + site)) =
        ∏ q : data.Q, (1 + 24 / (q.val : ℝ)) := by
    have hl (z : data.Q → Fin B) : g (data.paddingResidueOrigin z + site) =
        (paddingTiltWeight data.Q (paddingResidueAvailable data.Q B site z)) ^ 2 := by
      dsimp only [g]
      rw [actualPaddingWeight_lift data.Q B site z (data.paddingResidueOrigin z + site)
        (fun p => by rw [Int.cast_add, data.paddingResidueOrigin_spec])]
    simp_rw [hl]
    rw [paddingResidueLaw, padding_residue_average data.Q B
      (fun p hp => (data.primeQ p hp).two_le)
      (fun p hp => hB p (mem_union_right _ hp)) site
      (fun a => (paddingTiltWeight data.Q a) ^ 2)]
    exact padding_weight_square_average data.Q _
  rw [hq, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun _ _ => by positivity))
  exact prime_band_row_second_moment P
    (fun j p hp => (data.primeP p (hsub j hp)).two_le) data.P
    (fun p hp => (data.primeP p hp).two_le) hsub hdisjoint

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI
