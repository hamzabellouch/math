import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SingleEdgeWeight

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {h ℓ : ℕ}

lemma primeFactors_card_le_log (n : ℕ) (hn : 0 < n) (M : ℝ)
    (hM : (n : ℝ) ≤ Real.exp M) : (n.primeFactors.card : ℝ) ≤ M / Real.log 2 := by
  have hp : (2 : ℕ) ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    simpa only [prod_const] using prod_le_prod (s := n.primeFactors)
      (f := fun _ => (2 : ℕ)) (g := fun p => p)
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hnprod := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hpow' : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by
    exact_mod_cast hp.trans hnprod
  have hpow := hpow'.trans hM
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ)^n.primeFactors.card) hpow
  rw [Real.log_pow, Real.log_exp] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

def differencePrimeSupport (V : Finset ℤ) : Finset ℕ :=
  V.offDiag.biUnion (fun vu => (vu.2 - vu.1).natAbs.primeFactors)

lemma collision_mem_differencePrimeSupport (w : ClosedLine h ℓ) (p : S.Index)
    (hc : IsCollision w p) : (p : ℕ) ∈ differencePrimeSupport (treeVertices w) := by
  have hn : ¬∀ v ∈ treeVertices w, ∀ u ∈ treeVertices w,
      (v : ZMod (p : ℕ)) = (u : ZMod (p : ℕ)) → v = u := hc
  push Not at hn
  obtain ⟨v,hv,u,hu,heq,hne⟩ := hn
  apply mem_biUnion.mpr
  refine ⟨(v,u), mem_offDiag.mpr ⟨hv,hu,hne⟩, ?_⟩
  apply Nat.mem_primeFactors.mpr
  refine ⟨S.prime_mem p p.property, ?_, ?_⟩
  · exact Int.natCast_dvd.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub v u (p : ℕ)).mp heq)
  · exact Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hne.symm)

lemma card_differencePrimeSupport_le (V : Finset ℤ) (M : ℝ)
    (hM : ∀ v ∈ V, ∀ u ∈ V, v ≠ u → ((u-v).natAbs : ℝ) ≤ Real.exp M) :
    ((differencePrimeSupport V).card : ℝ) ≤ (V.offDiag.card : ℝ) * (M / Real.log 2) := by
  calc
    _ ≤ ∑ vu ∈ V.offDiag, ((vu.2-vu.1).natAbs.primeFactors.card : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ _vu ∈ V.offDiag, M / Real.log 2 := by
      apply sum_le_sum
      intro vu hvu
      obtain ⟨hv,hu,hne⟩ := mem_offDiag.mp hvu
      exact primeFactors_card_le_log _
        (Int.natAbs_pos.mpr (sub_ne_zero.mpr hne.symm)) M (hM vu.1 hv vu.2 hu hne)
    _ = _ := by simp

def collisionIndices (w : ClosedLine h ℓ) : Finset S.Index := univ.filter (IsCollision w)

lemma card_collisionIndices_le (w : ClosedLine h ℓ) (M : ℝ)
    (hM : ∀ v ∈ treeVertices w, ∀ u ∈ treeVertices w,
      v ≠ u → ((u-v).natAbs : ℝ) ≤ Real.exp M) :
    ((collisionIndices (S := S) w).card : ℝ) ≤
      ((treeVertices w).offDiag.card : ℝ) * (M / Real.log 2) := by
  have hsub : (collisionIndices (S := S) w).image Subtype.val ⊆
      differencePrimeSupport (treeVertices w) := by
    intro p hp
    obtain ⟨q,hq,hqp⟩ := mem_image.mp hp
    rw [← hqp]
    exact collision_mem_differencePrimeSupport w q (mem_filter.mp hq).2
  have hc : (collisionIndices (S := S) w).card ≤ (differencePrimeSupport (treeVertices w)).card := by
    rw [← card_image_of_injective _ Subtype.val_injective]
    exact card_le_card hsub
  have hc' : ((collisionIndices (S := S) w).card : ℝ) ≤
      ((differencePrimeSupport (treeVertices w)).card : ℝ) := by exact_mod_cast hc
  exact hc'.trans (card_differencePrimeSupport_le _ M hM)

lemma sum_inv_le_card_div (P : Finset S.Index) (P₀ : ℝ) (hP₀ : 0 < P₀)
    (hp : ∀ p ∈ P, P₀ ≤ (p : ℝ)) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (P.card : ℝ) / P₀ := by
  calc
    _ ≤ ∑ _p ∈ P, P₀⁻¹ := by
      apply sum_le_sum
      intro p hmem
      exact inv_anti₀ hP₀ (hp p hmem)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, div_eq_mul_inv]

lemma collision_reciprocal_mass (w : ClosedLine h ℓ) (M P₀ : ℝ) (hP₀ : 0 < P₀)
    (hp : ∀ p : S.Index, P₀ ≤ (p : ℝ))
    (hM : ∀ v ∈ treeVertices w, ∀ u ∈ treeVertices w,
      v ≠ u → ((u-v).natAbs : ℝ) ≤ Real.exp M) :
    (∑ p ∈ collisionIndices (S := S) w, (p : ℝ)⁻¹) ≤
      ((treeVertices w).offDiag.card : ℝ) * (M / Real.log 2) / P₀ := by
  exact (sum_inv_le_card_div _ P₀ hP₀ (fun p _ => hp p)).trans
    (div_le_div_of_nonneg_right (card_collisionIndices_le w M hM) hP₀.le)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
