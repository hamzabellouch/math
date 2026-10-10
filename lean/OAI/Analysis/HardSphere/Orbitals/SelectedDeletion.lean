import Mathlib
import OAI.Analysis.HardSphere.Geometry.FreePathExpectation
import OAI.Analysis.HardSphere.Geometry.PathPermutation

namespace OAI

section

section
noncomputable section
open scoped BigOperators
namespace HardSphere

def selectedPermutation {m n : ℕ} (S : Finset (Fin (m+n))) (hS : S.card=m) : Equiv.Perm (Fin (m+n)) := by
  classical
  have hc : Fintype.card {i : Fin (m+n) // i∉S}=n := by
    simp [hS]
  let eS : Fin m ≃ {i : Fin (m+n) //i∈S} := (S.equivFinOfCardEq hS).symm
  let eT : Fin n ≃ {i : Fin (m+n) //i∉S} := (Fintype.equivFinOfCardEq hc).symm
  exact (finSumFinEquiv (m:=m) (n:=n)).symm.trans
    ((eS.sumCongr eT).trans (Equiv.sumCompl fun i : Fin (m+n) ↦ i∈S))

lemma selectedPermutation_prod {m n : ℕ} (S : Finset (Fin (m+n))) (hS : S.card=m)
    {M : Type*} [CommMonoid M] (f : Fin (m+n) → M) :
    (∏ i : Fin m,f (selectedPermutation S hS (Fin.castAdd n i)))=∏i∈S,f i := by
  classical
  have he (i : Fin m) : selectedPermutation S hS (Fin.castAdd n i)=((S.equivFinOfCardEq hS).symm i).val := by
    simp [selectedPermutation]
  simp only [he]
  exact ((S.equivFinOfCardEq hS).symm.prod_comp (fun i : S ↦ f i.val)).trans (Finset.prod_coe_sort S f)

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open Wiener

@[simp] lemma onePathAt_permute {n : ℕ} {L : Length} (σ : Equiv.Perm (Fin n))
    (i : Fin n) (ω : ConfigurationPath n L) :
    onePathAt i (permuteConfigurationPath σ ω)=onePathAt (σ i) ω := rfl

@[simp] lemma onePathAt_split_left {m n : ℕ} {L : Length} (i : Fin m)
    (ω : ConfigurationPath (m+n) L) :
    onePathAt i (splitConfigurationPath m n L ω).1=onePathAt (Fin.castAdd n i) ω := rfl

lemma selected_product_deletion : ∃ C : ℝ, 0<C ∧
    ∀ (N : ℕ) (L : Length) (r t : ℝ), 0<r → 0<t →
    (N:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet N L, IsGroundVector N L r u →
    ∀ h : ConfigurationPath 1 L → ℝ≥0∞, Measurable h →
    (∀ ω,h (reverseConfigurationPath 1 L ω)=h ω) →
    ∀ S : Finset (Fin N),
      (∫⁻ ω : ConfigurationPath N L, ∏i∈S,h (onePathAt i ω) ∂groundPathLaw N L r t u) ≤
      ENNReal.ofReal (Real.exp (t*C*(S.card:ℝ)*(N:ℝ)*r/L.val^3))*
        ∫⁻ X : Configuration N L, ∏i∈S,oneFreeExpectation t h (X i) ∂groundPositionLaw N L u := by
  classical
  obtain ⟨C,hC,hdel⟩ := groundPathLaw_deletion
  refine ⟨C,hC,?_⟩
  intro N L r t hr ht hs u hu h hh hrev S
  have hc : S.card≤N := by simpa using Finset.card_le_univ S
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hc
  generalize hm : S.card=m at hn
  subst N
  let σ := selectedPermutation S hm
  let H : ConfigurationPath m L → ℝ≥0∞ := fun ω ↦ ∏i,h (onePathAt i ω)
  have hH : Measurable H := pathProduct_measurable Finset.univ hh
  have hHrev (ω : ConfigurationPath m L) : H (reverseConfigurationPath m L ω)=H ω := by
    simp only [H,onePathAt_reverse,hrev]
  have hD := hdel m n L r t hr ht hs u hu H hH hHrev
  have hexp : (∫⁻ ω : ConfigurationPath (m+n) L,H (splitConfigurationPath m n L ω).1
      ∂groundPathLaw (m+n) L r t u)=
      ∫⁻ ω : ConfigurationPath (m+n) L,∏i∈S,h (onePathAt i ω) ∂groundPathLaw (m+n) L r t u := by
    have hp := (groundPathLaw_permute u hu.2.1 r t σ).lintegral_comp
      (hH.comp (splitConfigurationPath_continuous m n L).measurable.fst)
    simp only [Function.comp_def] at hp
    rw [←hp]
    apply lintegral_congr
    intro ω
    simp only [H,onePathAt_split_left,onePathAt_permute]
    exact selectedPermutation_prod S hm (fun i ↦ h (onePathAt i ω))
  have hF (X : Configuration (m+n) L) :
      freePathExpectation t H (splitConfiguration m n L X).1=
        ∏i:Fin m,oneFreeExpectation t h (X (Fin.castAdd n i)) :=
    free_product_expectation t hh _
  have hM : Measurable (fun X : Configuration (m+n) L ↦
      ∏i:Fin m,oneFreeExpectation t h (X (Fin.castAdd n i))) :=
    Finset.measurable_prod Finset.univ fun i _ ↦ (oneFreeExpectation_measurable t hh).comp (measurable_pi_apply _)
  have hpos : (∫⁻ X : Configuration (m+n) L,
      freePathExpectation t H (splitConfiguration m n L X).1 ∂groundPositionLaw (m+n) L u)=
      ∫⁻ X : Configuration (m+n) L,∏i∈S,oneFreeExpectation t h (X i) ∂groundPositionLaw (m+n) L u := by
    simp only [hF]
    rw [←(groundPositionLaw_permute u hu.2.1 σ).lintegral_comp hM]
    apply lintegral_congr
    intro X
    exact selectedPermutation_prod S hm (fun i ↦ oneFreeExpectation t h (X i))
  rw [hexp,hpos] at hD
  simpa only [hm] using hD

lemma ground_product_one_add : ∃ C : ℝ, 0<C ∧
    ∀ (N : ℕ) (L : Length) (r t : ℝ), 0<r → 0<t →
    (N:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet N L, IsGroundVector N L r u →
    ∀ h : ConfigurationPath 1 L → ℝ≥0∞, Measurable h →
    (∀ ω,h (reverseConfigurationPath 1 L ω)=h ω) →
      (∫⁻ ω : ConfigurationPath N L, ∏i, (1+h (onePathAt i ω)) ∂groundPathLaw N L r t u) ≤
        ∫⁻ X : Configuration N L, ∏i,(1+ENNReal.ofReal (Real.exp (t*C*(N:ℝ)*r/L.val^3))*
          oneFreeExpectation t h (X i)) ∂groundPositionLaw N L u := by
  classical
  obtain ⟨C,hC,hdel⟩ := selected_product_deletion
  refine ⟨C,hC,?_⟩
  intro N L r t hr ht hs u hu h hh hrev
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (t*C*(N:ℝ)*r/L.val^3))
  have ha (S : Finset (Fin N)) :
      ENNReal.ofReal (Real.exp (t*C*(S.card:ℝ)*(N:ℝ)*r/L.val^3))=a^S.card := by
    rw [show t*C*(S.card:ℝ)*(N:ℝ)*r/L.val^3=(S.card:ℝ)*(t*C*(N:ℝ)*r/L.val^3) by ring,
      Real.exp_nat_mul,ENNReal.ofReal_pow (Real.exp_nonneg _)]
  have hb (S : Finset (Fin N)) : Measurable (fun X : Configuration N L ↦
      ∏i∈S,a*oneFreeExpectation t h (X i)) :=
    Finset.measurable_prod S fun i _ ↦ measurable_const.mul
      ((oneFreeExpectation_measurable t hh).comp (measurable_pi_apply i))
  simp only [Finset.prod_one_add]
  rw [lintegral_finsetSum _ (fun S _ ↦ pathProduct_measurable S hh),
    lintegral_finsetSum _ (fun S _ ↦ hb S)]
  apply Finset.sum_le_sum
  intro S _
  calc
    _ ≤ a^S.card*∫⁻ X : Configuration N L,∏i∈S,oneFreeExpectation t h (X i)
        ∂groundPositionLaw N L u := by simpa only [ha] using hdel N L r t hr ht hs u hu h hh hrev S
    _ = ∫⁻ X : Configuration N L,∏i∈S,a*oneFreeExpectation t h (X i) ∂groundPositionLaw N L u := by
      have hM : Measurable (fun X : Configuration N L ↦ ∏i∈S,oneFreeExpectation t h (X i)) :=
        Finset.measurable_prod S fun i _ ↦ (oneFreeExpectation_measurable t hh).comp (measurable_pi_apply i)
      rw [←lintegral_const_mul _ hM]
      apply lintegral_congr
      intro X
      simp only [Finset.prod_mul_distrib,Finset.prod_const]

end HardSphere

end
end

end

end OAI
