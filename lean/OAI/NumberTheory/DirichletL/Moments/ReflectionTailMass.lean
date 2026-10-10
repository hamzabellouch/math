import OAI.NumberTheory.DirichletL.Moments.ReflectionMass
import OAI.NumberTheory.DirichletL.Moments.ReflectionNegligible

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectionTailMass
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma subset_norm_le (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S) :
    (Ideal.absNorm (∏P∈D,P):ℝ)≤(Ideal.absNorm (∏P∈S,P):ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS)))
    (map_dvd Ideal.absNorm (Finset.prod_dvd_prod_of_subset D S (fun P=>P) hD))

lemma restoration_norm_one (S : Finset (Ideal O)) (H : SmoothIdeal S) : 1≤norm H.val := by
  unfold CenteredMomentReflectionDeletion.norm
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr H.val.property))

lemma dual_scale_bounds (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S)
    (H : SmoothIdeal S) (Q X U : ℝ) (hQ : 0<Q) (hX : 0<X)
    (hcap : Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤U*X) :
    0<Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val) ∧
    Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)≤U := by
  have hd := subset_product_norm_pos D (fun P hP=>hS P (hD hP))
  have hh := norm_pos H.val
  refine ⟨by positivity,?_⟩
  calc
    _≤Q*(Ideal.absNorm (∏P∈D,P):ℝ)/X :=
      div_le_div_of_nonneg_left (by positivity) hX
        (by nlinarith [restoration_norm_one S H])
    _≤Q*(Ideal.absNorm (∏P∈S,P):ℝ)/X :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (subset_norm_le S D hS hD) hQ.le) hX.le
    _≤U := (div_le_iff₀ hX).mpr hcap

theorem coefficient_column_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
      (η ηi : Character)(f : Finset (Ideal O)→SmoothIdeal S→ℂ)(B : ℝ),0≤B →
      (∀D∈S.powerset,∀H,‖f D H‖≤B) →
      (∀D∈S.powerset,Summable (fun H=>coefficient η ηi S D H*f D H)) ∧
      ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*f D H‖≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*B := by
  obtain ⟨C,hC,hbound⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi f B hB hf
  have hs (D : Finset (Ideal O)) (hD : D∈S.powerset) :
      Summable (fun H : SmoothIdeal S=>‖coefficient η ηi S D H*f D H‖) := by
    apply ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B).of_nonneg_of_le
      (fun _=>norm_nonneg _)
    intro H
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
  refine ⟨fun D hD=>(hs D hD).of_norm,?_⟩
  calc
    _≤∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H*f D H‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun D hD=>norm_tsum_le_tsum_norm (hs D hD)))
    _≤∑D∈S.powerset,(∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)*B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [←tsum_mul_right]
      apply (hs D hD).tsum_le_tsum _
        ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B)
      intro H
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
    _≤_ := by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hbound S hS η ηi).2 hB

theorem actual_deleted_discarded_negligible (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
        (η ηi χ : Character)(t Q X Z : ℝ),1≤Z → 0<Q → 0<X →
        Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X →
        let F := fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x
        (∀D∈S.powerset,Summable (fun H : SmoothIdeal S=>coefficient η ηi S D H*
          HeckeDyadic.polynomial χ false F
            (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0)) ∧
        ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*
          HeckeDyadic.polynomial χ false F
            (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0‖≤
          C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨n,hn⟩ := actual_reflected_upper_negligible a b xi saving L Cscale ha hxi hscale
  obtain ⟨D,hD,hDb⟩ := coefficient_column_bound ε hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hCb⟩ := hn W hs hW
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro S hS η ηi χ t Q X Z hZ hQ hX hcap
  dsimp only
  have hh := hDb S hS η ηi
    (fun E H=>HeckeDyadic.polynomial χ false
      (fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
        paperRadialFourier (CompletedHeight.normTwistedSource W t) x)
      (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm H.val)) 0 0)
    (C*(1+‖t‖)^n*Z^(-saving)) (by positivity) (by
      intro E hE H
      have hy := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) H Q X (Cscale*Z^L) hQ hX hcap
      exact hCb χ t _ Z hZ hy.1 hy.2)
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  ring

end SevenEighths.CenteredMomentReflectionTailMass

end

end OAI
