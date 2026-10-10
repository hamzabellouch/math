import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.NormIteratedFDerivSmoothStar
import OAI.MeasureTheory.FalconerCompletion.Graphs.SymbolFiniteProductDerivative2
import OAI.MeasureTheory.FalconerCompletion.Shells.WeightedMaskTransform

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Filter
open scoped ContDiff Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [DecidableEq ι]

theorem all_mask_product_admissibleND
    (W : Finset (List (V →L[ℝ] V))) (m b B k : ℕ)
    (hW : ∀ L ∈ W, L.length ≤ b) (C Ccount σ : ℝ) (hC : 0≤C) (hσ : 0<σ) :
    ∃ D : ℝ, 1≤D ∧ ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ι)
      (f : ι → SmoothFunctionND V) (L : ι → List (V →L[ℝ] V)) (A : ι → ℝ) (M : ℝ),
      (S.card:ℝ) ≤ Ccount*(N:ℝ)^k →
      (∀ i ∈ S, L i ∈ W) → (∑ i ∈ S, (L i).length ≤ B) →
      (∀ i ∈ S, 1 ≤ A i) → (∀ i ∈ S, A i ≤ M) → 0 ≤ M →
      (∀ i ∈ S, ∀ w, ‖w‖=1 → ‖(f i).1 w‖ ≤ 1) →
      (∀ i ∈ S, ∀ j ≤ m+b, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (f i).1 w‖ ≤ C*(A i)^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (smoothFinsetProductND S (fun i =>
          normalizedAngularWordND (A i) (L i) (f i))).1 w‖ ≤
            D^B*(((2:ℝ)^N)^σ*M)^j := by
  obtain ⟨D,hD,hbound⟩ := normalizedAngularProductND_admissible (ι := ι) W m b B hW C hC
  refine ⟨D,hD,?_⟩
  filter_upwards [shell_polynomial_subpowerND k (D*Ccount) σ hσ] with N hN
  intro S f L A M hcard hL hB hA hAM hM hf0 hf j hj w hw
  apply (hbound S f L A M (Ccount*(N:ℝ)^k) hL hB hA hAM hM hcard hf0 hf j hj w hw).trans
  calc
    _ = D^B*((D*Ccount*(N:ℝ)^k)*M)^j := by rw [pow_add]; simp only [mul_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hD) _)
      apply pow_le_pow_left₀
      · have hP : 0≤Ccount*(N:ℝ)^k := (Nat.cast_nonneg S.card).trans hcard
        simpa only [mul_assoc] using mul_nonneg (mul_nonneg (zero_le_one.trans hD) hP) hM
      · exact mul_le_mul_of_nonneg_right hN hM

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Filter
open scoped ContDiff Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem mask_product_admissibleND {ι : Type*} [DecidableEq ι]
    (m k : ℕ) (C Ccount σ : ℝ) (hC : 0≤C) (hσ : 0<σ) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ι) (f : ι → SmoothFunctionND V)
      (A : ι → ℝ) (M : ℝ), (S.card:ℝ) ≤ Ccount*(N:ℝ)^k →
      (∀ i ∈ S, 1 ≤ A i) → (∀ i ∈ S, A i ≤ M) → 0 ≤ M →
      (∀ i ∈ S, ∀ w, ‖w‖=1 → ‖(f i).1 w‖ ≤ 1) →
      (∀ i ∈ S, ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (f i).1 w‖ ≤ C*(A i)^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (smoothFinsetProductND S f).1 w‖ ≤
          (((2:ℝ)^N)^σ*M)^j := by
  classical
  obtain ⟨D,_,hbound⟩ := all_mask_product_admissibleND (ι := ι)
    ({[]} : Finset (List (V →L[ℝ] V))) m 0 0 k (by simp) C Ccount σ hC hσ
  filter_upwards [hbound] with N hN
  intro S f A M hcard hA hAM hM hf0 hf j hj w hw
  have hh := hN S f (fun _ => []) A M hcard (by simp) (by simp) hA hAM hM hf0
    (by simpa using hf) j hj w hw
  simpa [normalizedAngularWordND,angularWordOperatorND] using hh

omit [FiniteDimensional ℝ V] in
lemma norm_iteratedFDeriv_smoothStarND (f : SmoothFunctionND V) (j : ℕ) (w : V) :
    ‖iteratedFDeriv ℝ j (smoothStarND f).1 w‖ ≤ ‖iteratedFDeriv ℝ j f.1 w‖ := by
  have hj : (j : WithTop ℕ∞) ≤ (↑(⊤:ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)
  have h := Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (x := w) (smoothFunctionND_contDiff f).contDiffAt hj
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,Function.comp_def,Complex.conjLIE_apply,starRingEnd_apply,
    LinearIsometryEquiv.norm_toContinuousLinearMap,one_mul,smoothStarND] using h

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Filter
open scoped ContDiff Topology
variable {n : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
local notation "V" => EuclideanSpace ℝ (Fin (n+1))

theorem pair_mask_product_admissibleND (m k : ℕ) (C Ccount σ : ℝ)
    (hC : 0≤C) (hσ : 0<σ) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ι) (T : Finset κ)
      (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
      (A : ι → ℝ) (B : κ → ℝ) (M : ℝ) (z : V × V),
      ((S.card+T.card:ℕ):ℝ) ≤ Ccount*(N:ℝ)^k →
      (∀ i ∈ S, 1 ≤ A i ∧ A i ≤ M) → (∀ i ∈ T, 1 ≤ B i ∧ B i ≤ M) → 0 ≤ M →
      (∀ i ∈ S, ∀ w, ‖w‖=1 → ‖(f z.1 i).1 w‖ ≤ 1) →
      (∀ i ∈ T, ∀ w, ‖w‖=1 → ‖(g z.2 i).1 w‖ ≤ 1) →
      (∀ i ∈ S, ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (f z.1 i).1 w‖ ≤ C*(A i)^j) →
      (∀ i ∈ T, ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (g z.2 i).1 w‖ ≤ C*(B i)^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (pairMaskProductND S T f g z).1 w‖ ≤
          (((2:ℝ)^N)^σ*M)^j := by
  filter_upwards [@mask_product_admissibleND V _ _ _ (ι ⊕ κ) _ m k C Ccount σ hC hσ]
    with N hN
  intro S T f g A B M z hcard hA hB hM hf0 hg0 hf hg
  apply hN (S.disjSum T) (Sum.elim (f z.1) (fun i => smoothStarND (g z.2 i)))
    (Sum.elim A B) M (by simpa using hcard) ?_ ?_ hM ?_ ?_
  · intro i hi
    cases i with
    | inl i => exact (hA i (by simpa using hi)).1
    | inr i => exact (hB i (by simpa using hi)).1
  · intro i hi
    cases i with
    | inl i => exact (hA i (by simpa using hi)).2
    | inr i => exact (hB i (by simpa using hi)).2
  · intro i hi w hw
    cases i with
    | inl i => exact hf0 i (by simpa using hi) w hw
    | inr i => simpa [smoothStarND] using hg0 i (by simpa using hi) w hw
  · intro i hi j hj w hw
    cases i with
    | inl i => exact hf i (by simpa using hi) j hj w hw
    | inr i =>
      exact (norm_iteratedFDeriv_smoothStarND (g z.2 i) j w).trans
        (hg i (by simpa using hi) j hj w hw)

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
