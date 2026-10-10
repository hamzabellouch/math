import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.SymbolFiniteProductDerivative
import OAI.MeasureTheory.FalconerCompletion.Recursion.DescriptorSmooth
import OAI.MeasureTheory.FalconerCompletion.Shells.ShellPolynomialSubpower

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
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

end CurrentFalconer
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Filter
open scoped ENNReal RealInnerProductSpace ContDiff Topology Classical
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

noncomputable def actualAngularProduct (S : Finset ι) (b : ι → PolicyDescriptor)
    (L : ι → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    SmoothFunctionND (EuclideanSpace ℝ (Fin d)) :=
  smoothFinsetProductND S (fun e => actualEndpointAngular (L e) ρ m N sig C J i (b e) x)

omit [DecidableEq ι] in
lemma actualAngularProduct_measurable (S : Finset ι) (b : ι → PolicyDescriptor)
    (L : ι → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (actualAngularProduct S b L ρ m N sig C J i z.1).1 z.2) := by
  exact Finset.measurable_prod _ (fun e _ => actualEndpointAngular_measurable (L e) ρ m N sig C J i (b e))

omit [DecidableEq ι] in
lemma actualAngularProduct_even (S : Finset ι) (b : ι → PolicyDescriptor)
    (L : ι → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    Function.Even (actualAngularProduct S b L ρ m N sig C J i x).1 := by
  intro w
  exact Finset.prod_congr rfl (fun e _ => actualEndpointAngular_even (L e) ρ m N sig C J i (b e) x w)

lemma uniform_actualAngularProduct_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ρ →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ) (S : Finset ι) (b : ι → PolicyDescriptor),
      (∀ e ∈ S, ValidDescriptor N (b e)) →
      ∀ (L : ι → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
        (k : ℕ) (x w : EuclideanSpace ℝ (Fin d)), ‖w‖=1 →
      w ∈ tsupport (iteratedFDeriv ℝ k (actualAngularProduct S b L ρ m N sig C J i x).1) →
      ∀ e ∈ S, (x,w) ∈ endpointGood ρ m N sig C J (i+1) (b e) := by
  obtain ⟨N₀,h₀⟩ := uniform_actualEndpointAngular_support (d:=d) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hf m C i S b hb L k x w hw hs e he
  have hh := symbol_finite_product_supportND S
    (fun e => (actualEndpointAngular (L e) ρ m N sig C J i (b e) x).1) he k hs
  apply h₀ N hN ρ hf m C i (b e) (hb e he) (L e) 0 x w hw
  have hts : tsupport (iteratedFDeriv ℝ 0 (actualEndpointAngular (L e) ρ m N sig C J i (b e) x).1)=
      tsupport (actualEndpointAngular (L e) ρ m N sig C J i (b e) x).1 := by
    apply congrArg closure
    ext z
    simp only [Function.mem_support]
    rw [← norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
  rwa [hts]

lemma uniform_actualAngularProduct_derivatives
    (W : Finset (List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (M B total k : ℕ) (hW : ∀ L ∈ W, L.length ≤ B) (Ccount sig : ℝ) (hsig : 0<sig) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ι) (b : ι → PolicyDescriptor)
      (L : ι → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
      (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (C : ℝ) (J i l : ℕ),
      (S.card:ℝ) ≤ Ccount*(N:ℝ)^k →
      (∀ e ∈ S, L e ∈ W) → (∑ e ∈ S, (L e).length ≤ total) →
      (∀ e ∈ S, descriptorLength (b e) ≤ l) →
      ∀ (x : EuclideanSpace ℝ (Fin d)), ∀ j ≤ M, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (actualAngularProduct S b L ρ m N sig C J i x).1 w‖ ≤
        D^total*(((2:ℝ)^N)^sig*sourceMaskScaleND l ((2:ℝ)^N) sig)^j := by
  obtain ⟨C₀,hC,hCb⟩ := actualEndpointMask_derivatives d (M+B)
  obtain ⟨D,hD,hDb⟩ := all_mask_product_admissibleND (ι:=ι) W M B total k hW C₀ Ccount sig hC hsig
  refine ⟨D,hD,?_⟩
  filter_upwards [hDb] with N hDb
  intro S b L ρ m C J i l hcard hL htotal hl x j hj w hw
  apply hDb S (fun e => actualEndpointSmooth ρ m N sig C J i (b e) x) L
    (fun e => sourceMaskScaleND (descriptorLength (b e)) ((2:ℝ)^N) sig)
    (sourceMaskScaleND l ((2:ℝ)^N) sig) hcard hL htotal
    (fun _ _ => sourceMaskScaleND_one_le _ _ _)
    (fun e he => sourceMaskScaleND_mono (hl e he) (by positivity))
    (sourceMaskScaleND_pos _ _ _).le _ _ j hj w hw
  · intro e he z hz
    change ‖(actualEndpointMask ρ m N sig C J i (b e) x z:ℂ)‖ ≤ 1
    rw [Complex.norm_real,Real.norm_eq_abs]
    have hb := actualEndpointMask_bounds ρ m N sig C J i (b e) x hz.le
    simpa only [abs_of_nonneg hb.1] using hb.2
  · intro e he n hn z hz
    rw [actualEndpointSmooth_derivative_norm]
    exact hCb ρ m N sig C J i (b e) n hn x z

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
