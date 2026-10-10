import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Recursion.SourceSymbol

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma norm_iteratedFDeriv_smoothStarND (f : SmoothFunctionND V) (j : ℕ) (w : V) :
    ‖iteratedFDeriv ℝ j (smoothStarND f).1 w‖ ≤ ‖iteratedFDeriv ℝ j f.1 w‖ := by
  have hj : (j : WithTop ℕ∞) ≤ (↑(⊤:ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)
  have h := Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (x := w) (smoothFunctionND_contDiff f).contDiffAt hj
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,Function.comp_def,Complex.conjLIE_apply,starRingEnd_apply,
    LinearIsometryEquiv.norm_toContinuousLinearMap,one_mul,smoothStarND] using h

lemma tsupport_smoothStarND (f : SmoothFunctionND V) : tsupport (smoothStarND f).1=tsupport f.1 := by
  apply congrArg closure
  ext w
  change star (f.1 w)≠0 ↔ f.1 w≠0
  simp only [ne_eq,star_eq_zero]

noncomputable def pairSmoothSymbolsND (b c : V → SmoothFunctionND V) (z : V×V) : SmoothFunctionND V :=
  smoothMulND (b z.1) (smoothStarND (c z.2))

lemma pairSmoothSymbolsND_support (b c : V → SmoothFunctionND V) (z : V×V) (k : ℕ) :
    tsupport (iteratedFDeriv ℝ k (pairSmoothSymbolsND b c z).1) ⊆
      tsupport (b z.1).1 ∩ tsupport (c z.2).1 := by
  apply (tsupport_iteratedFDeriv_subset k).trans
  have hright : tsupport (pairSmoothSymbolsND b c z).1 ⊆ tsupport (smoothStarND (c z.2)).1 :=
    tsupport_mul_subset_right
  rw [tsupport_smoothStarND] at hright
  exact subset_inter tsupport_mul_subset_left hright

lemma pairSmoothSymbolsND_derivatives (b c : V → SmoothFunctionND V) (z : V×V) (M : ℕ)
    {C D A : ℝ} (hC : 0≤C) (hD : 0≤D) (hA : 0≤A) (w : V)
    (hb : ∀ j≤M, ‖iteratedFDeriv ℝ j (b z.1).1 w‖ ≤ C*A^j)
    (hc : ∀ j≤M, ‖iteratedFDeriv ℝ j (c z.2).1 w‖ ≤ D*A^j) :
    ‖iteratedFDeriv ℝ M (pairSmoothSymbolsND b c z).1 w‖ ≤ C*D*(2*A)^M :=
  symbol_mul_derivative_boundND _ _ M hC hD hA w hb
    (fun j hj => (norm_iteratedFDeriv_smoothStarND _ j w).trans (hc j hj))

lemma pairSmoothSymbolsND_measurable [MeasurableSpace V] [BorelSpace V]
    (b c : V → SmoothFunctionND V)
    (hb : Measurable (fun z : V×V => (b z.1).1 z.2))
    (hc : Measurable (fun z : V×V => (c z.1).1 z.2)) :
    Measurable (fun z : (V×V)×V => (pairSmoothSymbolsND b c z.1).1 z.2) := by
  have hs : Measurable (star : ℂ → ℂ) := continuous_star.measurable
  exact (hb.comp ((measurable_fst.fst).prodMk measurable_snd)).mul
    (hs.comp (hc.comp ((measurable_fst.snd).prodMk measurable_snd)))

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
variable {d : ℕ}

noncomputable def actualPairSourceSymbol
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d))) :=
  pairSmoothSymbolsND (actualSourceSymbol A N q a t L ρ m sig C J i f Q)
    (actualSourceSymbol A N q a t L ρ m sig C J i f Q)

lemma actualPairSourceSymbol_measurable
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : Measurable f)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d))) :
    Measurable (fun z : (EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d))×EuclideanSpace ℝ (Fin d) =>
      (actualPairSourceSymbol A N q a t L ρ m sig C J i f Q z.1).1 z.2) :=
  pairSmoothSymbolsND_measurable _ _ (actualSourceSymbol_measurable A N q a t L ρ m sig C J i f hf Q)
    (actualSourceSymbol_measurable A N q a t L ρ m sig C J i f hf Q)

noncomputable def actualPairAmbientGood
    (A : ℕ → ℝ) (N q a t : ℕ) (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) (z : EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d)) :=
  actualPolicyAmbientGood A N q a t ρ m sig C J i z.1 ∩
    actualPolicyAmbientGood A N q a t ρ m sig C J i z.2

lemma actualPairAmbientGood_even
    (A : ℕ → ℝ) (N q a t : ℕ) (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) (z : EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d))
    {w : EuclideanSpace ℝ (Fin d)} (hw : w∈actualPairAmbientGood A N q a t ρ m sig C J i z) :
    -w∈actualPairAmbientGood A N q a t ρ m sig C J i z :=
  ⟨actualPolicyAmbientGood_even A N q a t ρ m sig C J i z.1 hw.1,
   actualPolicyAmbientGood_even A N q a t ρ m sig C J i z.2 hw.2⟩

lemma actualPairAmbientGood_measurable
    (A : ℕ → ℝ) (N q a t : ℕ) (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) :
    MeasurableSet {z : (EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d))×EuclideanSpace ℝ (Fin d) |
      z.2∈actualPairAmbientGood A N q a t ρ m sig C J i z.1} := by
  have hh := actualPolicyAmbientGood_measurable A N q a t ρ m sig C J i
  let p₁ : ((EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d))×EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d) := fun z => (z.1.1,z.2)
  let p₂ : ((EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d))×EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d) := fun z => (z.1.2,z.2)
  have hp₁ : Measurable p₁ := measurable_fst.fst.prodMk measurable_snd
  have hp₂ : Measurable p₂ := measurable_fst.snd.prodMk measurable_snd
  change MeasurableSet (p₁ ⁻¹' {z | z.2∈actualPolicyAmbientGood A N q a t ρ m sig C J i z.1} ∩
    p₂ ⁻¹' {z | z.2∈actualPolicyAmbientGood A N q a t ρ m sig C J i z.1})
  exact (hh.preimage hp₁).inter (hh.preimage hp₂)

lemma uniform_actualPairSourceSymbol_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ρ →
      ∀ (A : ℕ → ℝ) (q a t : ℕ), 0<q → t≤N →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
        (f : EuclideanSpace ℝ (Fin d) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d)))
        (k : ℕ) (z : EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d)),
      tsupport (iteratedFDeriv ℝ k (actualPairSourceSymbol A N q a t L ρ m sig C J i f Q z).1) ⊆
        actualPairAmbientGood A N q a t ρ m sig C J (i+1) z := by
  obtain ⟨N₀,h₀⟩ := uniform_actualSourceSymbol_support (d:=d) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hf A q a t hq ht m C i L f Q k z w hw
  have hh := pairSmoothSymbolsND_support
    (actualSourceSymbol A N q a t L ρ m sig C J i f Q)
    (actualSourceSymbol A N q a t L ρ m sig C J i f Q) z k hw
  have hbase (x : EuclideanSpace ℝ (Fin d)) := h₀ N hN ρ hf A q a t hq ht m C i L f Q 0 x
  have hts (b : SmoothFunctionND (EuclideanSpace ℝ (Fin d))) :
      tsupport (iteratedFDeriv ℝ 0 b.1)=tsupport b.1 := by
    apply congrArg closure
    ext w
    simp only [Function.mem_support]
    rw [← norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
  simp only [hts] at hbase
  exact ⟨hbase z.1 hh.1,hbase z.2 hh.2⟩

lemma uniform_actualPairSourceSymbol_derivatives
    (W : Finset (List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (M B total : ℕ) (hW : ∀ L ∈ W, L.length ≤ B) (sig : ℝ) (hsig : 0<sig)
    (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ E : ℝ, 0≤E ∧ ∀ᶠ N : ℕ in atTop, ∀ (A : ℕ → ℝ) (q a t : ℕ), 0<q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
        (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (C : ℝ) (J i : ℕ)
        (f : EuclideanSpace ℝ (Fin d) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d))),
      (∀ b ∈ policyDescriptorList A N q a t, L b ∈ W) →
      (∑ b ∈ policyDescriptorList A N q a t, (L b).length ≤ total) →
      (∀ x, ‖f x‖≤1) → (∀ j≤M, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      ∀ (z : EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d)), ∀ j ≤ M, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (actualPairSourceSymbol A N q a t L ρ m sig C J i f Q z).1 w‖ ≤
        E*(((2:ℝ)^N)^sig*
          sourceMaskScaleND ((policyDescriptorList A N q a t).sup descriptorLength) ((2:ℝ)^N) sig)^j := by
  obtain ⟨E,hE,hEb⟩ := uniform_actualSourceSymbol_derivatives W M B total hW sig hsig Cq hCq
  refine ⟨E*E*2^M,by positivity,?_⟩
  filter_upwards [hEb] with N hEb
  intro A q a t hq L ρ m C J i f Q hL htotal hf hQ z j hj w hw
  let scale := ((2:ℝ)^N)^sig*sourceMaskScaleND
    ((policyDescriptorList A N q a t).sup descriptorLength) ((2:ℝ)^N) sig
  have hscale : 0 ≤ scale := by dsimp [scale]; exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sourceMaskScaleND_pos _ _ _).le
  have hb := pairSmoothSymbolsND_derivatives
    (actualSourceSymbol A N q a t L ρ m sig C J i f Q)
    (actualSourceSymbol A N q a t L ρ m sig C J i f Q) z j hE hE hscale w
    (fun k hk => hEb A q a t hq L ρ m C J i f Q hL htotal hf hQ z.1 k (hk.trans hj) w hw)
    (fun k hk => hEb A q a t hq L ρ m C J i f Q hL htotal hf hQ z.2 k (hk.trans hj) w hw)
  apply hb.trans
  rw [mul_pow]
  change E*E*(2^j*scale^j) ≤ E*E*2^M*scale^j
  rw [mul_assoc (E*E) (2^M)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj) (pow_nonneg hscale j))
    (mul_nonneg hE hE)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
