import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularOperator2
import OAI.MeasureTheory.FalconerCompletion.Angular.SymbolMulDerivativeBound
import OAI.MeasureTheory.FalconerCompletion.Graphs.AllMaskProductAdmissible
import OAI.MeasureTheory.FalconerCompletion.Recursion.MaskScale2

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Filter
open scoped ENNReal RealInnerProductSpace ContDiff Topology Classical ComplexConjugate
variable {d : ℕ}

noncomputable def actualListSourceSymbol
    (S : Finset PolicyDescriptor)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    SmoothFunctionND (EuclideanSpace ℝ (Fin d)) :=
  ⟨fun w => f x*(Q.1 w*(actualAngularProduct S id L ρ m N sig C J i x).1 w),
    contDiff_const.mul ((show ContDiff ℝ ∞ Q.1 from Q.2).mul
      (actualAngularProduct S id L ρ m N sig C J i x).2)⟩

lemma actualListSourceSymbol_measurable
    (S : Finset PolicyDescriptor)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ)
    (sig C : ℝ) (J i : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : Measurable f)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d))) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (actualListSourceSymbol S L ρ m N sig C J i f Q z.1).1 z.2) :=
  (hf.comp measurable_fst).mul (((show ContDiff ℝ ∞ Q.1 from Q.2).continuous.measurable.comp measurable_snd).mul
    (actualAngularProduct_measurable S id L ρ m N sig C J i))

lemma validDescriptorList_card {N : ℕ} (hN : 1 ≤ N) (S : Finset PolicyDescriptor)
    (hS : ∀ b ∈ S, ValidDescriptor N b) : (S.card:ℝ) ≤ 8*(N:ℝ)^2 := by
  let K := (Finset.range (N+1)).product (Finset.range (N+1))
  let U := K.image (fun z => PolicyDescriptor.parallel z.1 z.2) ∪
    K.image (fun z => PolicyDescriptor.projection z.1 z.2)
  have hsub : S ⊆ U := by
    intro b hb
    have hv := hS b hb
    cases b with
    | parallel g p =>
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(g,p),Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by dsimp [ValidDescriptor] at hv; omega),
          Finset.mem_range.mpr (by exact Nat.lt_succ_of_le hv.2)⟩,rfl⟩
    | projection p t =>
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(p,t),Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by dsimp [ValidDescriptor] at hv; omega),
          Finset.mem_range.mpr (by exact Nat.lt_succ_of_le hv.2)⟩,rfl⟩
  have hc : S.card ≤ 2*(N+1)^2 := by
    calc
      _ ≤ U.card := Finset.card_le_card hsub
      _ ≤ (K.image (fun z => PolicyDescriptor.parallel z.1 z.2)).card+
        (K.image (fun z => PolicyDescriptor.projection z.1 z.2)).card := Finset.card_union_le _ _
      _ ≤ K.card+K.card := add_le_add Finset.card_image_le Finset.card_image_le
      _ = _ := by simp [K,Finset.product_eq_sprod,Finset.card_product]; ring
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ 2*((N:ℝ)+1)^2 := by exact_mod_cast hc
    _ ≤ 8*(N:ℝ)^2 := by nlinarith

lemma uniform_actualListSourceSymbol_jets
    (W : Finset (List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (M B total : ℕ) (hW : ∀ L ∈ W, L.length ≤ B) (sig : ℝ) (hsig : 0<sig)
    (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ E : ℝ, 0≤E ∧ ∀ᶠ N : ℕ in atTop, ∀ (S : Finset PolicyDescriptor)
      (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
      (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (C : ℝ) (J i l : ℕ)
      (f : EuclideanSpace ℝ (Fin d) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d))),
      (∀ e ∈ S, ValidDescriptor N e) → (∀ e ∈ S, descriptorLength e ≤ l) →
      (∀ e ∈ S, L e ∈ W) → (∑ e ∈ S, (L e).length ≤ total) →
      Measurable f → (∀ x, ‖f x‖≤1) →
      (∀ j≤M, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      _root_.OAI.CurrentFalconer.GraphSymbolJet
        (fun x w => (actualListSourceSymbol S L ρ m N sig C J i f Q x).1 w) M
        (((2:ℝ)^N)^sig*sourceMaskScaleND l ((2:ℝ)^N) sig) E := by
  obtain ⟨D,hD,hDb⟩ := uniform_actualAngularProduct_derivatives (ι:=PolicyDescriptor)
    W M B total 2 hW 8 sig hsig
  refine ⟨Cq*D^total*2^M,by positivity,?_⟩
  filter_upwards [hDb,Filter.eventually_ge_atTop 1] with N hDb hN
  intro S L ρ m C J i l f Q hValid hl hL htotal hfm hf hQ
  refine ⟨actualListSourceSymbol_measurable S L ρ m N sig C J i f hfm Q,
    fun x => (actualListSourceSymbol S L ρ m N sig C J i f Q x).2,by positivity,?_⟩
  intro x j hj w hw
  let Z := actualAngularProduct S id L ρ m N sig C J i x
  let scale := ((2:ℝ)^N)^sig*sourceMaskScaleND l ((2:ℝ)^N) sig
  have hscale : 1 ≤ scale := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hsig.le)
    (sourceMaskScaleND_one_le _ _ _)
  have hb := symbol_mul_derivative_boundND Q Z j hCq (pow_nonneg (zero_le_one.trans hD) total)
    (zero_le_one.trans hscale) w (fun k hk =>
      (hQ k (hk.trans hj) w hw).trans (le_mul_of_one_le_right hCq (one_le_pow₀ hscale)))
    (fun k hk => hDb S id L ρ m C J i l (validDescriptorList_card hN S hValid)
      hL htotal hl x k (hk.trans hj) w hw)
  have hh := symbol_const_mul_derivative_boundND (smoothMulND Q Z) (f x) (hf x) j w
  apply hh.trans (hb.trans ?_)
  rw [mul_pow]
  change Cq*D^total*(2^j*scale^j) ≤ Cq*D^total*2^M*scale^j
  rw [mul_assoc (Cq*D^total) (2^M)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj)
      (pow_nonneg (zero_le_one.trans hscale) j)) (mul_nonneg hCq (pow_nonneg (zero_le_one.trans hD) total))

lemma uniform_actualListSourceSymbol_test {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ρ →
    ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ) (S : Finset PolicyDescriptor),
    (∀ e ∈ S, ValidDescriptor N e) →
    ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
      (f : EuclideanSpace ℝ (Fin d) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d)))
      (x w : EuclideanSpace ℝ (Fin d)), ‖w‖=1 →
    (actualListSourceSymbol S L ρ m N sig C J i f Q x).1 w ≠ 0 →
      ∀ e ∈ S, (x,w) ∈ endpointGood ρ m N sig C J (i+1) e := by
  obtain ⟨N₀,h₀⟩ := uniform_actualAngularProduct_support (d:=d) (ι:=PolicyDescriptor) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hρ m C i S hValid L f Q x w hw hn e he
  have hp : (actualAngularProduct S id L ρ m N sig C J i x).1 w ≠ 0 := by
    intro hz
    apply hn
    simp [actualListSourceSymbol,hz]
  apply h₀ N hN ρ hρ m C i S id hValid L 0 x w hw _ e he
  apply subset_closure
  rw [Function.mem_support,←norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
  exact hp

end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
