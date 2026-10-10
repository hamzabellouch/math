import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.InheritedPolicyState
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Recursion.AssemblyDescriptorList
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveUnit
import OAI.MeasureTheory.FalconerCompletion.Recursion.TensorCapCompact

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

noncomputable def assemblyInnerSymbol (e : RecursiveEnvironmentND n) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) :
    EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ :=
  fun x w => f x*(actualAngularProduct (policyDescriptorList e.profile e.N e.q c e.N)
    id L e.ρ e.mass e.N e.sig e.C e.J 0 x).1 w

noncomputable def assemblyOuterFactor (e : RecursiveEnvironmentND n) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (P : CellPath (n+1)) : EuclideanSpace ℝ (Fin (n+1)) → ℂ :=
  fun w => Q.1 w*(actualEndpointAngular (L (.parallel 0 c)) e.ρ e.mass e.N e.sig e.C e.J 0
    (.parallel 0 c) (treeCenter P)).1 w

lemma assemblySymbol_factor (e : RecursiveEnvironmentND n) (hq : 0<e.q) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (P : CellPath (n+1)) (hPc : c≤P.length) {x : EuclideanSpace ℝ (Fin (n+1))} (hx : x∈treeCell P)
    (w : EuclideanSpace ℝ (Fin (n+1))) :
    assemblySymbol e c L f Q x w=assemblyOuterFactor e c L Q P w*assemblyInnerSymbol e c L f x w := by
  have hn : PolicyDescriptor.parallel 0 c∉policyDescriptorList e.profile e.N e.q c e.N := by
    intro h
    have hh := policyDescriptor_anchor_gt_start e.profile hq h
    simp only [descriptorAnchor] at hh
    omega
  have hc := actualEndpointAngular_reached (L (.parallel 0 c)) e.ρ e.mass e.N e.sig e.C e.J 0
    (.parallel 0 c) (show descriptorAnchor (.parallel 0 c)≤P.length by simpa only [descriptorAnchor] using hPc) hx (treeCenter_mem P)
  change Q.1 w*f x*(∏ b∈insert (.parallel 0 c) (policyDescriptorList e.profile e.N e.q c e.N),
    (actualEndpointAngular (L b) e.ρ e.mass e.N e.sig e.C e.J 0 b x).1 w)=_
  rw [Finset.prod_insert hn,hc]
  simp only [assemblyOuterFactor,assemblyInnerSymbol,actualAngularProduct,smoothFinsetProductND,id_eq]
  ring

lemma assemblyTransform_factor (e : RecursiveEnvironmentND n) (hq : 0<e.q) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (P : CellPath (n+1)) (hPc : c≤P.length) (M r : ℝ) (w : EuclideanSpace ℝ (Fin (n+1))) :
    _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell P) M (assemblySymbol e c L f Q) r w=
    assemblyOuterFactor e c L Q P w*
    _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell P) M (assemblyInnerSymbol e c L f) r w := by
  unfold _root_.OAI.CurrentFalconer.sourceAngularTransformND
  rw [show (∫ x in treeCell P, _root_.OAI.CurrentFalconer.spherePlaneWaveND r x w*assemblySymbol e c L f Q x w ∂e.ρ)=
      ∫ x in treeCell P, assemblyOuterFactor e c L Q P w*
        (_root_.OAI.CurrentFalconer.spherePlaneWaveND r x w*assemblyInnerSymbol e c L f x w) ∂e.ρ by
    apply setIntegral_congr_fun (measurableSet_treeCell P)
    intro x hx
    dsimp only
    rw [assemblySymbol_factor e hq c L f Q P hPc hx w]
    ring]
  rw [integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

lemma assemblyInnerSymbol_initial (e : RecursiveEnvironmentND n) (hq : 0<e.q) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (P Q : CellPath (n+1)) :
    assemblyInnerSymbol e c L f=(e.angularData c e.N c e.N 0 P Q).symbol L f recursiveUnit c := by
  ext x w
  simp only [RecursiveAngularND.symbol,RecursiveEnvironmentND.angularData,RecursiveAngularND.profile,
    actualResidualSourceSymbol,unreachedDescriptorList_initial _ _ _ _ _ hq,
    recursiveUnit,one_mul,assemblyInnerSymbol]

lemma assemblyInnerSymbol_measurable (e : RecursiveEnvironmentND n) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : Measurable f) :
    Measurable (Function.uncurry (assemblyInnerSymbol e c L f)) :=
  (hf.comp measurable_fst).mul (actualAngularProduct_measurable _ _ _ _ _ _ _ _ _ _)

lemma assemblyInnerSymbol_bounded (e : RecursiveEnvironmentND n) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : ∀ x,‖f x‖≤1) :
    ∃ H : ℝ,0≤H ∧ ∀ x w,‖assemblyInnerSymbol e c L f x w‖≤H := by
  obtain ⟨H,hH,h⟩ := actualAngularProduct_global_bound
    (policyDescriptorList e.profile e.N e.q c e.N) id L e.ρ e.mass e.N e.sig e.C e.J 0
  refine ⟨H,hH,?_⟩
  intro x w
  change ‖f x*(actualAngularProduct _ _ _ _ _ _ _ _ _ _ x).1 w‖≤H
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)).trans (by simpa only [one_mul] using h x w)

lemma uniform_assemblyOuterFactor_bound
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B : ℕ) (hW : ∀ L∈W,L.length≤B) {sig : ℝ} (hsig : 0<sig) :
    ∃ D : ℝ,1≤D ∧ ∀ᶠ N : ℕ in atTop,∀ e : RecursiveEnvironmentND n,e.N=N → e.sig=sig →
      ∀ c L (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (Cq : ℝ),
      L (.parallel 0 c)∈W → (∀ w,‖w‖=1 → ‖Q.1 w‖≤Cq) →
      ∀ P w,‖w‖=1 → ‖assemblyOuterFactor e c L Q P w‖≤Cq*D^B := by
  obtain ⟨D,hD,h⟩ := uniform_actualAngularProduct_derivatives (ι:=PolicyDescriptor) W 0 B B 0 hW 1 sig hsig
  refine ⟨D,hD,?_⟩
  filter_upwards [h] with N hN
  intro e he hs c L Q Cq hL hQ P w hw
  subst N
  have hh := hN {PolicyDescriptor.parallel 0 c} id L e.ρ e.mass e.C e.J 0 c
    (by simp) (by simpa using hL) (by simpa using hW _ hL)
    (by simp [descriptorLength]) (treeCenter P) 0 (by omega) w hw
  simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at hh
  have hb : ‖(actualEndpointAngular (L (.parallel 0 c)) e.ρ e.mass e.N e.sig e.C e.J 0
      (.parallel 0 c) (treeCenter P)).1 w‖≤D^B := by
    simpa only [actualAngularProduct,smoothFinsetProductND,Finset.prod_singleton,id_eq,hs] using hh
  exact (norm_mul _ _).trans_le (mul_le_mul (hQ w hw) hb (norm_nonneg _) ((norm_nonneg _).trans (hQ w hw)))
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.AssemblyEstimate
open Set MeasureTheory
open scoped ComplexConjugate
variable {V : Type*} [MeasurableSpace V]
open Attempt4Near

lemma sourceAngularHND_two_profile_power (d : ℕ) (μ : Measure V) [IsFiniteMeasure μ]
    (a v : ℝ) {U W : ℝ × V → ℂ} (hU : Measurable U) (hW : Measurable W)
    {C E : ℝ} (hbU : ∀ r,∀ᵐ w ∂μ,‖U (r,w)‖≤C)
    (hbW : ∀ r,∀ᵐ w ∂μ,‖W (r,w)‖≤E)
    {Ψ : ℝ → ℝ} (hiΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v)))
    (hΨ : ∀ r,0≤Ψ r) {R g₁ g₂ : ℝ} (hR : 0<R)
    (h₁ : sourceAngularHND d μ a v Ψ U U≤R^g₁)
    (h₂ : sourceAngularHND d μ a v Ψ W W≤R^g₂) :
    sourceAngularHND d μ a v Ψ U W≤R^((g₁+g₂)/2) := by
  let t := R^((g₂-g₁)/2)
  have ht : 0<t := Real.rpow_pos_of_pos hR _
  have hi₁ := graph_weighted_moments_integrableND μ hU hU hbU hbU hiΨ
  have hi₂ := graph_weighted_moments_integrableND μ hW hW hbW hbW hiΨ
  have hpoint (A B : ℝ) : A*B≤(t*A*A+t⁻¹*B*B)/2 := by
    have hs := sq_nonneg (t*A-B)
    have hti : t*t⁻¹=1 := mul_inv_cancel₀ ht.ne'
    have he : t*(t*A*A+t⁻¹*B*B-2*(A*B))=(t*A-B)^2 := by
      calc
        _ = t^2*A^2+(t*t⁻¹)*B^2-2*t*A*B := by ring
        _ = _ := by rw [hti]; ring
    have hh : 0≤t*A*A+t⁻¹*B*B-2*(A*B) :=
      (mul_nonneg_iff_of_pos_left ht).mp (by rw [he]; exact hs)
    linarith
  have hh : (∫ r, Ψ (r/(2:ℝ)^v)*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r) ≤
      (t*(∫ r, Ψ (r/(2:ℝ)^v)*sourceAngularMomentND μ U r*sourceAngularMomentND μ U r)+
       t⁻¹*(∫ r, Ψ (r/(2:ℝ)^v)*sourceAngularMomentND μ W r*sourceAngularMomentND μ W r))/2 := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hi₁.const_mul t) (hi₂.const_mul t⁻¹),
      ← integral_div]
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun r => mul_nonneg
        (mul_nonneg (hΨ _) (sourceAngularMomentND_nonneg _ _ _)) (sourceAngularMomentND_nonneg _ _ _))
      (((hi₁.const_mul t).add (hi₂.const_mul t⁻¹)).div_const 2)
    filter_upwards with r
    have h := mul_le_mul_of_nonneg_left
      (hpoint (sourceAngularMomentND μ U r) (sourceAngularMomentND μ W r)) (hΨ (r/(2:ℝ)^v))
    simp only [Pi.add_apply]
    convert h using 1 <;> ring
  have hen : sourceAngularHND d μ a v Ψ U W ≤
      (t*sourceAngularHND d μ a v Ψ U U+t⁻¹*sourceAngularHND d μ a v Ψ W W)/2 := by
    have h := mul_le_mul_of_nonneg_left hh
      (show 0≤(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹ by positivity)
    unfold sourceAngularHND
    nlinarith only [h]
  have hr₁ : t*R^g₁=R^((g₁+g₂)/2) := by
    rw [← Real.rpow_add hR]; congr 1; ring
  have hr₂ : t⁻¹*R^g₂=R^((g₁+g₂)/2) := by
    dsimp only [t]
    rw [← Real.rpow_neg hR.le,← Real.rpow_add hR]; congr 1; ring
  calc
    _ ≤ (t*sourceAngularHND d μ a v Ψ U U+t⁻¹*sourceAngularHND d μ a v Ψ W W)/2 := hen
    _ ≤ (t*R^g₁+t⁻¹*R^g₂)/2 := by gcongr
    _ = _ := by rw [hr₁,hr₂]; ring
end CurrentFalconer.AssemblyEstimate
end
end

end OAI
