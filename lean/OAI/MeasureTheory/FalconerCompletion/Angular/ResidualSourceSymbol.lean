import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.AngularMomentBoundedFactor
import OAI.MeasureTheory.FalconerCompletion.Graphs.SpherePlaneWaveSub2
import OAI.MeasureTheory.FalconerCompletion.Recursion.SourceSymbol

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff Topology ENNReal
variable {n : ℕ}

noncomputable def actualResidualSourceSymbol
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (x : EuclideanSpace ℝ (Fin (n+1))) : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))) :=
  ⟨fun w => f x*(Q.1 w*(actualAngularProduct (unreachedDescriptorList A N q a t r) id L ρ m N sig C J i x).1 w),
    contDiff_const.mul ((show ContDiff ℝ ∞ Q.1 from Q.2).mul
      (show ContDiff ℝ ∞ (actualAngularProduct (unreachedDescriptorList A N q a t r) id L ρ m N sig C J i x).1 from
        (actualAngularProduct (unreachedDescriptorList A N q a t r) id L ρ m N sig C J i x).2))⟩

lemma actualResidualSourceSymbol_measurable
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : Measurable f)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
    Measurable (fun z : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)) =>
      (actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q z.1).1 z.2) := by
  exact (hf.comp measurable_fst).mul (((show ContDiff ℝ ∞ Q.1 from Q.2).continuous.measurable.comp measurable_snd).mul
    (actualAngularProduct_measurable (unreachedDescriptorList A N q a t r) id L ρ m N sig C J i))

lemma actualSourceSymbol_residual_factorization
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (P : CellPath (n+1)) {x : EuclideanSpace ℝ (Fin (n+1))} (hx : x∈treeCell P)
    (w : EuclideanSpace ℝ (Fin (n+1))) :
    (actualSourceSymbol A N q a t L ρ m sig C J i f Q x).1 w =
      (actualAngularProduct (reachedDescriptorList A N q a t P.length) id L ρ m N sig C J i (treeCenter P)).1 w *
      (actualResidualSourceSymbol A N q a t P.length L ρ m sig C J i f Q x).1 w := by
  have he := actualPolicyAngular_reached_factorization A N q a t P.length L ρ m sig C J i x
  have hc := reachedSymbol_constant_on_cell A N q a t L ρ m sig C J i hx (treeCenter_mem P)
  change f x*(Q.1 w*(actualPolicyAngular A N q a t L ρ m sig C J i x).1 w)=_
  rw [he]
  change f x*(Q.1 w*((actualAngularProduct (reachedDescriptorList A N q a t P.length) id L ρ m N sig C J i x).1 w * _))=_
  rw [hc]
  change f x*(Q.1 w*(_*_))=_*(f x*(Q.1 w*_))
  ring

lemma actualTransform_reached_factorization
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (P : CellPath (n+1)) (M r : ℝ) (w : EuclideanSpace ℝ (Fin (n+1))) :
    sourceAngularTransformND ρ (treeCell P) M
      (fun x => (actualSourceSymbol A N q a t L ρ m sig C J i f Q x).1) r w =
    (actualAngularProduct (reachedDescriptorList A N q a t P.length) id L ρ m N sig C J i (treeCenter P)).1 w *
    sourceAngularTransformND ρ (treeCell P) M
      (fun x => (actualResidualSourceSymbol A N q a t P.length L ρ m sig C J i f Q x).1) r w := by
  unfold sourceAngularTransformND
  rw [show (∫ x in treeCell P, spherePlaneWaveND r x w*(actualSourceSymbol A N q a t L ρ m sig C J i f Q x).1 w ∂ρ) =
      ∫ x in treeCell P, (actualAngularProduct (reachedDescriptorList A N q a t P.length) id L ρ m N sig C J i (treeCenter P)).1 w *
        (spherePlaneWaveND r x w*(actualResidualSourceSymbol A N q a t P.length L ρ m sig C J i f Q x).1 w) ∂ρ by
    apply setIntegral_congr_fun (measurableSet_treeCell P)
    intro x hx
    dsimp only
    rw [actualSourceSymbol_residual_factorization A N q a t L ρ m sig C J i f Q P hx w]
    ring]
  rw [integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

lemma uniform_actualResidualSourceSymbol_bound
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B) {sig : ℝ} (hsig : 0<sig) :
    ∃ D : ℝ, 1≤D ∧ ∀ᶠ N : ℕ in atTop, ∀ (A : ℕ → ℝ) (q a t r : ℕ), 0<q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (C : ℝ) (J i : ℕ)
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (Cq : ℝ),
      (∀ x, ‖f x‖≤1) → (∀ w, ‖w‖=1 → ‖Q.1 w‖≤Cq) →
      (∀ b∈policyDescriptorList A N q a t, L b∈W) →
      (∑ b∈policyDescriptorList A N q a t, (L b).length≤total) →
      ∀ x w, ‖w‖=1 → ‖(actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q x).1 w‖≤Cq*D^total := by
  obtain ⟨D,hD,hDb⟩ := uniform_actualAngularProduct_derivatives
    (ι:=PolicyDescriptor) W 0 B total 3 hW 8 sig hsig
  refine ⟨D,hD,?_⟩
  filter_upwards [hDb,eventually_ge_atTop 1] with N hDb hN
  intro A q a t r hq L ρ m C J i f Q Cq hf hQ hL htotal x w hw
  have hsub : unreachedDescriptorList A N q a t r ⊆ policyDescriptorList A N q a t := Finset.filter_subset _ _
  have hcard : ((unreachedDescriptorList A N q a t r).card:ℝ)≤8*(N:ℝ)^3 := by
    calc
      _ ≤ ((policyDescriptorList A N q a t).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ _ := actualPolicy_card_bound A hN hq
  have hsum : ∑ b∈unreachedDescriptorList A N q a t r, (L b).length≤total :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)).trans htotal
  have hh := hDb (unreachedDescriptorList A N q a t r) id L ρ m C J i
    ((policyDescriptorList A N q a t).sup descriptorLength) hcard
    (fun b hb => hL b (hsub hb)) hsum (fun b hb => Finset.le_sup (f:=descriptorLength) (hsub hb)) x 0 le_rfl w hw
  simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at hh
  have hQ0 : 0≤Cq := (norm_nonneg _).trans (hQ w hw)
  change ‖f x*(Q.1 w*_)‖≤_
  simp only [norm_mul]
  calc
    _ ≤ 1*(Cq*D^total) := mul_le_mul (hf x)
      (mul_le_mul (hQ w hw) hh (norm_nonneg _) hQ0) (by positivity) (by norm_num)
    _ = _ := one_mul _

theorem actual_energy_reached_removalND
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B) {sig : ℝ} (hsig : 0<sig) :
    ∃ D : ℝ, 1≤D ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (A : ℕ → ℝ) (q a t : ℕ), 0<q →
      ∀ (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (J i : ℕ)
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q S : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (Cq : ℝ),
      Measurable f → Measurable g → (∀ x, ‖f x‖≤1) → (∀ x, ‖g x‖≤1) →
      (∀ b∈policyDescriptorList A N q a t, L₁ b∈W) →
      (∀ b∈policyDescriptorList A N q a t, L₂ b∈W) →
      (∑ b∈policyDescriptorList A N q a t, (L₁ b).length≤total) →
      (∑ b∈policyDescriptorList A N q a t, (L₂ b).length≤total) →
      (∀ w, ‖w‖=1 → ‖Q.1 w‖≤Cq) → (∀ w, ‖w‖=1 → ‖S.1 w‖≤Cq) →
      ∀ (P R : CellPath (n+1)) (M K p v : ℝ) (Ψ : ℝ → ℝ),
      Integrable (fun r => Ψ (r/(2:ℝ)^v)) → (∀ r, 0≤Ψ r) →
      Attempt4Near.sourceAngularHND (n+1) (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) p v Ψ
        (fun z => sourceAngularTransformND ρ (treeCell P) M
          (fun x w => (actualSourceSymbol A N q a t L₁ ρ m sig C J i f Q x).1 w) z.1 z.2)
        (fun z => sourceAngularTransformND κ (treeCell R) K
          (fun x w => (actualSourceSymbol A N q a t L₂ κ m sig C J i g S x).1 w) z.1 z.2) ≤
      D^(4*total)*
        Attempt4Near.sourceAngularHND (n+1) (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) p v Ψ
          (fun z => sourceAngularTransformND ρ (treeCell P) M
            (fun x w => (actualResidualSourceSymbol A N q a t P.length L₁ ρ m sig C J i f Q x).1 w) z.1 z.2)
          (fun z => sourceAngularTransformND κ (treeCell R) K
            (fun x w => (actualResidualSourceSymbol A N q a t R.length L₂ κ m sig C J i g S x).1 w) z.1 z.2) := by
  obtain ⟨D,hD,hDb⟩ := uniform_reachedSymbol_bound W B total hW sig hsig
  obtain ⟨E,hE,hEb⟩ := uniform_actualResidualSourceSymbol_bound W B total hW hsig
  refine ⟨D,hD,?_⟩
  filter_upwards [hDb,hEb] with N hDb hEb
  intro ρ κ hρ hκ A q a t hq L₁ L₂ m C J i f g Q S Cq hf hg hfb hgb hL₁ hL₂ htotal₁ htotal₂ hQ hS P R M K p v Ψ hΨ hΨpos
  let b := fun x w => (actualResidualSourceSymbol A N q a t P.length L₁ ρ m sig C J i f Q x).1 w
  let c := fun x w => (actualResidualSourceSymbol A N q a t R.length L₂ κ m sig C J i g S x).1 w
  have hbm : Measurable (Function.uncurry b) :=
    actualResidualSourceSymbol_measurable A N q a t P.length L₁ ρ m sig C J i f hf Q
  have hcm : Measurable (Function.uncurry c) :=
    actualResidualSourceSymbol_measurable A N q a t R.length L₂ κ m sig C J i g hg S
  have hb : ∀ x w, ‖w‖=1 → ‖b x w‖≤Cq*E^total :=
    hEb A q a t P.length hq L₁ ρ m C J i f Q Cq hfb hQ hL₁ htotal₁
  have hc : ∀ x w, ‖w‖=1 → ‖c x w‖≤Cq*E^total :=
    hEb A q a t R.length hq L₂ κ m C J i g S Cq hgb hS hL₂ htotal₂
  have hbt (r : ℝ) : ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))),
      ‖sourceAngularTransformND ρ (treeCell P) M b r w‖≤|M⁻¹| *(ρ (treeCell P)).toReal*(Cq*E^total) := by
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact sourceAngularTransformND_norm_le ρ (treeCell P) M b r w (fun x => hb x w hw)
  have hct (r : ℝ) : ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))),
      ‖sourceAngularTransformND κ (treeCell R) K c r w‖≤|K⁻¹| *(κ (treeCell R)).toReal*(Cq*E^total) := by
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact sourceAngularTransformND_norm_le κ (treeCell R) K c r w (fun x => hc x w hw)
  have hψ : ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))),
      ‖(actualAngularProduct (reachedDescriptorList A N q a t P.length) id L₁ ρ m N sig C J i (treeCenter P)).1 w‖≤D^total := by
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact hDb A q a t P.length hq L₁ ρ m C J i hL₁ htotal₁ (treeCenter P) w hw
  have hφ : ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))),
      ‖(actualAngularProduct (reachedDescriptorList A N q a t R.length) id L₂ κ m N sig C J i (treeCenter R)).1 w‖≤D^total := by
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact hDb A q a t R.length hq L₂ κ m C J i hL₂ htotal₂ (treeCenter R) w hw
  have hh := Attempt4Near.sourceAngularHND_bounded_factors (n+1)
    (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) p v
    (sourceAngularTransformND_measurable ρ (treeCell P) M hbm)
    (sourceAngularTransformND_measurable κ (treeCell R) K hcm) hbt hct
    (fun w => (actualAngularProduct (reachedDescriptorList A N q a t P.length) id L₁ ρ m N sig C J i (treeCenter P)).1 w)
    (fun w => (actualAngularProduct (reachedDescriptorList A N q a t R.length) id L₂ κ m N sig C J i (treeCenter R)).1 w)
    hψ hφ hΨ hΨpos
  have hpow : (D^total)^2*(D^total)^2=D^(4*total) := by
    rw [← pow_add,← pow_mul]
    congr 1
    omega
  rw [hpow] at hh
  simp_rw [actualTransform_reached_factorization A N q a t L₁ ρ m sig C J i f Q P,
    actualTransform_reached_factorization A N q a t L₂ κ m sig C J i g S R]
  exact hh

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
