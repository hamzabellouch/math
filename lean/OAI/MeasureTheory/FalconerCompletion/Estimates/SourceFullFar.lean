import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.ComplexRadialNormalization
import OAI.MeasureTheory.FalconerCompletion.Estimates.EuclideanFarKernelConstMul
import OAI.MeasureTheory.FalconerCompletion.Graphs.FarPairDirectionMeasurable

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open _root_.OAI.GraphLiteralSupport.Attempt4FullFar Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal
variable {n : ℕ}

theorem actual_source_full_farND
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0<sig) (hsig₁ : sig≤1)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B)
    {Jmask : ℕ} (hJmask : 0<Jmask) (Cq : ℝ) (hCq : 0≤Cq)
    (err T D : ℝ) (ell : ℕ) (hK : 32*(n+2:ℝ)≤(2:ℝ)^ell) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (A : ℕ → ℝ) (q a₀ t₀ a h : ℕ), 0<q → t₀≤N →
      ∀ (words₁ words₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
        (X Y : Fin (n+1) → ℤ) (v ma : ℝ) (mb : ℕ → ℝ),
      Measurable f → Measurable g → (∀ x, ‖f x‖≤1) → (∀ x, ‖g x‖≤1) →
      (∀ b∈policyDescriptorList A N q a₀ t₀, words₁ b∈W) →
      (∀ b∈policyDescriptorList A N q a₀ t₀, words₂ b∈W) →
      (∑ b∈policyDescriptorList A N q a₀ t₀, (words₁ b).length≤total) →
      (∑ b∈policyDescriptorList A N q a₀ t₀, (words₂ b).length≤total) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j P.1 w‖≤Cq) →
      ∀ S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
        (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      MeasurableSet S → S⊆farOriginalSetND a h X Y → a≤h → v-a≤N →
      ((h+ell+2:ℕ):ℝ)≤v-2*(max ((policyDescriptorList A N q a₀ t₀).sup descriptorLength)
        (Nat.ceil (10*sig*N)):ℕ)+D →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ z∈occupiedDescendantsND ρ a k X,
        ((2:ℝ)^N)^(-mb k-err)≤(ρ (Attempt4FullFar.ambientGridCell k z)).toReal) →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ z∈occupiedDescendantsND κ a k Y,
        ((2:ℝ)^N)^(-mb k-err)≤(κ (Attempt4FullFar.ambientGridCell k z)).toReal) →
      (ρ (Attempt4FullFar.ambientGridCell a X)).toReal≤((2:ℝ)^N)^(-ma+err) →
      (κ (Attempt4FullFar.ambientGridCell a Y)).toReal≤((2:ℝ)^N)^(-ma+err) →
      let b := fun z => (actualPairSourceSymbol A N q a₀ t₀ words₁ ρ m sig C Jmask i f Q z).1
      let c := fun z => (actualPairSourceSymbol A N q a₀ t₀ words₂ κ m sig C Jmask i g P z).1
      let U := actualPairAmbientGood A N q a₀ t₀ ρ m sig C Jmask (i+1)
      let V := actualPairAmbientGood A N q a₀ t₀ κ m sig C Jmask (i+1)
      ((2:ℝ)^((n+1:ℝ)*(v-a))/(((2:ℝ)^N)^(-ma))^4)*
        ‖∫ z in S, euclideanFarKernelND Ψ v b c z ∂(ρ.prod ρ).prod (κ.prod κ)‖ ≤
      H*(∑ k∈Finset.Icc (a+1) (h+ell+2),
        ((2:ℝ)^N)^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X)
            (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y) v (((2:ℝ)^N)^(-mb k)) U V).toReal)+
        ((2:ℝ)^N)^(-T) := by
  obtain ⟨J,hfar⟩ := euclidean_source_full_far_budgetsND (n:=n) hΨ hs hsig hsig₁ err T D ell hK
  obtain ⟨E,hE,hpackage⟩ := actual_fullFar_symbol_package W (2*(J+1)+n+3) B total hW hsig hJmask Cq hCq
  obtain ⟨H,hH,hbound⟩ := hfar (fun _ => E)
  have hf : Tendsto (fun N : ℕ => (2:ℝ)^N) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine ⟨J,H,hH,?_⟩
  filter_upwards [hpackage,hf.eventually hbound,eventually_gt_atTop 0] with N hp hb hN
  intro ρ κ hρ hκ A q a₀ t₀ a h hq ht words₁ words₂ m C i f g Q P X Y v ma mb
    hfm hgm hfn hgn hw₁ hw₂ ht₁ ht₂ hQ hP S hS hSG hah hav hdepth hl₁ hl₂ hu₁ hu₂
  obtain ⟨hbm,hUm,hbsy⟩ := hp ρ A q a₀ t₀ hq ht words₁ m C i f Q hfm hfn hw₁ ht₁ hQ
  obtain ⟨hcm,hVm,hcsy⟩ := hp κ A q a₀ t₀ hq ht words₂ m C i g P hgm hgn hw₂ ht₂ hP
  exact hb N hN rfl ρ κ a ((policyDescriptorList A N q a₀ t₀).sup descriptorLength) h X Y v ma mb
    _ _ _ _ S hS hSG hah hav hdepth hl₁ hl₂ hu₁ hu₂ hbm hcm hUm hVm
    (ae_of_all _ hbsy) (ae_of_all _ hcsy)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal
variable {n : ℕ}

theorem actual_source_full_far_energyND
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0<sig) (hsig₁ : sig≤1)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B)
    {Jmask : ℕ} (hJmask : 0<Jmask) (Cq : ℝ) (hCq : 0≤Cq)
    (err T D : ℝ) (ell : ℕ) (hK : 32*(n+2:ℝ)≤(2:ℝ)^ell) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (A : ℕ → ℝ) (q a₀ t₀ a h : ℕ), 0<q → t₀≤N →
      ∀ (words₁ words₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
        (X Y : Fin (n+1) → ℤ) (v ma : ℝ) (mb : ℕ → ℝ),
      Measurable f → Measurable g → (∀ x, ‖f x‖≤1) → (∀ x, ‖g x‖≤1) →
      (∀ b∈policyDescriptorList A N q a₀ t₀, words₁ b∈W) →
      (∀ b∈policyDescriptorList A N q a₀ t₀, words₂ b∈W) →
      (∑ b∈policyDescriptorList A N q a₀ t₀, (words₁ b).length≤total) →
      (∑ b∈policyDescriptorList A N q a₀ t₀, (words₂ b).length≤total) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j P.1 w‖≤Cq) →
      a≤h → v-a≤N →
      ((h+ell+2:ℕ):ℝ)≤v-2*(max ((policyDescriptorList A N q a₀ t₀).sup descriptorLength)
        (Nat.ceil (10*sig*N)):ℕ)+D →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ z∈occupiedDescendantsND ρ a k X,
        ((2:ℝ)^N)^(-mb k-err)≤(ρ (Attempt4FullFar.ambientGridCell k z)).toReal) →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ z∈occupiedDescendantsND κ a k Y,
        ((2:ℝ)^N)^(-mb k-err)≤(κ (Attempt4FullFar.ambientGridCell k z)).toReal) →
      (ρ (Attempt4FullFar.ambientGridCell a X)).toReal≤((2:ℝ)^N)^(-ma+err) →
      (κ (Attempt4FullFar.ambientGridCell a Y)).toReal≤((2:ℝ)^N)^(-ma+err) →
      let b := fun x => (actualSourceSymbol A N q a₀ t₀ words₁ ρ m sig C Jmask i f Q x).1
      let c := fun x => (actualSourceSymbol A N q a₀ t₀ words₂ κ m sig C Jmask i g P x).1
      let U := actualPairAmbientGood A N q a₀ t₀ ρ m sig C Jmask (i+1)
      let V := actualPairAmbientGood A N q a₀ t₀ κ m sig C Jmask (i+1)
      Attempt4Near.farAngularEnergyND (n+1)
        (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) a h v
        (((2:ℝ)^N)^(-(mb h-ma))) (((2:ℝ)^N)^(-(mb h-ma))) Ψ
        (occupiedDescendantsND ρ a h X) (occupiedDescendantsND κ a h Y)
        (originalCellTransformND ρ h (((2:ℝ)^N)^(-mb h)) b)
        (originalCellTransformND κ h (((2:ℝ)^N)^(-mb h)) c) ≤
      H*(∑ k∈Finset.Icc (a+1) (h+ell+2),
        ((2:ℝ)^N)^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X)
            (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y) v (((2:ℝ)^N)^(-mb k)) U V).toReal)+
        ((2:ℝ)^N)^(-T) := by
  obtain ⟨J,H,hH,hfar⟩ := actual_source_full_farND hΨ hs hsig hsig₁ W B total hW hJmask Cq hCq err T D ell hK
  obtain ⟨E,hE,htrans⟩ := actual_transform_uniform_package W B total hW hsig Cq hCq
  refine ⟨J,H,hH,?_⟩
  filter_upwards [hfar,htrans] with N hf ht
  intro ρ κ hρ hκ A q a₀ t₀ a h hq ht₀ words₁ words₂ m C i f g Q P X Y v ma mb
    hfm hgm hfn hgn hw₁ hw₂ htotal₁ htotal₂ hQ hP hah hav hdepth hl₁ hl₂ hu₁ hu₂
  have hQ₀ : ∀ w, ‖w‖=1 → ‖Q.1 w‖≤Cq := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero] using hQ 0 (Nat.zero_le _) w hw
  have hP₀ : ∀ w, ‖w‖=1 → ‖P.1 w‖≤Cq := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero] using hP 0 (Nat.zero_le _) w hw
  obtain ⟨hbm,hbb,_⟩ := ht ρ A q a₀ t₀ hq words₁ m C Jmask i f Q hfm hfn hw₁ htotal₁ hQ₀
  obtain ⟨hcm,hcc,_⟩ := ht κ A q a₀ t₀ hq words₂ m C Jmask i g P hgm hgn hw₂ htotal₂ hP₀
  have hsub : originalFarRegionND h (occupiedDescendantsND ρ a h X) (occupiedDescendantsND κ a h Y)⊆
      farOriginalSetND a h X Y := by
    apply originalFarRegionND_subset
    · intro p hp
      exact ambientDescendantsND_subset hah (Finset.mem_filter.mp hp).1
    · intro p hp
      exact ambientDescendantsND_subset hah (Finset.mem_filter.mp hp).1
  have hh := hf ρ κ A q a₀ t₀ a h hq ht₀ words₁ words₂ m C i f g Q P X Y v ma mb
    hfm hgm hfn hgn hw₁ hw₂ htotal₁ htotal₂ hQ hP
    (originalFarRegionND h (occupiedDescendantsND ρ a h X) (occupiedDescendantsND κ a h Y))
    (originalFarRegionND_measurable _ _ _) hsub hah hav hdepth hl₁ hl₂ hu₁ hu₂
  have hi : Integrable Ψ := hΨ.continuous.continuousOn.integrableOn_Icc.integrable_of_forall_notMem_eq_zero
    (fun u hu => radial_cutoff_mem_of_ne_zero hs hu)
  dsimp only
  rw [physical_farAngularEnergyND_original hΨ.continuous.measurable hi a v _ _ ρ κ h _ _ _ _ _ _
    hbm hcm hE hE hbb hcc,
    physical_far_profile_coefficientND ((2:ℝ)^N) (by positivity) ma (mb h)]
  dsimp only at hh
  rw [actualPairSourceSymbol_eq_scalarPair A N q a₀ t₀ words₁ ρ m sig C Jmask i f Q,
    actualPairSourceSymbol_eq_scalarPair A N q a₀ t₀ words₂ κ m sig C Jmask i g P] at hh
  simpa only [Nat.cast_add,Nat.cast_one] using hh

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal
variable {n : ℕ}

theorem actual_source_near_far_energyND
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4)
    (hΨpos : ∀ t, 0≤Ψ t)
    {sig : ℝ} (hsig : 0<sig) (hsig₁ : sig≤1)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B)
    {Jmask : ℕ} (hJmask : 0<Jmask) (Cq : ℝ) (hCq : 0≤Cq)
    (err T D : ℝ) (ell : ℕ) (hK : 32*(n+2:ℝ)≤(2:ℝ)^ell) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (A : ℕ → ℝ) (q a₀ t₀ a h : ℕ), 0<q → t₀≤N →
      ∀ (words₁ words₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
        (X Y : Fin (n+1) → ℤ) (v ma : ℝ) (mb : ℕ → ℝ),
      Measurable f → Measurable g → (∀ x, ‖f x‖≤1) → (∀ x, ‖g x‖≤1) →
      (∀ b∈policyDescriptorList A N q a₀ t₀, words₁ b∈W) →
      (∀ b∈policyDescriptorList A N q a₀ t₀, words₂ b∈W) →
      (∑ b∈policyDescriptorList A N q a₀ t₀, (words₁ b).length≤total) →
      (∑ b∈policyDescriptorList A N q a₀ t₀, (words₂ b).length≤total) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j P.1 w‖≤Cq) →
      ∀ (hX : ρ (Attempt4FullFar.ambientGridCell a X)≠0)
        (hY : κ (Attempt4FullFar.ambientGridCell a Y)≠0) (hah : a<h), v-a≤N →
      ((h+ell+2:ℕ):ℝ)≤v-2*(max ((policyDescriptorList A N q a₀ t₀).sup descriptorLength)
        (Nat.ceil (10*sig*N)):ℕ)+D →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ z∈occupiedDescendantsND ρ a k X,
        ((2:ℝ)^N)^(-mb k-err)≤(ρ (Attempt4FullFar.ambientGridCell k z)).toReal) →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ z∈occupiedDescendantsND κ a k Y,
        ((2:ℝ)^N)^(-mb k-err)≤(κ (Attempt4FullFar.ambientGridCell k z)).toReal) →
      (ρ (Attempt4FullFar.ambientGridCell a X)).toReal≤((2:ℝ)^N)^(-ma+err) →
      (κ (Attempt4FullFar.ambientGridCell a Y)).toReal≤((2:ℝ)^N)^(-ma+err) →
      let b := fun x => (actualSourceSymbol A N q a₀ t₀ words₁ ρ m sig C Jmask i f Q x).1
      let c := fun x => (actualSourceSymbol A N q a₀ t₀ words₂ κ m sig C Jmask i g P x).1
      let U := actualPairAmbientGood A N q a₀ t₀ ρ m sig C Jmask (i+1)
      let V := actualPairAmbientGood A N q a₀ t₀ κ m sig C Jmask (i+1)
      let Aocc := occupiedDescendantsND ρ a h X
      let Docc := occupiedDescendantsND κ a h Y
      let hAD := (original_occupied_nonemptyND ρ hah.le X hX).product
        (original_occupied_nonemptyND κ hah.le Y hY)
      let μ := canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))
      Attempt4Near.sourceAngularHND (n+1) μ a v Ψ
        (originalCellTransformND ρ a (((2:ℝ)^N)^(-ma)) b X)
        (originalCellTransformND κ a (((2:ℝ)^N)^(-ma)) c Y) ≤
      (20*(n+2:ℝ)+5)^(2*(n+1))*
        ((2:ℝ)^N)^(-2*((mb h-(n+1:ℝ)*(h:ℝ)/(2*N))-(ma-(n+1:ℝ)*(a:ℝ)/(2*N)))+4*err)*
        Attempt4Near.graphChildMaxND (n+1) μ h v Ψ Aocc Docc hAD
          (originalCellTransformND ρ h (((2:ℝ)^N)^(-mb h)) b)
          (originalCellTransformND κ h (((2:ℝ)^N)^(-mb h)) c) +
      H*(∑ k∈Finset.Icc (a+1) (h+ell+2),
        ((2:ℝ)^N)^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X)
            (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y) v (((2:ℝ)^N)^(-mb k)) U V).toReal)+
        ((2:ℝ)^N)^(-T) := by
  obtain ⟨J,H,hH,hfar⟩ := actual_source_full_far_energyND hΨ hs hsig hsig₁ W B total hW hJmask Cq hCq err T D ell hK
  obtain ⟨E,hE,htrans⟩ := actual_transform_uniform_package W B total hW hsig Cq hCq
  refine ⟨J,H,hH,?_⟩
  filter_upwards [hfar,htrans,eventually_gt_atTop 0] with N hf ht hN
  intro ρ κ hρ hκ A q a₀ t₀ a h hq ht₀ words₁ words₂ m C i f g Q P X Y v ma mb
    hfm hgm hfn hgn hw₁ hw₂ htotal₁ htotal₂ hQ hP hX hY hah hav hdepth hl₁ hl₂ hu₁ hu₂
  have hQ₀ : ∀ w, ‖w‖=1 → ‖Q.1 w‖≤Cq := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero] using hQ 0 (Nat.zero_le _) w hw
  have hP₀ : ∀ w, ‖w‖=1 → ‖P.1 w‖≤Cq := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero] using hP 0 (Nat.zero_le _) w hw
  obtain ⟨hbm,hbb,_⟩ := ht ρ A q a₀ t₀ hq words₁ m C Jmask i f Q hfm hfn hw₁ htotal₁ hQ₀
  obtain ⟨hcm,hcc,_⟩ := ht κ A q a₀ t₀ hq words₂ m C Jmask i g P hgm hgn hw₂ htotal₂ hP₀
  have hh := hf ρ κ A q a₀ t₀ a h hq ht₀ words₁ words₂ m C i f g Q P X Y v ma mb
    hfm hgm hfn hgn hw₁ hw₂ htotal₁ htotal₂ hQ hP hah.le hav hdepth hl₁ hl₂ hu₁ hu₂
  have hirange : h∈Finset.Icc (a+1) (h+ell+2) := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hi : Integrable Ψ := hΨ.continuous.continuousOn.integrableOn_Icc.integrable_of_forall_notMem_eq_zero
    (fun u hu => radial_cutoff_mem_of_ne_zero hs hu)
  have hn := physical_near_far_profile_boundND hN ρ κ hah.le X Y hX hY v ma (mb h) err
    (hl₁ h hirange) (hl₂ h hirange) hu₁ hu₂
    (fun x => (actualSourceSymbol A N q a₀ t₀ words₁ ρ m sig C Jmask i f Q x).1)
    (fun x => (actualSourceSymbol A N q a₀ t₀ words₂ κ m sig C Jmask i g P x).1)
    hbm hcm hbb hcc hΨ.continuous.measurable (hi.comp_div (by positivity : (2:ℝ)^v≠0)) hΨpos
  dsimp only at hn hh ⊢
  have hsum := hn.trans (add_le_add le_rfl hh)
  simpa only [Nat.cast_add, Nat.cast_one, show (n:ℝ)+1+1=(n:ℝ)+2 by ring, add_assoc] using hsum

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
