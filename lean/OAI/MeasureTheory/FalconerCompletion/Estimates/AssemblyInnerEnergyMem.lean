import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.Falconer.Recursion.Potential
import OAI.MeasureTheory.FalconerCompletion.Angular.AssemblyInnerSymbol
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveProfileWithOverhead

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

lemma assemblyInner_energy_mem (e : RecursiveEnvironmentND n) (hq : 0<e.q)
    (K : ℝ) (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (total c : ℕ) (X : CellPath (n+1)) (hX : X∈dyadicPaths c) (ho : 0<e.ρ (treeCell X))
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : Measurable f) (hfn : ∀ x,‖f x‖≤1)
    (hL : ∀ b∈policyDescriptorList e.profile e.N e.q c e.N,L b∈W)
    (ht : (∑ b∈policyDescriptorList e.profile e.N e.q c e.N,(L b).length)≤total) (Ψ : ℝ → ℝ) :
    e.energies K W total Ψ (.H c e.N c e.N 0)
    (_root_.OAI.Attempt4Near.sourceAngularHND (n+1)
      (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) c e.N Ψ
      (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell X)
        (((2:ℝ)^e.N)^(-e.mass c)) (assemblyInnerSymbol e c L f) z.1 z.2)
      (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell X)
        (((2:ℝ)^e.N)^(-e.mass c)) (assemblyInnerSymbol e c L f) z.1 z.2)) := by
  refine ⟨X,X,hX,hX,ho,ho,L,L,f,f,hf,hf,hfn,hfn,hL,hL,ht,ht,?_⟩
  rw [assemblyInnerSymbol_initial e hq c L f X X]
  rfl

lemma assembly_child_two_profile (e₁ e₂ : RecursiveEnvironmentND n)
    [IsFiniteMeasure e₁.ρ] [IsFiniteMeasure e₂.ρ] (hN : e₂.N=e₁.N)
    (hq₁ : 0<e₁.q) (hq₂ : 0<e₂.q) (c : ℕ)
    (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : Measurable f) (hg : Measurable g)
    (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (X Y : CellPath (n+1)) (hX : c≤X.length) (hY : c≤Y.length)
    (Ψ : ℝ → ℝ) (hiΨ : Integrable (fun r => Ψ (r/(2:ℝ)^(e₁.N:ℝ)))) (hΨ : ∀ r,0≤Ψ r)
    (D₁ D₂ F₁ F₂ g₁ g₂ : ℝ)
    (hb₁ : ∀ x w,‖w‖=1 → ‖assemblyInnerSymbol e₁ c L₁ f x w‖≤D₁)
    (hb₂ : ∀ x w,‖w‖=1 → ‖assemblyInnerSymbol e₂ c L₂ g x w‖≤D₂)
    (hF₁ : ∀ w,‖w‖=1 → ‖assemblyOuterFactor e₁ c L₁ Q X w‖≤F₁)
    (hF₂ : ∀ w,‖w‖=1 → ‖assemblyOuterFactor e₂ c L₂ P Y w‖≤F₂)
    (hh₁ : _root_.OAI.Attempt4Near.sourceAngularHND (n+1)
      (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) c e₁.N Ψ
      (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e₁.ρ (treeCell X)
        (((2:ℝ)^e₁.N)^(-e₁.mass c)) (assemblyInnerSymbol e₁ c L₁ f) z.1 z.2)
      (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e₁.ρ (treeCell X)
        (((2:ℝ)^e₁.N)^(-e₁.mass c)) (assemblyInnerSymbol e₁ c L₁ f) z.1 z.2)≤((2:ℝ)^e₁.N)^g₁)
    (hh₂ : _root_.OAI.Attempt4Near.sourceAngularHND (n+1)
      (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) c e₂.N Ψ
      (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e₂.ρ (treeCell Y)
        (((2:ℝ)^e₂.N)^(-e₂.mass c)) (assemblyInnerSymbol e₂ c L₂ g) z.1 z.2)
      (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e₂.ρ (treeCell Y)
        (((2:ℝ)^e₂.N)^(-e₂.mass c)) (assemblyInnerSymbol e₂ c L₂ g) z.1 z.2)≤((2:ℝ)^e₁.N)^g₂) :
    _root_.OAI.Attempt4Near.sourceAngularHND (n+1)
      (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) c e₁.N Ψ
      (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e₁.ρ (treeCell X)
        (((2:ℝ)^e₁.N)^(-e₁.mass c)) (assemblySymbol e₁ c L₁ f Q) z.1 z.2)
      (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e₂.ρ (treeCell Y)
        (((2:ℝ)^e₂.N)^(-e₂.mass c)) (assemblySymbol e₂ c L₂ g P) z.1 z.2)≤
    F₁^2*F₂^2*((2:ℝ)^e₁.N)^((g₁+g₂)/2) := by
  let μ := _root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))
  have hm₁ := _root_.OAI.CurrentFalconer.sourceAngularTransformND_measurable e₁.ρ (treeCell X)
    (((2:ℝ)^e₁.N)^(-e₁.mass c)) (assemblyInnerSymbol_measurable e₁ c L₁ f hf)
  have hm₂ := _root_.OAI.CurrentFalconer.sourceAngularTransformND_measurable e₂.ρ (treeCell Y)
    (((2:ℝ)^e₂.N)^(-e₂.mass c)) (assemblyInnerSymbol_measurable e₂ c L₂ g hg)
  have ht₁ : ∀ r,∀ᵐ w ∂μ,‖_root_.OAI.CurrentFalconer.sourceAngularTransformND e₁.ρ (treeCell X)
      (((2:ℝ)^e₁.N)^(-e₁.mass c)) (assemblyInnerSymbol e₁ c L₁ f) r w‖≤
      |(((2:ℝ)^e₁.N)^(-e₁.mass c))⁻¹| *(e₁.ρ (treeCell X)).toReal*D₁ := by
    intro r
    filter_upwards [_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND_ae_norm (V:=EuclideanSpace ℝ (Fin (n+1)))] with w hw
    exact _root_.OAI.CurrentFalconer.sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hb₁ x w hw)
  have ht₂ : ∀ r,∀ᵐ w ∂μ,‖_root_.OAI.CurrentFalconer.sourceAngularTransformND e₂.ρ (treeCell Y)
      (((2:ℝ)^e₂.N)^(-e₂.mass c)) (assemblyInnerSymbol e₂ c L₂ g) r w‖≤
      |(((2:ℝ)^e₂.N)^(-e₂.mass c))⁻¹| *(e₂.ρ (treeCell Y)).toReal*D₂ := by
    intro r
    filter_upwards [_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND_ae_norm (V:=EuclideanSpace ℝ (Fin (n+1)))] with w hw
    exact _root_.OAI.CurrentFalconer.sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hb₂ x w hw)
  have ha₁ : ∀ᵐ w ∂μ,‖assemblyOuterFactor e₁ c L₁ Q X w‖≤F₁ := by
    filter_upwards [_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND_ae_norm (V:=EuclideanSpace ℝ (Fin (n+1)))] with w hw
    exact hF₁ w hw
  have ha₂ : ∀ᵐ w ∂μ,‖assemblyOuterFactor e₂ c L₂ P Y w‖≤F₂ := by
    filter_upwards [_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND_ae_norm (V:=EuclideanSpace ℝ (Fin (n+1)))] with w hw
    exact hF₂ w hw
  have hcs := _root_.OAI.CurrentFalconer.AssemblyEstimate.sourceAngularHND_two_profile_power
    (n+1) μ c e₁.N hm₁ hm₂ ht₁ ht₂ hiΨ hΨ (by positivity : 0<(2:ℝ)^e₁.N) hh₁
    (by simpa only [hN] using hh₂)
  simp_rw [assemblyTransform_factor e₁ hq₁ c L₁ f Q X hX,assemblyTransform_factor e₂ hq₂ c L₂ g P Y hY]
  exact (GraphLiteralSupport.Attempt4Near.sourceAngularHND_bounded_factors (n+1) μ c e₁.N hm₁ hm₂ ht₁ ht₂
    _ _ ha₁ ha₂ hiΨ hΨ).trans (mul_le_mul_of_nonneg_left hcs (by positivity))
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

noncomputable def assemblySelfEnergy (e : RecursiveEnvironmentND n) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (X : CellPath (n+1)) (Ψ : ℝ → ℝ) : ℝ :=
  _root_.OAI.Attempt4Near.sourceAngularHND (n+1)
    (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) c e.N Ψ
    (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell X)
      (((2:ℝ)^e.N)^(-e.mass c)) (assemblyInnerSymbol e c L f) z.1 z.2)
    (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell X)
      (((2:ℝ)^e.N)^(-e.mass c)) (assemblyInnerSymbol e c L f) z.1 z.2)

lemma assembly_child_max_bound (e₁ e₂ : RecursiveEnvironmentND n)
    [IsFiniteMeasure e₁.ρ] [IsFiniteMeasure e₂.ρ] (hN : e₂.N=e₁.N)
    (hq₁ : 0<e₁.q) (hq₂ : 0<e₂.q) (c : ℕ)
    (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ x,‖f x‖≤1) (hgn : ∀ x,‖g x‖≤1)
    (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (Ψ : ℝ → ℝ) (hiΨ : Integrable Ψ) (hΨ : ∀ r,0≤Ψ r) (F g₁ g₂ : ℝ)
    (hF₁ : ∀ X w,‖w‖=1 → ‖assemblyOuterFactor e₁ c L₁ Q X w‖≤F)
    (hF₂ : ∀ Y w,‖w‖=1 → ‖assemblyOuterFactor e₂ c L₂ P Y w‖≤F)
    (hh₁ : ∀ X,X∈dyadicPaths c → 0<e₁.ρ (treeCell X) →
      assemblySelfEnergy e₁ c L₁ f X Ψ≤((2:ℝ)^e₁.N)^g₁)
    (hh₂ : ∀ Y,Y∈dyadicPaths c → 0<e₂.ρ (treeCell Y) →
      assemblySelfEnergy e₂ c L₂ g Y Ψ≤((2:ℝ)^e₁.N)^g₂) :
    _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax e₁.ρ e₂.ρ 0 c e₁.N [] []
      (((2:ℝ)^e₁.N)^(-e₁.mass c)) (((2:ℝ)^e₂.N)^(-e₂.mass c)) Ψ
      (assemblySymbol e₁ c L₁ f Q) (assemblySymbol e₂ c L₂ g P)≤
    F^4*((2:ℝ)^e₁.N)^((g₁+g₂)/2) := by
  obtain ⟨D₁,hD₁,hb₁⟩ := assemblyInnerSymbol_bounded e₁ c L₁ f hfn
  obtain ⟨D₂,hD₂,hb₂⟩ := assemblyInnerSymbol_bounded e₂ c L₂ g hgn
  unfold _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax
  split_ifs with h
  · apply Finset.sup'_le
    intro z hz
    obtain ⟨hX,hY⟩ := Finset.mem_product.mp hz
    have hlX := _root_.OAI.CurrentFalconer.TreeND.graphChildren_length hX
    have hlY := _root_.OAI.CurrentFalconer.TreeND.graphChildren_length hY
    have hoX := (Finset.mem_filter.mp hX).2
    have hoY := (Finset.mem_filter.mp hY).2
    have hmemX : z.1∈dyadicPaths c := (mem_dyadicPaths _ _).mpr hlX
    have hmemY : z.2∈dyadicPaths c := (mem_dyadicPaths _ _).mpr hlY
    have hh := assembly_child_two_profile e₁ e₂ hN hq₁ hq₂ c L₁ L₂ f g hf hg Q P z.1 z.2
      (by omega) (by omega) Ψ (hiΨ.comp_div (by positivity)) hΨ D₁ D₂ F F g₁ g₂
      (fun x w _ => hb₁ x w) (fun x w _ => hb₂ x w) (hF₁ _) (hF₂ _)
      (hh₁ _ hmemX (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hoX))
      (hh₂ _ hmemY (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hoY))
    simpa only [show F^2*F^2=F^4 by ring,_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hh
  · positivity

noncomputable def assemblyProfileExponent (e : RecursiveEnvironmentND n) (c : ℕ) : ℝ :=
  2*e.profile c-potential e.profile c e.N (10*e.q)

lemma uniform_assembly_child_max (hn : 1≤n) (Ctest : ℝ)
    {sig kap eta : ℝ} (hsig : 0<sig) (hkap : 0<kap) (hkap1 : kap≤1)
    (hgap : sig<kap/1000) (heta : 0<eta)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W,L.length≤B)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ⊆Ioo (1/4:ℝ) 4)
    (hΨ0 : ∀ r,0≤Ψ r) (hΨ1 : ∀ r∈Icc (1/2:ℝ) 2,1≤Ψ r) :
    ∃ D : ℝ,1≤D ∧ ∃ N₀ : ℕ,0<N₀ ∧ ∀ e₁ e₂ : RecursiveEnvironmentND n,
      N₀≤e₁.N → e₂.N=e₁.N → e₁.sig=sig → e₂.sig=sig → e₁.C=Ctest → e₂.C=Ctest →
      e₁.q=sourcePolicyBlock e₁.N kap → e₂.q=sourcePolicyBlock e₂.N kap →
      e₁.J=sourceSmoothingLevels sig kap → e₂.J=sourceSmoothingLevels sig kap →
      ∀ B₀ s₁ s₂,RegularizedProfileData e₁.ρ e₁.N B₀ s₁ sig e₁.mass →
      RegularizedProfileData e₂.ρ e₂.N B₀ s₂ sig e₂.mass →
      ∀ c,c+100*e₁.q<e₁.N →
      ∀ (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
        (Cq : ℝ),
      Measurable f → Measurable g → (∀ x,‖f x‖≤1) → (∀ x,‖g x‖≤1) →
      (∀ b∈assemblyDescriptorList e₁.profile e₁.N e₁.q c,L₁ b∈W) →
      (∀ b∈assemblyDescriptorList e₂.profile e₂.N e₂.q c,L₂ b∈W) →
      (∑ b∈assemblyDescriptorList e₁.profile e₁.N e₁.q c,(L₁ b).length)≤total →
      (∑ b∈assemblyDescriptorList e₂.profile e₂.N e₂.q c,(L₂ b).length)≤total →
      (∀ w,‖w‖=1 → ‖Q.1 w‖≤Cq) → (∀ w,‖w‖=1 → ‖P.1 w‖≤Cq) →
      _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax e₁.ρ e₂.ρ 0 c e₁.N [] []
        (((2:ℝ)^e₁.N)^(-e₁.mass c)) (((2:ℝ)^e₂.N)^(-e₂.mass c)) Ψ
        (assemblySymbol e₁ c L₁ f Q) (assemblySymbol e₂ c L₂ g P)≤
      (Cq*D^B)^4*((2:ℝ)^e₁.N)^((assemblyProfileExponent e₁ c+assemblyProfileExponent e₂ c)/2+
        profileDimLoss n Ctest*(kap+sig/kap)+eta) := by
  have hiΨ : Integrable Ψ := hΨ.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset isClosed_closure (hsupp.trans Ioo_subset_Icc_self))
  obtain ⟨ell,hK⟩ := pow_unbounded_of_one_lt (1000*(n+2:ℝ)) (show (1:ℝ)<2 by norm_num)
  obtain ⟨Order,hmain⟩ := uniform_actual_recursive_profile hn Ctest hsig hkap hkap1 hgap heta
    ell hK Ψ hΨ hsupp hΨ0 hΨ1 hiΨ
  let W' := W∪prefixInverseVocabulary n Order
  let B' := max B (2*Order)
  let total' := max total (2*Order)
  have hW' : ∀ L∈W',L.length≤B' := by
    intro L hL
    rcases Finset.mem_union.mp hL with hL | hL
    · exact (hW L hL).trans (le_max_left _ _)
    · exact (prefixInverseVocabulary_budget Order hL).trans (le_max_right _ _)
  obtain ⟨N₁,hN₁,hmain⟩ := hmain W' B' total' hW' Finset.subset_union_right (le_max_right _ _)
  obtain ⟨D,hD,hF⟩ := uniform_assemblyOuterFactor_bound W B hW hsig
  obtain ⟨N₂,hF⟩ := Filter.eventually_atTop.mp hF
  refine ⟨D,hD,max N₁ N₂,by omega,?_⟩
  intro e₁ e₂ hN heN hs₁ hs₂ hC₁ hC₂ hq₁ hq₂ hJ₁ hJ₂ B₀ s₁ s₂ hd₁ hd₂ c hwidth
    L₁ L₂ f g Q P Cq hf hg hfn hgn hL₁ hL₂ ht₁ ht₂ hQ hP
  let := hd₁.probability
  let := hd₂.probability
  have hqpos₁ : 0<e₁.q := by rw [hq₁]; exact sourcePolicyBlock_pos (by omega) hkap
  have hqpos₂ : 0<e₂.q := by rw [hq₂,heN]; exact sourcePolicyBlock_pos (by omega) hkap
  have heq : e₂.q=e₁.q := by rw [hq₂,hq₁,heN]
  have hinner (e : RecursiveEnvironmentND n) (he : e.N=e₁.N) (hes : e.sig=sig) (heC : e.C=Ctest)
      (heq : e.q=sourcePolicyBlock e.N kap) (heJ : e.J=sourceSmoothingLevels sig kap)
      (s : ℝ) (hd : RegularizedProfileData e.ρ e.N B₀ s sig e.mass) (hw : c+100*e.q<e.N)
      (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
      (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : Measurable f) (hfn : ∀ x,‖f x‖≤1)
      (hL : ∀ b∈assemblyDescriptorList e.profile e.N e.q c,L b∈W)
      (ht : (∑ b∈assemblyDescriptorList e.profile e.N e.q c,(L b).length)≤total)
      (X : CellPath (n+1)) (hX : X∈dyadicPaths c) (ho : 0<e.ρ (treeCell X)) :
      assemblySelfEnergy e c L f X Ψ≤((2:ℝ)^e₁.N)^(assemblyProfileExponent e c+
        profileDimLoss n Ctest*(kap+sig/kap)+eta) := by
    have hq : 0<e.q := by rw [heq,he]; exact sourcePolicyBlock_pos (by omega) hkap
    have hsub : policyDescriptorList e.profile e.N e.q c e.N⊆assemblyDescriptorList e.profile e.N e.q c :=
      Finset.subset_insert _ _
    have ht' : (∑ b∈policyDescriptorList e.profile e.N e.q c e.N,(L b).length)≤total' :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans (ht.trans (le_max_left _ _))
    have hv : BranchState.Valid e.N sig (.H c e.N c e.N 0) := by
      refine ⟨le_rfl,by omega,le_rfl,le_rfl,?_⟩
      nlinarith [Nat.cast_nonneg (α:=ℝ) e.N]
    have hm := assemblyInner_energy_mem e hq ((2:ℝ)^ell) W' total' c X hX ho L f hf hfn
      (fun b hb => Finset.mem_union_left _ (hL b (hsub hb))) ht' Ψ
    have hh := hmain e (by omega) hes heC heq heJ B₀ s hd (.H c e.N c e.N 0) hv rfl
      (by change c+10*e.q≤e.N; omega) _ hm
    simpa only [assemblySelfEnergy,assemblyProfileExponent,BranchState.start,BranchState.finish,he] using hh
  have hh := assembly_child_max_bound e₁ e₂ heN hqpos₁ hqpos₂ c L₁ L₂ f g hf hg hfn hgn Q P Ψ hiΨ hΨ0
    (Cq*D^B) (assemblyProfileExponent e₁ c+profileDimLoss n Ctest*(kap+sig/kap)+eta)
    (assemblyProfileExponent e₂ c+profileDimLoss n Ctest*(kap+sig/kap)+eta)
    (hF e₁.N (by omega) e₁ rfl hs₁ c L₁ Q Cq (hL₁ _ (Finset.mem_insert_self _ _)) hQ)
    (hF e₂.N (by omega) e₂ rfl hs₂ c L₂ P Cq (hL₂ _ (Finset.mem_insert_self _ _)) hP)
    (hinner e₁ rfl hs₁ hC₁ hq₁ hJ₁ s₁ hd₁ hwidth L₁ f hf hfn hL₁ ht₁)
    (hinner e₂ heN hs₂ hC₂ hq₂ hJ₂ s₂ hd₂ (by omega) L₂ g hg hgn hL₂ ht₂)
  convert hh using 1
  ring_nf
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

lemma assembly_profile_zero (e : RecursiveEnvironmentND n) {B : ℕ} {s sig : ℝ}
    (hd : RegularizedProfileData e.ρ e.N B s sig e.mass) : e.profile 0=0 := by
  simp only [RecursiveEnvironmentND.profile,adjustedProfile,Nat.cast_zero,mul_zero,zero_div,sub_zero,hd.zero]

lemma assembly_profile_lower (e : RecursiveEnvironmentND n) {B : ℕ} {chi sig : ℝ}
    (hd : RegularizedProfileData e.ρ e.N B ((n+1:ℝ)/2+chi) sig e.mass)
    {j : ℕ} (hj : j≤e.N) : chi*(j:ℝ)/e.N-(n+4:ℝ)*sig≤e.profile j := by
  have hh := (hd.envelope j hj).1
  dsimp only [RecursiveEnvironmentND.profile,adjustedProfile]
  push_cast at hh ⊢
  ring_nf at hh ⊢
  linarith only [hh]

lemma assembly_entry_estimates (hn : 1≤n) (e₁ e₂ : RecursiveEnvironmentND n) (heN : e₂.N=e₁.N)
    {B₀ : ℕ} {chi beta sig kap : ℝ} (hN : 1000≤e₁.N)
    (hd₁ : RegularizedProfileData e₁.ρ e₁.N B₀ ((n+1:ℝ)/2+chi) sig e₁.mass)
    (hd₂ : RegularizedProfileData e₂.ρ e₂.N B₀ ((n+1:ℝ)/2+chi) sig e₂.mass)
    (hchi : 0<chi) (hbeta : 0<beta) (hbeta1 : beta<1/10)
    (hsmall : beta+(n+4:ℝ)*sig<chi/4) (hkap : 0<kap) (hkap1 : kap≤1/1000)
    (hq₁ : e₁.q=sourcePolicyBlock e₁.N kap) (hq₂ : e₂.q=sourcePolicyBlock e₂.N kap) :
    let c := GraphLiteralSupport.CurrentFalconer.entryDepthND
      (fun j : Fin 2 => if j=0 then e₁.profile else e₂.profile) e₁.N beta
    ⌊beta*(e₁.N:ℝ)/(n+1:ℝ)⌋₊≤c ∧ (c:ℝ)<(e₁.N:ℝ)/4 ∧ c+100*e₁.q<e₁.N ∧
    -e₁.profile c-e₂.profile c+min (height e₁.profile 0 c) (height e₂.profile 0 c)+
      ((2*e₁.profile c-potential e₁.profile c e₁.N (10*e₁.q))+
       (2*e₂.profile c-potential e₂.profile c e₂.N (10*e₂.q)))/2≤
        -beta+(n+4:ℝ)*sig+(n+1:ℝ)/e₁.N := by
  let A : Fin 2 → ℕ → ℝ := fun j => if j=0 then e₁.profile else e₂.profile
  have hdpos : 0<(n+1:ℝ)/2 := by positivity
  have hzero : ∀ j,A j 0=0 := by
    intro j
    dsimp only [A]
    split_ifs
    · exact assembly_profile_zero e₁ hd₁
    · exact assembly_profile_zero e₂ hd₂
  have hlip : ∀ j a b,a≤e₁.N → b≤e₁.N →
      |A j a-A j b|≤((n+1:ℝ)/2)*|(a:ℝ)-b|/e₁.N := by
    intro j a b ha hb
    dsimp only [A]
    split_ifs
    · exact hd₁.environment_lipschitz e₁ a ha b hb
    · simpa only [heN] using hd₂.environment_lipschitz e₂ a (by omega) b (by omega)
  have hlower : ∀ j a,a≤e₁.N → chi*(a:ℝ)/e₁.N-(n+4:ℝ)*sig≤A j a := by
    intro j a ha
    dsimp only [A]
    split_ifs
    · exact assembly_profile_lower e₁ hd₁ ha
    · simpa only [heN] using assembly_profile_lower e₂ hd₂ (by omega : a≤e₂.N)
  have hb : beta≤2*((n+1:ℝ)/2) := by
    have hn0 := Nat.cast_nonneg (α:=ℝ) n
    linarith only [hbeta1,hn0]
  have hh := GraphLiteralSupport.CurrentFalconer.entry_profile_boundsND A (by omega : 0<e₁.N)
    hdpos hchi hbeta hb hsmall hzero hlip hlower
  have hg := GraphLiteralSupport.CurrentFalconer.entry_potential_gainND A hN
    hdpos hchi hbeta hb hsmall hkap hkap1 hzero hlip hlower
  have heq : e₂.q=e₁.q := by rw [hq₂,hq₁,heN]
  have hden : 2*((n+1:ℝ)/2)=(n+1:ℝ) := by ring
  dsimp only at hh hg ⊢
  refine ⟨?_,hh.2.1,?_,?_⟩
  · simpa only [hden] using hh.1
  · simpa only [hq₁,sourcePolicyBlock] using hg.1
  · simpa only [A,Fin.zero_eta,↓reduceIte,Fin.isValue,show (1:Fin 2)≠0 by decide,
      hden,heN,heq,hq₁,sourcePolicyBlock] using hg.2.2
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
