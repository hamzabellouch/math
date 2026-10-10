import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.MinimalDescriptorLength
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.SuffixDescendants
import OAI.MeasureTheory.FalconerCompletion.Recursion.ListSourceSymbol
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveEnvironment

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

noncomputable def assemblyDescriptorList (A : ℕ → ℝ) (N q c : ℕ) : Finset PolicyDescriptor :=
  insert (.parallel 0 c) (policyDescriptorList A N q c N)

noncomputable def assemblySymbol (e : RecursiveEnvironmentND n) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
    EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ :=
  fun x w => Q.1 w * f x *
    (actualAngularProduct (assemblyDescriptorList e.profile e.N e.q c) id L
      e.ρ e.mass e.N e.sig e.C e.J 0 x).1 w

noncomputable def assemblyRootEnergy (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ)
    (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (Ψ : ℝ → ℝ) (ψ : EuclideanSpace ℝ (Fin (n+1)) → ℂ) : ℝ :=
  _root_.OAI.Attempt4Near.sourceAngularHFND (n+1)
    (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) 0 e₁.N Ψ ψ
    (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e₁.ρ (treeCell [])
      (((2:ℝ)^e₁.N)^(-e₁.mass 0)) (assemblySymbol e₁ c L₁ f Q) z.1 z.2)
    (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e₂.ρ (treeCell [])
      (((2:ℝ)^e₂.N)^(-e₂.mass 0)) (assemblySymbol e₂ c L₂ g P) z.1 z.2)
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

lemma assemblyDescriptorList_valid (A : ℕ → ℝ) {N q c : ℕ} (hq : 0<q) (hc : c≤N)
    {b : PolicyDescriptor} (hb : b∈assemblyDescriptorList A N q c) : ValidDescriptor N b := by
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact ⟨Nat.zero_le _,hc⟩
  · exact policyDescriptor_valid A hq le_rfl hb

lemma assemblyDescriptorList_length (A : ℕ → ℝ) {N q c : ℕ} (hq : 0<q) (hc : 2*c≤N) :
    2*(assemblyDescriptorList A N q c).sup descriptorLength≤N := by
  have h : (assemblyDescriptorList A N q c).sup descriptorLength≤N/2 := by
    apply Finset.sup_le
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · simp only [descriptorLength,Nat.sub_zero]; omega
    · have hh := policyDescriptor_twice_length A hq hb
      omega
  omega

lemma assemblySymbol_measurable (e : RecursiveEnvironmentND n) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : Measurable f)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
    Measurable (Function.uncurry (assemblySymbol e c L f Q)) :=
  (((show ContDiff ℝ ∞ Q.1 from Q.2).continuous.measurable.comp measurable_snd).mul (hf.comp measurable_fst)).mul
    (actualAngularProduct_measurable _ _ _ _ _ _ _ _ _ _)

lemma assemblySymbol_smooth (e : RecursiveEnvironmentND n) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (x : EuclideanSpace ℝ (Fin (n+1))) :
    ContDiff ℝ ∞ (assemblySymbol e c L f Q x) :=
  ((show ContDiff ℝ ∞ Q.1 from Q.2).mul contDiff_const).mul
    (show ContDiff ℝ ∞ (actualAngularProduct _ _ _ _ _ _ _ _ _ _ x).1 from (actualAngularProduct _ _ _ _ _ _ _ _ _ _ x).2)

lemma assemblySymbol_eq (e : RecursiveEnvironmentND n) (c : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
    assemblySymbol e c L f Q = fun x w =>
      (actualListSourceSymbol (assemblyDescriptorList e.profile e.N e.q c) L
        e.ρ e.mass e.N e.sig e.C e.J 0 f Q x).1 w := by
  ext x w
  dsimp only [assemblySymbol,actualListSourceSymbol]
  ring

lemma uniform_assemblySymbol_jets
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (M B total : ℕ) (hW : ∀ L∈W,L.length≤B) {sig : ℝ} (hsig : 0<sig)
    (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ E : ℝ,0≤E ∧ ∀ᶠ N : ℕ in atTop,∀ e : RecursiveEnvironmentND n,
      e.N=N → e.sig=sig → 0<e.q → ∀ c l,c≤N →
      (∀ b∈assemblyDescriptorList e.profile e.N e.q c,descriptorLength b≤l) →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      Measurable f → (∀ x,‖f x‖≤1) →
      (∀ b∈assemblyDescriptorList e.profile e.N e.q c,L b∈W) →
      (∑ b∈assemblyDescriptorList e.profile e.N e.q c,(L b).length)≤total →
      (∀ j≤M,∀ w,‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      _root_.OAI.CurrentFalconer.GraphSymbolJet (assemblySymbol e c L f Q) M
        (((2:ℝ)^N)^sig*max 1 ((2:ℝ)^l*((2:ℝ)^N)^(-50*sig))) E := by
  obtain ⟨E,hE,h⟩ := uniform_actualListSourceSymbol_jets W M B total hW sig hsig Cq hCq
  refine ⟨E,hE,?_⟩
  filter_upwards [h] with N hN
  intro e he hs hq c l hc hl L f Q hf hfn hL htotal hQ
  subst N
  rw [assemblySymbol_eq]
  simpa only [sourceMaskScaleND,Real.rpow_natCast,hs] using
    hN (assemblyDescriptorList e.profile e.N e.q c) L e.ρ e.mass e.C e.J 0 l f Q
      (fun b hb => assemblyDescriptorList_valid e.profile hq hc hb) hl hL htotal hf hfn hQ

lemma uniform_assemblySymbol_imposes {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ,∀ e : RecursiveEnvironmentND n,N₀≤e.N → e.sig=sig → e.J=J →
      IsFiniteMeasure e.ρ → 0<e.q → ∀ c,c≤e.N →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      _root_.OAI.CurrentFalconer.TreeND.ImposesParallelTest e.ρ 0 c
        (_root_.OAI.CurrentFalconer.TreeND.testWidth e.N J 1 c sig)
        (((2:ℝ)^e.N)^(height e.profile 0 c+e.C*sig)) (assemblySymbol e c L f Q) := by
  obtain ⟨N₀,h⟩ := uniform_actualListSourceSymbol_test (d:=n+1) hsig hJ
  refine ⟨N₀,?_⟩
  intro e hN hs hJ' hf hq c hc L f Q P hP x hx w hw hn
  rw [assemblySymbol_eq] at hn
  have hn' : (actualListSourceSymbol (assemblyDescriptorList e.profile e.N e.q c) L
      e.ρ e.mass e.N sig e.C J 0 f Q x).1 w≠0 := by simpa only [hs,hJ'] using hn
  have hh := h e.N hN e.ρ hf e.mass e.C 0 (assemblyDescriptorList e.profile e.N e.q c)
    (fun b hb => assemblyDescriptorList_valid e.profile hq hc hb) L f Q x w hw hn'
    (.parallel 0 c) (Finset.mem_insert_self _ _)
  have hg := hh P
    (by simpa only [descriptorAnchor,_root_.OAI.CurrentFalconer.TreeND.literal_dyadicPaths] using hP)
    (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hx)
  simpa only [descriptorGood,testWidth,_root_.OAI.CurrentFalconer.TreeND.testWidth,
    _root_.OAI.CurrentFalconer.TreeND.literal_fullParallelCount,RecursiveEnvironmentND.profile] using hg.2
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
