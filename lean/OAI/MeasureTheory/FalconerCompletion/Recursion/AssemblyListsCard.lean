import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Estimates.AssemblyEndpointSmooth
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphSymbolJetConj

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical Topology ComplexConjugate
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))

lemma assemblyLists_card (e₁ e₂ : RecursiveEnvironmentND n) (hN : 1≤e₁.N)
    (heN : e₂.N=e₁.N) (hq₁ : 0<e₁.q) (hq₂ : 0<e₂.q) {c : ℕ} (hc : c≤e₁.N) :
    max 1 (((assemblyDescriptorList e₁.profile e₁.N e₁.q c).card+
      (assemblyDescriptorList e₂.profile e₂.N e₂.q c).card:ℕ):ℝ) ≤ 16*(e₁.N:ℝ)^2 := by
  have h₁ := validDescriptorList_card hN (assemblyDescriptorList e₁.profile e₁.N e₁.q c)
    (fun _ hb => assemblyDescriptorList_valid e₁.profile hq₁ hc hb)
  have h₂ := validDescriptorList_card (by omega : 1≤e₂.N) (assemblyDescriptorList e₂.profile e₂.N e₂.q c)
    (fun _ hb => assemblyDescriptorList_valid e₂.profile hq₂ (by omega) hb)
  rw [heN] at h₂
  have hN' : (1:ℝ)≤e₁.N := by exact_mod_cast hN
  apply max_le
  · nlinarith only [hN',sq_nonneg ((e₁.N:ℝ)-1)]
  · push_cast
    rw [heN]
    linarith only [h₁,h₂]

lemma assemblyDescriptor_scale (e : RecursiveEnvironmentND n) (hq : 0<e.q)
    {c : ℕ} (hc : 2*c≤e.N) {b : PolicyDescriptor}
    (hb : b∈assemblyDescriptorList e.profile e.N e.q c) :
    1 ≤ sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig ∧
      sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig ≤
        Attempt4PrefixShell.sourceMaskScaleND (e.N/2) ((2:ℝ)^e.N) e.sig := by
  refine ⟨sourceMaskScaleND_one_le _ _ _,?_⟩
  change sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig ≤
    sourceMaskScaleND (e.N/2) ((2:ℝ)^e.N) e.sig
  apply sourceMaskScaleND_mono _ (by positivity)
  have h := assemblyDescriptorList_length e.profile hq hc
  have hb' := Finset.le_sup (f:=descriptorLength) hb
  omega

lemma assembly_pairMask_eq (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ) (z : V×V) (w : V) :
    (Attempt4PrefixShell.pairMaskProductND
      (assemblyDescriptorList e₁.profile e₁.N e₁.q c) (assemblyDescriptorList e₂.profile e₂.N e₂.q c)
      (assemblyEndpointSmooth e₁) (assemblyEndpointSmooth e₂) z).1 w =
    ((∏ b∈assemblyDescriptorList e₁.profile e₁.N e₁.q c,
      actualEndpointMask e₁.ρ e₁.mass e₁.N e₁.sig e₁.C e₁.J 0 b z.1 w)*
    (∏ b∈assemblyDescriptorList e₂.profile e₂.N e₂.q c,
      actualEndpointMask e₂.ρ e₂.mass e₂.N e₂.sig e₂.C e₂.J 0 b z.2 w):ℝ) := by
  simp only [Attempt4PrefixShell.pairMaskProductND,Attempt4PrefixShell.smoothFinsetProductND,
    Finset.prod_disjSum,Sum.elim_inl,Sum.elim_inr,Attempt4PrefixShell.smoothStarND,
    assemblyEndpointSmooth,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_prod]

lemma assembly_endpoint_radial_left (e : RecursiveEnvironmentND n) (b : PolicyDescriptor) :
    Measurable (fun z : V×V => actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J 0 b z.1
      ((dist z.1 z.2)⁻¹ • (z.1-z.2))) := by
  simpa only [radialVector,dist_eq_norm,Function.comp_def] using
    (actualEndpointMask_measurable e.ρ e.mass e.N e.sig e.C e.J 0 b).comp
      (measurable_fst.prodMk measurable_radialVector)
lemma assembly_endpoint_radial_right (e : RecursiveEnvironmentND n) (b : PolicyDescriptor) :
    Measurable (fun z : V×V => actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J 0 b z.2
      ((dist z.1 z.2)⁻¹ • (z.1-z.2))) := by
  simpa only [radialVector,dist_eq_norm,Function.comp_def] using
    (actualEndpointMask_measurable e.ρ e.mass e.N e.sig e.C e.J 0 b).comp
      (measurable_snd.prodMk measurable_radialVector)

lemma assembly_pairMask_radial_measurable (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ) :
    Measurable (fun z : V×V =>
      (Attempt4PrefixShell.pairMaskProductND
      (assemblyDescriptorList e₁.profile e₁.N e₁.q c) (assemblyDescriptorList e₂.profile e₂.N e₂.q c)
      (assemblyEndpointSmooth e₁) (assemblyEndpointSmooth e₂) z).1
        ((dist z.1 z.2)⁻¹ • (z.1-z.2))) := by
  simp only [assembly_pairMask_eq]
  apply Complex.continuous_ofReal.measurable.comp
  exact (Finset.measurable_prod _ (fun b _ => assembly_endpoint_radial_left e₁ b)).mul
    (Finset.measurable_prod _ (fun b _ => assembly_endpoint_radial_right e₂ b))

lemma assembly_pairMask_measurable (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ)
    {f g : V → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun z : V×V => (f z.1*conj (g z.2))*
      (Attempt4PrefixShell.pairMaskProductND
      (assemblyDescriptorList e₁.profile e₁.N e₁.q c) (assemblyDescriptorList e₂.profile e₂.N e₂.q c)
      (assemblyEndpointSmooth e₁) (assemblyEndpointSmooth e₂) z).1
        ((dist z.1 z.2)⁻¹ • (z.1-z.2))) := by
  exact ((hf.comp measurable_fst).mul (Complex.continuous_conj.measurable.comp (hg.comp measurable_snd))).mul
    (assembly_pairMask_radial_measurable e₁ e₂ c)
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
