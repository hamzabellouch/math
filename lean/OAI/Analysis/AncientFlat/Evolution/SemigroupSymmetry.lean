import OAI.Analysis.AncientFlat.Evolution.MovingSymmetry

namespace OAI
noncomputable section
open Set
open scoped ZeroAtInfty
namespace FlatSimilarity
open FlatSymmetry
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
  (S : ℝ → C₀(V,ℂ) →L[ℂ] C₀(V,ℂ))
  (hE : ∀ d : C₀(V,ℂ), ∃ u : ℝ → C₀(V,ℂ), MovesClassically Af Bf d u ∧
    ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S t d x=u t (Real.exp (-t/4) • x))
include h hE in
lemma actual_rotate (hAf : Radial Af) (hBf : Radial Bf) (R : V ≃ₗᵢ[ℝ] V)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (d : C₀(V,ℂ)) :
    rotate R (S t d)=S t (rotate R d) := by
  obtain ⟨u,hu,hue⟩ := hE d
  obtain ⟨w,hw,hwe⟩ := hE (rotate R d)
  have he := (hu.rotated hAf hBf R).unique h hw t ht
  ext x
  change S t d (R x)=S t (rotate R d) x
  rw [hue t ht,hwe t ht,←R.map_smul]
  exact congrArg (fun f : C₀(V,ℂ) => f (Real.exp (-t/4) • x)) he
include h hE in
lemma actual_star (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (d : C₀(V,ℂ)) :
    star (S t d)=S t (star d) := by
  obtain ⟨u,hu,hue⟩ := hE d
  obtain ⟨w,hw,hwe⟩ := hE (star d)
  have he := hu.conjugate.unique h hw t ht
  ext x
  change star (S t d x)=S t (star d) x
  rw [hue t ht,hwe t ht]
  exact congrArg (fun f : C₀(V,ℂ) => f (Real.exp (-t/4) • x)) he
end FlatSimilarity

end

end OAI
