import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ComparisonRefinement

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)
local instance finiteRefinementImportRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance finiteRefinementImportAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance finiteRefinementImportAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance finiteRefinementImportNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance finiteRefinementImportNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma finite_refinement_import_positive
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (D : ℕ) (l : List (ComparisonCrossing v Ω δ k B))
    (href : ∀N,∃l',WordRefines v Ω δ k B D l l' ∧ ∀n≤N,
      coeff n (comparisonWordOld v Ω hΩ δ k p hp hδ B l').val.val=coeff n 1)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (F : PowerSeries (PowerSeries (Torus v Ω)))
    (hf : PowerSeries.map (expandFiber v Ω hΩ k p) f=
      PowerSeries.map (HahnSeries.ofPowerSeries ℤ (Torus v Ω)) F) :
    coeff D (comparisonWordAction v Ω hΩ δ k p hp B l f)=coeff D f := by
  apply expandFiber_injective v Ω hΩ k p hp
  apply HahnSeries.ext
  funext z
  have HX (N : ℕ) (l' : List (ComparisonCrossing v Ω δ k B))
      (hR : WordRefines v Ω δ k B D l l') :
      (expandFiber v Ω hΩ k p (coeff D (comparisonWordAction v Ω hΩ δ k p hp B l f))).coeff z=
        (coeff D (oldLaurent v Ω δ k (comparisonWordOld v Ω hΩ δ k p hp hδ B l').val.val*
          PowerSeries.map (HahnSeries.ofPowerSeries ℤ (Torus v Ω)) F*
          oldLaurent v Ω δ k (comparisonWordOld v Ω hΩ δ k p hp hδ B l').inv.val)).coeff z := by
    rw [hR.action v Ω hΩ δ k p hp B f f (fun _ _=>rfl) D le_rfl]
    have H:=congrArg (fun a : PowerSeries (HahnSeries ℤ (Torus v Ω))=>(coeff D a).coeff z)
      (comparisonWord_expansion v Ω hΩ δ k p hp hδ B hq l' f)
    simp only [coeff_map] at H
    rw [hf] at H
    exact H
  have HF:=congrArg (fun a : PowerSeries (HahnSeries ℤ (Torus v Ω))=>(coeff D a).coeff z) hf
  simp only [coeff_map] at HF
  rw [HF]
  rcases le_or_gt 0 z with hz|hz
  · lift z to ℕ using hz with e he
    obtain ⟨l',hR,hN⟩:=href (D+e)
    rw [HX (D+e) l' hR,HahnSeries.ofPowerSeries_apply_coeff]
    apply oldLaurent_inner_through v Ω δ k (comparisonWordOld v Ω hΩ δ k p hp hδ B l') (D+e) hN
      (oldUnit_inverse_congr v Ω δ k _ 1 (D+e) hN) F D e le_rfl
  · obtain ⟨l',hR,hN⟩:=href 0
    rw [HX 0 l' hR,hahn_power_negative v Ω _ z hz]
    unfold oldLaurent
    rw [←map_mul,←map_mul,coeff_map,hahn_power_negative v Ω _ z hz]
end
end ElementaryPositivity.RationalFiber

end

end OAI
