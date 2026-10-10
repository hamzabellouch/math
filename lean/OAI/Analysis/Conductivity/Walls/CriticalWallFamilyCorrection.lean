import Mathlib
import OAI.Analysis.Conductivity.Walls.WallVanishingMomentCoefficients
import OAI.Analysis.Conductivity.Sobolev.WallParticularFinish

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem critical_wall_family_correction
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    (hz : ∀ q z,wallDerivative (fun y => v (q,y)) (z,0)=0)
    {U : Set Coord3} (hU : IsOpen U)
    (hcp : IsPreconnected (U∩{x : Coord3 | 0<x 2}))
    (hcn : IsPreconnected (U∩{x : Coord3 | x 2<0}))
    (hne₀ : ∀ x∈U,wallQuotient (wallDerivative (fun y => v (p,y))) (boxCoordinates x)≠0)
    {χ : Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hχU : boxCoordinates ⁻¹' tsupport χ⊆U)
    {S : Set Box3} (hS : IsCompact S) (hSU : boxCoordinates ⁻¹' S⊆U)
    {K : Set (ℝ×ℝ)} (hK : IsClosed K)
    (hcore : ∀ z∈K,χ =ᶠ[𝓝 (z,0)] (fun _ => 1))
    {l t a b σ lam : ℝ} (hlt : l<t) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    (hrect : Icc l t×ˢIcc a b⊆K)
    (hlim : ∀ z : ℝ×ℝ,v (p,(z,0))=σ*Real.exp (-lam*z.1))
    {r : Fin 2 → P×Box3 → ℝ}
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    (hs : ∀ᶠ q in 𝓝 p,∀ j,tsupport (fun y => r j (q,y))⊆S∩Prod.fst ⁻¹' K)
    (hrz : ∀ j y,r j (p,y)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,
      physicalSourceMoment (wallCoordinatePair (fun y => v (q,y))) (wallInputPair r q)=0 →
      BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q,y))) U (wallInputPair r q) ε := by
  have hvq (q : P) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (q,y)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  have hrq (q : P) (j : Fin 2) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => r j (q,y)) :=
    (hr j).comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨V,hV,hp,hne⟩ := compact_parameter_nonzero_neighborhood
    (wallQuotient_parametric_smooth (wallDerivative_parametric_smooth hv)).continuous hχc
    (fun z hz => by
      have h := hne₀ (boxCoordinates.symm z) (hχU (by
        change boxCoordinates (boxCoordinates.symm z)∈tsupport χ
        simpa only [boxCoordinates.apply_symm_apply] using hz))
      simpa only [boxCoordinates.apply_symm_apply] using h)
  obtain ⟨δ,hδ,hgap⟩ := exists_uniform_particular_residual_gap hχ hχc hK hS hcore
  let R := wallResidualFamily χ v r
  have hRs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => R j (q,x))
      (boxCoordinates ⁻¹' (S∪tsupport χ)) := by
    filter_upwards [hs] with q hq
    exact fun j => wallResidualFamily_tsupport hχc (fun j => (hq j).trans inter_subset_left) j
  have hRg : ∀ᶠ q in 𝓝 p,∀ j x,x∈tsupport (fun y => R j (q,y)) → δ≤|x 2| := by
    filter_upwards [hs,hV.mem_nhds hp] with q hq hqV
    exact hgap (fun y => v (q,y)) (fun y => r 0 (q,y)) (fun y => r 1 (q,y))
      (hvq q) (hrq q 0) (hrq q 1) (hz q) (hne q hqV) (hq 0) (hq 1)
  have hD (x : Coord3) (hx : x∈U) (hn : x 2≠0) :
      Function.Surjective (fderiv ℝ (wallCoordinatePair (fun y => v (p,y))) x) :=
    wallCoordinatePair_surjective_off_wall (hvq p) (hz p) hn (hne₀ x hx)
  have hRU : boxCoordinates ⁻¹' (S∪tsupport χ)⊆U := by
    intro x hx
    rcases hx with hx | hx
    · exact hSU hx
    · exact hχU hx
  have hsolve := critical_wall_vanishing_transfer_correction hv p hU hcp hcn hD hχ hχc hχU
    hlt hab hσ hlam (fun z hz => hcore z (hrect hz)) hlim hV hp
    (fun q _ => hz q) hne (wallResidualFamily_smoothOn hχ hv hr hV hne)
    (boxCoordinates.toHomeomorph.isCompact_preimage.mpr (hS.union hχc)) hRU hRs hδ hRg
    (wallResidualFamily_zero hrz) (by linarith : 0<ε/2)
  have hsmall := wallParticularFamily_small hχ hχc hv hr hV hp hne hrz (by linarith : 0<ε/2)
  filter_upwards [hsolve,hsmall,hs,hV.mem_nhds hp] with q solve small supp hq hm
  have hrs (j) : HasCompactSupport (fun y => r j (q,y)) :=
    hS.of_isClosed_subset (isClosed_tsupport _) ((supp j).trans inter_subset_left)
  exact wall_particular_family_finishes hχ hχc hv hr q hχU hrs (hne q hq) hm small solve

end ScalarConductivity

end
end

end OAI
