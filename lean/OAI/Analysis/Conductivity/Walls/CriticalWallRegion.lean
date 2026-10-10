import Mathlib
import OAI.Analysis.Conductivity.Walls.CriticalWallFamilyCorrection
import OAI.Analysis.Conductivity.Branching.SmoothFamilyCorrectionTransport

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def criticalWallRegion
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    (hz : ∀ q z,wallDerivative (fun y => v (q,y)) (z,0)=0)
    {U W : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUW : U⊆W) (hneU : U.Nonempty)
    (hcp : IsPreconnected (U∩{x : Coord3 | 0<x 2}))
    (hcn : IsPreconnected (U∩{x : Coord3 | x 2<0}))
    (hproj : ∀ x∈U,boxCoordinates.symm ((boxCoordinates x).1,0)∈U)
    (hne₀ : ∀ x∈U,wallQuotient (wallDerivative (fun y => v (p,y))) (boxCoordinates x)≠0)
    {l t a b σ lam : ℝ} (hlt : l<t) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    (hrectU : ∀ z∈Icc l t×ˢIcc a b,boxCoordinates.symm (z,0)∈U)
    (hlim : ∀ z : ℝ×ℝ,v (p,(z,0))=σ*Real.exp (-lam*z.1)) :
    VanishingCorrectionRegion (fun z => wallCoordinatePair (fun y => v (z.1,y)) z.2) p W := by
  classical
  refine ⟨U,hU,hneU,hUW,hUb,?_⟩
  intro r hr ε hε
  obtain ⟨S,hS,hSU,hss⟩ := hr.2.2
  let T : Set Box3 := boxCoordinates '' S
  have hT : IsCompact T := hS.image boxCoordinates.continuous
  let K : Set (ℝ×ℝ) := Prod.fst '' T ∪ (Icc l t×ˢIcc a b)
  have hK : IsCompact K := (hT.image continuous_fst).union (isCompact_Icc.prod isCompact_Icc)
  let J : Set Box3 := (fun z : ℝ×ℝ => (z,(0:ℝ))) '' K
  have hJ : IsCompact J := hK.image (continuous_id.prodMk continuous_const)
  let Ω : Set Box3 := boxCoordinates.symm ⁻¹' U
  have hΩ : IsOpen Ω := hU.preimage boxCoordinates.symm.continuous
  have hΩb : Bornology.IsBounded Ω := by
    rw [show Ω=boxCoordinates '' U from by
      ext z
      constructor
      · intro hz; exact ⟨boxCoordinates.symm z,hz,boxCoordinates.apply_symm_apply z⟩
      · rintro ⟨x,hx,rfl⟩; simpa only [Ω,mem_preimage,boxCoordinates.symm_apply_apply] using hx]
    exact boxCoordinates.toContinuousLinearMap.lipschitzWith.isBounded_image hUb
  have hJU : J⊆Ω := by
    rintro _ ⟨z,hz,rfl⟩
    rcases hz with hz | hz
    · rcases hz with ⟨w,⟨x,hx,rfl⟩,rfl⟩
      exact hproj x (hSU hx)
    · exact hrectU z hz
  obtain ⟨χ,hχ,hχc,hχU,_,hχone⟩ := exists_smooth_core_cutoff hJ hΩ hΩb hJU
  let R : Fin 2 → P×Box3 → ℝ := fun j z => r j (z.1,boxCoordinates.symm z.2)
  have hR (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (R j) :=
    (hr.1 j).comp (contDiff_fst.prodMk (boxCoordinates.symm.contDiff.comp contDiff_snd))
  have hRs : ∀ q j,tsupport (fun y => R j (q,y))⊆T∩Prod.fst ⁻¹' K := by
    intro q j y hy
    have hh : boxCoordinates.symm y∈S := hss q j
      ((tsupport_comp_subset_preimage (fun x => r j (q,x)) boxCoordinates.symm.continuous) hy)
    have hyT : y∈T := ⟨boxCoordinates.symm y,hh,boxCoordinates.apply_symm_apply y⟩
    exact ⟨hyT,Or.inl ⟨y,hyT,rfl⟩⟩
  have hsolve := critical_wall_family_correction hv p hz hU hcp hcn hne₀ hχ hχc
    (fun x hx => by
      have hh : boxCoordinates.symm (boxCoordinates x)∈U := hχU hx
      simpa only [boxCoordinates.symm_apply_apply] using hh) hT
    (fun x hx => by rcases hx with ⟨y,hy,he⟩; exact hSU (boxCoordinates.injective he ▸ hy))
    hK.isClosed (fun z hz => hχone (z,0) ⟨z,hz,rfl⟩) hlt hab hσ hlam
    (fun _ hz => Or.inr hz) hlim hR (Filter.Eventually.of_forall hRs)
    (fun j y => hr.2.1 j _) hε
  filter_upwards [hsolve] with q hq hm
  have he : wallInputPair R q=(fun j x => r j (q,x)) := by
    funext j x
    simp only [wallInputPair,R,boxCoordinates.symm_apply_apply]
  rw [he] at hq
  exact (hq hm).region_mono hUW

end ScalarConductivity

end
end

end OAI
