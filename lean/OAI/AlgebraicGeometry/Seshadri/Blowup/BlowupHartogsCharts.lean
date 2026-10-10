import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.FiniteCenters
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupIntegral
import OAI.AlgebraicGeometry.Seshadri.Configurations.AffinePointParameters
import OAI.AlgebraicGeometry.Seshadri.Sheaves.EtaleLineFrame

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

lemma affineComplexPoint_not_mem_basicOpen (S : Surface) (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) (t : Γ(S.scheme,U.1)) (ht : ρ t = 0) :
    (affineComplexPoint S.structureMap U ρ).left (fieldPoint ℂ) ∉ S.scheme.basicOpen t := by
  let z : PrimeSpectrum Γ(S.scheme,U.1) := ⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩
  change ¬ U.2.fromSpec z ∈ S.scheme.basicOpen t
  change ¬ z ∈ U.2.fromSpec ⁻¹ᵁ S.scheme.basicOpen t
  rw [U.2.fromSpec_preimage_basicOpen]
  exact fun h => h ht

lemma Surface.hartogs_chart (S : Surface) {r : ℕ} (p : Configuration S r)
    (W : S.scheme.Opens) (x : S.scheme) (hx : x ∈ W) :
    ∃ U : S.scheme.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
        (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
        ∀ i, S.scheme.basicOpen (t i) ≤ centreComplement (centreIdeal S r p) := by
  classical
  let q : Fin r → (Spec (.of ℂ) ⟶ S.scheme) := fun i => (p.val i).left
  have hq : ∀ i, q i ≫ S.structureMap = 𝟙 _ := fun i => (p.val i).w
  have hd : Function.Injective (fun i => q i (fieldPoint ℂ)) := p.property
  by_cases hc : x ∈ (centreIdeal S r p).support
  · obtain ⟨j,hj⟩ := (FinitePointBlowup.mem_centre_support q x).mp hc
    have hxj : x = q j (fieldPoint ℂ) := by
      change x ∈ ((q j).ker.support : Set S.scheme) at hj
      rwa [FinitePointBlowup.point_support q S.structureMap hq j] at hj
    obtain ⟨U,hxU,hUW,e,t,het⟩ := S.etale_line_frame_inside (⟨O S.scheme, fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso _⟩⟩⟩)
      (W ⊓ FinitePointBlowup.pointOpen q j) x
      ⟨hx,hxj ▸ FinitePointBlowup.point_mem_own_open q S.structureMap hq hd j _⟩
    have hp : (p.val j).left (fieldPoint ℂ) ∈ U.1 := hxj ▸ hxU
    obtain ⟨ρ,hρ⟩ := affineComplexPoint_factor S.structureMap U (p.val j) hp
    let := (openScalars S.structureMap U.1).toAlgebra
    let a : Fin 2 → Γ(S.scheme,U.1) := fun i => t i - algebraMap ℂ _ (ρ (t i))
    refine ⟨U,hxU,hUW.trans inf_le_left,a,
      MaximalSeshadri.AlgebraicJets.etale_aeval_center t het ρ,?_⟩
    intro i y hy hyc
    obtain ⟨k,hk⟩ := (FinitePointBlowup.mem_centre_support q y).mp hyc
    have hyU := S.scheme.basicOpen_le (a i) hy
    have hyOpen := (hUW hyU).2
    have hkj : k = j := by
      by_contra hne
      exact (FinitePointBlowup.mem_pointOpen q j y).mp hyOpen k hne hk
    subst k
    have hyj : y = q j (fieldPoint ℂ) := by
      change y ∈ ((q j).ker.support : Set S.scheme) at hk
      rwa [FinitePointBlowup.point_support q S.structureMap hq j] at hk
    have hn := affineComplexPoint_not_mem_basicOpen S U ρ (a i) (by simp [a])
    rw [hρ] at hn
    exact hn (hyj ▸ hy)
  · obtain ⟨U,hxU,hUW,e,t,het⟩ := S.etale_line_frame_inside (⟨O S.scheme, fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso _⟩⟩⟩)
      (W ⊓ centreComplement (centreIdeal S r p)) x ⟨hx,hc⟩
    exact ⟨U,hxU,hUW.trans inf_le_left,t,het,fun i =>
      (S.scheme.basicOpen_le (t i)).trans (hUW.trans inf_le_right)⟩

end
end MaximalSeshadri.Geometry

end


end OAI
