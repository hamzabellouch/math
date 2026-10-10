import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Configurations.Configurations
import OAI.AlgebraicGeometry.Seshadri.Jets.JetOpenConfigurations
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtaleAffineTest

namespace OAI


                                                  
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.eventual_very_general_interpolation (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ U : S.scheme.affineOpens, ∃ eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
        ∃ Z : ℕ → Set (Configuration S r),
          (∀ n, IsClosed (Z n) ∧ Z n ≠ Set.univ) ∧
          (∃ p : Configuration S r, ∀ n, p ∉ Z n) ∧
          ∀ p : Configuration S r, (∀ n, p ∉ Z n) →
            ∀ k m : ℕ, 0 < k → 0 < m →
            (k:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (m:ℝ) →
            ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
                Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
              (∀ i, affineComplexPoint S.structureMap U (ρ i) = p.val i) ∧
              ∀ s : O S.scheme ⟶ (L.pow k).sheaf,
                (∀ i, affineCoefficient U (localPowerFrame U.1 eL k) s ∈
                  (RingHom.ker (ρ i))^m) → s = 0 := by
  classical
  obtain ⟨U,eL,t,het,r₀,hr₀,htest⟩ := S.eventual_etale_affine_section_test L hL
  let := (openScalars S.structureMap U.1).toAlgebra
  refine ⟨U,eL,r₀,hr₀,?_⟩
  intro r hr
  let Good (a : ℕ × ℕ) : Prop := 0 < a.1 ∧ 0 < a.2 ∧
    (a.1:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (a.2:ℝ)
  let Test (a : ℕ × ℕ) (p : Configuration S r) : Prop :=
    ∃ ρ : Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
      (∀ i, affineComplexPoint S.structureMap U (ρ i) = p.val i) ∧
      ∀ s : O S.scheme ⟶ (L.pow a.1).sheaf,
        (∀ i, affineCoefficient U (localPowerFrame U.1 eL a.1) s ∈
          (RingHom.ker (ρ i))^a.2) → s = 0
  have hW (a : ℕ × ℕ) (ha : Good a) :
      ∃ W : (surfacePower S r).left.Opens,
        (∃ p : Configuration S r, tupleImage S r p.val ∈ W) ∧
        ∀ p : Configuration S r, tupleImage S r p.val ∈ W → Test a p := by
    obtain ⟨ρ,hρ,hsep⟩ := htest r hr a.1 a.2 ha.1 ha.2.1 ha.2.2
    let ℓ := affineCoefficientLinear S.structureMap U (localPowerFrame U.1 eL a.1)
    obtain ⟨W,hρW,hW⟩ := @exists_open_jet_configuration S r U t het _ _
      (complexSectionModule S.structureMap (L.pow a.1).sheaf)
      (S.sections_finite L hL (L.pow a.1)) ℓ a.2 ha.2.1 ρ hsep
    let p : Configuration S r := ⟨fun i => affineComplexPoint S.structureMap U (ρ i), by
      intro i j hij
      apply hρ
      exact affineComplexPoint_image_injective S.structureMap U hij⟩
    exact ⟨W,⟨p,hρW⟩,fun q hq => hW q.val hq⟩
  choose W hmem hTest using hW
  let V (a : ℕ × ℕ) : (surfacePower S r).left.Opens :=
    if h : Good a then W a h else ⊤
  let Z : ℕ → Set (Configuration S r) := fun n =>
    {p | tupleImage S r p.val ∉ V (Nat.unpair n)}
  have hZ (n : ℕ) : IsClosed (Z n) ∧ Z n ≠ Set.univ := by
    constructor
    · have hc : Continuous (fun p : Configuration S r => tupleImage S r p.val) := by
        change @Continuous _ _ (TopologicalSpace.induced Subtype.val
          (TopologicalSpace.induced (tupleImage S r) inferInstance)) _ _
        rw [induced_compose]
        exact continuous_induced_dom
      exact ((V (Nat.unpair n)).isOpen.preimage hc).isClosed_compl
    · intro heq
      by_cases h : Good (Nat.unpair n)
      · obtain ⟨p,hp⟩ := hmem _ h
        have hpZ : p ∈ Z n := heq ▸ Set.mem_univ p
        exact hpZ (by simpa [V,h] using hp)
      · have : IsIntegral (Over.mk S.structureMap).left := S.integral
        have : SmoothOfRelativeDimension 2 (Over.mk S.structureMap).hom := S.smooth
        obtain ⟨q,hq⟩ := exists_distinct_rational_tuple (Over.mk S.structureMap) 2
          (by norm_num) r
        let p : Configuration S r := ⟨q,hq⟩
        have hpZ : p ∈ Z n := heq ▸ Set.mem_univ p
        exact hpZ (by simp [V,h])
  refine ⟨Z,hZ, surface_configuration_outside_countable_closed S r Z
    (fun n => (hZ n).1) (fun n => (hZ n).2),?_⟩
  intro p hp k m hk hm hkm
  have hab : Good (k,m) := ⟨hk,hm,hkm⟩
  have hpV : tupleImage S r p.val ∈ V (k,m) := by
    have HH := hp (Nat.pair k m)
    simpa only [Z,Nat.unpair_pair,Set.mem_ofPred_eq,not_not] using HH
  exact hTest (k,m) hab p (by simpa [V,hab] using hpV)
end
end MaximalSeshadri.Geometry

end

end OAI
