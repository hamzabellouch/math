import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.AssemblyEndpointNormLe
import OAI.MeasureTheory.FalconerCompletion.Angular.TwoProfileOuterAngularBound
import OAI.MeasureTheory.FalconerCompletion.Graphs.AssemblyPairMass
import OAI.MeasureTheory.FalconerCompletion.Recursion.AssemblyListsCard

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

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

theorem actual_two_profile_component_shell (hn : 1 ≤ n) (Ctest : ℝ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (chi beta sig kap eta : ℝ),
      0 < chi → 0 < beta → beta < min (chi/10) (1/10) →
      0 < kap → kap ≤ 1/1000 → 0 < sig → sig < kap/1000 →
      beta+(n+4:ℝ)*sig < chi/4 → 0 < eta →
      ∀ (Ψ : ℝ → ℝ), ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Ioo (1/4:ℝ) 4 →
        (∀ r, 0 ≤ Ψ r) → (∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) →
      ∀ (ψ : EuclideanSpace ℝ (Fin (n+1)) → ℂ), ContDiff ℝ ∞ ψ →
        (∀ w, ‖w‖=1 → ‖ψ w‖ ≤ 1) →
      ∀ (δ K : ℝ), 0 < δ → 0 < K → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (ρ ν : Measure (EuclideanSpace ℝ (Fin (n+1)))) (B₀ : ℕ) (m₁ m₂ : ℝ → ℝ),
        RegularizedProfileData ρ N B₀ ((n+1:ℝ)/2+chi) sig m₁ →
        RegularizedProfileData ν N B₀ ((n+1:ℝ)/2+chi) sig m₂ →
        ρ (treeCell [])=1 → ν (treeCell [])=1 →
      let e₁ : RecursiveEnvironmentND n := ⟨ρ,m₁,N,sourcePolicyBlock N kap,sourceSmoothingLevels sig kap,sig,Ctest⟩
      let e₂ : RecursiveEnvironmentND n := ⟨ν,m₂,N,sourcePolicyBlock N kap,sourceSmoothingLevels sig kap,sig,Ctest⟩
      let c := GraphLiteralSupport.CurrentFalconer.entryDepthND (fun j : Fin 2 => if j=0 then e₁.profile else e₂.profile) N beta
      ∀ (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ),
        MeasurableSet X → MeasurableSet Y → X ⊆ treeCell [] → Y ⊆ treeCell [] →
        Measurable f → Measurable g → (∀ x, ‖f x‖ ≤ 1) → (∀ x, ‖g x‖ ≤ 1) →
        (∀ x ∈ X, ∀ y ∈ Y, δ ≤ dist x y ∧ dist x y ≤ K) →
        (∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y),
          ψ =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
          ψ =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0)) →
      Integrable (fun r => ‖assemblyDistanceTransform e₁ e₂ c X Y f g r‖^2)
        (volume.restrict (Icc ((2:ℝ)^N/2) (2*(2:ℝ)^N))) ∧
      (∫ r in Icc ((2:ℝ)^N/2) (2*(2:ℝ)^N),
          ‖assemblyDistanceTransform e₁ e₂ c X Y f g r‖^2) ≤
        ((2:ℝ)^N)^(-beta+Cd*(kap+sig/kap)+eta)
 := by
  obtain ⟨Cd,hCd,hroot⟩ := actual_two_profile_outer_angular_bound hn Ctest
  refine ⟨Cd,hCd,?_⟩
  intro chi beta sig kap eta hchi hbeta hbetasm hkap hkap1 hsig hsigkap hsmall heta
    Ψ hΨ hsupp hΨ0 hΨ1 ψ hψ hψ1 δ K hδ hK
  obtain ⟨φ,hφ,hφeq,P,hP⟩ := assembly_bounded_cutoff ψ hψ
  have hφ1 : ∀ w, ‖w‖=1 → ‖φ w‖ ≤ 1 := by
    intro w hw
    rw [(hφeq w hw).eq_of_nhds]
    exact hψ1 w hw
  have hsig1 : sig ≤ 1 := by linarith only [hsigkap,hkap1]
  choose D hD hderiv using (fun m : ℕ => uniform_assemblyEndpoint_derivatives (n:=n) m)
  obtain ⟨J,hsh⟩ := Attempt4PrefixShell.source_weighted_shellND (ι:=PolicyDescriptor) (κ:=PolicyDescriptor)
    φ hφ 2 D sig (eta/4) 2 0 16 δ K hsig hsig1 hD (by positivity) hδ hK
  obtain ⟨N₁,hsh⟩ := Filter.eventually_atTop.mp hsh
  obtain ⟨M,hroot⟩ := hroot chi beta sig kap (eta/4) hchi hbeta hbetasm hkap hkap1 hsig hsigkap
    hsmall (by positivity) (prefixInverseVocabulary n J) (2*J) (2*J)
    (fun _ hL => prefixInverseVocabulary_budget J hL) Ψ hΨ hsupp hΨ0 hΨ1 φ hφ hφ1
  obtain ⟨N₂,hroot⟩ := hroot 1 zero_le_one
  obtain ⟨N₃,hconst⟩ := fixed_constant_absorbed (show 0<eta/2 by positivity) 2
  refine ⟨max 1000 (max N₁ (max N₂ N₃)),?_⟩
  intro N hN ρ ν B₀ m₁ m₂ hd₁ hd₂ hroot₁ hroot₂ e₁ e₂ c X Y f g hX hY hXroot hYroot hf hg hfn hgn hsep hcut
  let := hd₁.probability
  let := hd₂.probability
  have hNp : 0<N := by omega
  have hNR : 0<(N:ℝ) := by exact_mod_cast hNp
  have hq : 0<sourcePolicyBlock N kap := sourcePolicyBlock_pos hNp hkap
  have hentry := assembly_entry_estimates hn e₁ e₂ rfl (by change 1000≤N;omega)
    hd₁ hd₂ hchi hbeta (hbetasm.trans_le (min_le_right _ _)) hsmall hkap hkap1 rfl rfl
  have hcR : (c:ℝ)<(N:ℝ)/4 := hentry.2.1
  have hc : 2*c≤N := by
    have hh : (2*c:ℝ)≤N := by linarith only [hcR,hNR]
    exact_mod_cast hh
  have hcN : c≤N := by omega
  let S := assemblyDescriptorList e₁.profile e₁.N e₁.q c
  let T := assemblyDescriptorList e₂.profile e₂.N e₂.q c
  let R : ℝ := (2:ℝ)^N
  let G : ℝ := -beta+Cd*(kap+sig/kap)
  let BHF : ℝ := R^(G+eta/4)
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hRp : 0<R := by dsimp [R];positivity
  have hBHF : 0≤BHF := Real.rpow_nonneg hRp.le _
  have hM₁ : (((2:ℝ)^e₁.N)^(-e₁.mass 0))=1 := by
    change (((2:ℝ)^N)^(-m₁ 0))=1
    rw [hd₁.zero,neg_zero,Real.rpow_zero]
  have hM₂ : (((2:ℝ)^e₂.N)^(-e₂.mass 0))=1 := by
    change (((2:ℝ)^N)^(-m₂ 0))=1
    rw [hd₂.zero,neg_zero,Real.rpow_zero]
  have hmass : |((((2:ℝ)^e₁.N)^(-e₁.mass 0)*((2:ℝ)^e₂.N)^(-e₂.mass 0))⁻¹)| *
      ((ρ.restrict X).prod (ν.restrict Y)).real univ ≤ R^(0:ℝ) := by
    simpa only [hM₁,hM₂,one_mul,inv_one,abs_one,Real.rpow_zero] using assembly_pair_mass ρ ν X Y
  have hcompact : HasCompactSupport Ψ :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport Ψ) (hsupp.trans Ioo_subset_Icc_self)
  have hiΨ : Integrable (fun r => Ψ (r/(2:ℝ)^(N:ℝ))) := by
    simpa only [Real.rpow_natCast] using
      (hΨ.continuous.integrable_of_hasCompactSupport hcompact).comp_div (by positivity : (2:ℝ)^N≠0)
  have hcut' := assembly_cutoff_transfer ρ ν hX hY hδ
    (fun x hx y hy => (hsep x hx y hy).1) hφeq hcut
  choose BL BR hBL hBR using (fun p : PrefixAssignment n => assemblyInverse_bounds e₁ e₂ c hfn hgn p)
  have hHF : ∀ j≤J,∀ p∈Attempt4PrefixShell.inverseAngularTermsND j (S.disjSum T),∀ ξ : V,
      Attempt4PrefixShell.sourceAngularHFND (n+1) (Attempt4PrefixShell.canonicalSphereMeasureND V)
        0 (N:ℝ) Ψ φ
        (fun z => Attempt4PrefixShell.spatialEndpointTransformND 1 ρ X (((2:ℝ)^e₁.N)^(-e₁.mass 0))
          (assemblyInverseLeft e₁ c f p) (ξ,z))
        (fun z => Attempt4PrefixShell.spatialEndpointTransformND 1 ν Y (((2:ℝ)^e₂.N)^(-e₂.mass 0))
          (assemblyInverseRight e₂ c g p) (ξ,z)) ≤ BHF := by
    intro j hj p hp ξ
    rw [assembly_HF_transform e₁ e₂ c hX hY hXroot hYroot f g p ξ Ψ φ]
    have hbudget := (assemblyInverse_total S T j hp).trans (Nat.mul_le_mul_left 2 hj)
    apply hroot N (by omega) ρ ν B₀ m₁ m₂ hd₁ hd₂ hroot₁ hroot₂
      (prefixLeftWords p) (prefixRightWords p) (assemblySpatialFactor X f ξ) (assemblySpatialFactor Y g ξ)
      recursiveUnit recursiveUnit
      (assemblySpatialFactor_measurable hX hf ξ) (assemblySpatialFactor_measurable hY hg ξ)
      (assemblySpatialFactor_norm hfn ξ) (assemblySpatialFactor_norm hgn ξ)
      (fun b _ => prefixInverseVocabulary_mem J j hj _ hp (Sum.inl b))
      (fun b _ => prefixInverseVocabulary_mem J j hj _ hp (Sum.inr b))
      (by change (∑ b∈S,(prefixLeftWords p b).length)≤2*J;omega)
      (by change (∑ b∈T,(prefixRightWords p b).length)≤2*J;omega)
      (fun l _ w _ => recursiveUnit_jets l w) (fun l _ w _ => recursiveUnit_jets l w)
  have hreg₁ : 20*sig*(N:ℝ) ≤ (N:ℝ)-0 := by
    have hs : 20*sig ≤ 1 := by linarith only [hsigkap,hkap1]
    simpa only [sub_zero,one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hs hNR.le
  have hreg₂ : ((N/2:ℕ):ℝ) ≤ ((N:ℝ)-0)/2+sig*N := by
    have hh : ((N/2:ℕ):ℝ) ≤ (N:ℝ)/2 := by
      have hn : 2*(N/2)≤N := by omega
      have hn' : (2:ℝ)*(N/2:ℕ)≤N := by exact_mod_cast hn
      linarith only [hn']
    have := mul_nonneg hsig.le hNR.le
    linarith only [hh,this]
  have hFG : ∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y), ‖f z.1*conj (g z.2)‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro z
    rw [norm_mul,Complex.norm_conj]
    simpa only [one_mul] using mul_le_mul (hfn z.1) (hgn z.2) (norm_nonneg _) zero_le_one
  have hshell := hsh N (by omega) S T (assemblyEndpointSmooth e₁) (assemblyEndpointSmooth e₂) f g
    (fun b => sourceMaskScaleND (descriptorLength b) R sig)
    (fun b => sourceMaskScaleND (descriptorLength b) R sig)
    (assemblyLists_card e₁ e₂ (by change 1≤N;omega) rfl hq hq hcN) ρ ν X Y hX hY (N/2)
    (((2:ℝ)^e₁.N)^(-e₁.mass 0)) (((2:ℝ)^e₂.N)^(-e₂.mass 0)) 0 N
    hreg₁ hreg₂ (by linarith only [hNR]) hmass
    (fun b hb => assemblyDescriptor_scale e₁ hq hc hb)
    (fun b hb => assemblyDescriptor_scale e₂ hq hc hb)
    (fun x _ b _ w hw => assemblyEndpoint_norm_le e₁ x w b hw)
    (fun x _ b _ w hw => assemblyEndpoint_norm_le e₂ x w b hw)
    (fun x _ b _ j hj w _ => hderiv _ e₁ x b j hj w)
    (fun x _ b _ j hj w _ => hderiv _ e₂ x b j hj w)
    (by simpa only [Real.rpow_zero,mul_one] using hsep)
    hcut' hFG (assembly_pairMask_measurable e₁ e₂ c hf hg) P hP
    (fun _ => BL) (fun _ => BR)
    (fun _ _ p _ => assemblyInverseLeft_measurable e₁ c hf p)
    (fun _ _ p _ => assemblyInverseRight_measurable e₂ c hg p)
    (fun _ _ p _ x w => hBL p x w) (fun _ _ p _ x w => hBR p x w)
    Ψ hiΨ hΨ0 hΨ1 BHF hBHF (by simpa only [Real.rpow_zero,inv_one,assemblyInverseLeft,assemblyInverseRight,S,T,R,e₁,e₂] using hHF)
  have htarget : (∫ r in Icc ((2:ℝ)^N/2) (2*(2:ℝ)^N),
      ‖assemblyDistanceTransform e₁ e₂ c X Y f g r‖^2) ≤ R^(eta/4)*BHF+R^(-2:ℝ) := by
    simpa only [neg_zero,Real.rpow_zero,one_mul,Real.rpow_natCast,assemblyDistanceTransform]
      using hshell.2
  refine ⟨?_,htarget.trans ?_⟩
  · simpa only [Real.rpow_natCast,assemblyDistanceTransform] using hshell.1
  · have herr : (-2:ℝ) ≤ G+eta/2 := by
      have hb : beta<1/10 := hbetasm.trans_le (min_le_right _ _)
      have hp : 0≤Cd*(kap+sig/kap) := by positivity
      dsimp only [G]
      linarith only [hb,hp,heta]
    have htwo : (2:ℝ)≤R^(eta/2) := hconst N (by omega)
    calc
      R^(eta/4)*BHF+R^(-2:ℝ) = R^(G+eta/2)+R^(-2:ℝ) := by
        dsimp only [BHF]
        rw [←Real.rpow_add hRp]
        congr 2
        ring
      _ ≤ R^(G+eta/2)+R^(G+eta/2) := add_le_add le_rfl
        (Real.rpow_le_rpow_of_exponent_le hR herr)
      _ = 2*R^(G+eta/2) := by ring
      _ ≤ R^(eta/2)*R^(G+eta/2) := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hRp.le _)
      _ = R^(G+eta) := by rw [←Real.rpow_add hRp];congr 1;ring

end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
