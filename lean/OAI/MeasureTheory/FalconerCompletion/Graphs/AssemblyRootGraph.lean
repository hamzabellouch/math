import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Estimates.AssemblyInnerEnergyMem

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

lemma uniform_assembly_root_graph (Ctest : ℝ) {sig : ℝ} (hsig : 0<sig)
    (hsig1 : sig≤1/100) {J : ℕ} (hJ : 0<J)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W,L.length≤B)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ⊆Ioo (1/4:ℝ) 4)
    (hΨ0 : ∀ r,0≤Ψ r) (ψ : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hψ1 : ∀ w,‖w‖=1 → ‖ψ w‖≤1) :
    ∃ M : ℕ,∀ Cq : ℝ,0≤Cq → ∃ Cerr : ℝ,0≤Cerr ∧ ∃ N₀ : ℕ,
    ∀ e₁ e₂ : RecursiveEnvironmentND n,N₀≤e₁.N → e₂.N=e₁.N →
      e₁.sig=sig → e₂.sig=sig → e₁.C=Ctest → e₂.C=Ctest →
      e₁.J=J → e₂.J=J → 0<e₁.q → 0<e₂.q →
      ∀ B₀ s₁ s₂,RegularizedProfileData e₁.ρ e₁.N B₀ s₁ sig e₁.mass →
      RegularizedProfileData e₂.ρ e₂.N B₀ s₂ sig e₂.mass →
      e₁.ρ (treeCell [])=1 → e₂.ρ (treeCell [])=1 →
      ∀ c : ℕ,0<c → (c:ℝ)<(e₁.N:ℝ)/4 →
      ∀ (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
        Measurable f → Measurable g → (∀ x,‖f x‖≤1) → (∀ x,‖g x‖≤1) →
        (∀ b∈assemblyDescriptorList e₁.profile e₁.N e₁.q c,L₁ b∈W) →
        (∀ b∈assemblyDescriptorList e₂.profile e₂.N e₂.q c,L₂ b∈W) →
        (∑ b∈assemblyDescriptorList e₁.profile e₁.N e₁.q c,(L₁ b).length)≤total →
        (∑ b∈assemblyDescriptorList e₂.profile e₂.N e₂.q c,(L₂ b).length)≤total →
        (∀ j≤M,∀ w,‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
        (∀ j≤M,∀ w,‖w‖=1 → ‖iteratedFDeriv ℝ j P.1 w‖≤Cq) →
      assemblyRootEnergy e₁ e₂ c L₁ L₂ f g Q P Ψ ψ ≤
        ((2:ℝ)^e₁.N)^(-e₁.profile c-e₂.profile c+
          min (height e₁.profile 0 c) (height e₂.profile 0 c)+(Ctest+36*(n+1:ℝ)+5)*sig)*
        _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax e₁.ρ e₂.ρ 0 c e₁.N [] []
          (((2:ℝ)^e₁.N)^(-e₁.mass c)) (((2:ℝ)^e₂.N)^(-e₂.mass c)) Ψ
          (assemblySymbol e₁ c L₁ f Q) (assemblySymbol e₂ c L₂ g P)+
        Cerr*((2:ℝ)^e₁.N)^(-2:ℝ) := by
  let c₀ : ℝ := 1/(4*(n+2:ℝ))
  have hc₀ : 0<c₀ := by dsimp [c₀]; positivity
  have hcsmall : ((n+1:ℕ)+1:ℝ)*c₀≤1/2 := by
    have he : ((n+1:ℕ)+1:ℝ)*c₀=1/4 := by
      dsimp [c₀]; push_cast; field_simp; ring
    rw [he]; norm_num
  obtain ⟨M,C,hC,N₁,hgraph⟩ := _root_.OAI.CurrentFalconer.TreeND.graph_HF_finite_jet_estimate
    (d:=n+1) hsig hc₀ hcsmall (le_refl (0:ℝ)) 2
  obtain ⟨K,hK0,hK,hdK⟩ := _root_.OAI.CurrentFalconer.graph_fixed_radial_budget hΨ
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport Ψ) (hsupp.trans Ioo_subset_Icc_self)) M
  obtain ⟨Pcut,hPcut,hcut⟩ := _root_.OAI.CurrentFalconer.graph_fixed_angular_budget hψ M
  refine ⟨M,?_⟩
  intro Cq hCq
  obtain ⟨E,hE,hjets⟩ := uniform_assemblySymbol_jets W M B total hW hsig Cq hCq
  obtain ⟨N₂,hjets⟩ := Filter.eventually_atTop.mp hjets
  obtain ⟨N₃,himposes⟩ := uniform_assemblySymbol_imposes (n:=n) hsig hJ
  refine ⟨C*K*Pcut^2*E^4,by positivity,max N₁ (max N₂ N₃),?_⟩
  intro e₁ e₂ hN heN hs₁ hs₂ hC₁ hC₂ hJ₁ hJ₂ hq₁ hq₂ B₀ s₁ s₂ hd₁ hd₂ hroot₁ hroot₂
    c hcpos hc L₁ L₂ f g Q P hf hg hfn hgn hL₁ hL₂ ht₁ ht₂ hQ hP
  let := hd₁.probability
  let := hd₂.probability
  have hNc : (c:ℝ)≤e₁.N := by have := Nat.cast_nonneg (α:=ℝ) e₁.N; linarith only [hc,this]
  have hcN : c≤e₁.N := by exact_mod_cast hNc
  have hcN₂ : c≤e₂.N := by omega
  have h2c : 2*c≤e₁.N := by exact_mod_cast (show (2:ℝ)*c≤e₁.N by linarith only [hc,Nat.cast_nonneg (α:=ℝ) e₁.N])
  have h2c₂ : 2*c≤e₂.N := by omega
  have hlist₁ (b) (hb : b∈assemblyDescriptorList e₁.profile e₁.N e₁.q c) : descriptorLength b≤e₁.N/2 := by
    have hh := assemblyDescriptorList_length e₁.profile hq₁ h2c
    have hb' := Finset.le_sup (s:=assemblyDescriptorList e₁.profile e₁.N e₁.q c) (f:=descriptorLength) hb
    omega
  have hlist₂ (b) (hb : b∈assemblyDescriptorList e₂.profile e₂.N e₂.q c) : descriptorLength b≤e₁.N/2 := by
    have hh := assemblyDescriptorList_length e₂.profile hq₂ h2c₂
    have hb' := Finset.le_sup (s:=assemblyDescriptorList e₂.profile e₂.N e₂.q c) (f:=descriptorLength) hb
    omega
  have hj₁ := hjets e₁.N (by omega) e₁ rfl hs₁ hq₁ c (e₁.N/2) hcN hlist₁ L₁ f Q hf hfn hL₁ ht₁ hQ
  have hj₂ := hjets e₁.N (by omega) e₂ heN hs₂ hq₂ c (e₁.N/2) (by omega) hlist₂ L₂ g P hg hgn hL₂ ht₂ hP
  have hi₁ := himposes e₁ (by omega) hs₁ hJ₁ inferInstance hq₁ c hcN L₁ f Q
  have hi₂ := himposes e₂ (by omega) hs₂ hJ₂ inferInstance hq₂ c hcN₂ L₂ g P
  have hd₁' := (_root_.OAI.CurrentFalconer.TreeND.literal_regularizedProfileData_iff _ _ _ _ _ _).mp hd₁
  have hd₂' := (_root_.OAI.CurrentFalconer.TreeND.literal_regularizedProfileData_iff _ _ _ _ _ _).mp hd₂
  rw [heN] at hd₂'
  have hroot₁' : 0<e₁.ρ (_root_.OAI.CurrentFalconer.TreeND.treeCell []) := by
    have hr : 0<e₁.ρ (treeCell []) := by rw [hroot₁]; exact zero_lt_one
    simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hr
  have hroot₂' : 0<e₂.ρ (_root_.OAI.CurrentFalconer.TreeND.treeCell []) := by
    have hr : 0<e₂.ρ (treeCell []) := by rw [hroot₂]; exact zero_lt_one
    simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hr
  have hrange : (c:ℝ)≤(e₁.N:ℝ)-c+2*sig*e₁.N := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) e₁.N]
  have hL : ((e₁.N/2:ℕ):ℝ)≤(e₁.N:ℝ)-c+2*sig*e₁.N := by
    have hh : ((e₁.N/2:ℕ):ℝ)≤(e₁.N:ℝ)/2 := by simpa using (Nat.cast_div_le (α:=ℝ) (m:=e₁.N) (n:=2))
    nlinarith [Nat.cast_nonneg (α:=ℝ) e₁.N]
  have hgap : 10*sig*e₁.N≤(e₁.N:ℝ)-c := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) e₁.N]
  have hi₁' := hi₁
  have hi₂' := hi₂
  simp only [hC₁] at hi₁'
  simp only [RecursiveEnvironmentND.profile,heN,hC₂] at hi₂'
  have hh := hgraph e₁.N (by omega) e₁.ρ e₂.ρ B₀ s₁ s₂ e₁.mass e₂.mass hd₁' hd₂'
    0 c e₁.N (e₁.N/2:ℕ) Ctest K E Pcut J 1 1 0 0 [] [] Ψ ψ
    (assemblySymbol e₁ c L₁ f Q) (assemblySymbol e₂ c L₂ g P)
    hcpos hNc le_rfl (by simpa using hrange) hL hgap (Nat.zero_le _) (Nat.zero_le _) hcpos hcpos
    (by norm_num only [Nat.cast_zero,zero_add]; positivity) (by norm_num only [Nat.cast_zero,zero_add]; positivity) hJ hJ hJ
    (by simp [_root_.OAI.CurrentFalconer.TreeND.mem_dyadicPaths])
    (by simp [_root_.OAI.CurrentFalconer.TreeND.mem_dyadicPaths])
    hroot₁' hroot₂' (by simp) hΨ (hsupp.trans Ioo_subset_Icc_self) hΨ0 hK (hdK M le_rfl) hK0
    (by simpa only [Real.rpow_natCast] using hj₁)
    (by simpa only [Real.rpow_natCast] using hj₂)
    hPcut hψ hψ1 hcut hi₁' hi₂'
  have hz₁ := assembly_profile_zero e₁ hd₁
  have hz₂ := assembly_profile_zero e₂ hd₂
  change _root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e₁.mass e₁.N 0=0 at hz₁
  change _root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e₂.mass e₂.N 0=0 at hz₂
  rw [heN] at hz₂
  simp only [hz₁,hz₂,sub_zero,Nat.cast_zero,Nat.cast_add,Nat.cast_one] at hh
  have hpow : -(e₁.profile c+e₂.profile c)+min (height e₁.profile 0 c) (height e₂.profile 0 c)+
      (Ctest+36*(n+1:ℝ)+5)*sig = -e₁.profile c-e₂.profile c+min (height e₁.profile 0 c) (height e₂.profile 0 c)+
      (Ctest+36*(n+1:ℝ)+5)*sig := by ring
  have hp₁ : _root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e₁.mass e₁.N=e₁.profile := rfl
  have hp₂ : _root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e₂.mass e₁.N=e₂.profile := by
    rw [←heN]; rfl
  simp only [hp₁,hp₂,hpow] at hh
  simpa only [assemblyRootEnergy,heN,_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hh
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
