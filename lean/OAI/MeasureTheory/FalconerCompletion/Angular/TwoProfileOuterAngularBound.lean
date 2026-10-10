import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.AssemblyRootGraph

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

theorem actual_two_profile_outer_angular_bound (hn : 1≤n) (Ctest : ℝ) :
    ∃ Cd : ℝ,0≤Cd ∧ ∀ (chi beta sig kap eta : ℝ),
      0<chi → 0<beta → beta < min (chi/10) (1/10) →
      0<kap → kap≤1/1000 → 0<sig → sig<kap/1000 →
      beta+(n+4:ℝ)*sig<chi/4 → 0<eta →
      ∀ (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
        (B total : ℕ), (∀ L∈W,L.length≤B) →
      ∀ (Ψ : ℝ → ℝ), ContDiff ℝ ∞ Ψ → tsupport Ψ⊆Ioo (1/4:ℝ) 4 →
        (∀ r,0≤Ψ r) → (∀ r∈Icc (1/2:ℝ) 2,1≤Ψ r) →
      ∀ (ψ : EuclideanSpace ℝ (Fin (n+1)) → ℂ), ContDiff ℝ ∞ ψ →
        (∀ w,‖w‖=1 → ‖ψ w‖≤1) →
      ∃ M : ℕ,∀ Cq : ℝ,0≤Cq → ∃ N₀ : ℕ,∀ N≥N₀,
      ∀ (ρ ν : Measure (EuclideanSpace ℝ (Fin (n+1)))) (B₀ : ℕ) (m₁ m₂ : ℝ → ℝ),
        RegularizedProfileData ρ N B₀ ((n+1:ℝ)/2+chi) sig m₁ →
        RegularizedProfileData ν N B₀ ((n+1:ℝ)/2+chi) sig m₂ →
        ρ (treeCell [])=1 → ν (treeCell [])=1 →
      let e₁ : RecursiveEnvironmentND n := ⟨ρ,m₁,N,sourcePolicyBlock N kap,sourceSmoothingLevels sig kap,sig,Ctest⟩
      let e₂ : RecursiveEnvironmentND n := ⟨ν,m₂,N,sourcePolicyBlock N kap,sourceSmoothingLevels sig kap,sig,Ctest⟩
      let c := GraphLiteralSupport.CurrentFalconer.entryDepthND (fun j : Fin 2 => if j=0 then e₁.profile else e₂.profile) N beta
      ∀ (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
        Measurable f → Measurable g → (∀ x,‖f x‖≤1) → (∀ x,‖g x‖≤1) →
        (∀ b∈assemblyDescriptorList e₁.profile N e₁.q c,L₁ b∈W) →
        (∀ b∈assemblyDescriptorList e₂.profile N e₂.q c,L₂ b∈W) →
        (∑ b∈assemblyDescriptorList e₁.profile N e₁.q c,(L₁ b).length)≤total →
        (∑ b∈assemblyDescriptorList e₂.profile N e₂.q c,(L₂ b).length)≤total →
        (∀ j≤M,∀ w,‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
        (∀ j≤M,∀ w,‖w‖=1 → ‖iteratedFDeriv ℝ j P.1 w‖≤Cq) →
      assemblyRootEnergy e₁ e₂ c L₁ L₂ f g Q P Ψ ψ ≤
        ((2:ℝ)^N)^(-beta+Cd*(kap+sig/kap)+eta)
 := by
  let Dloss : ℝ := |Ctest|+100*(n+2:ℝ)
  let Cd : ℝ := profileDimLoss n Ctest+Dloss
  have hDloss : 0≤Dloss := by dsimp [Dloss]; positivity
  have hCd : 0≤Cd := add_nonneg (profileDimLoss_nonneg n Ctest) hDloss
  refine ⟨Cd,hCd,?_⟩
  intro chi beta sig kap eta hchi hbeta hbetasm hkap hkap1 hsig hsigkap hsmall heta
    W B total hW Ψ hΨ hsupp hΨ0 hΨ1 ψ hψ hψ1
  have hbeta1 : beta<1/10 := hbetasm.trans_le (min_le_right _ _)
  have hkap1' : kap≤1 := by linarith only [hkap1]
  have hsig1 : sig≤1/100 := by linarith only [hsigkap,hkap1]
  obtain ⟨D,hD,N₁,hN₁,hchild⟩ := uniform_assembly_child_max hn Ctest hsig hkap hkap1' hsigkap
    (show 0<eta/4 by positivity) W B total hW Ψ hΨ hsupp hΨ0 hΨ1
  obtain ⟨M,hgraph⟩ := uniform_assembly_root_graph Ctest hsig hsig1
    (sourceSmoothingLevels_pos hsig hkap) W B total hW Ψ hΨ hsupp hΨ0 ψ hψ hψ1
  refine ⟨M,?_⟩
  intro Cq hCq
  obtain ⟨Cerr,hCerr,N₂,hgraph⟩ := hgraph Cq hCq
  obtain ⟨N₃,hconst⟩ := fixed_constant_absorbed (show 0<eta/2 by positivity) ((Cq*D^B)^4+Cerr)
  obtain ⟨N₄,hN₄⟩ := exists_nat_ge ((n+1:ℝ)/(eta/4))
  obtain ⟨N₅,hN₅⟩ := exists_nat_ge ((n+1:ℝ)/beta)
  refine ⟨max 1000 (max N₁ (max N₂ (max N₃ (max N₄ N₅)))),?_⟩
  intro N hN ρ ν B₀ m₁ m₂ hd₁ hd₂ hroot₁ hroot₂ e₁ e₂ c
    L₁ L₂ f g Q P hf hg hfn hgn hL₁ hL₂ ht₁ ht₂ hQ hP
  have hNp : 0<N := by omega
  have hNR : 0<(N:ℝ) := by exact_mod_cast hNp
  have hq : 0<sourcePolicyBlock N kap := sourcePolicyBlock_pos hNp hkap
  have heN : e₂.N=e₁.N := rfl
  have hentry := assembly_entry_estimates hn e₁ e₂ heN (by change 1000≤N; omega)
    hd₁ hd₂ hchi hbeta hbeta1 hsmall hkap hkap1 rfl rfl
  change ⌊beta*(N:ℝ)/(n+1:ℝ)⌋₊≤c ∧ (c:ℝ)<(N:ℝ)/4 ∧ c+100*e₁.q<N ∧ _ at hentry
  have hfloor : 1≤⌊beta*(N:ℝ)/(n+1:ℝ)⌋₊ := by
    apply (Nat.le_floor_iff (by positivity : 0≤beta*(N:ℝ)/(n+1:ℝ))).mpr
    have hN5 : (N₅:ℝ)≤N := by exact_mod_cast (show N₅≤N by omega)
    have hh := (div_le_iff₀ hbeta).mp (hN₅.trans hN5)
    apply (le_div_iff₀ (by positivity : 0<(n+1:ℝ))).mpr
    norm_num
    nlinarith only [hh]
  have hcpos : 0<c := by omega
  have hQ0 : ∀ w,‖w‖=1 → ‖Q.1 w‖≤Cq := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero] using hQ 0 (Nat.zero_le _) w hw
  have hP0 : ∀ w,‖w‖=1 → ‖P.1 w‖≤Cq := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero] using hP 0 (Nat.zero_le _) w hw
  have hch := hchild e₁ e₂ (by change N₁≤N;omega) rfl rfl rfl rfl rfl rfl rfl rfl rfl
    B₀ ((n+1:ℝ)/2+chi) ((n+1:ℝ)/2+chi) hd₁ hd₂ c hentry.2.2.1
    L₁ L₂ f g Q P Cq hf hg hfn hgn hL₁ hL₂ ht₁ ht₂ hQ0 hP0
  have hgr := hgraph e₁ e₂ (by change N₂≤N;omega) rfl rfl rfl rfl rfl rfl rfl hq hq
    B₀ ((n+1:ℝ)/2+chi) ((n+1:ℝ)/2+chi) hd₁ hd₂ hroot₁ hroot₂
    c hcpos hentry.2.1 L₁ L₂ f g Q P hf hg hfn hgn hL₁ hL₂ ht₁ ht₂ hQ hP
  let R : ℝ := (2:ℝ)^N
  let u : ℝ := -e₁.profile c-e₂.profile c+min (height e₁.profile 0 c) (height e₂.profile 0 c)+
    (Ctest+36*(n+1:ℝ)+5)*sig
  let v : ℝ := (assemblyProfileExponent e₁ c+assemblyProfileExponent e₂ c)/2+
    profileDimLoss n Ctest*(kap+sig/kap)+eta/4
  let G : ℝ := -beta+Cd*(kap+sig/kap)
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hRp : 0<R := by dsimp [R]; positivity
  have hcorr : (n+1:ℝ)/(N:ℝ)≤eta/4 := by
    apply (div_le_iff₀ hNR).mpr
    have hN4 : (N₄:ℝ)≤N := by exact_mod_cast (show N₄≤N by omega)
    have hh := (div_le_iff₀ (show 0<eta/4 by positivity)).mp (hN₄.trans hN4)
    nlinarith only [hh]
  have hsigloss : sig≤kap+sig/kap := by
    have hh : sig ≤ sig/kap := by
      apply (le_div_iff₀ hkap).mpr
      nlinarith only [hkap1',hsig]
    linarith only [hh,hkap]
  have hcoefficient : (n+4:ℝ)+Ctest+36*(n+1:ℝ)+5≤Dloss := by
    have hn0 := Nat.cast_nonneg (α:=ℝ) n
    have hC := le_abs_self Ctest
    dsimp only [Dloss]
    linarith only [hn0,hC]
  have hcf : ((n+4:ℝ)+Ctest+36*(n+1:ℝ)+5)*sig≤Dloss*(kap+sig/kap) :=
    (mul_le_mul_of_nonneg_right hcoefficient hsig.le).trans (mul_le_mul_of_nonneg_left hsigloss hDloss)
  have huv : u+v≤G+eta/2 := by
    have he := hentry.2.2.2
    change -e₁.profile c-e₂.profile c+min (height e₁.profile 0 c) (height e₂.profile 0 c)+
      (assemblyProfileExponent e₁ c+assemblyProfileExponent e₂ c)/2≤-beta+(n+4:ℝ)*sig+(n+1:ℝ)/N at he
    dsimp only [u,v,G,Cd]
    nlinarith only [he,hcorr,hcf]
  have herr : (-2:ℝ)≤G+eta/2 := by
    have hpos : 0≤Cd*(kap+sig/kap) := mul_nonneg hCd (by positivity)
    dsimp only [G]
    linarith only [hbeta1,hpos,heta]
  have hnum : (Cq*D^B)^4+Cerr≤R^(eta/2) := hconst N (by omega)
  change assemblyRootEnergy e₁ e₂ c L₁ L₂ f g Q P Ψ ψ≤R^(G+eta)
  change assemblyRootEnergy e₁ e₂ c L₁ L₂ f g Q P Ψ ψ≤R^u*_+Cerr*R^(-2:ℝ) at hgr
  change _≤(Cq*D^B)^4*R^v at hch
  calc
    assemblyRootEnergy e₁ e₂ c L₁ L₂ f g Q P Ψ ψ
      ≤R^u*((Cq*D^B)^4*R^v)+Cerr*R^(-2:ℝ) :=
      hgr.trans (add_le_add (mul_le_mul_of_nonneg_left hch (Real.rpow_nonneg hRp.le _)) le_rfl)
    _=(Cq*D^B)^4*R^(u+v)+Cerr*R^(-2:ℝ) := by rw [Real.rpow_add hRp u v]; ring
    _≤(Cq*D^B)^4*R^(G+eta/2)+Cerr*R^(G+eta/2) :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR huv) (by positivity))
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR herr) hCerr)
    _=((Cq*D^B)^4+Cerr)*R^(G+eta/2) := by ring
    _≤R^(eta/2)*R^(G+eta/2) := mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg hRp.le _)
    _=R^(G+eta) := by rw [←Real.rpow_add hRp]; congr 1; ring

end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
