import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualDirectBuffer
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy
import OAI.MeasureTheory.Falconer.Recursion.Potential
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveSuffixRule

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

theorem uniform_recursive_rules (hn : 1≤n) {sig kap eps T : ℝ}
    (hsig : 0<sig) (hkap : 0<kap) (hkap1 : kap≤1) (hgap : sig<kap/1000)
    (heps : 0<eps) (hT : 0<T) (ell : ℕ) (hK : 1000*(n+2:ℝ)<(2:ℝ)^ell)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ⊆Ioo (1/4:ℝ) 4)
    (hΨ0 : ∀ r,0≤Ψ r) (hΨ1 : ∀ r∈Icc (1/2:ℝ) 2,1≤Ψ r) (hiΨ : Integrable Ψ) :
    ∃ Order : ℕ,∀ (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
      (B total : ℕ), (∀ L∈W,L.length≤B) → prefixInverseVocabulary n Order⊆W → 2*Order≤total →
    ∃ H E : ℝ,1≤H ∧ 0≤E ∧ ∃ N₀ : ℕ,0<N₀ ∧ ∀ e : RecursiveEnvironmentND n,
      N₀≤e.N → e.sig=sig → e.q=sourcePolicyBlock e.N kap → e.J=sourceSmoothingLevels sig kap →
      ∀ B₀ s,RegularizedProfileData e.ρ e.N B₀ s sig e.mass →
      ∀ state : BranchState,state.Valid e.N sig → state.index<e.J → state.start+100*e.q<state.finish →
      ∀ M : ℝ,0≤M → ((2:ℝ)^e.N)^(4*(n+2:ℝ)*sig)≤M →
      (∀ u l,DimensionalPolicy.BranchStep e.profile e.N e.q (ell+2) sig state l u →
        ∀ x,e.energies ((2:ℝ)^ell) W total Ψ u x →
        ((2:ℝ)^e.N)^(DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps state l u)*x≤M) →
      ∀ x,e.energies ((2:ℝ)^ell) W total Ψ state x →
        x≤H*((e.N:ℝ)+1)*M+E*((2:ℝ)^e.N)^(-T) := by
  have hsig1 : sig≤1 := by linarith
  have hK' : 32*(n+2:ℝ)≤(2:ℝ)^ell := by nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤(n:ℝ))]
  have hJ : 0<sourceSmoothingLevels sig kap := sourceSmoothingLevels_pos hsig hkap
  obtain ⟨Order,hpref⟩ := uniform_recursive_prefix_rule hn hsig hsig1 hK' _ hJ eps T heps hT Ψ hΨ hsupp hΨ0 hΨ1 hiΨ
  obtain ⟨Hs,hHs,Ns,hsuff⟩ := uniform_recursive_suffix_rule (n:=n) hsig hJ
  obtain ⟨Nc,hNc,hceil⟩ := uniform_source_ceiling_slack hsig hgap
  refine ⟨Order,?_⟩
  intro W B total hW hV htotal
  obtain ⟨Hp,Ep,hHp,hEp,Np,hpref⟩ := hpref W B total hW hV htotal
  obtain ⟨Hd,Ed,hHd,hEd,Nd,hdir⟩ := uniform_recursive_direct_rule hsig T _ hJ Ψ hΨ hsupp hΨ0 hiΨ W B total hW
  obtain ⟨Hf,hHf,Nf,hnf⟩ := uniform_recursive_near_far_rule Ψ hΨ hsupp hΨ0 hsig hsig1 W B total hW hJ T ell hK'
  let H := 1+Hs+Hp+Hd+Hf
  let E := 1+Ep+Ed
  have hH : 1≤H := by dsimp only [H]; linarith
  have hE : 0≤E := by dsimp only [E]; positivity
  refine ⟨H,E,hH,hE,max Nc (max Ns (max Np (max Nd Nf))),by omega,?_⟩
  intro e hN he hqeq hJe B₀ s hd state hv hi hw M hM hfloor hchildren x hx
  let := hd.probability
  have hq : 0<e.q := by rw [hqeq]; exact sourcePolicyBlock_pos (by omega) hkap
  have hcl := hceil e.N (by omega)
  have hslack10 : 10*sig*(e.N:ℝ)≤e.q := by
    rw [hqeq]
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hcl.1.le)
  have hslack : sig*(e.N:ℝ)≤e.q := by nlinarith [mul_nonneg hsig.le (Nat.cast_nonneg e.N : (0:ℝ)≤(e.N:ℝ))]
  have hcl' : ⌈10*sig*(e.N:ℝ)⌉₊<e.q := by simpa only [hqeq] using hcl.1
  have hN0 : 0≤(e.N:ℝ) := Nat.cast_nonneg e.N
  have hpow : 0≤((2:ℝ)^e.N)^(-T) := by positivity
  have hfH : ∀ A : ℝ,0≤A → A≤H → A*M≤H*((e.N:ℝ)+1)*M := by
    intro A hA hAH
    have h₁ := mul_le_mul_of_nonneg_right hAH hM
    have h₂ : 0≤H*(e.N:ℝ)*M := by positivity
    nlinarith only [h₁,h₂]
  have hfHE : ∀ A F : ℝ,0≤A → A≤H → F≤E →
      A*((e.N:ℝ)+1)*M+F*((2:ℝ)^e.N)^(-T)≤H*((e.N:ℝ)+1)*M+E*((2:ℝ)^e.N)^(-T) := by
    intro A F hA hAH hFE
    exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAH (by positivity)) hM)
      (mul_le_mul_of_nonneg_right hFE hpow)
  cases state with
  | D a t i =>
    by_cases hp : 2*policyDepth e.profile e.N e.q a t≤a+t
    · have hh := hpref e (by omega) he hJe B₀ s hd hq hslack a t i (ell+2) hi hv.2 hw hp M hM hfloor hchildren x hx
      exact hh.trans (hfHE Hp Ep hHp (by dsimp only [H]; linarith) (by dsimp only [E]; linarith))
    · have hh := hsuff e (by omega) he hJe (show IsFiniteMeasure e.ρ from inferInstance) hq _ hK W total (ell+2) a t i Ψ eps heps.le hi hv.2 hw (by omega) M
        (fun y hy => hchildren _ _ (.suffix hw (by omega)) y hy) x hx
      exact hh.trans ((hfH Hs hHs (by dsimp only [H]; linarith)).trans (le_add_of_nonneg_right (mul_nonneg hE hpow)))
  | H a₀ t₀ a v i =>
    by_cases hnear : a<(BranchState.H a₀ t₀ a v i).nearDepth e.profile e.N e.q sig
    · have hh := hnf e (by omega) he hJe B₀ s hd hq a₀ t₀ a v i hv hw hnear eps M heps.le hM hchildren x hx
      have hb := hfHE Hf 1 hHf (by dsimp only [H]; linarith) (by dsimp only [E]; linarith)
      simpa only [one_mul] using hh.trans (by simpa only [one_mul] using hb)
    · have hh := hdir e (by omega) he hJe B₀ s hd hq hcl' hslack hslack10 a₀ t₀ a v i (ell+2) hi hv hw (by omega) _ eps M heps.le hM hchildren x hx
      exact hh.trans (add_le_add (hfH Hd (by linarith) (by dsimp only [H]; linarith))
        (mul_le_mul_of_nonneg_right (by dsimp only [E]; linarith) hpow))
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

lemma recursiveLoss_dim_self (n : ℕ) (C : ℝ) : 4*(n+2:ℝ)≤recursiveLoss n C := by
  unfold recursiveLoss
  nlinarith [abs_nonneg C,(Nat.cast_nonneg n : (0:ℝ)≤(n:ℝ))]

lemma RegularizedProfileData.environment_lipschitz (e : RecursiveEnvironmentND n)
    {B : ℕ} {s sig : ℝ} (h : RegularizedProfileData e.ρ e.N B s sig e.mass) :
    DimensionalPolicy.ProfileLipschitzND e.profile e.N ((n+1:ℝ)/2) := by
  intro i hi j hj
  have hh := h.adjusted (j:ℝ) (i:ℝ) (Nat.cast_nonneg _) (Nat.cast_le.mpr hj)
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hi)
  simpa only [RecursiveEnvironmentND.profile,adjustedProfile,Nat.cast_add,Nat.cast_one] using hh

lemma profile_exponent_lowerND {A : ℕ → ℝ} {N a t Q : ℕ} {L : ℝ}
    (hA : DimensionalPolicy.ProfileLipschitzND A N L) (hN : 0<N) (hL : 0≤L)
    (hQ : 0<Q) (hw : a+Q≤t) (ht : t≤N) :
    -2*L≤2*A a-potential A a t Q := by
  have ha : a≤t := by omega
  have hpot := DimensionalPolicy.potential_le_final_startND hN hL hA hQ hw ht (le_refl a) ha
  have hQN : (Q:ℝ)≤N := Nat.cast_le.mpr (by omega)
  have hfrac : (Q:ℝ)/(N:ℝ)≤1 := (div_le_one (Nat.cast_pos.mpr hN)).mpr hQN
  have hh := mul_le_mul_of_nonneg_left hfrac (show 0≤2*L by positivity)
  rw [←mul_div_assoc] at hh
  linarith

theorem recursion_overhead_absorptionND (D : ℕ) (H E : ℝ)
    {eta theta B : ℝ} (heta : 0<eta) (htheta : theta≤eta/4)
    (hH : 1≤H) (hE : 0≤E) :
    ∃ N₀ : ℕ,∀ N≥N₀,∀ g : ℝ,-B≤g →
      (H*((N:ℝ)+1)+1)^(D+1)*(H*((2:ℝ)^N)^g+E*((2:ℝ)^N)^(-B))≤
      ((2:ℝ)^N)^(g+eta-theta) := by
  obtain ⟨N₁,h₁⟩ := fixed_polynomial_subpower (d:=2) (2*(D+1)+2) (show 0<eta-theta by linarith)
  refine ⟨max 2 (max N₁ (Nat.ceil (max H E))),?_⟩
  intro N hN g hg
  have hNR : 2≤(N:ℝ) := Nat.cast_le.mpr (show 2≤N by omega)
  have hCE : max H E≤(N:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
  have hHN : H≤(N:ℝ) := (le_max_left _ _).trans hCE
  have hEN : E≤(N:ℝ) := (le_max_right _ _).trans hCE
  have hp : 0<((2:ℝ)^N)^g := by positivity
  have herr : ((2:ℝ)^N)^(-B)≤((2:ℝ)^N)^g :=
    Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hg
  have hsum : H*((2:ℝ)^N)^g+E*((2:ℝ)^N)^(-B)≤(2*(N:ℝ))*((2:ℝ)^N)^g := by
    have hh := mul_le_mul_of_nonneg_left herr hE
    have hh₁ := mul_le_mul_of_nonneg_right hHN hp.le
    have hh₂ := mul_le_mul_of_nonneg_right hEN hp.le
    linarith only [hh,hh₁,hh₂]
  have hbase : H*((N:ℝ)+1)+1≤(4*(N:ℝ)+1)^2 := by
    have hh := mul_le_mul_of_nonneg_right hHN (show 0≤(N:ℝ)+1 by linarith)
    nlinarith only [hh,hNR]
  have hpoly : (H*((N:ℝ)+1)+1)^(D+1)*(2*(N:ℝ))≤(4*(N:ℝ)+1)^(2*(D+1)+2) := by
    calc
      _≤((4*(N:ℝ)+1)^2)^(D+1)*(2*(N:ℝ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase _) (by positivity)
      _≤((4*(N:ℝ)+1)^2)^(D+1)*(4*(N:ℝ)+1)^2 :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hNR]) (by positivity)
      _=_ := by rw [←pow_mul,←pow_add]
  calc
    _≤(H*((N:ℝ)+1)+1)^(D+1)*((2*(N:ℝ))*((2:ℝ)^N)^g) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _≤(4*(N:ℝ)+1)^(2*(D+1)+2)*((2:ℝ)^N)^g := by
      rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hpoly hp.le
    _≤((2:ℝ)^N)^(eta-theta)*((2:ℝ)^N)^g :=
      mul_le_mul_of_nonneg_right (by have hh := h₁ N (by omega); norm_num at hh; exact hh) hp.le
    _=_ := by rw [←Real.rpow_add (by positivity : 0<(2:ℝ)^N)]; congr 1; ring
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
