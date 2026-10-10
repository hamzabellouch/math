import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Estimates.Assembly
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.Potential
import OAI.MeasureTheory.FalconerCompletion.Estimates.SourceWeightedErrorGeneral
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveRules

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

theorem uniform_recursive_profile_with_overhead (hn : 1≤n) (Ctest : ℝ)
    {sig kap theta : ℝ} (hsig : 0<sig) (hkap : 0<kap) (hkap1 : kap≤1)
    (hgap : sig<kap/1000)
    (htheta : 0<theta) (htheta1 : theta≤1) (ell : ℕ) (hK : 1000*(n+2:ℝ)<(2:ℝ)^ell)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ⊆Ioo (1/4:ℝ) 4)
    (hΨ0 : ∀ r,0≤Ψ r) (hΨ1 : ∀ r∈Icc (1/2:ℝ) 2,1≤Ψ r) (hiΨ : Integrable Ψ) :
    ∃ Order : ℕ,∀ (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
      (B total : ℕ), (∀ L∈W,L.length≤B) → prefixInverseVocabulary n Order⊆W → 2*Order≤total →
    ∃ H E : ℝ,1≤H ∧ 0≤E ∧ ∃ N₀ : ℕ,0<N₀ ∧ ∀ e : RecursiveEnvironmentND n,
      N₀≤e.N → e.sig=sig → e.C=Ctest → e.q=sourcePolicyBlock e.N kap → e.J=sourceSmoothingLevels sig kap →
      ∀ B₀ s,RegularizedProfileData e.ρ e.N B₀ s sig e.mass →
      ∀ root : BranchState,root.Valid e.N sig → root.index=0 → root.start+10*e.q≤root.finish →
      ∀ x,e.energies ((2:ℝ)^ell) W total Ψ root x →
      x≤(H*((e.N:ℝ)+1)+1)^(⌈20/kap+1/sig⌉₊+1)*
        (H*((2:ℝ)^e.N)^(2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)+
          500*((n+1:ℝ)/2)*kap+200*recursiveLoss n Ctest*sig/kap+theta)+
          E*((2:ℝ)^e.N)^(-4*(n+2:ℝ))) := by
  let C := recursiveLoss n Ctest
  let L : ℝ := (n+1:ℝ)/2
  have hC : 0≤C := (recursiveLoss_pos n Ctest).le
  have hL : 0≤L := by dsimp only [L]; positivity
  let Dstar : ℝ := 1+20/kap+1/sig
  have hDstar : 1≤Dstar := by
    have hk : 0≤20/kap := by positivity
    have hs : 0≤1/sig := by positivity
    dsimp only [Dstar]
    linarith
  let eps := theta/(2*Dstar)
  have heps : 0<eps := by dsimp only [eps]; positivity
  have heps1 : eps≤1 := by
    apply (div_le_iff₀ (show 0<2*Dstar by positivity)).mpr
    linarith
  let T : ℝ := (3*L+C*(sig+sig)+1)*(20/kap+1/sig)+4*(n+2:ℝ)+1
  have hT : 0<T := by dsimp only [T]; positivity
  obtain ⟨Order,hrules⟩ := uniform_recursive_rules hn hsig hkap hkap1 hgap heps hT ell hK Ψ hΨ hsupp hΨ0 hΨ1 hiΨ
  obtain ⟨Nv,_,hvalid⟩ := DimensionalPolicy.uniform_branch_successor_validity (ell+2) hsig hkap hgap
  obtain ⟨Nd,_,hdepth⟩ := DimensionalPolicy.uniform_source_branch_depth (ell+2) hsig hkap hkap1 hgap
  obtain ⟨Nw,_,hweight⟩ := DimensionalPolicy.uniform_source_weighted_terminalND (ell+2) hsig.le hsig hkap hkap1 hgap htheta hL hC
  obtain ⟨Ne,_,herror⟩ := DimensionalPolicy.uniform_source_weighted_error_generalND (ell+2) hsig hkap hkap1 hgap hL hC heps1
    (show (3*L+C*(sig+sig)+1)*(20/kap+1/sig)+4*(n+2:ℝ)≤T by dsimp only [T]; linarith)
  refine ⟨Order,?_⟩
  intro W B total hW hV htotal
  obtain ⟨Hr,E,hHr,hE,Nr,hNr,hrules⟩ := hrules W B total hW hV htotal
  obtain ⟨Ht,hHt,Nt,hNt,hterminal⟩ := uniform_recursive_terminal hiΨ W B total hW hsig
  let H := max Hr Ht
  have hH : 1≤H := hHr.trans (le_max_left _ _)
  refine ⟨H,E,hH,hE,max Nr (max Nt (max Nv (max Nd (max Nw Ne)))),by omega,?_⟩
  intro e hN he hCe hqeq hJe B₀ s hd root hv hi hw x hx
  have hNp : 0<e.N := by omega
  have hqp := sourcePolicyBlock_pos hNp hkap
  have hq : 0<e.q := by simpa only [hqeq] using hqp
  have hA := hd.environment_lipschitz e
  let D : ℕ := ⌈20/kap+1/sig⌉₊
  let g := 2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)+500*L*kap+200*C*sig/kap+theta
  let terminal := H*((2:ℝ)^e.N)^(200*L*(e.q:ℝ)/e.N+C*sig+theta/2)
  let floor := ((2:ℝ)^e.N)^(4*(n+2:ℝ)*sig)
  have hfloor : floor≤terminal := by
    apply le_trans _ (le_mul_of_one_le_left (by positivity) hH)
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    have hh := mul_le_mul_of_nonneg_right (recursiveLoss_dim_self n Ctest) hsig.le
    have hnn : 0≤200*L*(e.q:ℝ)/e.N := by positivity
    change 4*(n+2:ℝ)*sig≤200*L*(e.q:ℝ)/e.N+C*sig+theta/2
    dsimp only [C] at *
    linarith only [hh,hnn,htheta]
  have hbdepth : ∀ j,∀ b : DimensionalPolicy.PolicyBranch e.profile e.N (sourcePolicyBlock e.N kap) (ell+2) sig j,
      b.state 0=root → j≤D := by
    intro j b hb
    have hidx : (b.state 0).index=0 := by rw [hb]; exact hi
    exact Nat.cast_le.mp (((hdepth e.N (by omega) e.profile j b hidx).2.2.1).trans (Nat.le_ceil _))
  have htermWeight : ∀ j,∀ b : DimensionalPolicy.PolicyBranch e.profile e.N (sourcePolicyBlock e.N kap) (ell+2) sig j,
      b.state 0=root → b.weight C sig eps*terminal≤H*((2:ℝ)^e.N)^g := by
    intro j b hb
    have hw' : (b.state 0).start+10*sourcePolicyBlock e.N kap≤(b.state 0).finish := by simpa only [hb,hqeq] using hw
    have hh := hweight e.N (by omega) e.profile hA j b hw'
    have hh' : b.weight C sig eps*((2:ℝ)^e.N)^(200*L*(e.q:ℝ)/e.N+C*sig+theta/2)≤((2:ℝ)^e.N)^g := by
      convert hh using 1 <;> simp only [g,hb,hqeq,eps,Dstar]
      congr 2
      ring
    dsimp only [terminal]
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left hh' (by positivity)
  have htcap : ∀ state : BranchState,state.Valid e.N sig → state.finish ≤ state.start+100*sourcePolicyBlock e.N kap →
      ∀ y,e.energies ((2:ℝ)^ell) W total Ψ state y → y≤terminal := by
    intro state hv ht y hy
    have hh := hterminal e (by omega) he hq B₀ s hd _ state hv (by simpa only [hqeq] using ht) y hy
    apply hh.trans
    apply mul_le_mul (le_max_right Hr Ht) _ (by positivity) (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    have hdim := mul_le_mul_of_nonneg_right (recursiveLoss_dim_self n Ctest) hsig.le
    dsimp only [L]
    change 100*(n+1:ℝ)*(e.q:ℝ)/e.N+4*(n+2:ℝ)*sig≤200*((n+1:ℝ)/2)*(e.q:ℝ)/e.N+C*sig+theta/2
    dsimp only [C]
    have halg : 200*((n+1:ℝ)/2)*(e.q:ℝ)/e.N=100*(n+1:ℝ)*(e.q:ℝ)/e.N := by ring
    rw [halg]
    linarith only [hdim,htheta]
  have hind := DimensionalPolicy.weighted_branch_energy_induction e.profile e.N (sourcePolicyBlock e.N kap) (ell+2) D
    sig C sig eps (H*((e.N:ℝ)+1)) terminal floor (E*((2:ℝ)^e.N)^(-T))
    (H*((2:ℝ)^e.N)^g) (E*((2:ℝ)^e.N)^(-4*(n+2:ℝ))) root (e.energies ((2:ℝ)^ell) W total Ψ)
    hNp hqp hsig (by nlinarith [Nat.cast_nonneg (α:=ℝ) e.N]) (by positivity) (by positivity)
    (fun state u l hv hstep => (hvalid e.N (by omega) e.profile state u l hv hstep).1)
    hbdepth htcap
    (by
      intro state hv hr hw M hM hfloorM hchildren y hy
      obtain ⟨j,b,hb,hbs⟩ := hr
      have hidx : (b.state 0).index=0 := by rw [hb]; exact hi
      have hindex := ((hdepth e.N (by omega) e.profile j b hidx).2.2.2 j le_rfl).2
      rw [hbs,←hJe] at hindex
      have hh := hrules e (by omega) he hqeq hJe B₀ s hd state hv (by omega) (by simpa only [hqeq] using hw) M hM hfloorM
        (fun u l hstep z hz => by
          have hstep' := hstep
          rw [hqeq] at hstep'
          have hh := hchildren u l hstep' z hz
          simpa only [hCe,C] using hh) y hy
      exact hh.trans (add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Hr Ht) (by positivity)) hM) le_rfl))
    htermWeight
    (fun j b hb => (mul_le_mul_of_nonneg_left hfloor (b.weight_pos C sig eps).le).trans (htermWeight j b hb))
    (by
      intro j b hb
      have hh := herror e.N (by omega) e.profile hA j b
      dsimp only [C] at *
      rw [mul_left_comm]
      have hh' := mul_le_mul_of_nonneg_left hh hE
      simpa only [neg_mul] using hh')
  let b : DimensionalPolicy.PolicyBranch e.profile e.N (sourcePolicyBlock e.N kap) (ell+2) sig 0 :=
    ⟨fun _ => root,fun _ => .low,fun _ _ => hv,by omega⟩
  have hh := hind 0 b rfl x hx
  simpa only [DimensionalPolicy.PolicyBranch.weight_zero,one_mul,Nat.sub_zero] using hh
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

noncomputable def profileDimLoss (n : ℕ) (C : ℝ) : ℝ :=
  500*((n+1:ℝ)/2)+200*recursiveLoss n C
lemma profileDimLoss_nonneg (n : ℕ) (C : ℝ) : 0≤profileDimLoss n C := by
  have h := (recursiveLoss_pos n C).le
  unfold profileDimLoss
  positivity

theorem uniform_actual_recursive_profile (hn : 1≤n) (Ctest : ℝ)
    {sig kap eta : ℝ} (hsig : 0<sig) (hkap : 0<kap) (hkap1 : kap≤1)
    (hgap : sig<kap/1000) (heta : 0<eta) (ell : ℕ) (hK : 1000*(n+2:ℝ)<(2:ℝ)^ell)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ⊆Ioo (1/4:ℝ) 4)
    (hΨ0 : ∀ r,0≤Ψ r) (hΨ1 : ∀ r∈Icc (1/2:ℝ) 2,1≤Ψ r) (hiΨ : Integrable Ψ) :
    ∃ Order : ℕ,∀ (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
      (B total : ℕ), (∀ L∈W,L.length≤B) → prefixInverseVocabulary n Order⊆W → 2*Order≤total →
    ∃ N₀ : ℕ,0<N₀ ∧ ∀ e : RecursiveEnvironmentND n,
      N₀≤e.N → e.sig=sig → e.C=Ctest → e.q=sourcePolicyBlock e.N kap → e.J=sourceSmoothingLevels sig kap →
      ∀ B₀ s,RegularizedProfileData e.ρ e.N B₀ s sig e.mass →
      ∀ root : BranchState,root.Valid e.N sig → root.index=0 → root.start+10*e.q≤root.finish →
      ∀ x,e.energies ((2:ℝ)^ell) W total Ψ root x →
      x≤((2:ℝ)^e.N)^(2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)+
          profileDimLoss n Ctest*(kap+sig/kap)+eta) := by
  let theta := min 1 (eta/4)
  have ht : 0<theta := lt_min (by norm_num) (by positivity)
  have ht1 : theta≤1 := min_le_left _ _
  have hteta : theta≤eta/4 := min_le_right _ _
  obtain ⟨Order,hmain⟩ := uniform_recursive_profile_with_overhead hn Ctest hsig hkap hkap1 hgap ht ht1 ell hK Ψ hΨ hsupp hΨ0 hΨ1 hiΨ
  refine ⟨Order,?_⟩
  intro W B total hW hV htotal
  obtain ⟨H,E,hH,hE,N₁,hN₁,h₁⟩ := hmain W B total hW hV htotal
  obtain ⟨N₂,h₂⟩ := recursion_overhead_absorptionND ⌈20/kap+1/sig⌉₊ H E (B:=4*(n+2:ℝ)) heta hteta hH hE
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro e hN hes heC heq heJ B₀ s hd root hv hi hw x hx
  have hNp : 0<e.N := by omega
  have hq : 0<e.q := by rw [heq]; exact sourcePolicyBlock_pos hNp hkap
  let g := 2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)+
    500*((n+1:ℝ)/2)*kap+200*recursiveLoss n Ctest*sig/kap+theta
  have hglower : -4*(n+2:ℝ)≤g := by
    have hb := profile_exponent_lowerND (hd.environment_lipschitz e) hNp (by positivity : 0≤(n+1:ℝ)/2)
      (by omega : 0<10*e.q) hw (BranchState.valid_depths hv).2
    have h₁ : 0≤500*((n+1:ℝ)/2)*kap := by positivity
    have h₂ : 0≤200*recursiveLoss n Ctest*sig/kap := by
      have hc := (recursiveLoss_pos n Ctest).le
      positivity
    have hnn := Nat.cast_nonneg (α:=ℝ) n
    dsimp only [g]
    linarith only [hb,h₁,h₂,ht,hnn]
  have hh := h₁ e (by omega) hes heC heq heJ B₀ s hd root hv hi hw x hx
  have happ0 := h₂ e.N (by omega) g (by simpa only [neg_mul] using hglower)
  simp only [neg_mul] at hh
  have happ := hh.trans happ0
  apply happ.trans
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  have hcross₁ : 0≤500*((n+1:ℝ)/2)*(sig/kap) := by positivity
  have hcross₂ : 0≤200*recursiveLoss n Ctest*kap := by
    have hc := (recursiveLoss_pos n Ctest).le
    positivity
  dsimp only [g,profileDimLoss]
  ring_nf at hcross₁ hcross₂ ⊢
  linarith only [hcross₁,hcross₂]
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport

namespace CurrentFalconer
open PlanarFalconer

noncomputable def entryDepthND (A : Fin 2 → ℕ → ℝ) (N : ℕ) (β : ℝ) : ℕ := by
  classical
  exact ((Finset.range (N+1)).filter (fun n => min (A 0 n) (A 1 n) ≤ β)).sup id

lemma entryDepthND_spec (A : Fin 2 → ℕ → ℝ) (N : ℕ) {β : ℝ}
    (h0 : min (A 0 0) (A 1 0) ≤ β) :
    entryDepthND A N β ≤ N ∧ min (A 0 (entryDepthND A N β)) (A 1 (entryDepthND A N β)) ≤ β ∧
    ∀ n, entryDepthND A N β<n → n ≤ N → β < min (A 0 n) (A 1 n) := by
  classical
  obtain ⟨c,hcN,hc,hlast⟩ := exists_last_crossing (fun n => min (A 0 n) (A 1 n)) N β h0
  have he : entryDepthND A N β=c := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i hi
      have hi' := Finset.mem_filter.mp hi
      have hiN : i ≤ N := by simpa using Finset.mem_range.mp hi'.1
      dsimp only [id_eq]
      by_contra hic
      exact (not_lt_of_ge hi'.2) (hlast i (by omega) hiN)
    · apply Finset.le_sup (f := id)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hc⟩
  rw [he]
  exact ⟨hcN,hc,hlast⟩

theorem entry_profile_boundsND (A : Fin 2 → ℕ → ℝ) {N : ℕ} (hN : 0<N)
    {d χ β err : ℝ} (hd : 0<d) (hχ : 0<χ) (hβ : 0<β)
    (hβd : β ≤ 2*d) (hsmall : β+err<χ/4)
    (hzero : ∀ j, A j 0=0)
    (hlip : ∀ j n t, n ≤ N → t ≤ N → |A j n-A j t| ≤ d*|(n:ℝ)-t|/N)
    (hlower : ∀ j n, n ≤ N → χ*(n:ℝ)/N-err ≤ A j n) :
    let c := entryDepthND A N β
    ⌊β*(N:ℝ)/(2*d)⌋₊ ≤ c ∧ (c:ℝ)<(N:ℝ)/4 ∧
    (∀ j n, c ≤ n → n ≤ N → β-d/N ≤ A j n) ∧
    min (height (A 0) 0 c) (height (A 1) 0 c) ≤ β+err := by
  classical
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  let c := entryDepthND A N β
  have hs := entryDepthND_spec A N (β := β) (by simp [hzero,hβ.le])
  change c ≤ N ∧ min (A 0 c) (A 1 c) ≤ β ∧ _ at hs
  have hroot (j : Fin 2) (n : ℕ) (hn : n ≤ N) : A j n ≤ d*n/N := by
    have hh := (abs_le.mp (hlip j n 0 hn (Nat.zero_le _))).2
    simpa only [hzero,sub_zero,Nat.cast_zero,abs_of_nonneg ((Nat.cast_nonneg n : (0:ℝ) ≤ n))] using hh
  have hc : (c:ℝ)<(N:ℝ)/4 := by
    by_contra h
    have hl (j : Fin 2) : β<A j c := by
      have hh := hlower j c hs.1
      have hc' : (N:ℝ)/4 ≤ c := le_of_not_gt h
      have hh' : χ/4 ≤ χ*c/N := by
        apply (le_div_iff₀ hNr).mpr
        nlinarith
      linarith
    exact (not_lt_of_ge hs.2.1) (lt_min (hl 0) (hl 1))
  have hcN : c<N := by exact_mod_cast (show (c:ℝ)<N by linarith)
  have htail : ∀ j n, c ≤ n → n ≤ N → β-d/N ≤ A j n := by
    intro j n hcn hnN
    by_cases hn : c=n
    · subst n
      have hnext := hs.2.2 (c+1) (by omega) (by omega)
      have hh := (abs_le.mp (hlip j (c+1) c (by omega) hs.1)).2
      have he : |((c+1:ℕ):ℝ)-(c:ℝ)|=1 := by push_cast; simp
      rw [he,mul_one] at hh
      have hjnext : β<A j (c+1) := by
        fin_cases j
        · exact lt_of_lt_of_le hnext (min_le_left _ _)
        · exact lt_of_lt_of_le hnext (min_le_right _ _)
      linarith
    · have hh := hs.2.2 n (by omega) hnN
      have hjn : β<A j n := by
        fin_cases j
        · exact lt_of_lt_of_le hh (min_le_left _ _)
        · exact lt_of_lt_of_le hh (min_le_right _ _)
      exact (sub_le_self β (div_nonneg hd.le hNr.le)).trans hjn.le
  have hfloor : ⌊β*(N:ℝ)/(2*d)⌋₊ ≤ c := by
    let n := ⌊β*(N:ℝ)/(2*d)⌋₊
    have hn : (n:ℝ) ≤ β*N/(2*d) := Nat.floor_le (by positivity)
    have hnN : n ≤ N := by
      have hh : (n:ℝ) ≤ (N:ℝ) := by
        apply hn.trans
        apply (div_le_iff₀ (by positivity : 0<2*d)).mpr
        nlinarith
      exact_mod_cast hh
    have hqual (j : Fin 2) : A j n ≤ β := by
      have hh : d*(n:ℝ)/N ≤ β/2 := by
        apply (div_le_iff₀ hNr).mpr
        have hh := (le_div_iff₀ (by positivity : 0<2*d)).mp hn
        nlinarith
      exact (hroot j n hnN).trans (hh.trans (by linarith))
    by_contra h
    exact (not_lt_of_ge ((min_le_left _ _).trans (hqual 0))) (hs.2.2 n (by omega) hnN)
  have hl (j : Fin 2) (n : ℕ) (hn : n ≤ c) : -err ≤ A j n := by
    have hh := hlower j n (hn.trans hs.1)
    have hpos : 0 ≤ χ*(n:ℝ)/N := by positivity
    linarith
  exact ⟨hfloor,hc,htail,min_height_le (A 0) (A 1) c hs.2.1 (hl 0) (hl 1)⟩

lemma entry_nonterminalND {N c : ℕ} {κ : ℝ} (hN : 1000 ≤ N)
    (hκ : 0<κ) (hκsmall : κ ≤ 1/1000) (hc : (c:ℝ)<(N:ℝ)/4) :
    0<⌈κ*N⌉₊ ∧ c+100*⌈κ*N⌉₊ < N := by
  have hNr : (1000:ℝ) ≤ N := by exact_mod_cast hN
  have hn : 0<(N:ℝ) := by linarith
  have hq := Nat.ceil_lt_add_one (show 0 ≤ κ*(N:ℝ) by positivity)
  constructor
  · exact Nat.ceil_pos.mpr (by positivity)
  · have hh : (c:ℝ)+100*(⌈κ*(N:ℝ)⌉₊:ℝ)<N := by
      have hk : κ*(N:ℝ) ≤ (N:ℝ)/1000 := by nlinarith
      linarith
    exact_mod_cast hh

theorem entry_potential_gainND (A : Fin 2 → ℕ → ℝ) {N : ℕ} (hN : 1000 ≤ N)
    {d χ β err κ : ℝ} (hd : 0<d) (hχ : 0<χ) (hβ : 0<β)
    (hβd : β ≤ 2*d) (hsmall : β+err<χ/4)
    (hκ : 0<κ) (hκsmall : κ ≤ 1/1000)
    (hzero : ∀ j, A j 0=0)
    (hlip : ∀ j n t, n ≤ N → t ≤ N → |A j n-A j t| ≤ d*|(n:ℝ)-t|/N)
    (hlower : ∀ j n, n ≤ N → χ*(n:ℝ)/N-err ≤ A j n) :
    let c := entryDepthND A N β
    let Q := 10*⌈κ*N⌉₊
    c+100*⌈κ*N⌉₊<N ∧
    (∀ j, 2*β-2*d/N ≤ potential (A j) c N Q) ∧
    -A 0 c-A 1 c+min (height (A 0) 0 c) (height (A 1) 0 c)+
      ((2*A 0 c-potential (A 0) c N Q)+(2*A 1 c-potential (A 1) c N Q))/2 ≤
        -β+err+2*d/N := by
  have hb := entry_profile_boundsND A (by omega : 0<N) hd hχ hβ hβd hsmall hzero hlip hlower
  dsimp only at hb ⊢
  let c := entryDepthND A N β
  let q := ⌈κ*(N:ℝ)⌉₊
  have hnt := entry_nonterminalND hN hκ hκsmall hb.2.1
  change 0<q ∧ c+100*q<N at hnt
  have hw : c+10*q ≤ N := by omega
  have hpot (j : Fin 2) : 2*β-2*d/N ≤ potential (A j) c N (10*q) := by
    have h := potential_lower (A j) (by omega : 0<10*q) hw (hb.2.2.1 j)
    convert h using 1; ring
  refine ⟨hnt.2,hpot,?_⟩
  rw [outer_exponent_identity]
  have h₀ := hpot 0
  have h₁ := hpot 1
  have hk := hb.2.2.2
  change min (height (A 0) 0 c) (height (A 1) 0 c) ≤ β+err at hk
  change min (height (A 0) 0 c) (height (A 1) 0 c)-
    (potential (A 0) c N (10*q)+potential (A 1) c N (10*q))/2 ≤ _
  linarith

end CurrentFalconer

end GraphLiteralSupport
end
end

end OAI
