import OAI.MeasureTheory.Falconer.Graphs.RecursiveEnergyFamily
import OAI.MeasureTheory.Falconer.Recursion.WeightedBranchInduction

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem RecursiveEnvironment.energies_mono (e : RecursiveEnvironment) {K L : ℕ}
    (hKL : K ≤ L) (Ψ : ℝ → ℝ) {s : BranchState} {x : ℝ}
    (hx : e.energies K Ψ s x) : e.energies L Ψ s x := by
  cases s with
  | D a t i => exact hx
  | H a₀ t₀ a v i =>
    obtain ⟨X,Y,hX,hY,k,hk,h,hh,hhb,hx⟩ := hx
    exact ⟨X,Y,hX,hY,k,fun l => (hk l).trans hKL,h,hh,hhb,hx⟩

theorem uniform_actual_profile_with_overhead {lam sig kap theta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) (K₀ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ e : RecursiveEnvironment,
      e.lam = lam → e.sig = sig → e.q = sourcePolicyBlock e.N kap →
      e.J = sourceSmoothingLevels sig kap → N₀ ≤ e.N → e.Q.side = 1 → e.ρ e.Q.carrierᶜ = 0 →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData e.Q e.ρ e.N B δ e.lam e.mass →
      ∀ root : BranchState, root.Valid e.N e.sig → root.index = 0 →
      root.start+10*e.q ≤ root.finish → ∀ x, e.energies K₀ Ψ root x →
      x ≤ ((e.N:ℝ)+4)^(⌈20/kap+1/sig⌉₊+1) *
        (((2:ℝ)^e.N)^(2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)
          +500*kap+10^6*(lam+sig)/kap+theta)+((2:ℝ)^e.N)^(-10:ℝ)) := by
  let Dstar : ℝ := 1+20/kap+1/sig
  have hDstar : 1 ≤ Dstar := by
    have hk : 0 ≤ 20/kap := by positivity
    have hs : 0 ≤ 1/sig := by positivity
    dsimp only [Dstar]
    linarith
  have hDpos : 0 < Dstar := by linarith
  let eps := theta/(2*Dstar)
  have heps : 0 < eps := div_pos htheta (by positivity)
  have hepstau : eps ≤ theta/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Dstar)).mpr
    nlinarith
  have heps1 : eps ≤ 1 := by linarith
  let T : ℝ := 1000*(1/sig+1/kap)+1001
  have hT : 0 < T := by dsimp [T]; positivity
  have hTlarge : 1000*(1/sig+1/kap)+1000 < T := by dsimp [T]; linarith
  obtain ⟨K,hK,N₁,hN₁,h₁⟩ := uniform_recursive_energy_rules hlam hsig hkap hgap heps
    (half_pos htheta) hT K₀ hΨ hpos hs hone
  obtain ⟨N₂,_,h₂⟩ := uniform_branch_successor_validity hsig hkap hgap
  obtain ⟨N₃,_,h₃⟩ := uniform_source_branch_depth hsig hkap hkap1 hgap
  obtain ⟨N₄,_,h₄⟩ := uniform_source_weighted_terminal hlam hsig hkap hkap1 hgap htheta
  obtain ⟨N₅,_,h₅⟩ := uniform_source_weighted_error hsig hkap hkap1 hgap hloss heps1 hTlarge
  refine ⟨max N₁ (max N₂ (max N₃ (max N₄ N₅))),by omega,?_⟩
  intro e hdlam hdsig hdq hdJ hN hQ hcarry B δ hprof root hroot hi hwide x hx
  have hNp : 0 < e.N := by omega
  have hqp := sourcePolicyBlock_pos hNp hkap
  have hA := hprof.discrete_lipschitz
  have hrules := h₁ e hdlam hdsig hdq hdJ (by omega) hQ hcarry B δ hprof
  let D : ℕ := ⌈20/kap+1/sig⌉₊
  let L := ((2:ℝ)^e.N)^(2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)
    +500*kap+10^6*(lam+sig)/kap+theta)
  let terminal := ((2:ℝ)^e.N)^(200*(e.q:ℝ)/e.N+12*lam+theta/2)
  let floor := ((2:ℝ)^e.N)^(12*lam+eps)
  have hfloor : floor ≤ terminal := by
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    have hnonneg : 0 ≤ 200*(e.q:ℝ)/e.N := by positivity
    linarith
  have hdepth : ∀ n, ∀ b : PolicyBranch e.profile e.N (sourcePolicyBlock e.N kap) sig n,
      b.state 0 = root → n ≤ D := by
    intro n b hb
    have hidx : (b.state 0).index = 0 := by rw [hb]; exact hi
    have hn := (h₃ e.N (by omega) e.profile n b hidx).2.2.1
    exact Nat.cast_le.mp (hn.trans (Nat.le_ceil _))
  have htermWeight : ∀ n, ∀ b : PolicyBranch e.profile e.N (sourcePolicyBlock e.N kap) sig n,
      b.state 0 = root → b.weight lam eps*terminal ≤ L := by
    intro n b hb
    have hw : (b.state 0).start+10*sourcePolicyBlock e.N kap ≤ (b.state 0).finish := by
      simpa only [hb,hdq] using hwide
    have hh := h₄ e.N (by omega) e.profile hA n b hw
    simpa only [hb,← hdq] using hh
  have hind := weighted_branch_energy_induction e.profile e.N (sourcePolicyBlock e.N kap) D
    sig lam eps ((e.N:ℝ)+3) terminal floor (((2:ℝ)^e.N)^(-T)) L (((2:ℝ)^e.N)^(-10:ℝ))
    root (e.energies K Ψ) hNp hqp hsig
    (by linarith [Nat.cast_nonneg (α := ℝ) e.N]) (by positivity) (by positivity)
    (fun s u l hv hstep => (h₂ e.N (by omega) e.profile s u l hv hstep).1)
    hdepth
    (by
      intro s hv ht y hy
      exact hrules.1 s (by simpa only [hdsig] using hv) (by simpa only [hdq] using ht) y hy)
    (by
      intro s hv hr hw M hM hfloorM hchildren y hy
      obtain ⟨n,b,hb,hbs⟩ := hr
      have hidx : (b.state 0).index = 0 := by rw [hb]; exact hi
      have hindex := ((h₃ e.N (by omega) e.profile n b hidx).2.2.2 n le_rfl).2
      rw [hbs,← hdJ] at hindex
      apply hrules.2 s (by simpa only [hdsig] using hv) hindex.le
        (by simpa only [hdq] using hw) M hM hfloorM _ y hy
      intro u l hstep z hz
      exact hchildren u l (by simpa only [hdq,hdsig] using hstep) z hz)
    htermWeight
    (fun n b hb => (mul_le_mul_of_nonneg_left hfloor (b.weight_pos lam eps).le).trans (htermWeight n b hb))
    (by
      intro n b hb
      have hidx : (b.state 0).index = 0 := by rw [hb]; exact hi
      exact h₅ e.N (by omega) e.profile hA n b hidx)
  let b : PolicyBranch e.profile e.N (sourcePolicyBlock e.N kap) sig 0 :=
    ⟨fun _ => root,fun _ => .low,fun _ _ => by simpa only [hdsig] using hroot,by omega⟩
  have hh := hind 0 b rfl x (e.energies_mono hK Ψ hx)
  simpa only [PolicyBranch.weight_zero,one_mul,Nat.sub_zero,show (e.N:ℝ)+3+1 = (e.N:ℝ)+4 by ring] using hh

theorem recursion_overhead_absorption (D : ℕ) {eta theta : ℝ}
    (heta : 0 < eta) (htheta : theta ≤ eta/4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g : ℝ, -4 ≤ g →
      ((N:ℝ)+4)^(D+1)*(((2:ℝ)^N)^g+((2:ℝ)^N)^(-10:ℝ)) ≤
        ((2:ℝ)^N)^(g+eta-theta) := by
  have he : 0 < eta-theta := by linarith
  obtain ⟨N₁,h₁⟩ := fixed_polynomial_subpower (D+2) he
  refine ⟨max 2 N₁,?_⟩
  intro N hN g hg
  have hNR : 2 ≤ (N:ℝ) := by exact_mod_cast (show 2 ≤ N by omega)
  have hRp : 0 < (2:ℝ)^N := by positivity
  have herr : ((2:ℝ)^N)^(-10:ℝ) ≤ ((2:ℝ)^N)^g :=
    Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
  have hpol : 2*((N:ℝ)+4)^(D+1) ≤ (4*(N:ℝ)+1)^(D+2) := by
    calc
      _ ≤ 2*(4*(N:ℝ)+1)^(D+1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) (by linarith) (D+1)) (by norm_num)
      _ ≤ (4*(N:ℝ)+1)^(D+1)*(4*(N:ℝ)+1) := by nlinarith [pow_nonneg (by linarith : 0 ≤ 4*(N:ℝ)+1) (D+1)]
      _ = _ := (pow_succ _ (D+1)).symm
  calc
    _ ≤ (2*((N:ℝ)+4)^(D+1))*((2:ℝ)^N)^g := by nlinarith [pow_nonneg (by linarith : 0 ≤ (N:ℝ)+4) (D+1)]
    _ ≤ ((2:ℝ)^N)^(eta-theta)*((2:ℝ)^N)^g :=
      mul_le_mul_of_nonneg_right (hpol.trans (h₁ N (by omega))) (by positivity)
    _ = _ := by rw [← Real.rpow_add hRp]; congr 1; ring

theorem uniform_actual_recursive_profile {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1) (heta : 0 < eta) (K₀ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ e : RecursiveEnvironment,
      e.lam = lam → e.sig = sig → e.q = sourcePolicyBlock e.N kap →
      e.J = sourceSmoothingLevels sig kap → N₀ ≤ e.N → e.Q.side = 1 → e.ρ e.Q.carrierᶜ = 0 →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData e.Q e.ρ e.N B δ e.lam e.mass →
      ∀ root : BranchState, root.Valid e.N e.sig → root.index = 0 →
      root.start+10*e.q ≤ root.finish → ∀ x, e.energies K₀ Ψ root x →
      x ≤ ((2:ℝ)^e.N)^(2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)
        +500*kap+10^6*(lam+sig)/kap+eta) := by
  let theta := min (eta/4) 1
  have htheta : 0 < theta := lt_min (by positivity) (by norm_num)
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_actual_profile_with_overhead hlam hsig hkap hkap1 hgap hloss
    htheta (min_le_right _ _) K₀ hΨ hpos hs hone
  obtain ⟨N₂,h₂⟩ := recursion_overhead_absorption ⌈20/kap+1/sig⌉₊ heta (min_le_left (eta/4) 1)
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro e hdlam hdsig hdq hdJ hN hQ hcarry B δ hprof root hv hi hw x hx
  have hNp : 0 < e.N := by omega
  have hq : 0 < e.q := by rw [hdq]; exact sourcePolicyBlock_pos hNp hkap
  have hA := hprof.discrete_lipschitz
  have hzero : e.profile 0 = 0 := by simp only [RecursiveEnvironment.profile,Nat.cast_zero,hprof.zero,zero_div,sub_zero]
  have hrootdepth := BranchState.valid_depths hv
  have hbase := source_profile_exponent_lower hA hNp hzero (by omega : 0 < 10*e.q) hw hrootdepth.2
  change -4 ≤ 2*e.profile root.start-potential e.profile root.start root.finish (10*e.q) at hbase
  have hg : -4 ≤ 2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)
      +500*kap+10^6*(lam+sig)/kap+theta := by
    have hloss0 : 0 ≤ 10^6*(lam+sig)/kap := by positivity
    linarith
  have hh := h₁ e hdlam hdsig hdq hdJ (by omega) hQ hcarry B δ hprof root hv hi hw x hx
  have habs := h₂ e.N (by omega) _ hg
  have hh := hh.trans habs
  apply hh.trans_eq
  congr 1
  dsimp only [theta]
  ring

end PlanarFalconer

end OAI
