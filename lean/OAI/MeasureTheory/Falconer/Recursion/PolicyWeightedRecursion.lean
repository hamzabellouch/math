import OAI.MeasureTheory.Falconer.Estimates.PolicyEnergyInduction

namespace OAI

/-! # Weighted induction for the actual all-dimensional policy energies -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (BranchState PolicyBranch sourcePolicyBlock sourceSmoothingLevels)

theorem PolicyEnergy.profile_lipschitz {m K L : ℕ} {Ψ : ℝ → ℝ}
    {w₀ : Sphere (m+3)} {Γ : PolicyContext m} {s : BranchState} {x : ℝ}
    (hx : PolicyEnergy K L Ψ w₀ Γ s x)
    (hprofile : Γ.policy = profileExcess (d := m+3) Γ.profile Γ.N) :
    DimensionalProfileLipschitz (m+3) Γ.policy Γ.N := by
  cases hx with
  | positive P _ _ _ _ =>
    change DimensionalProfileLipschitz (m+3) P.policy P.N
    change P.policy = profileExcess (d := m+3) P.profile P.N at hprofile
    rw [hprofile]
    exact profileExcess_dimensional_lipschitz P.regular P.N_pos
  | angular P =>
    change DimensionalProfileLipschitz (m+3) P.policy P.N
    change P.policy = profileExcess (d := m+3) P.profile P.N at hprofile
    rw [hprofile]
    exact profileExcess_dimensional_lipschitz P.regular P.N_pos

theorem exists_policy_weighted_recursion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ (Γ : PolicyContext m), Γ.lam = lam → Γ.σ = σ →
      Γ.J = sourceSmoothingLevels σ κ → Γ.q = sourcePolicyBlock Γ.N κ → Γ.Z = Z →
      N₀ ≤ Γ.N → Γ.policy = profileExcess (d := m+3) Γ.profile Γ.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ Γ.masks b,
        dist w c ≤ descriptorMaskRadius Γ.N Γ.σ b/2) →
      ∀ (w₀ : Sphere (m+3)) (root : BranchState), root.Valid Γ.N σ → root.index = 0 →
      root.start+100*sourcePolicyBlock Γ.N κ < root.finish →
      ∀ x, PolicyEnergy K L Ψ w₀ Γ root x →
      x ≤ 4^(sourceSmoothingLevels σ κ+1)*
        (((2:ℝ)^Γ.N)^(2*Γ.policy root.start-
          PlanarFalconer.potential Γ.policy root.start root.finish (10*sourcePolicyBlock Γ.N κ)+
          500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) lam σ+σ)/κ+η)+
          ((2:ℝ)^Γ.N)^(-10:ℝ)) := by
  let ε := η/(2*(1+20/κ+1/σ))
  let reserve := dimensionalBranchReserve (m+3) lam σ
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεη : ε ≤ η/2 := by
    dsimp [ε]
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)).mpr
    have hh : 0 ≤ 20/κ+1/σ := by positivity
    nlinarith
  have hε1 : ε ≤ 1 := by linarith
  have hreserve : 0 ≤ reserve := dimensionalBranchReserve_nonneg (m+3) hlam hσ.le
  have hσ1 : σ ≤ 1 := by linarith
  have hTp : 0 ≤ T := by
    have hh : 0 < (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2) := by positivity
    linarith
  have hJ : 0 < sourceSmoothingLevels σ κ := by
    have hh := PlanarFalconer.source_smoothing_reserve hσ hκ
    have hh' : 0 < 1+20/κ+1/σ := by positivity
    exact_mod_cast (lt_trans hh' hh)
  obtain ⟨K,L,Z,Nr,hminJet,hZ,hrec⟩ := exists_policy_recursion_bounds hgnomonic hquadratic m
    hlam hσ hσ1 hε hTp hJ φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp minJet
  obtain ⟨Nt,hterm⟩ := eventual_policyEnergy_terminal m K (half_pos hη) hV Ψ hΨV
    (fun u hu => by by_contra hn; exact (not_lt_of_ge (hsupp u hn).2.le) hu)
  obtain ⟨Nw,_,hweight⟩ := dimensional_uniform_source_weighted_terminal
    (d := m+3) hreserve hσ hκ hκ1 hgap hη
  obtain ⟨Ne,_,herror⟩ := dimensional_uniform_source_weighted_error
    (d := m+3) hσ hκ hκ1 hgap hloss hε1 hT
  obtain ⟨Nv,_,hvalid⟩ := PlanarFalconer.uniform_branch_successor_validity hσ hκ hgap
  obtain ⟨Nd,_,hdepth⟩ := PlanarFalconer.uniform_source_branch_depth hσ hκ hκ1 hgap
  obtain ⟨Ns,_,hslack⟩ := PlanarFalconer.uniform_source_ceiling_slack hσ hgap
  let N₀ := Nr+Nt+Nw+Ne+Nv+Nd+Ns+1
  refine ⟨K,L,Z,N₀,hminJet,hZ,by dsimp [N₀]; omega,?_⟩
  intro Γ hLam hσΓ hJG hqΓ hZΓ hN hprofile hcover w₀ root hroot hindex hwide x hx
  have hNr : Nr ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNt : Nt ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNw : Nw ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNe : Ne ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNv : Nv ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNd : Nd ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNs : Ns ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNp : 0 < Γ.N := by dsimp [N₀] at hN; omega
  have hA := hx.profile_lipschitz hprofile
  let R : ℝ := (2:ℝ)^Γ.N
  let terminal : ℝ := R^(200*((m+3:ℕ):ℝ)*(sourcePolicyBlock Γ.N κ:ℝ)/Γ.N+12*reserve+η/2)
  let floor : ℝ := R^(4*(((m+3:ℕ):ℝ)+1)*lam+ε)
  let B : ℝ := R^(2*Γ.policy root.start-
    PlanarFalconer.potential Γ.policy root.start root.finish (10*sourcePolicyBlock Γ.N κ)+
    500*((m+3:ℕ):ℝ)*κ+10^6*(reserve+σ)/κ+η)
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hpaid : 4*(((m+3:ℕ):ℝ)+1)*lam ≤ 12*reserve := by
    dsimp [reserve,dimensionalBranchReserve]
    nlinarith [mul_nonneg (show 0 ≤ ((m+3:ℕ):ℝ)+1 by positivity) hlam,
      mul_nonneg (show 0 ≤ ((m+3:ℕ):ℝ)+1 by positivity) hσ.le]
  have hfloorTerminal : floor ≤ terminal := by
    apply Real.rpow_le_rpow_of_exponent_le hR
    have hh : 0 ≤ 200*((m+3:ℕ):ℝ)*(sourcePolicyBlock Γ.N κ:ℝ)/Γ.N := by positivity
    linarith
  have hrecΓ : PolicyRecursionBounds m K L Γ.J Γ.lam Γ.σ ε T Γ.Z Nr Ψ := by
    simpa only [hLam,hσΓ,hJG,hZΓ] using hrec
  have hind := PlanarFalconer.weighted_branch_energy_induction Γ.policy Γ.N
    (sourcePolicyBlock Γ.N κ) (sourceSmoothingLevels σ κ) σ reserve ε 3 terminal floor
    (R^(-T)) B (R^(-10:ℝ)) root (PolicyEnergy K L Ψ w₀ Γ)
    hNp (PlanarFalconer.sourcePolicyBlock_pos hNp hκ) hσ (by norm_num)
    (by dsimp [B]; positivity) (by positivity)
    (fun s u l hs hstep => (hvalid Γ.N hNv Γ.policy s u l hs hstep).1)
    (by
      intro n b hb
      have hi : (b.state 0).index = 0 := by rw [hb]; exact hindex
      have hn := (hdepth Γ.N hNd Γ.policy n b hi).2.2.1
      have hh := PlanarFalconer.source_smoothing_reserve hσ hκ
      have hn' : (n:ℝ) < sourceSmoothingLevels σ κ := by linarith
      exact (Nat.cast_lt.mp hn').le)
    (by
      intro s hs hstop y hy
      have hsΓ : s.Valid Γ.N Γ.σ := by simpa only [hσΓ] using hs
      have hstopΓ : s.finish ≤ s.start+100*Γ.q := by simpa only [hqΓ] using hstop
      have ht := hterm Γ L hNt (by simpa only [hZΓ] using hZ) w₀ s hsΓ hstopΓ y hy
      apply ht.trans
      apply Real.rpow_le_rpow_of_exponent_le hR
      rw [hLam,hqΓ]
      change 100*((m+3:ℕ):ℝ)*(sourcePolicyBlock Γ.N κ:ℝ)/Γ.N+
        4*(((m+3:ℕ):ℝ)+1)*lam+η/2 ≤ _
      have hw : 100*((m+3:ℕ):ℝ)*(sourcePolicyBlock Γ.N κ:ℝ)/Γ.N ≤
          200*((m+3:ℕ):ℝ)*(sourcePolicyBlock Γ.N κ:ℝ)/Γ.N := by
        gcongr
        norm_num
      exact add_le_add_left (add_le_add hw hpaid) (η/2))
    (by
      intro s hs hreached hw M hM hfloor hchildren y hy
      obtain ⟨n,b,hb,hsb⟩ := hreached
      have hi : (b.state 0).index = 0 := by rw [hb]; exact hindex
      have hsi := ((hdepth Γ.N hNd Γ.policy n b hi).2.2.2 n le_rfl).2
      rw [hsb] at hsi
      apply PolicyEnergy.recursion_step w₀ Γ hrecΓ hNr
        (by simpa only [hσΓ] using hσ) (by simpa only [hZΓ] using hZ) hprofile hcover
        (by simpa only [hσΓ,hqΓ] using (hslack Γ.N hNs).2.2)
        (by simpa only [hσΓ,hqΓ] using (hslack Γ.N hNs).1)
        (by simpa only [hσΓ,hqΓ] using (hslack Γ.N hNs).2.1)
        s (by simpa only [hσΓ] using hs) (by simpa only [hJG] using hsi.le)
        (by simpa only [hqΓ] using hw) M hM
        (by simpa only [floor,R,hLam] using hfloor) ?_ y hy
      intro u l hstep z hz
      have hstep' : PlanarFalconer.BranchStep Γ.policy Γ.N (sourcePolicyBlock Γ.N κ) σ s l u := by
        simpa only [hσΓ,hqΓ] using hstep
      simpa only [hσΓ,hLam,reserve,R] using hchildren u l hstep' z hz)
    (by
      intro n b hb
      have hw := hweight Γ.N hNw Γ.policy hA n b (by rw [hb]; omega)
      simpa only [hb,ε,terminal,B,R] using hw)
    (by
      intro n b hb
      apply (mul_le_mul_of_nonneg_left hfloorTerminal (b.weight_pos reserve ε).le).trans
      have hw := hweight Γ.N hNw Γ.policy hA n b (by rw [hb]; omega)
      simpa only [hb,ε,terminal,B,R] using hw)
    (by
      intro n b hb
      apply herror Γ.N hNe Γ.policy hA n b
      rw [hb]
      exact hindex)
  let b₀ : PolicyBranch Γ.policy Γ.N (sourcePolicyBlock Γ.N κ) σ 0 :=
    ⟨fun _ => root,fun _ => .low,fun _ _ => hroot,by omega⟩
  have hb := hind 0 b₀ rfl x hx
  simpa only [PolicyBranch.weight_zero,one_mul,Nat.sub_zero,B,R,reserve,
    show (3:ℝ)+1 = 4 by norm_num] using hb

end Falconer

end OAI
