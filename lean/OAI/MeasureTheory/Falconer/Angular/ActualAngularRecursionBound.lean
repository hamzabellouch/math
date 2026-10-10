import OAI.MeasureTheory.Falconer.Recursion.RecursiveCellInvariants
import OAI.MeasureTheory.Falconer.Recursion.BranchExponent

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem AngularStateData.mul_childMaximum_le (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (p : ℕ) (Ψ : ℝ → ℝ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hb : ∀ row ∈ d.children p, c*((d.successor p row).energy k h Ψ).toReal ≤ M) :
    c*d.childMaximum k h p Ψ ≤ M := by
  have hh := d.childMaximum_le k h p Ψ (div_nonneg hM hc.le)
    (fun row hr => (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb row hr))
  exact (mul_le_mul_of_nonneg_left hh hc.le).trans_eq (by field_simp)

theorem AngularStateData.mul_farDistanceMaximum_le (d : AngularStateData)
    [IsFiniteMeasure d.ρ] (b : ℕ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hb : ∀ row ∈ d.children b, ∀ col ∈ d.children b,
      angularSeparated d.Q d.Q b row col →
      c*((d.distanceSuccessor b).atCells row.1 col.1).coincidence.toReal ≤ M ∧
      c*((d.distanceSuccessor b).atCells row.2 col.2).coincidence.toReal ≤ M) :
    c*(d.farDistanceMaximum b).toReal ≤ M := by
  have hh := d.farDistanceMaximum_le b (div_nonneg hM hc.le) (by
    intro row hr col hcol hs
    have hh := hb row hr col hcol hs
    exact ⟨(le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh.1),
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh.2)⟩)
  exact (mul_le_mul_of_nonneg_left hh hc.le).trans_eq (by field_simp)

theorem uniform_actual_angular_recursion_bound {lam sig kap eps : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (T : ℝ) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : AngularStateData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N →
      d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
      d.branchState.Valid d.N d.sig → d.a+100*d.q < d.v → d.i+1 ≤ d.J →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ e ∈ d.retainedList d.a, k l e ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ p l, BranchStep d.profile d.N d.q d.sig d.branchState l (.H d.a₀ d.t₀ p d.v d.i) →
        ∀ row ∈ d.children p,
        ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState l (.H d.a₀ d.t₀ p d.v d.i)) *
          ((d.successor p row).energy k h Ψ).toReal ≤ M) →
      (∀ b, BranchStep d.profile d.N d.q d.sig d.branchState .far (.D b d.v (d.i+1)) →
        ∀ row ∈ d.children b, ∀ col ∈ d.children b, angularSeparated d.Q d.Q b row col →
        ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far (.D b d.v (d.i+1))) *
          ((d.distanceSuccessor b).atCells row.1 col.1).coincidence.toReal ≤ M ∧
        ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far (.D b d.v (d.i+1))) *
          ((d.distanceSuccessor b).atCells row.2 col.2).coincidence.toReal ≤ M) →
      d.energy k h Ψ ≠ ⊤ ∧
        (d.energy k h Ψ).toReal ≤ ((d.N:ℝ)+1)*M+((2:ℝ)^d.N)^(-T) := by
  obtain ⟨N₀,h₀⟩ := source_angular_reduction hlam hsig hkap hgap heps T K hΨ hpos hs
  refine ⟨N₀,?_⟩
  intro d hdlam hdsig hdq hdJ hN hQ hcarry hv hw hi hX hY B δ hprof k hk h hh hhb M hM hH hD
  change d.a₀ ≤ d.a ∧ d.a ≤ d.v ∧ d.v ≤ d.t₀ ∧ d.t₀ ≤ d.N ∧
    (d.t₀:ℝ) ≤ d.v+d.sig*d.N at hv
  have ht : (d.t₀:ℝ) ≤ d.v+sig*d.N := by simpa only [hdsig] using hv.2.2.2.2
  obtain ⟨hfinite,p,hap,hpv,_,_,hd | hn⟩ := h₀ d hdlam hdsig hdq hdJ hN hQ hcarry
    hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 ht hw hi hX hY B δ hprof k hk h hh hhb
  · obtain ⟨e,rfl,he,hbound⟩ := hd
    have hstep : BranchStep d.profile d.N d.q d.sig d.branchState .direct
        (.H d.a₀ d.t₀ (descriptorAnchor e) d.v d.i) := BranchStep.direct hw he
    have hm := d.mul_childMaximum_le k h (descriptorAnchor e) Ψ
      (by positivity : 0 < ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .direct
        (.H d.a₀ d.t₀ (descriptorAnchor e) d.v d.i))) hM (hH _ _ hstep)
    simp only [branchExponent,branchCost,BranchState.start,AngularStateData.branchState,
      reduceCtorEq,ite_false] at hm
    refine ⟨hfinite,hbound.trans ?_⟩
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d.N) hM]
  · obtain ⟨rfl,hp5,_,hbound⟩ := hn
    let p := d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig
    have hstep : BranchStep d.profile d.N d.q d.sig d.branchState .near
        (.H d.a₀ d.t₀ p d.v d.i) := BranchStep.near hw hap
    have hm := d.mul_childMaximum_le k h p Ψ
      (by positivity : 0 < ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .near
        (.H d.a₀ d.t₀ p d.v d.i))) hM (hH _ _ hstep)
    simp only [branchExponent,branchCost,BranchState.start,AngularStateData.branchState,
      reduceCtorEq,ite_false,add_zero] at hm
    have hnear : ((2:ℝ)^d.N)^(-2*(d.profile p-d.profile d.a)+12*lam+eps)*
        d.childMaximum k h p Ψ ≤ M := by
      apply le_trans _ hm
      apply mul_le_mul_of_nonneg_right _ (d.childMaximum_nonneg k h p Ψ)
      exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
    let := hprof.probability
    have hfar : d.farSum p ≤ (d.N:ℝ)*M := by
      apply d.farSum_le_depth_factor p hp5 (hv.2.2.1.trans hv.2.2.2.1) hM
      intro b hb
      have hb' : b ∈ Finset.Icc (d.a+9) (p+6) := Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hb).1, by have := (Finset.mem_Icc.mp hb).2; omega⟩
      have hstep : BranchStep d.profile d.N d.q d.sig d.branchState .far (.D b d.v (d.i+1)) :=
        BranchStep.far hw hap hb'
      have hm := d.mul_farDistanceMaximum_le b
        (by positivity : 0 < ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far
          (.D b d.v (d.i+1)))) hM (hD b hstep)
      simp only [branchExponent,branchCost,BranchState.start,AngularStateData.branchState,
        reduceCtorEq,ite_false,add_zero] at hm
      apply le_trans _ hm
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
      simp only [hdlam,hdsig]
      linarith
    refine ⟨hfinite,hbound.trans ?_⟩
    change _ ≤ ((d.N:ℝ)+1)*M+_
    dsimp only [p] at hnear hfar
    nlinarith

end PlanarFalconer

end OAI
