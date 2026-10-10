import OAI.MeasureTheory.Falconer.Angular.ActualAngularRecursionBound

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem PositiveDistanceData.mul_prefixLowMaximum_le (d : PositiveDistanceData)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hb : ∀ v ∈ d.prefixLowDepths,
      c*({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence.toReal ≤ M) :
    c*d.prefixLowMaximum ≤ M := by
  have hh := d.prefixLowMaximum_le (div_nonneg hM hc.le)
    (fun v hv => (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb v hv))
  exact (mul_le_mul_of_nonneg_left hh hc.le).trans_eq (by field_simp)

theorem uniform_actual_distance_recursion_bound {lam sig kap eps T : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (hT : 0 < T)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ Kinv N₀ : ℕ, ∀ K ≥ Kinv, ∀ d : PositiveDistanceData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N →
      d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 → d.RecursiveCells →
      d.branchState.Valid d.N d.sig → d.a+100*d.q < d.t → d.i+1 ≤ d.J →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ M : ℝ, 0 ≤ M → ((2:ℝ)^d.N)^(12*lam+eps) ≤ M →
      (∀ t i l, BranchStep d.branchProfile d.N d.q d.sig d.branchState l (.D d.a t i) →
        ((2:ℝ)^d.N)^(branchExponent d.branchProfile lam sig eps d.branchState l (.D d.a t i)) *
          ({d with t := t,i := i} : PositiveDistanceData).coincidence.toReal ≤ M) →
      (∀ p v, ∀ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a),
        BranchStep d.branchProfile d.N d.q d.sig d.branchState .high (.H d.a d.t p v d.i) →
        ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ e ∈ d.prefixRemainingList p, k l e ≤ K) →
        ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
        ((2:ℝ)^d.N)^(branchExponent d.branchProfile lam sig eps d.branchState .high (.H d.a d.t p v d.i)) *
          ((d.angularSuccessor p v row).energy k h Ψ).toReal ≤ M) →
      d.coincidence ≠ ⊤ ∧ d.coincidence.toReal ≤ 3*M+((2:ℝ)^d.N)^(eps-T) := by
  obtain ⟨N₁,h₁⟩ := source_positive_distance_suffix hlam hsig hkap heps
  obtain ⟨Kinv,N₂,h₂⟩ := source_positive_distance_prefix hlam hsig hkap hgap heps hT hΨ hpos hs hone
  refine ⟨Kinv,max N₁ N₂,?_⟩
  intro K hK d hdlam hdsig hdq hdJ hN hQ hcarry hcells hv hw hi B δ hprof M hM hfloor hD hH
  let := hprof.probability
  have hfinite := d.coincidence_ne_top
  change d.a ≤ d.t ∧ d.t ≤ d.N at hv
  let p := policyDepth d.branchProfile d.N d.q d.a d.t
  have hRp : 0 < (2:ℝ)^d.N := by positivity
  by_cases hp : d.a+d.t < 2*p
  · have hbound := h₁ d hdlam hdsig hdq hdJ (by omega) hQ
      (hcells.stronglySeparated hQ) hcells.1 hcells.2.1 B δ hprof hw hv.2 hi hp
    have hstep : BranchStep d.branchProfile d.N d.q d.sig d.branchState .suffix (.D d.a p (d.i+1)) :=
      BranchStep.suffix hw hp
    have hm := hD p (d.i+1) .suffix hstep
    have hboundR := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence_ne_top) hbound
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hboundR
    simp only [branchExponent,branchCost,PositiveDistanceData.branchState,BranchState.start,BranchState.finish,
      sub_self,mul_zero,zero_add,reduceCtorEq,ite_false] at hm
    have hboundM : d.coincidence.toReal ≤ M := hboundR.trans hm
    refine ⟨hfinite,hboundM.trans ?_⟩
    linarith [Real.rpow_pos_of_pos hRp (eps-T)]
  · have hp' : 2*p ≤ d.a+d.t := by omega
    have hbound := h₂ d hdlam hdsig hdq hdJ (by omega) hQ hcarry hcells.1 hcells.2.1
      hcells.2.2.1 hcells.2.2.2 B δ hprof hw hv.2 hi hp'
    have hlow : ((2:ℝ)^d.N)^eps*d.prefixLowMaximum ≤ M := by
      apply d.mul_prefixLowMaximum_le (by positivity) hM
      intro v hv
      have hm := hD v (d.i+1) .low (d.low_branch_transition hw hv)
      simpa only [branchExponent,branchCost,PositiveDistanceData.branchState,BranchState.start,sub_self,mul_zero,
        neg_zero,zero_add,ite_true] using hm
    let E := -2*(d.branchProfile p-d.branchProfile d.a)+height d.branchProfile d.a p+4000*(lam+sig)
    have hhigh : ((2:ℝ)^d.N)^(E+eps)*d.prefixSuccessorSupremum Kinv p Ψ ≤ M := by
      have hsup := d.prefixSuccessorSupremum_le Kinv p Ψ
        (div_nonneg hM (by positivity : 0 ≤ ((2:ℝ)^d.N)^(E+eps))) (by
          intro v hv hg row hr k hk h hh hhb
          have hm := hH p v row hr (d.high_branch_transition hw hp' hv hg row) k
            (fun l => (hk l).trans hK) h hh hhb
          apply (le_div_iff₀ (by positivity : 0 < ((2:ℝ)^d.N)^(E+eps))).mpr
          simpa only [branchExponent,branchCost,PositiveDistanceData.branchState,BranchState.start,
            reduceCtorEq,ite_false,E,mul_comm] using hm)
      exact (mul_le_mul_of_nonneg_left hsup (by positivity)).trans_eq (by field_simp)
    have hfloor' : ((2:ℝ)^d.N)^eps*((2:ℝ)^d.N)^(12*lam) ≤ M := by
      rw [← Real.rpow_add hRp,add_comm eps]
      exact hfloor
    have hhigh' : ((2:ℝ)^d.N)^eps*(((2:ℝ)^d.N)^E*d.prefixSuccessorSupremum Kinv p Ψ) ≤ M := by
      rw [← mul_assoc,← Real.rpow_add hRp,add_comm eps]
      exact hhigh
    have herr : ((2:ℝ)^d.N)^eps*((2:ℝ)^d.N)^(-T) = ((2:ℝ)^d.N)^(eps-T) := by
      rw [← Real.rpow_add hRp,sub_eq_add_neg]
    refine ⟨hfinite,hbound.trans ?_⟩
    change ((2:ℝ)^d.N)^eps * (((2:ℝ)^d.N)^(12*lam)+d.prefixLowMaximum+
      ((2:ℝ)^d.N)^E*d.prefixSuccessorSupremum Kinv p Ψ+((2:ℝ)^d.N)^(-T)) ≤ _
    simp only [mul_add]
    rw [herr]
    linarith

end PlanarFalconer

end OAI
