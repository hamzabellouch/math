import OAI.Analysis.BackwardIntertwiners.OperatorTransport

namespace OAI

namespace BackwardIntertwiners
open Filter Topology MeasureTheory Set
noncomputable section
lemma powerCost_quadratic {n : ℕ} (hn : 2 ≤ n) : (n:ℝ)^2 ≤ 10*(powerCost n:ℝ) := by
  have hr : (n+1)^2 < ((n+1)^2/4+1)*4 := by omega
  have hr' : ((n:ℝ)+1)^2 < ((powerCost n:ℝ)+1)*4 := by exact_mod_cast hr
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [sq_nonneg (n:ℝ)]
lemma rootnorm_tendsto_zero_of_bound (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, a n ≤ Real.exp (-10*(powerCost n:ℝ))) :
    Tendsto (fun n:ℕ=>a n ^ (1/(n:ℝ))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n=>Real.rpow_nonneg (ha n) _))
    (g:=fun n:ℕ=>Real.exp (-(n:ℝ)))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have h := Real.rpow_le_rpow (ha n) (hbound n) (one_div_nonneg.mpr hnpos.le)
    rw [←Real.exp_mul] at h
    apply h.trans
    apply Real.exp_le_exp.mpr
    have hc := powerCost_quadratic hn
    have hh : (-10*(powerCost n:ℝ))/n ≤ -(n:ℝ) :=
      (div_le_iff₀ hnpos).mpr (by nlinarith)
    simpa only [one_div,div_eq_mul_inv,one_mul] using hh
  · exact Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
lemma forwardOperator_quasinilpotent :
    Tendsto (fun n : ℕ=>‖forwardOperator^n‖^(1/(n:ℝ))) atTop (𝓝 0) :=
  rootnorm_tendsto_zero_of_bound _ (fun _=>norm_nonneg _) forwardOperator_power_norm
lemma forward_transitiveCommutant : Hyperinvariant233.TransitiveCommutant forwardOperator := by
  intro L hL hInv
  apply forward_backward_scalar_transitive L hL
  · exact hInv forwardOperator rfl
  · exact hInv backwardOperator forward_backward_commute.symm
  · intro g
    exact hInv (scalarMultiplier g) (forward_scalar_commute g).symm
lemma direct_mainClaim : Hyperinvariant233.MainClaim (H:=GlobalHilbert) :=
  ⟨forwardOperator,forwardOperator_ne_zero,forwardOperator_quasinilpotent,forward_transitiveCommutant⟩
open scoped ENNReal
instance fiber_separable : TopologicalSpace.SeparableSpace Fiber := by
  let s : Set Fiber := Set.range (fun j : ℤ => lp.single 2 j (1:ℂ))
  have hs : TopologicalSpace.IsSeparable s := (Set.countable_range _).isSeparable
  have hc : closure (Submodule.span ℂ s : Set Fiber) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    let P := (Submodule.span ℂ s).topologicalClosure
    change v ∈ P
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ∞) v)
    apply Filter.Eventually.of_forall
    intro t
    apply P.sum_mem
    intro j _
    apply Submodule.le_topologicalClosure
    have hj : (lp.single 2 j (1:ℂ) : Fiber) ∈ Submodule.span ℂ s :=
      Submodule.subset_span ⟨j,rfl⟩
    simpa only [←lp.single_smul,smul_eq_mul,mul_one] using
      (Submodule.span ℂ s).smul_mem (v j) hj
  exact TopologicalSpace.isSeparable_univ_iff.mp (hc ▸ hs.span.closure)
instance global_nontrivial : Nontrivial GlobalHilbert :=
  not_subsingleton_iff_nontrivial.mp (by
    intro hs
    let := hs
    exact globalHilbert_infinite inferInstance)
instance global_separable : TopologicalSpace.SeparableSpace GlobalHilbert := by
  change TopologicalSpace.SeparableSpace (Lp Fiber 2 baseMeasure)
  let : Fact ((2:ENNReal) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

lemma direct_fullClaim : Hyperinvariant233.FullClaim (H:=GlobalHilbert) :=
  Hyperinvariant233.fullClaim_of_mainClaim direct_mainClaim



theorem direct_algebra_corollary (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (hInf : ¬FiniteDimensional ℂ H) :
    Hyperinvariant233.FullClaim (H:=H) := by
  let : Nontrivial H := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    let : Subsingleton H := hs
    exact hInf inferInstance)
  obtain ⟨e⟩ := Hyperinvariant233.nonempty_linearIsometryEquiv
    (H:=GlobalHilbert) (K:=H) globalHilbert_infinite hInf
  exact Hyperinvariant233.fullClaim_of_mainClaim (Hyperinvariant233.mainClaim_transport e direct_mainClaim)




end
end BackwardIntertwiners

end OAI
