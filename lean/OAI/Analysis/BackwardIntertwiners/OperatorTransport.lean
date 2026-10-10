import OAI.Analysis.BackwardIntertwiners.HilbertClassification

namespace OAI

namespace Hyperinvariant233
open Filter
open scoped Topology
universe u v
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_conjugate_le (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖e.conjStarAlgEquiv T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖e (T (e.symm x))‖ ≤ ‖T‖ * ‖x‖
  rw [e.norm_map]
  simpa only [e.symm.norm_map] using T.le_opNorm (e.symm x)

theorem norm_conjugate (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖e.conjStarAlgEquiv T‖ = ‖T‖ := by
  apply le_antisymm (norm_conjugate_le e T)
  have he : e.symm.conjStarAlgEquiv (e.conjStarAlgEquiv T) = T := by
    ext x
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply]
  have h := norm_conjugate_le e.symm (e.conjStarAlgEquiv T)
  rwa [he] at h


theorem transitiveCommutant_conjugate (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H)
    (hT : TransitiveCommutant T) : TransitiveCommutant (e.conjStarAlgEquiv T) := by
  intro W hW hInv
  let U : Submodule ℂ H := W.comap e.toLinearMap
  have hU : IsClosed (U : Set H) := hW.preimage e.continuous
  have hUI : ∀ A : H →L[ℂ] H, A * T = T * A → ∀ x ∈ U, A x ∈ U := by
    intro A hA x hx
    change e (A x) ∈ W
    have hc : e.conjStarAlgEquiv A * e.conjStarAlgEquiv T =
        e.conjStarAlgEquiv T * e.conjStarAlgEquiv A := by
      simpa only [map_mul] using congrArg e.conjStarAlgEquiv hA
    have hm := hInv (e.conjStarAlgEquiv A) hc (e x) hx
    simpa using hm
  rcases hT U hU hUI with hz | ho
  · left
    apply le_antisymm _ bot_le
    intro y hy
    have hx : e.symm y ∈ U := by change e (e.symm y) ∈ W; simpa using hy
    rw [hz] at hx
    have hzero : e.symm y = 0 := hx
    have := congrArg e hzero
    simpa using this
  · right
    apply le_antisymm le_top
    intro y _
    have hx : e.symm y ∈ U := by rw [ho]; trivial
    change e (e.symm y) ∈ W at hx
    simpa using hx


theorem mainClaim_transport (e : H ≃ₗᵢ[ℂ] K) (h : MainClaim (H := H)) :
    MainClaim (H := K) := by
  obtain ⟨T, hT0, hq, ht⟩ := h
  refine ⟨e.conjStarAlgEquiv T, ?_, ?_, transitiveCommutant_conjugate e T ht⟩
  · exact fun hzero => hT0 (e.conjStarAlgEquiv.injective (by simpa using hzero))
  · have he : (fun n : ℕ => ‖(e.conjStarAlgEquiv T) ^ n‖ ^ (1 / (n : ℝ))) =
        (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) := by
      funext n
      rw [← map_pow, norm_conjugate]
    rwa [he]

end Hyperinvariant233


namespace Hyperinvariant233
open Filter
open scoped Topology
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


theorem mem_commutant_iff (T A : H →L[ℂ] H) :
    A ∈ commutant T ↔ A * T = T * A := by
  simp only [commutant, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact eq_comm

variable [completeSpace : CompleteSpace H]



omit completeSpace in
theorem commutant_isClosed_strong [CompleteSpace H] (T : H →L[ℂ] H) :
    @IsClosed (H →L[ℂ] H) strongOperatorTopology (commutant T : Set (H →L[ℂ] H)) := by
  let : TopologicalSpace (H →L[ℂ] H) := strongOperatorTopology
  have heval : ∀ x : H, Continuous (fun A : H →L[ℂ] H => A x) := by
    intro x
    exact (continuous_apply x).comp continuous_induced_dom
  have hset : (commutant T : Set (H →L[ℂ] H)) =
      ⋂ x : H, {A : H →L[ℂ] H | A (T x) = T (A x)} := by
    ext A
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_commutant_iff]
    constructor
    · intro h x
      exact congrArg (fun B : H →L[ℂ] H => B x) h
    · intro h
      ext x
      exact h x
  rw [hset]
  exact isClosed_iInter (fun x => isClosed_eq (heval (T x)) (T.continuous.comp (heval x)))



omit completeSpace in
theorem scalar_of_commutant_top [CompleteSpace H] (T : H →L[ℂ] H) (h : commutant T = ⊤) :
    ∃ c : ℂ, algebraMap ℂ (H →L[ℂ] H) c = T := by
  have hc : T ∈ Subalgebra.center ℂ (H →L[ℂ] H) := by
    rw [Subalgebra.mem_center_iff]
    intro A
    apply (mem_commutant_iff T A).mp
    rw [h]
    trivial
  rw [Algebra.IsCentral.center_eq_bot] at hc
  exact Algebra.mem_bot.mp hc



theorem commutant_ne_top_of_nonzero_quasinilpotent [Nontrivial H]
    (T : H →L[ℂ] H) (hT : T ≠ 0)
    (hlim : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    commutant T ≠ ⊤ := by
  intro htop
  obtain ⟨c, hc⟩ := scalar_of_commutant_top T htop
  have hroot (n : ℕ) (hn : n ≠ 0) : ‖T ^ n‖ ^ (1 / (n : ℝ)) = ‖c‖ := by
    rw [← hc, Algebra.algebraMap_eq_smul_one, smul_pow, one_pow,
      norm_smul, norm_pow, norm_one, mul_one, one_div]
    exact Real.pow_rpow_inv_natCast (norm_nonneg c) hn
  have hevent : (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) =ᶠ[atTop]
      (fun _ : ℕ => ‖c‖) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hroot n (Nat.ne_of_gt hn)
  have hconst : Tendsto (fun _ : ℕ => ‖c‖) atTop (𝓝 0) := hlim.congr' hevent
  have hc0 : ‖c‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  apply hT
  rw [← hc, norm_eq_zero.mp hc0, map_zero]


theorem fullClaim_of_mainClaim [Nontrivial H] (h : MainClaim (H := H)) :
    FullClaim (H := H) := by
  obtain ⟨T, hT, hlim, htrans⟩ := h
  exact ⟨T, hT, hlim, htrans,
    commutant_ne_top_of_nonzero_quasinilpotent T hT hlim,
    commutant_isClosed_strong T⟩

end Hyperinvariant233

end OAI
