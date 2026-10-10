import OAI.MeasureTheory.Falconer.Estimates.LaplacianBounds

namespace OAI

/-! # Local mixed derivative bounds on the actual stationary chart

The chart is smooth on an open pole patch. These lemmas localize the
vertical Laplacian estimate to that patch, without extending the chart
across its singularities.
-/

namespace Falconer
open Set
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_comp_clm_at (L : E →L[ℝ] F) {f : F → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f (L x)) (k : ℕ) :
    iteratedFDeriv ℝ k (f ∘ L) x =
      (iteratedFDeriv ℝ k f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U,hU,hx,hfU⟩ := hf.contDiffOn' (by simp : (k : ℕ∞ω) ≤ ∞) (by simp)
  have hfu : ContDiffOn ℝ k f U := by simpa using hfU
  have hp : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hfu hU.uniqueDiffOn hp.uniqueDiffOn hx le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hp hx,
    iteratedFDerivWithin_of_isOpen k hU hx] at he
  exact he

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℂ) := inferInstance
noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℂ) := inferInstance

theorem directionalLaplacian_contDiffAt {n : ℕ} (v : Fin n → E) {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (directionalLaplacian v f) x := by
  have h₁ : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) x := h₁.fderiv_right (by simp)
  exact (directionalLaplacianTrace v).contDiff.contDiffAt.comp x hd

theorem directionalLaplacian_derivative_bound_at {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (directionalLaplacian v f) x‖ ≤
      (n : ℝ) * ‖iteratedFDeriv ℝ (k+2) f x‖ := by
  have h₁ : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) x := h₁.fderiv_right (by simp)
  change ‖iteratedFDeriv ℝ k
    ((directionalLaplacianTrace v) ∘ (fderiv ℝ (fderiv ℝ f))) x‖ ≤ _
  rw [(directionalLaplacianTrace v).iteratedFDeriv_comp_left hd (by simp)]
  have h := (directionalLaplacianTrace v).norm_compContinuousMultilinearMap_le
    (iteratedFDeriv ℝ k (fderiv ℝ (fderiv ℝ f)) x)
  rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv] at h
  exact h.trans (mul_le_mul_of_nonneg_right (directionalLaplacianTrace_norm_le v hv)
    (norm_nonneg _))

theorem iteratedDirectionalLaplacian_contDiffAt {n : ℕ} (v : Fin n → E)
    {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) :
    ContDiffAt ℝ ∞ ((directionalLaplacian v)^[j] f) x := by
  induction j with
  | zero => exact hf
  | succ j hj =>
      rw [Function.iterate_succ_apply']
      exact directionalLaplacian_contDiffAt v hj

theorem iteratedDirectionalLaplacian_derivative_bound_at {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (j k : ℕ) :
    ‖iteratedFDeriv ℝ k ((directionalLaplacian v)^[j] f) x‖ ≤
      (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) f x‖ := by
  induction j generalizing k with
  | zero => simp
  | succ j hj =>
      rw [Function.iterate_succ_apply']
      have h₁ := directionalLaplacian_derivative_bound_at v hv
        (iteratedDirectionalLaplacian_contDiffAt v hf j) k
      have h₂ := mul_le_mul_of_nonneg_left (hj (k+2)) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      apply (h₁.trans h₂).trans_eq
      rw [show k+2+2*j = k+2*(j+1) by omega, pow_succ]
      ring

section Parameters
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem directionalLaplacian_vertical_at {n : ℕ} {F : P × Space n → ℂ}
    {p : P} {x : Space n} (hF : ContDiffAt ℝ ∞ F (p,x)) :
    directionalLaplacian (verticalDirections n) F (p,x) =
      Laplacian.laplacian (fun y => F (p,y)) x := by
  let g : P × Space n → ℂ := fun z => F ((p,0)+z)
  have hg : ContDiffAt ℝ ∞ g ((0 : P),x) := by
    have hc : ContDiffAt ℝ ∞ (fun z : P × Space n => (p,0)+z) ((0 : P),x) :=
      contDiffAt_const.add contDiffAt_id
    have hFx : ContDiffAt ℝ ∞ F ((p,0)+((0 : P),x)) := by simpa using hF
    have h := hFx.comp ((0 : P),x) hc
    simpa only [Function.comp_def, g] using h
  have hd := iteratedFDeriv_comp_clm_at (ContinuousLinearMap.inr ℝ P (Space n)) hg 2
  have heq : g ∘ ContinuousLinearMap.inr ℝ P (Space n) = fun y => F (p,y) := by
    funext y
    simp [g]
  rw [heq] at hd
  have hshift : iteratedFDeriv ℝ 2 g (0,x) = iteratedFDeriv ℝ 2 F (p,x) := by
    simpa only [g, Prod.mk_add_mk, add_zero, zero_add] using
      (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := F) 2 (p,0) (0,x))
  change iteratedFDeriv ℝ 2 (fun y => F (p,y)) x =
    (iteratedFDeriv ℝ 2 g (0,x)).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ P (Space n)) at hd
  rw [hshift] at hd
  rw [directionalLaplacian, directionalLaplacianTrace_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hd, ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply]
  rfl

theorem iteratedDirectionalLaplacian_vertical_on {n : ℕ} {F : P × Space n → ℂ}
    {U : Set (P × Space n)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (j : ℕ) {p : P} {x : Space n} (hx : (p,x) ∈ U) :
    ((directionalLaplacian (verticalDirections n))^[j] F) (p,x) =
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
        (fun y => F (p,y))) x := by
  induction j generalizing p x with
  | zero => rfl
  | succ j hj =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [directionalLaplacian_vertical_at
        (iteratedDirectionalLaplacian_contDiffAt _ ((hF _ hx).contDiffAt (hU.mem_nhds hx)) j)]
      have ht : Filter.Tendsto (fun y : Space n => (p,y)) (𝓝 x) (𝓝 (p,x)) :=
        continuous_const.continuousAt.prodMk continuous_id.continuousAt
      have he : (fun y => ((directionalLaplacian (verticalDirections n))^[j] F) (p,y))
          =ᶠ[𝓝 x] ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
            (fun y => F (p,y))) := by
        filter_upwards [ht (hU.mem_nhds hx)] with y hy
        exact hj hy
      exact (InnerProductSpace.laplacian_congr_nhds he).self_of_nhds

theorem partialIteratedLaplacian_derivative_bound_on {n : ℕ} {F : P × Space n → ℂ}
    {U : Set (P × Space n)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (j k : ℕ) {z : P × Space n} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ k (fun q : P × Space n =>
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
        (fun y => F (q.1,y))) q.2) z‖ ≤
      (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) F z‖ := by
  have he : (fun q : P × Space n =>
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
        (fun y => F (q.1,y))) q.2) =ᶠ[𝓝 z]
      (directionalLaplacian (verticalDirections n))^[j] F := by
    filter_upwards [hU.mem_nhds hz] with q hq
    exact (iteratedDirectionalLaplacian_vertical_on hU hF j hq).symm
  rw [(he.iteratedFDeriv ℝ k).self_of_nhds]
  exact iteratedDirectionalLaplacian_derivative_bound_at _ verticalDirections_norm
    ((hF z hz).contDiffAt (hU.mem_nhds hz)) j k

/-- The actual quadratic coefficient costs exactly `2j` additional
derivatives, also when differentiated in its external parameters. -/
theorem quadraticJetCoefficient_derivative_bound_on {n : ℕ} {F : P × Space n → ℂ}
    {U : Set (P × Space n)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (j k : ℕ) {p : P} (hp : (p,0) ∈ U) :
    ‖iteratedFDeriv ℝ k (fun q : P => quadraticJetCoefficient j (fun y => F (q,y))) p‖ ≤
      ‖sphereStationaryConstant n / ((2*Complex.I)^j * (j.factorial : ℂ))‖ *
        (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) F (p,0)‖ := by
  let g : P × Space n → ℂ := fun z =>
    ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
      (fun y => F (z.1,y))) z.2
  let c : ℂ := sphereStationaryConstant n / ((2*Complex.I)^j * (j.factorial : ℂ))
  let L : P →L[ℝ] P × Space n := ContinuousLinearMap.inl ℝ P (Space n)
  have hg : ContDiffAt ℝ ∞ g (p,0) :=
    partialIteratedLaplacian_contDiffAt ((hF _ hp).contDiffAt (hU.mem_nhds hp)) j
  have hgc : ContDiffAt ℝ ∞ (g ∘ L) p := hg.comp p L.contDiff.contDiffAt
  have he : (fun q : P => quadraticJetCoefficient j (fun y => F (q,y))) =
      c • (g ∘ L) := by
    funext q
    rfl
  rw [he, iteratedFDeriv_const_smul_apply (hgc.of_le (by simp)), norm_smul]
  have hsmall : ‖iteratedFDeriv ℝ k (g ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ k g (p,0)‖ := by
    rw [iteratedFDeriv_comp_clm_at L hg k]
    have h := (iteratedFDeriv ℝ k g (p,0)).norm_compContinuousLinearMap_le
      (fun _ : Fin k => L)
    have hnorm : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ P (Space n)
    have hp : (∏ _i : Fin k, ‖L‖) ≤ (1 : ℝ) := by
      simpa using pow_le_pow_left₀ (norm_nonneg L) hnorm k
    exact h.trans (by simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  calc
    _ ≤ ‖c‖ * ‖iteratedFDeriv ℝ k g (p,0)‖ :=
      mul_le_mul_of_nonneg_left hsmall (norm_nonneg c)
    _ ≤ ‖c‖ * ((n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) F (p,0)‖) :=
      mul_le_mul_of_nonneg_left (partialIteratedLaplacian_derivative_bound_on hU hF j k hp)
        (norm_nonneg c)
    _ = _ := by dsimp [c]; ring

end Parameters
end Falconer

end OAI
