import Mathlib

namespace OAI

noncomputable section
namespace NadelL2
open LinearPMap WithLp
open scoped InnerProductSpace
variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

 
theorem mem_graph_of_adjoint_identity
    (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) (hclosed : T.IsClosed)
    {u : E} {f : F}
    (hweak : ∀ v : T†.domain, inner 𝕜 u (T† v) = inner 𝕜 f (v : F)) :
    (u, f) ∈ T.graph := by
  let G : Submodule 𝕜 (WithLp 2 (E × F)) :=
    T.graph.comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
  have hGc : IsClosed (G : Set (WithLp 2 (E × F))) :=
    hclosed.preimage (WithLp.prod_continuous_ofLp 2 E F)
  have hm : toLp 2 (u, f) ∈ Gᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro z hz
    have hz' (x : T.domain) :
        inner 𝕜 (ofLp z).1 (x : E) + inner 𝕜 (ofLp z).2 (T x) = 0 := by
      have hx : toLp 2 ((x : E), T x) ∈ G := by
        change ((x : E), T x) ∈ T.graph
        exact T.mem_graph_iff.mpr ⟨x, rfl, rfl⟩
      have h := (G.mem_orthogonal' z).mp hz (toLp 2 ((x : E), T x)) hx
      simpa only [prod_inner_apply, ofLp_toLp] using h
    have hv : (ofLp z).2 ∈ T†.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨-(ofLp z).1, fun x => ?_⟩
      rw [inner_neg_left]
      exact (eq_neg_of_add_eq_zero_right (hz' x)).symm
    have ha : T† ⟨(ofLp z).2, hv⟩ = -(ofLp z).1 := by
      apply LinearPMap.adjoint_apply_eq hT
      intro x
      rw [inner_neg_left]
      exact (eq_neg_of_add_eq_zero_right (hz' x)).symm
    have hw := hweak ⟨(ofLp z).2, hv⟩
    rw [ha, inner_neg_right] at hw
    simp only [prod_inner_apply]
    rw [← hw]
    exact add_neg_cancel _
  rw [G.orthogonal_orthogonal_eq_closure, hGc.submodule_topologicalClosure_eq] at hm
  exact hm

 

theorem exists_solution_of_adjoint_bound
    (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) (hclosed : T.IsClosed)
    (f : F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v : T†.domain, ‖inner 𝕜 f (v : F)‖ ≤ C * ‖T† v‖) :
    ∃ u : T.domain, T u = f ∧ ‖(u : E)‖ ≤ C := by
  let A : T†.domain →ₗ[𝕜] E := T†.toFun
  let ell : T†.domain →ₗ[𝕜] 𝕜 := (innerₛₗ 𝕜 f).comp T†.domain.subtype
  have hk : A.ker ≤ ell.ker := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    change inner 𝕜 f (v : F) = 0
    apply norm_eq_zero.mp
    have hb := hbound v
    change ‖inner 𝕜 f (v : F)‖ ≤ C * ‖A v‖ at hb
    rw [hv, norm_zero, mul_zero] at hb
    exact le_antisymm hb (norm_nonneg _)
  let g : A.range →ₗ[𝕜] 𝕜 :=
    (A.ker.liftQ ell hk).comp A.quotKerEquivRange.symm.toLinearMap
  have hg (v : T†.domain) : g (A.rangeRestrict v) = ell v := by
    have he : A.quotKerEquivRange (Submodule.Quotient.mk v) = A.rangeRestrict v := by
      apply Subtype.ext
      exact A.quotKerEquivRange_apply_mk v
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, ← he,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hgb (x : A.range) : ‖g x‖ ≤ C * ‖x‖ := by
    obtain ⟨v, hv⟩ := x.property
    have he : A.rangeRestrict v = x := Subtype.ext hv
    rw [← he, hg]
    exact hbound v
  let gc : StrongDual 𝕜 A.range := g.mkContinuous C hgb
  obtain ⟨L, hL, hnL⟩ := exists_extension_norm_eq A.range gc
  let u : E := (InnerProductSpace.toDual 𝕜 E).symm L
  have hun : ‖u‖ ≤ C := by
    rw [show ‖u‖ = ‖L‖ from (InnerProductSpace.toDual 𝕜 E).symm.norm_map L, hnL]
    exact g.mkContinuous_norm_le hC hgb
  have hu : (u, f) ∈ T.graph := by
    apply mem_graph_of_adjoint_identity T hT hclosed
    intro v
    change inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm L) (A v) = ell v
    rw [InnerProductSpace.toDual_symm_apply]
    have h := hL (A.rangeRestrict v)
    exact h.trans (hg v)
  obtain ⟨u', hu', hTu'⟩ := T.mem_graph_iff.mp hu
  exact ⟨u', hTu', hu' ▸ hun⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

 

theorem exists_solution_of_complex_estimate
    (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] H)
    (hT : Dense (T.domain : Set E)) (hTc : T.IsClosed) (hSc : S.IsClosed)
    (hcomplex : ∀ x : T.domain, (T x, 0) ∈ S.graph)
    {ε : ℝ} (hε : 0 < ε)
    (hestimate : ∀ v : T†.domain, ∀ hv : (v : F) ∈ S.domain,
      ε * ‖(v : F)‖ ^ 2 ≤ ‖T† v‖ ^ 2 + ‖S ⟨(v : F), hv⟩‖ ^ 2)
    {f : F} (hf : (f, 0) ∈ S.graph) :
    ∃ u : T.domain, T u = f ∧ ‖(u : E)‖ ≤ ‖f‖ / Real.sqrt ε := by
  let K : Submodule 𝕜 F :=
    S.graph.comap ((LinearMap.id : F →ₗ[𝕜] F).prod (0 : F →ₗ[𝕜] H))
  have hKc : IsClosed (K : Set F) :=
    hSc.preimage (continuous_id.prodMk continuous_const)
  let : CompleteSpace K := hKc.completeSpace_coe
  have hKf : f ∈ K := hf
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  apply exists_solution_of_adjoint_bound T hT hTc f
    (div_nonneg (norm_nonneg _) hsqrt.le)
  intro v
  obtain ⟨p, hp, q, hq, hvpq⟩ := K.exists_add_mem_mem_orthogonal (v : F)
  have hqT (x : T.domain) : inner 𝕜 q (T x) = 0 :=
    (K.mem_orthogonal' q).mp hq (T x) (hcomplex x)
  have hqdom : q ∈ T†.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    exact ⟨0, fun x => by rw [inner_zero_left, hqT]⟩
  have hqadj : T† ⟨q, hqdom⟩ = 0 := by
    apply LinearPMap.adjoint_apply_eq hT
    intro x
    rw [inner_zero_left, hqT]
  have hpdom : p ∈ T†.domain := by
    have he : p = (v : F) - q := (eq_sub_iff_add_eq).mpr hvpq.symm
    rw [he]
    exact T†.domain.sub_mem v.property hqdom
  obtain ⟨⟨p, hpS⟩, rfl, hSp⟩ := S.mem_graph_iff.mp (show (p, 0) ∈ S.graph from hp)
  let vp : T†.domain := ⟨p, hpdom⟩
  have hvsum : v = vp + ⟨q, hqdom⟩ := Subtype.ext hvpq
  have hTp : T† vp = T† v := by
    rw [hvsum, LinearPMap.map_add, hqadj, add_zero]
  have hE : ε * ‖p‖ ^ 2 ≤ ‖T† v‖ ^ 2 := by
    simpa only [vp, hSp, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero,
      ← hTp] using hestimate vp hpS
  have hnp : ‖p‖ ≤ ‖T† v‖ / Real.sqrt ε := by
    apply (le_div_iff₀ hsqrt).mpr
    apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hsqrt.le) (norm_nonneg _)).mp
    simpa only [mul_pow, Real.sq_sqrt hε.le, mul_comm] using hE
  have hpair : inner 𝕜 f (v : F) = inner 𝕜 f p := by
    rw [hvpq, inner_add_right, K.inner_right_of_mem_orthogonal hKf hq, add_zero]
  rw [hpair]
  calc
    ‖inner 𝕜 f p‖ ≤ ‖f‖ * ‖p‖ := norm_inner_le_norm f p
    _ ≤ ‖f‖ * (‖T† v‖ / Real.sqrt ε) := mul_le_mul_of_nonneg_left hnp (norm_nonneg _)
    _ = (‖f‖ / Real.sqrt ε) * ‖T† v‖ := by ring

 

def jointGraph (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] H) : Set (F × E × H) :=
  {p | (p.1, p.2.1) ∈ T†.graph ∧ (p.1, p.2.2) ∈ S.graph}

 

theorem exists_solution_of_core_estimate
    (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] H)
    (hT : Dense (T.domain : Set E)) (hTc : T.IsClosed) (hSc : S.IsClosed)
    (hcomplex : ∀ x : T.domain, (T x, 0) ∈ S.graph)
    (D : Set (jointGraph T S)) (hD : Dense D)
    {ε : ℝ} (hε : 0 < ε)
    (hestimate : ∀ v ∈ D,
      ε * ‖v.val.1‖ ^ 2 ≤ ‖v.val.2.1‖ ^ 2 + ‖v.val.2.2‖ ^ 2)
    {f : F} (hf : (f, 0) ∈ S.graph) :
    ∃ u : T.domain, T u = f ∧ ‖(u : E)‖ ≤ ‖f‖ / Real.sqrt ε := by
  apply exists_solution_of_complex_estimate T S hT hTc hSc hcomplex hε _ hf
  intro v hv
  let p : jointGraph T S := ⟨((v : F), T† v, S ⟨(v : F), hv⟩),
    T†.mem_graph_iff.mpr ⟨v, rfl, rfl⟩,
    S.mem_graph_iff.mpr ⟨⟨(v : F), hv⟩, rfl, rfl⟩⟩
  have hc : IsClosed {w : jointGraph T S |
      ε * ‖w.val.1‖ ^ 2 ≤ ‖w.val.2.1‖ ^ 2 + ‖w.val.2.2‖ ^ 2} := by
    apply isClosed_le <;> fun_prop
  exact (closure_minimal hestimate hc) (hD p)

end NadelL2

end

end OAI
