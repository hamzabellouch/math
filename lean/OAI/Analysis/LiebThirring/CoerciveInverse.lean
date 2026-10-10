import OAI.Analysis.LiebThirring.Multiplication

namespace OAI

universe u182 u183 u184 u185 u186


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped Topology

lemma coercive_bijective {E : Type u182} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (B : E →L[ℂ] E) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c*‖u‖^2 ≤ (inner ℂ u (B u)).re) : Function.Bijective B := by
  have hbound : ∀ u, c*‖u‖ ≤ ‖B u‖ := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hinner : (inner ℂ u (B u)).re ≤ ‖u‖*‖B u‖ :=
        (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
      have hs := hB u
      have hm : c*‖u‖*‖u‖ ≤ ‖B u‖*‖u‖ := by nlinarith
      exact (mul_le_mul_iff_left₀ hn).mp (by nlinarith [hm])
  have hanti := B.antilipschitz_of_bound (K := ⟨c⁻¹,le_of_lt (inv_pos.mpr hc)⟩)
    (fun u ↦ by
      change ‖u‖ ≤ c⁻¹*‖B u‖
      rw [← div_eq_inv_mul,le_div_iff₀ hc]
      simpa only [mul_comm] using hbound u)
  refine ⟨hanti.injective,?_⟩
  have hclosed : IsClosed (B.range : Set E) := hanti.isClosed_range B.uniformContinuous
  let : CompleteSpace B.range := hclosed.completeSpace_coe
  have hr : B.range = ⊤ := by
    rw [← B.range.orthogonal_orthogonal]
    rw [Submodule.eq_top_iff']
    intro v w hw
    have hz : w = 0 := by
      have he : inner ℂ (B w) w = 0 := hw _ ⟨w,rfl⟩
      have he' : inner ℂ w (B w) = 0 := by rw [← inner_conj_symm,he]; simp
      have hs := hB w
      rw [he',Complex.zero_re] at hs
      have hnorm : ‖w‖^2 = 0 := (nonpos_of_mul_nonpos_right hs hc).antisymm (sq_nonneg _)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    simp [hz]
  exact LinearMap.range_eq_top.mp hr

end SharpLiebThirring.OperatorProof

end


noncomputable section
namespace SharpLiebThirring.OperatorProof
open Set
open scoped Topology

/-- A densely defined symmetric operator whose real translate is onto is self-adjoint. -/
lemma selfAdjoint_of_surjective_shift {E : Type u183} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (A : E →ₗ.[ℂ] E)
    (hd : Dense (A.domain : Set E)) (hs : A.IsFormalAdjoint A) (c : ℝ)
    (hr : ∀ f : E, ∃ u : A.domain, A u+(c:ℂ) • (u:E) = f) : IsSelfAdjoint A := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_,?_⟩
    · intro x hx
      let x' : A.adjoint.domain := ⟨x,hx⟩
      obtain ⟨y,hy⟩ := hr (A.adjoint x'+(c:ℂ) • x)
      have he : x = (y:E) := by
        apply ext_inner_right ℂ
        intro f
        obtain ⟨v,hv⟩ := hr f
        have ha := (A.adjoint_isFormalAdjoint hd) x' v
        have hb := hs y v
        have heq : inner ℂ ((A y)+(c:ℂ) • (y:E)) (v:E) =
            inner ℂ ((A.adjoint x')+(c:ℂ) • x) (v:E) := congrArg (fun t ↦ inner ℂ t (v:E)) hy
        simp only [inner_add_left,inner_smul_left] at heq
        rw [ha,hb] at heq
        rw [← hv]
        simp only [inner_add_right,inner_smul_right]
        have hc : (starRingEnd ℂ) (c:ℂ) = (c:ℂ) := by simp
        rw [hc] at heq
        exact heq.symm
      exact he ▸ y.2
    · intro x y hxy
      apply hd.eq_of_inner_left ℂ
      intro z hz
      have h1 := (A.adjoint_isFormalAdjoint hd) x ⟨z,hz⟩
      have h2 := hs y ⟨z,hz⟩
      rw [h1,h2,hxy]
  · exact hs.le_adjoint hd

/-- The inverse of an injective bounded symmetric map, translated by a real scalar. -/
def inverseShift {E : Type u184} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (R : E →L[ℂ] E) (hR : Function.Injective R) (c : ℝ) : E →ₗ.[ℂ] E where
  domain := R.range
  toFun := (LinearEquiv.ofInjective R.toLinearMap hR).symm.toLinearMap -
    (c:ℂ) • R.range.subtype

lemma inverseShift_apply {E : Type u185} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (R : E →L[ℂ] E) (hR : Function.Injective R) (c : ℝ) (x : E) :
    inverseShift R hR c ⟨R x,⟨x,rfl⟩⟩ = x-(c:ℂ) • R x := by
  change (LinearEquiv.ofInjective R.toLinearMap hR).symm
    ((LinearEquiv.ofInjective R.toLinearMap hR) x)-(c:ℂ) • R x = _
  rw [LinearEquiv.symm_apply_apply]

lemma inverseShift_selfAdjoint {E : Type u186} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (R : E →L[ℂ] E) (hR : Function.Injective R) (hS : R.IsSymmetric)
    (hd : Dense (Set.range R)) (c : ℝ) : IsSelfAdjoint (inverseShift R hR c) := by
  refine selfAdjoint_of_surjective_shift _ hd ?_ c ?_
  · intro x y
    rcases x with ⟨x,⟨u,rfl⟩⟩
    rcases y with ⟨y,⟨v,rfl⟩⟩
    erw [inverseShift_apply R hR c u,inverseShift_apply R hR c v]
    simp only [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right]
    rw [hS]
    simp
  · intro f
    refine ⟨⟨R f,⟨f,rfl⟩⟩,?_⟩
    rw [inverseShift_apply,sub_add_cancel]

end SharpLiebThirring.OperatorProof

end

end OAI
