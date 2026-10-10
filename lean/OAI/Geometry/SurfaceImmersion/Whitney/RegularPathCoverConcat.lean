import OAI.Geometry.SurfaceImmersion.Whitney.RegularPathCover

namespace OAI

/-! Concatenation preserves the finite closed-interval smooth formulas. -/
noncomputable section
open Set Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y z : M} {γ : Path x y} {δ : Path y z}
namespace RegularPathCover

noncomputable def trans (P : RegularPathCover (J := J) γ) (Q : RegularPathCover (J := J) δ) :
    RegularPathCover (J := J) (γ.trans δ) := by
  haveI := P.finite
  haveI := Q.finite
  let L : P.Index → Set ℝ := fun i => Icc 0 (1/2) ∩ (fun t => 2*t) ⁻¹' P.region i
  let R : Q.Index → Set ℝ := fun i => Icc (1/2) 1 ∩ (fun t => 2*t-1) ⁻¹' Q.region i
  refine {
    Index := P.Index ⊕ Q.Index
    finite := inferInstance
    region := Sum.elim L R
    closed := ?_
    convex := ?_
    subset := ?_
    arc := Sum.elim P.arc Q.arc
    slope := Sum.elim (fun i => 2*P.slope i) (fun i => 2*Q.slope i)
    offset := Sum.elim P.offset (fun i => Q.offset i-Q.slope i)
    cover := ?_
    parameter := ?_
    agree := ?_ }
  · intro i
    cases i with
    | inl i => exact isClosed_Icc.inter ((P.closed i).preimage (by fun_prop))
    | inr i => exact isClosed_Icc.inter ((Q.closed i).preimage (by fun_prop))
  · intro i
    cases i with
    | inl i =>
      exact (convex_Icc 0 (1/2)).inter (by
        simpa only [add_zero] using affine_preimage_convex (P.convex i) 2 0)
    | inr i =>
      exact (convex_Icc (1/2) 1).inter (by
        simpa only [sub_eq_add_neg] using affine_preimage_convex (Q.convex i) 2 (-1))
  · intro i t ht
    cases i with
    | inl i => exact ⟨ht.1.1,ht.1.2.trans (by norm_num)⟩
    | inr i => exact ⟨(by norm_num : (0:ℝ) ≤ 1/2).trans ht.1.1,ht.1.2⟩
  · intro t
    by_cases ht : (t:ℝ) ≤ 1/2
    · let u : I := ⟨2*t,by constructor <;> linarith [t.property.1]⟩
      obtain ⟨i,hi⟩ := P.cover u
      exact ⟨Sum.inl i,⟨t.property.1,ht⟩,hi⟩
    · let u : I := ⟨2*t-1,by constructor <;> linarith [t.property.2]⟩
      obtain ⟨i,hi⟩ := Q.cover u
      exact ⟨Sum.inr i,⟨(not_le.mp ht).le,t.property.2⟩,hi⟩
  · intro i t ht
    cases i with
    | inl i =>
      have h := P.parameter i (2*t) ht.2
      change 2*P.slope i*t+P.offset i ∈ Icc (P.arc i).start (P.arc i).finish
      convert h using 1; ring
    | inr i =>
      have h := Q.parameter i (2*t-1) ht.2
      change 2*Q.slope i*t+(Q.offset i-Q.slope i) ∈ Icc (Q.arc i).start (Q.arc i).finish
      convert h using 1; ring
  · intro i t ht
    cases i with
    | inl i =>
      let u : I := ⟨2*t,P.subset i ht.2⟩
      have hp : (γ.trans δ) t = γ u := by
        calc
          (γ.trans δ) t = (γ.trans δ).extend (t:ℝ) := ((γ.trans δ).extend_extends' t).symm
          _ = γ.extend (2*t) := Path.extend_trans_of_le_half γ δ ht.1.2
          _ = γ u := γ.extend_apply u.property
      rw [hp,P.agree i u ht.2]
      congr 1
      dsimp [u]
      ring
    | inr i =>
      let u : I := ⟨2*t-1,Q.subset i ht.2⟩
      have hp : (γ.trans δ) t = δ u := by
        calc
          (γ.trans δ) t = (γ.trans δ).extend (t:ℝ) := ((γ.trans δ).extend_extends' t).symm
          _ = δ.extend (2*t-1) := Path.extend_trans_of_half_le γ δ ht.1.1
          _ = δ u := δ.extend_apply u.property
      rw [hp,Q.agree i u ht.2]
      congr 1
      dsimp [u]
      ring

end RegularPathCover
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
