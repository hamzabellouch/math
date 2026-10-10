import OAI.Geometry.Convex.GeneralMahler.Rigid.Support
import OAI.Geometry.Convex.GeneralMahler.Rigid.Axes
import OAI.Geometry.Convex.GeneralMahler.Orthant

namespace OAI
/-! Cone image orthant rigidity. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Profile Segment
variable {m:ℕ}

theorem cone_axes (C:ProperCone ℝ (Rn m))
    {u v:Rn m} (hu:u∈interior (C:Set (Rn m))) (hv:v∈interior (posDual C:Set (Rn m)))
    (b:Basis (Fin m) ℝ (Rn m))
    (hh:diagDeriv C b): IsLinearOrthant m C := by
  classical
  have hs (x:Rn m) (hx:x∈C) (i:Fin m):
      b.coord i x • b i ∈ C := by
    let p:=b.coord i x • b i
    have h : coneProj C p=p := by
      apply b.equivFun.injective
      ext j; change b.coord j (coneProj C p)=b.coord j p
      by_cases he:i=j
      · subst j
        have hp : b.coord i p=b.coord i x := by simp [p]
        rw [lp_comp C b hh i p x hp,proj_of_mem _ hx,hp]
      have hp : b.coord j p=b.coord j 0 := by simp [p,Ne.symm he]
      rw [lp_comp C b hh j p 0 hp,proj_of_mem C C.zero_mem,hp]
    change p∈C; exact h ▸ proj_mem C p
  have h' (i:Fin m) : ∃ c:ℝ,c≠0 ∧ c • b i ∈ C := by
    by_cases hz: b.coord i u=0
    · let f := fun x:ℝ=> u+x • b i
      have hi : Continuous f := by unfold f; fun_prop
      have he : ∀ᶠ x in 𝓝[>] (0:ℝ),f x ∈ (C : Set (Rn m)) :=
        nhdsWithin_le_nhds ((hi.tendsto 0) (by simpa [f] using mem_interior_iff_mem_nhds.mp hu))
      obtain ⟨x,hx,hR⟩:= (he.and (show ∀ᶠ x in 𝓝[>] (0:ℝ),0<x from self_mem_nhdsWithin)).exists
      refine ⟨b.coord i (f x),?_,hs _ hx _⟩
      have ht : b.coord i (f x)=x := by rw [show f x=_ from rfl,_root_.map_add,hz]; simp
      rw [ht]; exact hR.ne'
    exact ⟨_, hz, hs u (interior_subset hu) i⟩
  choose c hc hcb using h'
  let w := fun i=> Units.mk0 (c i) (hc i)
  let d := b.unitsSMul w
  have he (i): d i=c i • b i := Basis.unitsSMul_apply i
  have hd (i): d i∈C := he i ▸ hcb i
  have hp (x:Rn m) (hx:x∈C) (i:Fin m): d.coord i x • d i ∈ C := by
    have heq : d.coord i x • d i=b.coord i x • b i := by
      rw [he]
      change d.repr x i • _= b.repr x i • b i
      rw [Basis.repr_unitsSMul]
      change ((c i)⁻¹*b.repr x i) • (c i • b i)=_
      rw [smul_smul,mul_comm _ (c i),← mul_assoc,mul_inv_cancel₀ (hc _),one_mul]
    rw [heq]; exact hs x hx i
  obtain ⟨a,ha,hav⟩:= interior_dual_bound hv
  have hv (i) : 0<⟪v,d i⟫ := lt_of_lt_of_le
    (mul_pos ha (norm_pos_iff.mpr (d.ne_zero i))) (hav _ (hd i))
  refine ⟨d,?_⟩
  ext x; rw [mem_orthant]; constructor
  · intro h i
    have hp := hp x h i
    have ht := hav _ hp; rw [real_inner_smul_right] at ht
    have hi := hv i
    change 0 ≤ d.coord i x; nlinarith [norm_nonneg (d.coord i x • d i)]
  intro h
  have ha (s:Finset (Fin m)) : ∑ i∈s,d.repr x i • d i ∈ C := by
    induction s using Finset.induction_on with
    | empty=> rw [Finset.sum_empty]; exact C.zero_mem
    | @insert i s hi hr =>
      rw [Finset.sum_insert hi]; exact C.add_mem (C.smul_mem (hd i) (h i)) hr
  simpa only [d.sum_repr] using ha Finset.univ

namespace ProjField
variable [NeZero m]

theorem C_bound (q:ProjField m) (T:Mat m) (h:Balanced q T) (hc:UpdatesOK Cp Kp)
    (hh:LayerOK) (hi:SegmentOK):
    1 ≤ chi q.C q.V*chi q.D q.U ∧ (chi q.C q.V*chi q.D q.U=1 →
      IsLinearOrthant m q.C) := by
  obtain ⟨h,h'⟩:= q.Bound_pt T h hc hh hi; refine ⟨h,?_⟩
  intro hz
  obtain ⟨_,h₁,h₂⟩ := h' hz
  have he (i j:Fin m): cmu (q.M i) (q.M j)=0 := q.nu_comm hh hi h₁ j i
  obtain ⟨b,hb⟩:= q.projD he (q.B_layer hh h₂)
  exact cone_axes _ q.U_in q.V_in b hb
end ProjField
end GeneralMahler

end

end OAI
