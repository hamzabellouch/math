import OAI.Geometry.Convex.GeneralMahler.Brouwer.Fixed
import OAI.Geometry.Convex.GeneralMahler.Inward
import OAI.Geometry.Convex.GeneralMahler.Update

namespace OAI
/-! Simultaneous normalization on two spectral boxes using scalar endpoint
and gap inequalities. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open ProjField
variable {m : ℕ} [NeZero m]
namespace Param
variable {R : ℝ}
lemma cont_ll (q:ProjField m) (hr:2≤R) (hr':0<R) :
    Continuous (fun p:Param m R => ∑ i, (coord i).smulRight ((p.instanceQ hr' q).M i)) := by
  apply continuous_finsetSum
  intro i _
  exact ((ContinuousLinearMap.smulRightL ℝ _ (Mat m) (coord i)).continuous.comp (cont_M q hr hr' i))

lemma cont_expL (q:ProjField m) (hr:2≤R) (hr':0<R) (f:ℝ→ℝ)
    (hf:Continuous f) (hp:PolyBound f) :
    Continuous (fun p:Param m R=> (p.instanceQ hr' q).expL f) := by
  let l := fun p:Param m R => ∑ i, (coord i).smulRight ((p.instanceQ hr' q).M i)
  have he (p:Param m R) (x) : l p x = (p.instanceQ hr' q).Lmat x := by simp [l,Lmat]
  apply continuous_iff_continuousAt.mpr
  intro p
  let b := ‖l p‖+1
  have hh : ∀ᶠ w in 𝓝 p, ‖l w‖≤b := by
    have hu : Continuous l := cont_ll q hr hr'
    have hb : Continuous (fun z : Rn m →L[ℝ] Mat m => ‖z‖) := continuous_norm (E:=Rn m →L[ℝ] Mat m)
    have h : ContinuousAt (fun w=>‖l w‖) p := (hb.comp hu).continuousAt
    filter_upwards [h.eventually (gt_mem_nhds (show ‖l p‖<b by unfold b; linarith))] with w hw
    exact le_of_lt hw
  obtain ⟨C,n,hC,h⟩ := hp
  let g := fun x:Rn m => C*(1+b*‖x‖)^n
  have hg : PolyBound g :=
    (PolyBound.const _).mul (((PolyBound.const _).add
      ((PolyBound.const _).mul (PolyBound.id.norm))).pow _)
  have hi := hg.gaussian_integrable (μ:=normal m) ((by unfold g; fun_prop : Continuous g).aestronglyMeasurable)
  have hc (y:Param m R) : Continuous fun x:Rn m=>cfc f ((y.instanceQ hr' q).Lmat x) :=
    (cfc_continuous_herm f hf).comp_continuous (y.instanceQ hr' q).L_cont (y.instanceQ hr' q).L_sym
  unfold expL
  apply continuousAt_of_dominated
    (Eventually.of_forall fun y => (hc y).aestronglyMeasurable) _ hi
  · apply ae_of_all
    intro x
    exact ((cfc_continuous_herm f hf).comp_continuous (cont_L q hr hr' x)
      (fun y=> (y.instanceQ hr' q).L_sym _)).continuousAt
  filter_upwards [hh] with y hy
  apply ae_of_all
  intro x
  apply le_trans (spectrum_poly_le f hC h ((y.instanceQ hr' q).L_sym _))
  unfold g
  rw [← he]
  have hi := ((l y).le_opNorm x).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
  gcongr
end Param

lemma param_fixed (m:ℕ) (R:ℝ) (hr:2≤R) (f : Param m R → Param m R) (hf : Continuous f) :
    ∃ x:Param m R, f x=x := by
  classical
  let A := params m R
  let g := fun x : Mat m × Mat m => if h:x∈A then (f ⟨x,h⟩).val else x
  have ha : MapsTo g A A := by intro x h; simp only [g,dite_eq_left h]; apply Subtype.property
  have hc : ContinuousOn g A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : A.domRestrict g = Subtype.val ∘ f := by funext x; simp [Set.domRestrict,g,A,x.property]
    rw [he]; exact continuous_subtype_val.comp hf
  have hh : R⁻¹≤R := by
    have h : 0<R := by linarith
    rw [← one_div, div_le_iff₀ h]; nlinarith
  have hl : tmin ≤ tmax := by norm_num [tmin,tmax]
  have ht : A.Nonempty := (specBox_nonempty m _ _ hh).prod (specBox_nonempty m _ _ hl)
  obtain ⟨x,hx,h⟩ := compact_fixedpoint A ((specBox_compact ..).prod (specBox_compact ..))
    ((specBox_convex ..).prod (specBox_convex ..)) ht g hc ha
  exact ⟨⟨x,hx⟩,Subtype.ext (by simpa only [g,dite_eq_left hx] using h)⟩

/-- For a field q0 supplying the original cone with a normalized pair,
a positive coordinate transform and companion field exist. -/
theorem simultaneous (q:ProjField m) {c k:ℝ→ℝ}
    (hck:UpdatesOK c k) :
    ∃ R≥(2:ℝ), ∃ hr : 0<R, ∃ x:Param m R,
      let q' := x.instanceQ hr q
      q'.avgA=0 ∧ updEq (q'.expL c) (q'.expL k) x.T = 0 ∧
        scalar m mstar ≤ updGap (q'.expL c) x.T := by
  obtain ⟨R,hr,h⟩ := inward q
  have H : 0 < R := by linarith
  let Q := fun x:Param m R => x.instanceQ H q
  let E := fun x:Param m R => (Q x).avgA
  let C := fun x:Param m R => (Q x).expL c
  let K := fun x:Param m R => (Q x).expL k
  let u := fun x:Param m R => updEq (C x) (K x) x.T
  have hu (x:Param m R) : (u x).IsHermitian :=
    upd_sym ((Q x).expL_sym hck.Cc hck.Cp) ((Q x).expL_sym hck.Kc hck.Kp)
      x.in_box.2.1
  have ht (x:Param m R) : (x.T+u x).IsHermitian := x.in_box.2.1.add (hu x)
  have he (x:Param m R) : (x.B+E x).IsHermitian := x.in_box.1.1.add ((Q x).avgA_sym)
  let g := fun x:Param m R =>
    (clip R⁻¹ R (x.B+E x), clip tmin tmax (x.T+u x))
  have ha : R⁻¹≤R := by rw [← one_div, div_le_iff₀ H]; nlinarith
  have hb : tmin≤tmax := by norm_num [tmin,tmax]
  have hg (x:Param m R) : g x∈params m R :=
    ⟨clip_mem _ _ ha (he x),clip_mem _ _ hb (ht x)⟩
  let f := fun x:Param m R => (⟨g x,hg x⟩:Param m R)
  have hc : Continuous f := by
    have hC : Continuous C := Param.cont_expL q hr H _ hck.Cc hck.Cp
    have hK : Continuous K := Param.cont_expL q hr H _ hck.Kc hck.Kp
    have hT : Continuous (@Param.T m R) := Param.cont_T
    have hl : Continuous u := by unfold u updEq jprod; fun_prop
    have hh : Continuous g :=
      ((cont_clip R⁻¹ R).comp_continuous (Param.cont_B.add (Param.cont_avgA q hr H)) he).prodMk
        ((cont_clip tmin tmax).comp_continuous (hT.add hl) ht)
    exact hh.subtype_mk _
  obtain ⟨p,hp⟩ := param_fixed m R hr f hc
  have hx := h H p
  have hz := clip_eq ha (congrArg Param.B hp) (he p)
    (fun v hv => (hx v hv).1) (fun v hv => (hx v hv).2)
  refine ⟨R,hr,H,p,hz,?_⟩
  have hi := (Q p).expL_bounds hck
  have hi' : u p=0 := by
    apply clip_eq hb (congrArg Param.T hp) (ht p)
    · intro v hv ha
      rw [show u p = _ from (rfl : u p = updEq _ _ _),upd_form p.in_box.2.1 ha]
      exact (op_posSemidef_iff.mp hi.2.2.1.posSemidef).2 v
    · intro v hv ha
      rw [show u p = _ from (rfl : u p = updEq _ _ _),upd_form p.in_box.2.1 ha]
      have HE := hi.2.2.2
      rw [← neg_nonneg] at HE
      have hf := (op_posSemidef_iff.mp HE.posSemidef).2 v
      rw [_root_.map_neg,_root_.neg_apply,inner_neg_right] at hf
      exact neg_nonneg.mp hf
  exact ⟨hi',gap_from_cov ((Q p).expL_sym hck.Cc hck.Cp) p.in_box.2 hi.1 hi.2.1 hi'⟩

end GeneralMahler

end

end OAI
