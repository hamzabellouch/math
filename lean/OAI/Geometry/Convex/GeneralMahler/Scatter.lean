import OAI.Geometry.Convex.GeneralMahler.Edge
import OAI.Geometry.Convex.GeneralMahler.LogDet

namespace OAI
/-! The cone-valued maps in the entropy bound. Use cutoffs proven earlier
to get pointwise spatially local Lipschitz control; this allows applying the
injective-area formula directly on a conull set. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ}

structure Scatter (m:ℕ) extends Edge m where
  cone : ProperCone ℝ (Rn m)
  B : Mat m
  inj : Function.Injective (op B)
  d : ℝ→Rn m
  dp : PolyBound d
  dc : Continuous d
  M : ℝ
  hm : 1≤M
  in_cone : ∀ (z:ℝ) x,M*(1+‖x‖)<z → op B x + d z ∈ cone
  opp : ∀ (z:ℝ) x,M*(1+‖x‖)< -z → -(op B x + d z) ∈ posDual cone
  diff : ∀ᵐ x:Rn m,∀ᵐ z:ℝ,
    HasFDerivAt (fun x=>coneProj cone (op B x+d z)) ((op (P z x)).comp (op B)) x

namespace Scatter
variable (q:Scatter m)
def y (z:ℝ) (x:Rn m) := coneProj q.cone (op q.B x+q.d z)
lemma yc : Continuous q.y.uncurry :=
  (coneProj_lip q.cone).continuous.comp
    (((op q.B).continuous.comp continuous_snd).add (q.dc.comp continuous_fst))
lemma yp : PolyBound q.y.uncurry := by
  change PolyBound (fun x:ℝ × Rn m=> coneProj q.cone (op q.B x.2 + q.d x.1))
  exact (PolyBound.lipschitz (coneProj_lip q.cone)).comp
    (((PolyBound.clm (op q.B)).comp PolyBound.snd).add (q.dp.comp PolyBound.fst))
lemma yl (z:ℝ) : LipschitzWith ‖op q.B‖₊ (q.y z) := by
  convert (coneProj_lip q.cone).comp ((op q.B).lipschitzWith.add (LipschitzWith.const (q.d z)))
    using 1
  all_goals first | rfl | simp
lemma zero_y (z x) (hz:q.M*(1+‖x‖)< -z) : q.y z x=0 :=
  proj_zero_of_dual _ _ (q.opp z x hz)
lemma linear_y (z x) (hz:q.M*(1+‖x‖)<z) : q.y z x=op q.B x+q.d z :=
  proj_of_mem _ (q.in_cone z x hz)

def ky (z:ℝ) (x:Rn m) := MillsW z • q.y z x
lemma kc : Continuous q.ky.uncurry := (c_mw.comp continuous_fst).smul q.yc

lemma km : mixed q.ky := by
  let f := fun z x => (MillsW z * st z) • q.y z x
  let g := fun z x => (MillsW z-MillsW z*st z) • q.y z x
  have he : q.ky = fun z x=>f z x+g z x := by ext; simp only [f,g,sub_smul,ky]; abel_nf
  rw [he]
  have hh : mixed f :=
    (mixed.of_rapid (Y:=Rn m) rapid_mws).product q.yp fun x y=>by unfold f; rw [norm_smul]
  apply hh.add
  have ht := poly_mw.comp (PolyBound.fst (E:=Rn m))
  have hs := Edge.st_poly.comp (PolyBound.fst (E:=Rn m))
  let d := fun x:Rn m=> q.M*(1+‖x‖)
  apply mixed.of_cutoff (show PolyBound g.uncurry from (ht.sub (ht.mul hs)).smul q.yp)
    (show PolyBound d from (PolyBound.const _).mul ((PolyBound.const _).add PolyBound.id.norm))
  intro z x hx
  unfold g st
  split_ifs with h
  · simp
  rw [q.zero_y _ _ (by change q.M*(1+‖x‖)<‖z‖ at hx; rwa [Real.norm_eq_abs,abs_of_neg (lt_of_not_ge h)] at hx),smul_zero]

lemma ki (x:Rn m) : Integrable (fun z=>q.ky z x) :=
  mixed_integrable_left q.km x (q.kc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
lemma Ki : Integrable q.ky.uncurry (volume.prod (normal m)) :=
  mixed_integrable q.km q.kc.aestronglyMeasurable
lemma klip (x:Rn m) :
    ∃ h:ℝ→ℝ, Integrable h ∧ ∀ z w, w∈ball x 1 →
      ‖q.ky z w-q.ky z x‖ ≤ h z*‖w-x‖ := by
  classical
  let L := q.M*(1+‖x‖+1)
  have hm := q.hm
  let S := Ioi (-L-1)
  let f := fun z:ℝ=> ‖op q.B‖*MillsW z
  refine ⟨S.indicator f, (integrable_indicator_iff measurableSet_Ioi).mpr
    ((mw_tail _).1.const_mul _),?_⟩
  intro z w hw
  unfold ky; rw [← smul_sub,norm_smul,Real.norm_of_nonneg (mw_pos z).le]
  by_cases hz:z∈S
  · rw [indicator_of_mem hz]
    have hu := (q.yl z).dist_le_mul w x
    rw [dist_eq_norm,dist_eq_norm] at hu
    exact le_trans (mul_le_mul_of_nonneg_left hu (mw_pos _).le) (by unfold f; simp; apply le_of_eq; ring)
  rw [indicator_of_notMem hz]
  have hh : ‖w‖ ≤ 1+‖x‖ := by
    apply le_trans (show ‖w‖ ≤ ‖w-x‖+‖x‖ by simpa using norm_add_le (w-x) x)
    change dist w x < 1 at hw; rw [dist_eq_norm] at hw; linarith
  change ¬-(q.M*(1+‖x‖+1))-1 < z at hz
  rw [q.zero_y z w (by nlinarith),q.zero_y z x (by nlinarith)]
  simp

def t (x:Rn m) := ∫ z,q.ky z x
lemma tsm : StronglyMeasurable q.t := q.kc.stronglyMeasurable.integral_prod_left
lemma tp : PolyBound q.t := poly_integral_left q.km fun x=>(q.ki x).aestronglyMeasurable
lemma ti : Integrable q.t (normal m) := q.tp.gaussian_integrable q.tsm.aestronglyMeasurable

lemma t_in (x) : q.t x∈ q.cone := by
  apply (show ∀ v, (v:Rn m) ∈ posDual (posDual q.cone) → v∈q.cone from by
    intro v; rw [show posDual (posDual q.cone) = q.cone from ProperCone.innerDual_innerDual _]; exact id)
  rw [mem_posDual]
  intro w hw
  let l : Rn m→L[ℝ]ℝ := innerSL ℝ w
  change 0 ≤ l (∫ z,q.ky z x)
  rw [← l.integral_comp_comm (q.ki x)]
  apply integral_nonneg
  intro z
  change 0 ≤ ⟪w,MillsW z • q.y z x⟫
  rw [real_inner_smul_right,real_inner_comm]
  exact mul_nonneg (mw_pos _).le (mem_posDual.mp hw (proj_mem ..))

lemma t_injective : Function.Injective q.t := by
  intro x y hxy
  by_contra he
  let b := op q.B x-op q.B y
  have hh : b≠0 := sub_ne_zero.mpr (fun heq=>he (q.inj heq))
  let l : Rn m →L[ℝ]ℝ := innerSL ℝ b
  let f := fun z => l (q.ky z x-q.ky z y)
  have hi : Integrable f := l.integrable_comp ((q.ki x).sub (q.ki y))
  have hu : (∫ z,f z)=0 := by
    unfold f
    rw [l.integral_comp_comm (show Integrable (fun z=>q.ky z x-q.ky z y) volume from (q.ki x).sub (q.ki y)), integral_sub (q.ki x) (q.ki y)]
    change l (q.t x - q.t y)=0
    rw [hxy,sub_self,_root_.map_zero]
  let L := max (q.M*(1+‖x‖)) (q.M*(1+‖y‖))
  have hf (z) : f z=MillsW z*⟪b,q.y z x-q.y z y⟫ := by unfold f ky; rw [← smul_sub,_root_.map_smul]; rfl
  have hn (z) : 0 ≤ f z := by
    rw [hf]
    apply mul_nonneg (mw_pos _).le
    have h := proj_firm q.cone (op q.B x+q.d z) (op q.B y+q.d z)
    rw [add_sub_add_right_eq_sub] at h
    exact (sq_nonneg _).trans h
  have he : Ioi L ⊆ Function.support f := by
    intro z hz
    rw [Function.mem_support,hf,q.linear_y _ _ (lt_of_le_of_lt (le_max_left ..) hz),q.linear_y _ _ (lt_of_le_of_lt (le_max_right ..) hz),add_sub_add_right_eq_sub]
    exact (mul_pos (mw_pos _) (real_inner_self_pos.mpr hh)).ne'
  have hpos := (integral_pos_iff_support_of_nonneg hn hi).mpr
    ((isOpen_Ioi.measure_pos volume (nonempty_Ioi (a:=L))).trans_le (measure_mono he))
  linarith

def TJ (x:Rn m) := q.toEdge.Jedge x * q.B
lemma td [NeZero m] : ∀ᵐ x:Rn m, HasFDerivAt q.t (op (q.TJ x)) x := by
  let : CompleteSpace (Rn m →L[ℝ] Rn m) := ContinuousLinearMap.instCompleteSpace
  filter_upwards [q.diff] with x hx
  let F := fun x z=> q.ky z x
  let A := fun z=> q.toEdge.WP z x*q.B
  let f := fun z=> op (A z)
  let l : Mat m→L[ℝ] Mat m := (ContinuousLinearMap.mul ℝ _).flip q.B
  have hi := q.toEdge.wp_slice_i x
  have ha : Integrable A := l.integrable_comp hi
  obtain ⟨b,hb,h⟩ := q.klip x
  have HH := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (F:=F) (F':=f) (𝕜:=ℝ) (ball_mem_nhds x (show (0:ℝ)<1 by norm_num))
    (fun x _=> (q.ki x).aestronglyMeasurable) (q.ki x)
    (opCLE.toContinuousLinearMap.integrable_comp ha).aestronglyMeasurable (ae_of_all _ h) hb ?_
  · have he : (∫ z,f z)=op (q.TJ x) := by
      change ∫ z,opCLE.toContinuousLinearMap (A z)=_
      rw [opCLE.toContinuousLinearMap.integral_comp_comm ha]
      have he : (∫ z,A z)=q.TJ x := l.integral_comp_comm hi
      rw [he]; rfl
    exact he ▸ HH.2
  filter_upwards [hx] with z hz
  unfold f A Edge.WP
  rw [smul_mul_assoc,_root_.map_smul,_root_.map_mul]
  exact hz.const_smul (MillsW z)

end Scatter
end GeneralMahler

end

end OAI
