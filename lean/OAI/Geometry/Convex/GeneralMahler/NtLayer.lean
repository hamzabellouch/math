import OAI.Geometry.Convex.GeneralMahler.EdgeBand

namespace OAI
/-! Nonthreshold kernel and integration over the ordered halves.
We use (l,z) as pair of variables and ordinary product volume. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
abbrev Plane := ℝ × ℝ
variable {m:ℕ}

namespace Edge
variable (e:Edge m)
def NTm (u:Plane) (x:Rn m) :=
  jprod (e.P (min u.1 u.2) x) (1-e.P (max u.1 u.2) x)
def nt0 (u:Plane) (x:Rn m) := trN (e.NTm u x)
lemma nt_sym (u x) : e.nt0 u.swap x=e.nt0 u x := by simp [nt0,NTm,min_comm,max_comm]
lemma nt_pos (u x) : 0 ≤ e.nt0 u x := by
  unfold nt0 NTm; rw [trN_j]
  exact trN_mul_nonneg (e.psd ..) (sub_nonneg.mpr (e.le_one ..))
lemma nt_meas : Measurable e.NTm.uncurry := by
  let m₁ := fun v:Plane×Rn m=> e.P (min v.1.1 v.1.2) v.2
  let m₂ := fun v:Plane×Rn m=> 1-e.P (max v.1.1 v.1.2) v.2
  have he : Measurable m₁ := e.meas.comp (show Measurable (fun v:Plane×Rn m => (min v.1.1 v.1.2,v.2)) from by fun_prop)
  have hh : Measurable m₂ := measurable_const.sub (e.meas.comp (show Measurable (fun v:Plane×Rn m => (max v.1.1 v.1.2,v.2)) from by fun_prop))
  exact (show Measurable (fun _:Plane × Rn m=> (1/2:ℝ)) from measurable_const).smul ((he.mul hh).add (hh.mul he))
lemma nt_mixed : mixed e.NTm := by
  let f := fun v:Plane × Rn m => e.P (min v.1.1 v.1.2) v.2
  let g := fun v:Plane × Rn m => e.P (max v.1.1 v.1.2) v.2
  have hf : PolyBound f := PolyBound.of_bound 1 fun v=> e.Pcont ..
  have hg : PolyBound g := PolyBound.of_bound 1 fun v=> e.Pcont ..
  have hh := (PolyBound.const 1).sub hg
  have hp : PolyBound e.NTm.uncurry :=
    (PolyBound.const _).smul ((hf.mul hh).add (hh.mul hf))
  apply mixed.of_cutoff hp e.r_poly
  rintro ⟨z,w⟩ x hx
  let c := e.radius x
  change c < max ‖z‖ ‖w‖ at hx
  have hr : c< max z w ∨ min z w < -c := by
    simp only [Real.norm_eq_abs,lt_max_iff,lt_abs,min_lt_iff] at *
    grind
  rcases hr with h|h
  · simp only [NTm,e.tend_pos (max z w) x h,sub_self,jprod,mul_zero,zero_mul,add_zero,smul_zero]
  have he : e.P (min z w) x=0 := e.tend_neg _ _ (show c < -min z w by linarith)
  simp [NTm,he,jprod]

lemma n0_meas : StronglyMeasurable e.nt0.uncurry := (meas_trN.comp e.nt_meas).stronglyMeasurable
lemma n0_mixed : mixed e.nt0 := by
  let f := fun (_:Plane) (_:Rn m) => ‖(trL:Mat m→L[ℝ]ℝ)‖
  have hf : PolyBound f.uncurry := PolyBound.const _
  apply e.nt_mixed.product hf
  intro u x
  unfold nt0 f
  rw [← trL_apply,Real.norm_of_nonneg (norm_nonneg (trL:Mat m→L[ℝ]ℝ)),mul_comm]
  apply ContinuousLinearMap.le_opNorm
lemma n0_i (x:Rn m) : Integrable (fun u=> e.nt0 u x) :=
  mixed_integrable_left e.n0_mixed x
    ((e.n0_meas.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
lemma n0_int : Integrable e.nt0.uncurry (volume.prod (normal m)) :=
  mixed_integrable e.n0_mixed e.n0_meas.aestronglyMeasurable

-- reflection swap on ordered band
lemma nt_ref (u x) : e.ref.nt0 (-u.swap) x=e.nt0 u x := by
  change trN (jprod (1-e.P (-(min (-u.2) (-u.1))) x) (1-(1-e.P (-(max (-u.2) (-u.1))) x)))= _
  rw [show -(min (-u.2) (-u.1))=max u.1 u.2 from by grind, show -(max (-u.2) (-u.1))=min u.1 u.2 from by grind]
  simp [nt0,NTm,jprod,add_comm]

def BandS : Set Plane := {u|0 ≤ u.2 ∧ u.1∈Icc (-u.2) u.2}
lemma meas_BS : MeasurableSet BandS :=
  ((isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd.neg continuous_fst).inter
      (isClosed_le continuous_fst continuous_snd))).measurableSet

variable [NeZero m]

lemma band_area (x:Rn m) :
    (∫ u:Plane in BandS,e.nt0 u x) ≤ 4*∫ l,e.beta x l := by
  classical
  let f := fun u:Plane=> e.nt0 u x
  let g := BandS.indicator f
  have hi := (e.n0_i x).indicator meas_BS
  have he (z:ℝ) :
      (∫ l:ℝ,g (l,z)) ≤ 4*e.beta x z := by
    by_cases hz : 0≤z
    · have hh : (fun l:ℝ=>g (l,z)) = (Icc (-z) z).indicator (e.ntb x z) := by
        ext l
        by_cases hu:l∈Icc (-z) z
        · have hh : l≤z := hu.2
          unfold g; rw [indicator_of_mem (show (l,z)∈BandS from ⟨hz,hu⟩),indicator_of_mem hu]
          unfold f ntb nt0 NTm
          simp only [min_eq_left hh,max_eq_right hh,trN_j]
        unfold g; rw [indicator_of_notMem (show (l,z)∉BandS from fun h=>hu h.2),indicator_of_notMem hu]
      apply le_trans _ (e.band x z hz)
      rw [intervalIntegral.integral_of_le (by linarith),hh,integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc]
    have hh : (fun l:ℝ=>g (l,z))=fun _=>0 := by
      ext l
      exact indicator_of_notMem (show (l,z)∉BandS from fun h=> hz h.1) f
    rw [hh,integral_zero]; exact mul_nonneg (by norm_num) (e.beta_bound ..).1
  have hb : Integrable (e.beta x) := mixed_integrable_left e.beta_mixed x
    (e.meas_beta.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  rw [← integral_indicator meas_BS]
  change (∫ u:Plane,g u ∂volume.prod volume) ≤ _
  rw [integral_prod_symm _ hi,← integral_const_mul]
  exact integral_mono hi.integral_prod_right (hb.const_mul _) he

-- measure transformations preserving volume
def rs (u:Plane) := -u.swap
lemma rs_int (f:Plane→ℝ) : (∫ u,f (rs u))=∫ u,f u := by
  change (∫ u:Plane,(fun u=>f (-u)) u.swap ∂volume.prod volume)=∫ u,f u
  rw [integral_prod_swap (fun u:Plane=> f (-u))]
  exact integral_neg_eq_self f volume

lemma total_surplus (x:Rn m) :
    (∫ u:Plane,e.nt0 u x) ≤ 8*((∫ l,e.beta x l)+(∫ l,e.ref.beta x l)) := by
  classical
  let f := fun u:Plane=>e.nt0 u x
  let g := BandS.indicator f
  let h := BandS.indicator fun u:Plane=>e.ref.nt0 u x
  have he (u:Plane) :
      f u ≤ g u+g u.swap+h (rs u)+h (rs u.swap) := by
    have hi (w:Plane) : h (rs w)=if rs w∈BandS then f w else 0 := by
      unfold h; simp [indicator,e.nt_ref,f,rs]; rfl
    rw [hi,hi]
    have Hv : f u.swap=f u := e.nt_sym ..
    unfold g
    rw [Set.indicator_apply,Set.indicator_apply]
    rw [Hv]
    have hx := e.nt_pos u x
    change 0 ≤ f u at hx
    by_cases hs:u.1≤u.2
    · by_cases ht:0≤u.1+u.2
      · have hb:u∈BandS := by change 0≤_ ∧ _ ≤ _ ∧ _ ≤ _; grind
        split_ifs <;> linarith
      have hb:rs u∈BandS := by change 0 ≤ -_ ∧ - -_ ≤ -_ ∧ -_ ≤ -_; grind
      split_ifs <;> linarith
    by_cases ht:0≤u.1+u.2
    · have hb:u.swap∈BandS := by change 0≤u.1∧ _≤u.2 ∧ _ ≤ u.1; grind
      split_ifs <;> linarith
    have hb:rs u.swap∈BandS := by change 0≤ -u.2∧ - -u.2≤ -u.1 ∧ -u.1≤ -u.2; grind
    split_ifs <;> linarith
  have hi : Integrable f := e.n0_i x
  have hg : Integrable g := hi.indicator meas_BS
  have hh : Integrable h := (e.ref.n0_i x).indicator meas_BS
  have hu : Integrable (fun u=> h (rs u)) := by
    have ha : Integrable (fun u=>h (-u)) :=
      (Measure.measurePreserving_neg volume).integrable_comp_emb (Homeomorph.neg _).measurableEmbedding |>.mpr hh
    apply ha.swap
  apply le_trans (integral_mono hi (((hg.add hg.swap).add hu).add hu.swap) he)
  let v := fun u=>h (rs u)
  change (∫ u:Plane,g u+g u.swap+v u+v u.swap) ≤ _
  rw [integral_add, integral_add, integral_add]
  · have Hb := e.band_area x
    have Hc := e.ref.band_area x
    rw [← integral_indicator meas_BS] at Hb Hc
    have Hv := rs_int h
    change (∫ u,v u)=_ at Hv
    have H₁ (f:Plane→ℝ) : (∫ u:Plane,f u.swap)=∫ u,f u := integral_prod_swap _
    rw [H₁,H₁,Hv]
    change (∫ u,g u) ≤ _ at Hb; change (∫ u,h u) ≤ _ at Hc
    linarith
  all_goals first | exact hg | exact hg.swap | exact hu |
    exact hu.swap | exact hg.add hg.swap | exact (hg.add hg.swap).add hu

end Edge
end GeneralMahler

end

end OAI
