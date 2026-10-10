import Mathlib
import OAI.Probability.LatticeSurface.Convexity.HeatBath
import OAI.Probability.LatticeSurface.Dynamics.IntervalResampling

namespace OAI

namespace BoundedData

open Set MeasureTheory ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

lemma lower_update (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (h : Free pins → ℝ) (x : Free pins) (t : ℝ) :
    lower G pins hn b (Function.update h x t) x=lower G pins hn b h x := by
  classical
  unfold lower
  apply Finset.sup'_congr (hn x) rfl
  intro y hy
  have hyx : y≠(x:V) := (show G.Adj x y by simpa using hy).ne.symm
  rw [restore_update,ite_eq_right hyx]

lemma upper_update (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (h : Free pins → ℝ) (x : Free pins) (t : ℝ) :
    upper G pins hn b (Function.update h x t) x=upper G pins hn b h x := by
  classical
  unfold upper
  apply Finset.inf'_congr (hn x) rfl
  intro y hy
  have hyx : y≠(x:V) := (show G.Adj x y by simpa using hy).ne.symm
  rw [restore_update,ite_eq_right hyx]

omit [Fintype V] in
lemma split_inv_update (pins : Set V) (x : Free pins)
    (w : Free (insert (x:V) pins) → ℝ) (s t : ℝ) :
    (splitCoordinate pins x x.property).symm (w,t)=
      Function.update ((splitCoordinate pins x x.property).symm (w,s)) x t := by
  classical
  ext y
  have hleft := coordinate_restore pins x x.property (fun _ => 0) w t (y:V)
  have hright := coordinate_restore pins x x.property (fun _ => 0) w s (y:V)
  have hrest := restore_update pins (fun _ => 0) ((splitCoordinate pins x x.property).symm (w,s)) x t (y:V)
  have hy : restore pins (fun _ : V => (0:ℝ)) ((splitCoordinate pins x x.property).symm (w,t)) y=
      restore pins (fun _ => 0) (Function.update ((splitCoordinate pins x x.property).symm (w,s)) x t) y := by
    rw [hleft,hrest,hright]
    split <;> rfl
  simpa only [restore,dite_eq_right y.property] using hy

lemma continuous_update (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (x : Free pins) : Continuous (fun z : (Free pins → ℝ)×ℝ => update G pins hn b x z.1 z.2) := by
  classical
  apply continuous_pi
  intro y
  by_cases hy : y=x
  · subst y
    simpa [update] using (show Continuous (fun z : (Free pins → ℝ)×ℝ =>
      (1-z.2)*lower G pins hn b z.1 x+z.2*upper G pins hn b z.1 x) from
      ((continuous_const.sub continuous_snd).mul ((continuous_lower G pins hn b x).comp continuous_fst)).add
      (continuous_snd.mul ((continuous_upper G pins hn b x).comp continuous_fst)))
  · simpa only [update,Function.update_of_ne hy,Function.comp_def] using (continuous_apply y).comp continuous_fst

lemma split_body_region (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (x : Free pins) :
    ∃ (R : Set (Free (insert (x:V) pins) → ℝ)) (l u : (Free (insert (x:V) pins) → ℝ) → ℝ),
      MeasurableSet R ∧ Measurable l ∧ Measurable u ∧
      (splitCoordinate pins x x.property).symm ⁻¹' conditionalBody G pins b=IntervalResampling.region R l u ∧
      ∀ w t,lower G pins hn b ((splitCoordinate pins x x.property).symm (w,t)) x=l w ∧
        upper G pins hn b ((splitCoordinate pins x x.property).symm (w,t)) x=u w := by
  classical
  let e := splitCoordinate pins x x.property
  let h₀ := fun w => e.symm (w,0)
  let R := {w | ∀ y z,G.Adj y z → y≠(x:V) → z≠(x:V) → |restore pins b (h₀ w) y-restore pins b (h₀ w) z|≤1}
  let l := fun w => lower G pins hn b (h₀ w) x
  let u := fun w => upper G pins hn b (h₀ w) x
  have hm : Measurable h₀ := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hR : MeasurableSet R := by
    dsimp [R]
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro y
    apply MeasurableSet.iInter
    intro z
    apply MeasurableSet.iInter
    intro hyz
    apply MeasurableSet.iInter
    intro hy
    apply MeasurableSet.iInter
    intro hz
    exact measurableSet_le (((continuous_restore pins b y).measurable.comp hm).sub
      ((continuous_restore pins b z).measurable.comp hm)).abs measurable_const
  have hlu (w) (t : ℝ) : lower G pins hn b (e.symm (w,t)) x=l w ∧ upper G pins hn b (e.symm (w,t)) x=u w := by
    rw [split_inv_update pins x w 0 t,lower_update,upper_update]
    exact ⟨rfl,rfl⟩
  refine ⟨R,l,u,hR,(continuous_lower G pins hn b x).measurable.comp hm,
    (continuous_upper G pins hn b x).measurable.comp hm,?_,hlu⟩
  ext ⟨w,t⟩
  have hxval : e.symm (w,t) x=t := by
    have := coordinate_restore pins x x.property b w t x
    simpa [restore,x.property] using this
  constructor
  · intro hh
    refine ⟨?_,?_,?_⟩
    · intro y z hyz hy hz
      have ht := hh y z hyz
      change |restore pins b (e.symm (w,t)) y-restore pins b (e.symm (w,t)) z|≤1 at ht
      rw [split_inv_update pins x w 0 t,restore_update,restore_update,ite_eq_right hy,ite_eq_right hz] at ht
      exact ht
    · simpa only [(hlu w t).1,hxval] using lower_le G pins hn b (e.symm (w,t)) hh x
    · simpa only [(hlu w t).2,hxval] using le_upper G pins hn b (e.symm (w,t)) hh x
  · rintro ⟨hw,htl,htu⟩ y z hyz
    change |restore pins b (e.symm (w,t)) y-restore pins b (e.symm (w,t)) z|≤1
    rw [split_inv_update pins x w 0 t,restore_update,restore_update]
    have ha (y : V) (hy : G.Adj x y) : |t-restore pins b (h₀ w) y|≤1 := by
      have hl := (Finset.le_sup' (s := G.neighborFinset x) (f := fun y => restore pins b (h₀ w) y-1) (by simpa using hy)).trans htl
      have hu := htu.trans (Finset.inf'_le (s := G.neighborFinset x) (f := fun y => restore pins b (h₀ w) y+1) (by simpa using hy))
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    by_cases hy : y=(x:V)
    · subst y
      simpa only [ite_true,ite_eq_left rfl,ite_eq_right hyz.ne.symm] using ha z hyz
    · by_cases hz : z=(x:V)
      · subst z
        simpa only [ite_true,ite_eq_right hy,ite_eq_left rfl,abs_sub_comm] using ha y hyz.symm
      · simpa only [ite_eq_right hy,ite_eq_right hz] using hw y z hyz hy hz

end BoundedData

namespace BoundedData

open Set MeasureTheory ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

lemma lower_bound_difference (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b c : V → ℝ) (h k : Free pins → ℝ) (x : Free pins) (C : ℝ)
    (hb : ∀ y,|restore pins b h y-restore pins c k y|≤C) :
    |lower G pins hn b h x-lower G pins hn c k x|≤C := by
  have hle (b c : V → ℝ) (h k : Free pins → ℝ)
      (hb : ∀ y,restore pins b h y-restore pins c k y≤C) :
      lower G pins hn b h x≤lower G pins hn c k x+C := by
    apply Finset.sup'_le
    intro y hy
    have hc := Finset.le_sup' (s := G.neighborFinset x) (f := fun y => restore pins c k y-1) hy
    change restore pins c k y-1≤lower G pins hn c k x at hc
    linarith [hb y]
  exact abs_le.mpr ⟨by linarith [hle c b k h (fun y => by linarith [(abs_le.mp (hb y)).1])],
    by linarith [hle b c h k (fun y => (abs_le.mp (hb y)).2)]⟩

lemma upper_bound_difference (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b c : V → ℝ) (h k : Free pins → ℝ) (x : Free pins) (C : ℝ)
    (hb : ∀ y,|restore pins b h y-restore pins c k y|≤C) :
    |upper G pins hn b h x-upper G pins hn c k x|≤C := by
  have hle (b c : V → ℝ) (h k : Free pins → ℝ)
      (hb : ∀ y,restore pins b h y-restore pins c k y≤C) :
      upper G pins hn b h x≤upper G pins hn c k x+C := by
    obtain ⟨y,hy,he⟩ := Finset.exists_mem_eq_inf' (hn x) (fun y => restore pins c k y+1)
    have hc := Finset.inf'_le (s := G.neighborFinset x) (f := fun y => restore pins b h y+1) hy
    change upper G pins hn b h x≤restore pins b h y+1 at hc
    change upper G pins hn c k x=restore pins c k y+1 at he
    linarith [hb y]
  exact abs_le.mpr ⟨by linarith [hle c b k h (fun y => by linarith [(abs_le.mp (hb y)).1])],
    by linarith [hle b c h k (fun y => (abs_le.mp (hb y)).2)]⟩

lemma update_bound_difference (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b c : V → ℝ) (h k : Free pins → ℝ) (x : Free pins) (C : ℝ)
    (hb : ∀ y,|restore pins b h y-restore pins c k y|≤C) {t : ℝ} (ht : t∈Icc 0 1) :
    ∀ y,|restore pins b (update G pins hn b x h t) y-restore pins c (update G pins hn c x k t) y|≤C := by
  intro y
  unfold update
  rw [restore_update,restore_update]
  by_cases hy : y=(x:V)
  · rw [ite_eq_left hy,ite_eq_left hy]
    have hl := abs_le.mp (lower_bound_difference G pins hn b c h k x C hb)
    have hu := abs_le.mp (upper_bound_difference G pins hn b c h k x C hb)
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hl.1),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hl.2),
      mul_nonneg ht.1 (sub_nonneg.mpr hu.1),mul_nonneg ht.1 (sub_nonneg.mpr hu.2)]
  · simpa only [ite_eq_right hy] using hb y

lemma update_norm_difference (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b c : V → ℝ) (h k : Free pins → ℝ) (x : Free pins) {t : ℝ} (ht : t∈Icc 0 1) :
    ‖restore pins b (update G pins hn b x h t)-restore pins c (update G pins hn c x k t)‖≤
    ‖restore pins b h-restore pins c k‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro y
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using update_bound_difference G pins hn b c h k x
    ‖restore pins b h-restore pins c k‖ (fun y => by simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (restore pins b h-restore pins c k) y) ht y

lemma update_sum (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (h : Free pins → ℝ) (x : Free pins) :
    (∑ y,update G pins hn b x h 0 y)=(∑ y,h y)-h x+lower G pins hn b h x := by
  classical
  simp only [update,sub_zero,one_mul,zero_mul,add_zero]
  rw [Finset.sum_update_of_mem (Finset.mem_univ x),← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

end BoundedData

end OAI
