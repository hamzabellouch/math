import OAI.Geometry.PlaneColoring.PaletteTransport

namespace OAI

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
/-- Common unit neighbor for the transverse chord of length `t`. -/
def evenOffset (v : ℂ) (t : ℝ) : ℂ :=
  ((Real.sqrt (1-t^2/4) : ℂ)+((t/2 : ℝ) : ℂ)*Complex.I)*v
lemma norm_even_wing {t : ℝ} (ht : |t|<2) :
    ‖(Real.sqrt (1-t^2/4) : ℂ)+((t/2 : ℝ) : ℂ)*Complex.I‖=1 := by
  have ht2 : t^2≤4 := by
    have hh := mul_self_le_mul_self (abs_nonneg t) ht.le
    nlinarith [sq_abs t]
  have hsq := Real.sq_sqrt (show 0≤1-t^2/4 by linarith)
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : 0≤(1:ℝ))).mp
  rw [Complex.sq_norm,Complex.normSq_apply]
  norm_num only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im,mul_zero,zero_mul,sub_zero,
    add_zero,zero_add,mul_one]
  nlinarith
lemma evenOffset_distances {v : ℂ} (hv : ‖v‖=1) {t : ℝ} (ht : |t|<2) :
    ‖evenOffset v t‖=1 ∧ ‖evenOffset v t-(t:ℂ)*(Complex.I*v)‖=1 := by
  constructor
  · rw [evenOffset,norm_mul,norm_even_wing ht,hv,mul_one]
  · have he : evenOffset v t-(t:ℂ)*(Complex.I*v)=evenOffset v (-t) := by
      simp only [evenOffset,neg_sq,neg_div,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
      ring
    rw [he,evenOffset,norm_mul,norm_even_wing (by simpa only [abs_neg] using ht),hv,mul_one]
@[fun_prop] lemma continuous_evenOffset (v : ℂ) : Continuous (evenOffset v) := by
  unfold evenOffset
  fun_prop
lemma evenOffset_zero (v : ℂ) : evenOffset v 0=v := by simp [evenOffset]
def transverseDet (v w : ℂ) : ℝ :=
  (Complex.I*v).re*(Complex.I*w).im-(Complex.I*w).re*(Complex.I*v).im
def transverseFirst (v w h : ℂ) : ℝ :=
  (h.re*(Complex.I*w).im-(Complex.I*w).re*h.im)/transverseDet v w
def transverseSecond (v w h : ℂ) : ℝ :=
  ((Complex.I*v).re*h.im-h.re*(Complex.I*v).im)/transverseDet v w
lemma transverse_decompose {v w : ℂ} (hd : transverseDet v w≠0) (h : ℂ) :
    (transverseFirst v w h : ℂ)*(Complex.I*v)+
      (transverseSecond v w h : ℂ)*(Complex.I*w)=h := by
  apply Complex.ext <;>
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.add_im,Complex.mul_im,zero_mul,sub_zero,add_zero,
      transverseFirst,transverseSecond] <;>
    field_simp <;> dsimp [transverseDet] <;>
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,zero_add] <;> ring
@[fun_prop] lemma continuous_transverseFirst (v w : ℂ) : Continuous (transverseFirst v w) := by
  unfold transverseFirst
  fun_prop
@[fun_prop] lemma continuous_transverseSecond (v w : ℂ) : Continuous (transverseSecond v w) := by
  unfold transverseSecond
  fun_prop
lemma transverseFirst_zero (v w : ℂ) : transverseFirst v w 0=0 := by simp [transverseFirst]
lemma transverseSecond_zero (v w : ℂ) : transverseSecond v w 0=0 := by simp [transverseSecond]
def evenPath (v w h : ℂ) : Fin 5 → ℂ := ![0,
  evenOffset v (transverseFirst v w h),
  (transverseFirst v w h : ℂ)*(Complex.I*v),
  (transverseFirst v w h : ℂ)*(Complex.I*v)+evenOffset w (transverseSecond v w h),h]
lemma evenPath_edges {v w h : ℂ} (hv : ‖v‖=1) (hw : ‖w‖=1)
    (hd : transverseDet v w≠0) (h₁ : |transverseFirst v w h|<2)
    (h₂ : |transverseSecond v w h|<2) :
    ∀i : Fin 4, ‖evenPath v w h i.castSucc-evenPath v w h i.succ‖=1 := by
  have he₁ := evenOffset_distances hv h₁
  have he₂ := evenOffset_distances hw h₂
  have hdec := transverse_decompose hd h
  intro i
  fin_cases i
  · change ‖0-evenOffset v (transverseFirst v w h)‖=1
    simpa only [zero_sub,norm_neg] using he₁.1
  · exact he₁.2
  · change ‖(transverseFirst v w h : ℂ)*(Complex.I*v)-
        ((transverseFirst v w h : ℂ)*(Complex.I*v)+evenOffset w (transverseSecond v w h))‖=1
    simpa only [sub_add_cancel_left,norm_neg] using he₂.1
  · change ‖(transverseFirst v w h : ℂ)*(Complex.I*v)+evenOffset w (transverseSecond v w h)-h‖=1
    calc
      _ = ‖evenOffset w (transverseSecond v w h)-(transverseSecond v w h : ℂ)*(Complex.I*w)‖ :=
        congrArg norm (by linear_combination hdec)
      _ = 1 := he₂.2
/-- Actual four-unit-edge paths stay inside the prescribed two open sets for
all small starting-point and displacement perturbations. -/
lemma evenPath_local {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {p v w : ℂ} (hp : p∈U) (hpv : p+v∈V) (hpw : p+w∈V) :
    ∃r>0,∃δ>0,∀q h : ℂ,q∈Metric.ball p r → ‖h‖<δ →
      |transverseFirst v w h|<2 ∧ |transverseSecond v w h|<2 ∧
      (∀i : Fin 5,(q+evenPath v w h i)∈if i.val%2=0 then U else V) := by
  let P : ℂ × ℂ → Prop := fun z => |transverseFirst v w z.2|<2 ∧
    |transverseSecond v w z.2|<2 ∧
    (∀i : Fin 5,(z.1+evenPath v w z.2 i)∈if i.val%2=0 then U else V)
  have hm : ∀ᶠz in 𝓝 (p,(0:ℂ)),P z := by
    have ha : ∀ᶠz : ℂ × ℂ in 𝓝 (p,(0:ℂ)), |transverseFirst v w z.2|<2 := by
      apply ((continuous_transverseFirst v w).comp continuous_snd).abs.continuousAt.eventually_lt continuousAt_const
      simp [transverseFirst_zero]
    have hb : ∀ᶠz : ℂ × ℂ in 𝓝 (p,(0:ℂ)), |transverseSecond v w z.2|<2 := by
      apply ((continuous_transverseSecond v w).comp continuous_snd).abs.continuousAt.eventually_lt continuousAt_const
      simp [transverseSecond_zero]
    have hc (i : Fin 5) : ∀ᶠz : ℂ × ℂ in 𝓝 (p,(0:ℂ)),
        (z.1+evenPath v w z.2 i)∈if i.val%2=0 then U else V := by
      have hco : Continuous (fun z : ℂ × ℂ => z.1+evenPath v w z.2 i) := by
        fin_cases i <;> dsimp [evenPath] <;> fun_prop
      apply hco.continuousAt.eventually
      fin_cases i <;> norm_num [evenPath,transverseFirst_zero,transverseSecond_zero,evenOffset_zero]
      · exact hU.mem_nhds hp
      · exact hV.mem_nhds hpv
      · exact hU.mem_nhds hp
      · exact hV.mem_nhds hpw
      · exact hU.mem_nhds hp
    exact ha.and (hb.and (eventually_all.mpr hc))
  obtain ⟨ε,hε,hb⟩ := Metric.mem_nhds_iff.mp hm
  refine ⟨ε,hε,ε,hε,?_⟩
  intro q h hq hh
  exact hb (show (q,h)∈Metric.ball (p,(0:ℂ)) ε by
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_zero_right,max_lt_iff] using And.intro hq hh)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Local invariance for every sufficiently small fixed translation forces
local essential constancy. This is the Fubini/shear step of angular-binary-local. -/
lemma local_ae_translation_constant {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Countable ι] (c : ℂ → ι) (hc : Measurable c) {p : ℂ} {r δ : ℝ}
    (hr : 0<r) (hδ : 0<δ)
    (hshift : ∀h : ℂ,‖h‖<δ → ∀ᵐq : ℂ∂volume,q∈Metric.ball p r → c (q+h)=c q) :
    ∃s>0,s≤r ∧ ∃i,∀ᵐq : ℂ∂volume,q∈Metric.ball p s → c q=i := by
  let s : ℝ := min r δ/4
  have hs : 0<s := by dsimp [s]; positivity
  have hsr : s≤r := by dsimp [s]; linarith [min_le_left r δ,lt_min hr hδ]
  have hsd : 2*s<δ := by dsimp [s]; linarith [min_le_right r δ,lt_min hr hδ]
  have hpair : ∀ᵐz : ℂ × ℂ∂volume.prod volume,
      ‖z.1‖<δ → z.2∈Metric.ball p r → c (z.2+z.1)=c z.2 := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · exact Eventually.of_forall fun h => by
        by_cases hh : ‖h‖<δ
        · exact (hshift h hh).mono fun q hq _ => hq
        · exact Eventually.of_forall fun _ hh' => (hh hh').elim
    · have hx : MeasurableSet {z : ℂ × ℂ | ‖z.1‖<δ} := measurableSet_lt measurable_fst.norm measurable_const
      have hy : MeasurableSet {z : ℂ × ℂ | z.2∈Metric.ball p r} := Metric.isOpen_ball.measurableSet.preimage measurable_snd
      have hz : MeasurableSet {z : ℂ × ℂ | c (z.2+z.1)=c z.2} :=
        measurableSet_eq_fun (hc.comp (measurable_snd.add measurable_fst)) (hc.comp measurable_snd)
      exact hx.imp (hy.imp hz)
  have hd := (measurePreserving_sub_prod (volume : Measure ℂ) volume).quasiMeasurePreserving.ae hpair
  have he : ∀ᵐz : ℂ × ℂ∂volume.prod volume,
      z.1∈Metric.ball p s → z.2∈Metric.ball p s → c z.1=c z.2 := by
    filter_upwards [hd] with z hz h1 h2
    have hdist : ‖z.1-z.2‖<δ := by
      rw [←dist_eq_norm]
      have h := dist_triangle z.1 p z.2
      have h2' : dist p z.2<s := by simpa only [Metric.mem_ball,dist_comm] using h2
      have h1' : dist z.1 p<s := h1
      linarith
    have hh := hz hdist (Metric.ball_subset_ball hsr h2)
    simpa only [add_sub_cancel] using hh
  have hae := Measure.ae_ae_of_ae_prod he
  obtain ⟨q,hq,hqae⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (Metric.measure_ball_pos volume p hs).ne' (ae_restrict_of_ae hae)
  refine ⟨s,hs,hsr,c q,?_⟩
  exact hqae.mono fun z hz hzs => (hz hq hzs).symm
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma binary_two_edges {ι : Type*} {a b u v w : ι} (hu : u=a ∨ u=b)
    (hv : v=a ∨ v=b) (hw : w=a ∨ w=b) (huv : u≠v) (hvw : v≠w) : u=w := by
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> rcases hw with rfl|rfl <;> tauto
lemma ae_translated_unit_pair {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (hw : WeakColoring k c)
    {a b : ℂ} (hab : ‖a-b‖=1) : ∀ᵐq : ℂ∂volume,c (q+a)≠c (q+b) := by
  obtain ⟨t,ht⟩ := direction_exists (u:=b-a) (by simpa only [norm_sub_rev] using hab)
  have hh := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (weak_all_directions c hc hw t)
  filter_upwards [hh] with q hq
  simpa only [ht,show q+a+(b-a)=q+b by ring] using hq
/-- Local essential constancy inside two-color open regions, from the source's
actual four-edge paths. The directions are genuine unit directions landing in V. -/
lemma binary_open_local_rigidity {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (hw : WeakColoring k c)
    {a b : Fin k} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : ∀ᵐq : ℂ∂volume,q∈U → c q=a ∨ c q=b)
    (hVc : ∀ᵐq : ℂ∂volume,q∈V → c q=a ∨ c q=b)
    {p v w : ℂ} (hp : p∈U) (hpv : p+v∈V) (hpw : p+w∈V)
    (hv : ‖v‖=1) (hw' : ‖w‖=1) (hd : transverseDet v w≠0) :
    ∃r>0,∃i : Fin k,∀ᵐq : ℂ∂volume,q∈Metric.ball p r → c q=i := by
  obtain ⟨r,hr,δ,hδ,hinside⟩ := evenPath_local hU hV hp hpv hpw
  have hshift (h : ℂ) (hh : ‖h‖<δ) :
      ∀ᵐq : ℂ∂volume,q∈Metric.ball p r → c (q+h)=c q := by
    have hsmall := hinside p h (Metric.mem_ball_self hr) hh
    have hedges := evenPath_edges hv hw' hd hsmall.1 hsmall.2.1
    have hcm (i : Fin 5) := (measurePreserving_add_right volume (evenPath v w h i)).quasiMeasurePreserving.ae (hUc.and hVc)
    have hne (i : Fin 4) := ae_translated_unit_pair hc hw (hedges i)
    filter_upwards [ae_all_iff.mpr hcm,ae_all_iff.mpr hne] with q hqc hqp hq
    have hi := (hinside q h hq hh).2.2
    have hcol (i : Fin 5) : c (q+evenPath v w h i)=a ∨ c (q+evenPath v w h i)=b := by
      have hii := hi i
      by_cases he : i.val%2=0
      · exact (hqc i).1 (by simpa only [he,ite_true] using hii)
      · exact (hqc i).2 (by simpa only [he,ite_false] using hii)
    have he02 := binary_two_edges (hcol 0) (hcol 1) (hcol 2) (hqp 0) (hqp 1)
    have he24 := binary_two_edges (hcol 2) (hcol 3) (hcol 4) (hqp 2) (hqp 3)
    change c (q+0)=c (q+evenPath v w h 2) at he02
    change c (q+evenPath v w h 2)=c (q+h) at he24
    simpa only [add_zero] using (he02.trans he24).symm
  obtain ⟨s,hs,_,i,hi⟩ := local_ae_translation_constant c hc hr hδ hshift
  exact ⟨s,hs,i,hi⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma transverseDet_mul_unit {v : ℂ} (hv : ‖v‖=1) (z : ℂ) :
    transverseDet v (z*v)=z.im := by
  have hh : v.re^2+v.im^2=1 := by
    calc
      v.re^2+v.im^2 = ‖v‖^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
      _ = 1 := by rw [hv]; norm_num
  calc
    transverseDet v (z*v) = (v.re^2+v.im^2)*z.im := by
      simp only [transverseDet,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im]
      ring
    _ = z.im := by rw [hh,one_mul]
/-- An open set meeting a unit circle contains two nonparallel unit directions
from its center. No regularity of the color classes is involved. -/
lemma open_two_unit_directions {V : Set ℂ} (hV : IsOpen V) {p v : ℂ}
    (hv : ‖v‖=1) (hpv : p+v∈V) :
    ∃w : ℂ,p+w∈V ∧ ‖w‖=1 ∧ transverseDet v w≠0 := by
  have ht : Continuous (fun t : ℝ => p+(Circle.exp t : ℂ)*v) := by fun_prop
  have hm : (fun t : ℝ => p+(Circle.exp t : ℂ)*v) ⁻¹' V∈𝓝 0 := by
    apply ht.continuousAt.preimage_mem_nhds
    simpa only [Circle.exp_zero,Circle.coe_one,one_mul] using hV.mem_nhds hpv
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hm
  let t : ℝ := min δ Real.pi/2
  have hp := Real.pi_pos
  have hmin : 0 < min δ Real.pi := lt_min hδ hp
  have htp : 0<t := by dsimp [t]; positivity
  have htd : t<δ := by dsimp [t]; linarith [min_le_left δ Real.pi]
  have htπ : t<Real.pi := by dsimp [t]; linarith [min_le_right δ Real.pi]
  refine ⟨(Circle.exp t : ℂ)*v,hd ?_,by rw [norm_mul,Circle.norm_coe,hv,one_mul],?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos htp] using htd
  · rw [transverseDet_mul_unit hv]
    simpa [Circle.coe_exp,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin] using
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi htp htπ))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma double_cos_circle (t : ℝ) :
    (2*Real.cos t : ℂ)*(Circle.exp t : ℂ)-1=(Circle.exp (2*t) : ℂ) := by
  apply Complex.ext <;>
    simp only [Circle.coe_exp,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin,
      Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.sub_re,
      Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Complex.one_re,Complex.one_im,Complex.re_ofNat,Complex.im_ofNat,
      Real.cos_two_mul,Real.sin_two_mul] <;> ring
/-- The unit circle from one endpoint penetrates either prescribed radial side
near its equilateral neighbor. This is the constructive version of the source IFT step. -/
lemma radial_unit_contact {x e : ℂ} (he : ‖e‖=1) {δ : ℝ} (hδ : 0<δ)
    {V : Set ℂ} (b : Bool)
    (hstrip : ∀e' : ℂ,‖e'‖=1 → dist e' (e*(Circle.exp (Real.pi/3) : ℂ))<δ →
      ∀r : ℝ,0<r → |r-1|<δ → (if b then 1<r else r<1) → x+(r:ℂ)*e'∈V) :
    ∃v : ℂ,‖v‖=1 ∧ (x+e)+v∈V := by
  let a : ℝ := Real.pi/3
  let r : ℝ → ℝ := fun t => 2*Real.cos t
  let E : ℝ → ℂ := fun t => e*(Circle.exp t : ℂ)
  have hr : Continuous r := by fun_prop
  have hE : Continuous E := by fun_prop
  have hra : r a=1 := by norm_num [r,a,Real.cos_pi_div_three]
  have ha : 0<a ∧ a<Real.pi := by dsimp [a]; constructor <;> linarith [Real.pi_pos]
  have hn : ∀ᶠt in 𝓝 a,0<r t ∧ |r t-1|<δ ∧ dist (E t) (E a)<δ ∧ 0<t ∧ t<Real.pi := by
    have h₁ : ∀ᶠt in 𝓝 a,0<r t := continuousAt_const.eventually_lt hr.continuousAt (by rw [hra]; norm_num)
    have h₂ : ∀ᶠt in 𝓝 a,|r t-1|<δ :=
      (hr.sub continuous_const).abs.continuousAt.eventually_lt_const (by simpa only [Pi.sub_apply,hra,sub_self,abs_zero] using hδ)
    have h₃ : ∀ᶠt in 𝓝 a,dist (E t) (E a)<δ :=
      (hE.dist continuous_const).continuousAt.eventually_lt_const (by simpa only [dist_self] using hδ)
    exact h₁.and (h₂.and (h₃.and ((eventually_gt_nhds ha.1).and (eventually_lt_nhds ha.2))))
  have hex : ∃t,(0<r t ∧ |r t-1|<δ ∧ dist (E t) (E a)<δ) ∧ (if b then 1<r t else r t<1) := by
    cases b
    · obtain ⟨t,ht,hat⟩ := ((hn.filter_mono nhdsWithin_le_nhds).and
          (self_mem_nhdsWithin : ∀ᶠt in 𝓝[>] a,t∈Ioi a)).exists
      refine ⟨t,⟨ht.1,ht.2.1,ht.2.2.1⟩,?_⟩
      have hc := Real.cos_lt_cos_of_nonneg_of_le_pi ha.1.le ht.2.2.2.2.le hat
      dsimp [r]
      have hh : 2*Real.cos a=1 := hra
      linarith
    · obtain ⟨t,ht,hta⟩ := ((hn.filter_mono nhdsWithin_le_nhds).and
          (self_mem_nhdsWithin : ∀ᶠt in 𝓝[<] a,t∈Iio a)).exists
      refine ⟨t,⟨ht.1,ht.2.1,ht.2.2.1⟩,?_⟩
      have hc := Real.cos_lt_cos_of_nonneg_of_le_pi ht.2.2.2.1.le ha.2.le hta
      dsimp [r]
      have hh : 2*Real.cos a=1 := hra
      linarith
  obtain ⟨t,ht,hside⟩ := hex
  have hEt : ‖E t‖=1 := by
    change ‖e*(Circle.exp t : ℂ)‖=1
    rw [norm_mul,he,Circle.norm_coe,one_mul]
  have hmem := hstrip (E t) hEt ht.2.2 (r t) ht.1 ht.2.1 hside
  let v : ℂ := (r t:ℂ)*E t-e
  have hve : v=e*(Circle.exp (2*t) : ℂ) := by
    change ((2*Real.cos t : ℝ):ℂ)*(e*(Circle.exp t : ℂ))-e=e*(Circle.exp (2*t) : ℂ)
    calc
      _ = e*((2*Real.cos t : ℂ)*(Circle.exp t : ℂ)-1) := by push_cast; ring
      _ = _ := by rw [double_cos_circle]
  refine ⟨v,by rw [hve,norm_mul,he,Circle.norm_coe,one_mul],?_⟩
  have hvq : (x+e)+v=x+(r t:ℂ)*E t := by dsimp [v]; ring
  exact hvq ▸ hmem
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
def radialSide (b : Bool) (ε : ℝ) : Set ℝ := if b then Ioo 1 (1+ε) else Ioo (1-ε) 1
def polarBox (x e : ℂ) (b : Bool) (ε : ℝ) : Set ℂ :=
  (fun rt : ℝ × ℝ => x+(rt.1:ℂ)*(e*(Circle.exp rt.2 : ℂ))) ''
    (radialSide b ε ×ˢ Ioo (-ε) ε)
lemma radialSide_connected (b : Bool) {ε : ℝ} (hε : 0<ε) : IsConnected (radialSide b ε) := by
  cases b <;> dsimp [radialSide] <;> apply isConnected_Ioo <;> linarith
lemma radialSide_abs {b : Bool} {ε r : ℝ} (hr : r∈radialSide b ε) : |r-1|<ε := by
  cases b <;> dsimp [radialSide] at hr
  all_goals rw [abs_lt]; constructor <;> linarith [hr.1,hr.2]
lemma mem_radialSide {b : Bool} {ε r : ℝ} (hr : |r-1|<ε)
    (hb : if b then 1<r else r<1) : r∈radialSide b ε := by
  rw [abs_lt] at hr
  cases b <;> dsimp [radialSide] at * <;> constructor <;> linarith [hr.1,hr.2]
lemma polarBox_connected (x e : ℂ) (b : Bool) {ε : ℝ} (hε : 0<ε) :
    IsConnected (polarBox x e b ε) := by
  apply ((radialSide_connected b hε).prod (isConnected_Ioo (by linarith : -ε<ε))).image
  fun_prop
/-- Arbitrarily small connected polar boxes on either side of a unit circle. -/
lemma polarBox_small {x e : ℂ} {b : Bool} {δ : ℝ} (hδ : 0<δ)
    {U W : Set ℂ} (hW : IsOpen W) (hp : x+e∈W)
    (hstrip : ∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,
      0<r → |r-1|<δ → (if b then 1<r else r<1) → x+(r:ℂ)*e'∈U)
    (he : ‖e‖=1) : ∃ε>0,polarBox x e b ε⊆U∩W := by
  let F : ℝ × ℝ → ℂ := fun rt => x+(rt.1:ℂ)*(e*(Circle.exp rt.2 : ℂ))
  let E : ℝ × ℝ → ℂ := fun rt => e*(Circle.exp rt.2 : ℂ)
  have hF : Continuous F := by fun_prop
  have hE : Continuous E := by fun_prop
  have hF0 : F (1,0)=x+e := by simp [F]
  have hE0 : E (1,0)=e := by simp [E]
  have hn : ∀ᶠrt in 𝓝 ((1,0) : ℝ × ℝ),F rt∈W ∧ dist (E rt) e<δ ∧ 0<rt.1 ∧ |rt.1-1|<δ := by
    have h₁ : ∀ᶠrt in 𝓝 ((1,0) : ℝ × ℝ),F rt∈W := hF.continuousAt.preimage_mem_nhds (hW.mem_nhds (hF0 ▸ hp))
    have h₂ : ∀ᶠrt in 𝓝 ((1,0) : ℝ × ℝ),dist (E rt) e<δ :=
      (hE.dist continuous_const).continuousAt.eventually_lt_const (by simpa [hE0] using hδ)
    have h₃ : ∀ᶠrt in 𝓝 ((1,0) : ℝ × ℝ),0<rt.1 :=
      continuousAt_const.eventually_lt continuous_fst.continuousAt (by norm_num)
    have h₄ : ∀ᶠrt in 𝓝 ((1,0) : ℝ × ℝ),|rt.1-1|<δ :=
      (continuous_fst.sub continuous_const).abs.continuousAt.eventually_lt_const (by simpa using hδ)
    exact h₁.and (h₂.and (h₃.and h₄))
  obtain ⟨ε,hε,hh⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε,hε,?_⟩
  rintro q ⟨⟨r,t⟩,⟨hr,ht⟩,rfl⟩
  have hrt : (r,t)∈Metric.ball ((1,0) : ℝ × ℝ) ε := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by simpa [Real.dist_eq] using radialSide_abs hr,by simpa [Real.dist_eq,abs_lt] using ht⟩
  have hz := hh hrt
  refine ⟨hstrip (E (r,t)) ?_ hz.2.1 r hz.2.2.1 hz.2.2.2 ?_,hz.1⟩
  · change ‖e*(Circle.exp t : ℂ)‖=1
    rw [norm_mul,he,Circle.norm_coe,one_mul]
  · cases b <;> dsimp [radialSide] at hr ⊢
    · exact hr.2
    · exact hr.1
/-- A polar box contains a complete one-sided radial strip, not just selected rays. -/
lemma polarBox_contains_strip {x e : ℂ} (he : ‖e‖=1) (b : Bool)
    {ε : ℝ} (hε : 0<ε) : ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,
      |r-1|<δ → (if b then 1<r else r<1) → x+(r:ℂ)*e'∈polarBox x e b ε := by
  have he0 : e≠0 := by intro h; simp [h] at he
  have ha : ContinuousAt (fun z : ℂ => Complex.arg (z/e)) e := by
    have hh : ContinuousAt Complex.arg (e/e) := Complex.continuousAt_arg (by
      simpa only [div_self he0] using Complex.one_mem_slitPlane)
    exact hh.comp (f := fun z : ℂ => z/e) (by fun_prop)
  have hn : ∀ᶠz in 𝓝 e,|Complex.arg (z/e)|<ε :=
    ha.abs.eventually_lt_const (by simpa [div_self he0] using hε)
  obtain ⟨δ,hδ,hh⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨min δ ε,lt_min hδ hε,?_⟩
  intro e' he' hdist r hr hb
  let t : ℝ := Complex.arg (e'/e)
  have ht : -ε<t ∧ t<ε := abs_lt.mp (hh (hdist.trans_le (min_le_left _ _)))
  have heq : e*(Circle.exp t : ℂ)=e' := by
    have hnorm : ‖e'/e‖=1 := by rw [norm_div,he',he,div_one]
    have h := Complex.norm_mul_exp_arg_mul_I (e'/e)
    rw [hnorm,Complex.ofReal_one,one_mul] at h
    change e*Complex.exp ((t:ℂ)*Complex.I)=e'
    rw [show Complex.exp ((t:ℂ)*Complex.I)=e'/e from h]
    field_simp
  refine ⟨(r,t),⟨mem_radialSide (hr.trans_le (min_le_right _ _)) hb,ht⟩,?_⟩
  change x+(r:ℂ)*(e*(Circle.exp t : ℂ))=x+(r:ℂ)*e'
  rw [heq]
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Points having a fixed essential color on some ambient neighborhood. -/
def essentialLocalSet {ι : Type*} (c : ℂ → ι) (i : ι) : Set ℂ :=
  {p | ∃U : Set ℂ,IsOpen U ∧ p∈U ∧ ∀ᵐq : ℂ∂volume,q∈U → c q=i}
lemma essentialLocalSet_open {ι : Type*} (c : ℂ → ι) (i : ι) : IsOpen (essentialLocalSet c i) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro p ⟨U,hU,hp,hae⟩
  exact ⟨U,fun q hq => ⟨U,hU,hq,hae⟩,hU,hp⟩
lemma essentialLocalSet_disjoint {ι : Type*} (c : ℂ → ι) {i j : ι} (hne : i≠j) :
    Disjoint (essentialLocalSet c i) (essentialLocalSet c j) := by
  apply disjoint_left.mpr
  rintro p ⟨U,hU,hp,hu⟩ ⟨V,hV,hp',hv⟩
  have hpos := (hU.inter hV).measure_pos (volume : Measure ℂ) ⟨p,hp,hp'⟩
  obtain ⟨q,hq,hqa⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' (ae_restrict_of_ae (hu.and hv))
  exact hne ((hqa.1 hq.1).symm.trans (hqa.2 hq.2))
lemma essentialLocalSet_ae {ι : Type*} (c : ℂ → ι) (i : ι) :
    ∀ᵐq : ℂ∂volume,q∈essentialLocalSet c i → c q=i :=
  ae_of_locally_ae volume (fun _ h => h)
/-- Local essential constancy on a connected set has one global essential value.
The connected set need not be open, which permits polar product images directly. -/
lemma connected_local_ae_constant {ι : Type*} {c : ℂ → ι} {S : Set ℂ}
    (hS : IsConnected S) (hl : ∀p∈S,∃i,p∈essentialLocalSet c i) :
    ∃i,S⊆essentialLocalSet c i ∧ (∀ᵐq : ℂ∂volume,q∈S → c q=i) := by
  classical
  obtain ⟨p,hp⟩ := hS.nonempty
  obtain ⟨i,hi⟩ := hl p hp
  let V : Set ℂ := ⋃j≠i,essentialLocalSet c j
  have hv : IsOpen V := isOpen_iUnion fun j => isOpen_iUnion fun _ => essentialLocalSet_open c j
  have hd : Disjoint (essentialLocalSet c i) V := by
    apply disjoint_iUnion_right.mpr
    intro j
    apply disjoint_iUnion_right.mpr
    intro hji
    exact essentialLocalSet_disjoint c (Ne.symm hji)
  have hsuv : S⊆essentialLocalSet c i∪V := by
    intro q hq
    obtain ⟨j,hj⟩ := hl q hq
    by_cases hji : j=i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j,hji,hj⟩)
  have hs := hS.isPreconnected.subset_left_of_subset_union (essentialLocalSet_open c i) hv hd hsuv ⟨p,hp,hi⟩
  exact ⟨i,hs,(essentialLocalSet_ae c i).mono fun q hq hs' => hq (hs hs')⟩
end EuclideanFiveColor
end

end OAI
