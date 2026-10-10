import OAI.Geometry.Convex.GeneralMahler.Entropy
import OAI.Geometry.Convex.GeneralMahler.Hermite.H

namespace OAI
/-! Kernel integrations for §04. Plane is Euclidean pair (with product
volume), split along diagonal. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile

def Rlo : Set Plane := {u|u.1 < u.2}
lemma Rlo_m : MeasurableSet Rlo := (isOpen_lt continuous_fst continuous_snd).measurableSet
lemma upper1 (f:Plane→ℝ) (hf:IntegrableOn f Rlo) :
    (∫ u in Rlo,f u)=∫ a:ℝ,∫ b in Ioi a,f (a,b) := by
  classical
  let g := Rlo.indicator f
  have hi : Integrable g := (integrable_indicator_iff Rlo_m).mpr hf
  rw [← integral_indicator Rlo_m,show volume=volume.prod volume from rfl, integral_prod _ hi]
  congr 1
  ext a
  rw [← integral_indicator measurableSet_Ioi]; rfl
lemma upper2 (f:Plane→ℝ) (hf:IntegrableOn f Rlo) :
    (∫ u in Rlo,f u)=∫ b:ℝ,∫ a in Iio b,f (a,b) := by
  classical
  let g := Rlo.indicator f
  have hi : Integrable g := (integrable_indicator_iff Rlo_m).mpr hf
  rw [← integral_indicator Rlo_m,show volume=volume.prod volume from rfl, integral_prod_symm _ hi]
  congr 1; ext; rw [← integral_indicator measurableSet_Iio]; rfl
lemma off_diag : ∀ᵐ u:Plane,u.1≠u.2 := by
  apply (ae_prod_iff_ae_ae (((isClosed_eq continuous_fst continuous_snd).measurableSet.compl))).mpr
  filter_upwards with x
  rw [ae_iff]; simp []
lemma split_plane (f:Plane→ℝ) (hf:Integrable f) :
    (∫ u,f u) = (∫ u in Rlo,f u)+(∫ u in Rlo,f u.swap) := by
  classical
  rw [← integral_add_compl Rlo_m hf]
  congr 1
  rw [← integral_indicator Rlo_m.compl,← integral_indicator Rlo_m]
  let g := Rloᶜ.indicator f
  have he : (∫ u,g u)=(∫ u:Plane,g u.swap) :=
    (integral_prod_swap (μ:=volume) (ν:=volume) g).symm
  change (∫ u,g u)=_
  rw [he]
  apply integral_congr_ae
  filter_upwards [off_diag] with u hu
  rcases lt_or_gt_of_ne hu with h|h
  · have hh:u∈Rlo := h
    have h':u.swap∈Rloᶜ := not_lt_of_ge h.le
    unfold g; rw [indicator_of_mem h',indicator_of_mem hh]
  have hh : u∉Rlo := not_lt_of_ge h.le
  have h': u.swap∉Rloᶜ := fun he=> he (show u.swap∈Rlo from h)
  unfold g; rw [indicator_of_notMem h',indicator_of_notMem hh]

lemma real_slice (K:Plane→ℝ) (hK:Measurable K) (hp:∀ u,0≤K u) (hm:ℝ→ℝ)
    (hi:∀ x:ℝ, Integrable fun y=>K (x,y)) (he:∀ x, (∫ y,K (x,y))=hm x)
    (hh:MomentF hm) (n:ℕ) :
    Integrable fun u:Plane=> K u*(1+‖u.1‖)^n := by
  let f := fun u:Plane=> K u*(1+‖u.1‖)^n
  have hf : Measurable f := hK.mul (by fun_prop)
  apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ fun x=> (hi x).mul_const ((1+‖x‖)^n),?_⟩
  have hv (x y:ℝ) : ‖f (x,y)‖=K (x,y)*(1+‖x‖)^n :=
    Real.norm_of_nonneg (mul_nonneg (hp _) (by positivity))
  simp_rw [hv,integral_mul_const,he]
  exact hh _ (by fun_prop) (((PolyBound.const _).add PolyBound.id.norm).pow _)

lemma pairMoment (K:Plane→ℝ) (hK:Measurable K) (hp:∀ u,0≤K u) (hm:ℝ→ℝ)
    (hi:∀ x:ℝ, Integrable fun y=>K (x,y)) (he:∀ x, (∫ y,K (x,y))=hm x)
    (hh:MomentF hm) (hs:∀ u:Plane,K u.swap=K u)
    {f:Plane→ℝ} (hf:PolyBound f) (hf':Measurable f) :
    Integrable fun u=>K u*f u := by
  obtain ⟨C,n,hc,h⟩ := hf
  let g := fun u:Plane=> K u*(1+‖u.1‖)^n
  have hg : Integrable g := real_slice K hK hp hm hi he hh n
  let G := fun u:Plane=> C*(g u+g u.swap)
  have hi : Integrable G := (hg.add hg.swap).const_mul _
  apply hi.mono' (hK.mul hf').aestronglyMeasurable (ae_of_all _ ?_)
  intro u; change ‖K u*f u‖≤_
  rw [norm_mul,Real.norm_of_nonneg (hp _)]
  apply le_trans (mul_le_mul_of_nonneg_left (h u) (hp _))
  change _ ≤ C*(K u*(1+‖u.1‖)^n+K u.swap*(1+‖u.2‖)^n)
  rw [hs]
  have h₁ : ‖u‖ = max ‖u.1‖ ‖u.2‖ := rfl
  rw [h₁]
  rcases max_choice ‖u.1‖ ‖u.2‖ with h|h <;> rw [h] <;> rw [← sub_nonneg] <;>
    ring_nf <;> have he := hp u <;> positivity

-- One-dimensional with right/left densities r=r1 or q0. Base p/a fixed.
structure rightLayer where
  r : ℝ→ℝ
  B : ℝ→ℝ
  hr : ∀ x,0≤r x
  hc : Continuous r
  drB : ∀ x,HasDerivAt B (-r x) x
  hb : rapid (fun x=>B x*st x)
  poly : PolyBound B
  hw : MomentF fun x=>p x*B x+a x*r x

namespace rightLayer
variable (q:rightLayer)
def Km (x:Plane) := p (min x.1 x.2)*q.r (max x.1 x.2)
def mrg (x:ℝ) := p x*q.B x+a x*q.r x

lemma p_slice (x:ℝ) : IntegrableOn p (Iic x) ∧ (∫ y in Iic x,p y) = a x := by
  have he : IntegrableOn p (Iic x) := by
    -- comparison used in §02
    obtain ⟨C,hc,h⟩ := p_small
    let c := max x (0:ℝ)
    have hu : IntegrableOn p (Iic 0) := by
      refine ((i_phi.mul_const C).integrableOn).mono'
        cp.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
      have he := h (-y) (neg_nonneg.mpr (mem_Iic.mp hy))
      simpa only [Real.norm_of_nonneg (p_pos _).le,neg_neg,neg_phi] using he
    exact (hu.union (cp.integrableOn_Icc (a:=0) (b:=c))).mono_set (fun z hz=>by
      by_cases h:z≤0
      · exact Or.inl h
      exact Or.inr ⟨le_of_lt (lt_of_not_ge h),(mem_Iic.mp hz).trans (le_max_left ..)⟩)
  exact ⟨he,by simpa using integral_Iic_of_hasDerivAt_of_tendsto' (fun y _=>d_a y) he abot'⟩
lemma r_slice (x:ℝ) : IntegrableOn q.r (Ioi x) ∧ (∫ y in Ioi x,q.r y)=q.B x := by
  have h : Tendsto q.B atTop (𝓝 0) := by
    apply Tendsto.congr' _ q.hb.tail_limit
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx; simp [st,hx]
  have hh (x:ℝ) : HasDerivAt (fun x=> -q.B x) (q.r x) x := by
    convert (q.drB x).neg using 1
    all_goals first | rfl | simp
  have hi : Tendsto (fun x=> -q.B x) atTop (𝓝 0) := by simpa using h.neg
  have he := integrableOn_Ioi_deriv_of_nonneg' (fun y _=>hh y) (a:=x) (fun y _=>q.hr y) hi
  exact ⟨he,by simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (fun y _=>hh y) he hi⟩
lemma marg (x:ℝ) :
    Integrable (fun y=>q.Km (x,y)) ∧ (∫ y,q.Km (x,y))=q.mrg x := by
  classical
  let s := Iic x
  let f := s.indicator fun y=>p y*q.r x
  let g := (Ioi x).indicator fun y=>p x*q.r y
  have hf : Integrable f := (integrable_indicator_iff measurableSet_Iic).mpr ((p_slice x).1.mul_const _)
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr ((q.r_slice x).1.const_mul _)
  have he : (fun y=>q.Km (x,y))=fun y=> f y+g y := by
    ext y
    rcases le_or_gt y x with h|h
    · simp [f,g,s,Km,h,not_lt_of_ge h]
    simp [f,g,s,Km,h,h.le,not_le_of_gt h]
  rw [he]
  refine ⟨hf.add hg,?_⟩
  rw [integral_add hf hg,show (∫ y,f y)= _ from integral_indicator measurableSet_Iic,
    show (∫ y,g y)=_ from integral_indicator measurableSet_Ioi,
    integral_mul_const,integral_const_mul, (p_slice x).2,(q.r_slice x).2]
  unfold mrg; ring
lemma K_pair {f:Plane→ℝ} (h:PolyBound f) (hf:Measurable f) :
    Integrable fun u=> q.Km u*f u :=
  pairMoment q.Km ((cp.measurable.comp (by fun_prop)).mul (q.hc.measurable.comp (by fun_prop)))
    (fun u=>mul_nonneg (p_pos _).le (q.hr _)) q.mrg (fun x=>(q.marg x).1)
    (fun x=>(q.marg x).2) q.hw (fun u=>by simp [Km,min_comm,max_comm]) h hf

def Q (f j:ℝ→ℝ) := ∫ u:Plane,q.Km u*(f u.1*j u.2)

lemma Q_int {f j:ℝ→ℝ} (hf:TestF f) (hj:TestF j) :
    Integrable fun u:Plane=>q.Km u*(f u.1*j u.2) :=
  q.K_pair ((hf.poly.comp PolyBound.fst).mul (hj.poly.comp PolyBound.snd))
    ((hf.cont.measurable.comp measurable_fst).mul (hj.cont.measurable.comp measurable_snd))

lemma Q_split {f j:ℝ→ℝ} (hf:TestF f) (hj:TestF j) :
    q.Q f j=(∫ x,q.r x*j x*∫ y in Iio x,p y*f y)+
      (∫ x,q.r x*f x*∫ y in Iio x,p y*j y) := by
  let g : Plane→ℝ := fun u=> q.Km u*(f u.1*j u.2)
  have hi := q.Q_int hf hj
  have h (f j:ℝ→ℝ) (hi:IntegrableOn (fun u:Plane=>q.Km u*(f u.1*j u.2)) Rlo) :
      (∫ u in Rlo,q.Km u*(f u.1*j u.2))=(∫ x,q.r x*j x*∫ y in Iio x,p y*f y) := by
    rw [upper2 _ hi]
    congr 1; ext x
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iio
    intro y hy
    have h := mem_Iio.mp hy
    dsimp only [Km]; rw [min_eq_left h.le,max_eq_right h.le]; ring
  unfold Q
  rw [split_plane _ hi,h _ _ hi.integrableOn]
  have he (x:Plane) : g x.swap=q.Km x*(j x.1*f x.2) := by simp [g,Km,min_comm,max_comm,mul_comm]
  congr 1
  rw [← h j f (q.Q_int hj hf).integrableOn]
  change (∫ x in Rlo,g x.swap)=_
  simp_rw [he]
end rightLayer
end GeneralMahler

end

end OAI
