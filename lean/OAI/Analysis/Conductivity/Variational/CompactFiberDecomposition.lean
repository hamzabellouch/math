import Mathlib
import OAI.Analysis.Conductivity.Variational.UnitSquarePoincare
import OAI.Analysis.Conductivity.Walls.WallMomentIndependence

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def compactFiberMarginal (a b : ℝ) (f : E × ℝ → ℝ) (x : E) : ℝ :=
  ∫ t in a..b, f (x,t)

lemma compactFiberMarginal_smooth {a b : ℝ} (hab : a≤b) {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (compactFiberMarginal a b f) := by
  have he : compactFiberMarginal a b f=fun x => ∫ t in Icc a b, f (x,t) := by
    funext x
    rw [compactFiberMarginal,intervalIntegral.integral_of_le hab,integral_Icc_eq_integral_Ioc]
  rw [he]
  exact contDiff_compact_integral hf isCompact_Icc

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma compactFiberMarginal_support {a b : ℝ} {f : E × ℝ → ℝ}
    (hs : HasCompactSupport f) :
    HasCompactSupport (compactFiberMarginal a b f) ∧
      tsupport (compactFiberMarginal a b f) ⊆ Prod.fst '' tsupport f := by
  have hc := hs.image continuous_fst
  have hsub : Function.support (compactFiberMarginal a b f) ⊆ Prod.fst '' tsupport f := by
    intro x hx
    by_contra hn
    have hz : ∀ t, f (x,t)=0 := by
      intro t
      by_contra hf
      exact hn ⟨(x,t),subset_tsupport f hf,rfl⟩
    exact hx (by simp [compactFiberMarginal,hz])
  exact ⟨HasCompactSupport.of_support_subset_isCompact hc hsub,closure_minimal hsub hc.isClosed⟩

lemma exists_unit_interval_bump {a b : ℝ} (hab : a<b) :
    ∃ η : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioo a b ∧ (∫ t in a..b, η t)=1 := by
  let l := (2*a+b)/3
  let r := (a+2*b)/3
  have hal : a<l := by dsimp [l]; linarith
  have hlr : l<r := by dsimp [l,r]; linarith
  have hrb : r<b := by dsimp [r]; linarith
  obtain ⟨χ,hc,hs,hn,hp,hsub⟩ := positive_interval_bump hlr
  have hI : 0<∫ t, χ t := by
    apply integral_pos_iff_support_of_nonneg (fun t => hn t) (hc.continuous.integrable_of_hasCompactSupport hs) |>.2
    apply lt_of_lt_of_le ((Measure.measure_Ioo_pos volume).mpr hlr)
    exact measure_mono (fun t ht => (hp t ht).ne')
  let η := fun t => χ t/(∫ s, χ s)
  have hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η := hc.div_const _
  have hsη : HasCompactSupport η := by
    apply HasCompactSupport.of_support_subset_isCompact hs
    intro t ht
    apply subset_tsupport χ
    exact (div_ne_zero_iff.mp ht).1
  have hsubη : tsupport η ⊆ Ioo a b := by
    change tsupport (fun t => χ t*(∫ s, χ s)⁻¹) ⊆ _
    apply tsupport_mul_subset_left.trans
    exact hsub.trans (fun t ht => ⟨hal.trans_le ht.1,ht.2.trans_lt hrb⟩)
  refine ⟨η,hη,hsη,hsubη,?_⟩
  rw [intervalIntegral.integral_of_le hab.le]
  have he : ∫ t in Ioc a b, η t=∫ t, η t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    exact fun hh => ht ⟨(hsubη hh).1,(hsubη hh).2.le⟩
  rw [he]
  dsimp [η]
  rw [integral_div,div_self hI.ne']

theorem compact_fiber_decomposition {a b : ℝ} (hab : a<b)
    {f : E × ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : HasCompactSupport f) (hv : ∀ p, f p≠0 → p.2∈Ioo a b)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η) (hsη : HasCompactSupport η)
    (hvη : tsupport η⊆Ioo a b) (hiη : (∫ t in a..b, η t)=1) :
    ∃ F : E × ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) F ∧ HasCompactSupport F ∧
      (∀ p, wallDerivative F p+η p.2*compactFiberMarginal a b f p.1=f p) ∧
      tsupport F⊆(Prod.fst '' tsupport f) ×ˢ Icc a b := by
  let R := compactFiberMarginal a b f
  have hR := compactFiberMarginal_smooth hab.le hf
  have hsR : HasCompactSupport R := (compactFiberMarginal_support (a := a) (b := b) hs).1
  let g := fun p : E × ℝ => f p-η p.2*R p.1
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := hf.sub ((hη.comp contDiff_snd).mul (hR.comp contDiff_fst))
  have hsg : HasCompactSupport g := by
    apply hs.sub
    apply HasCompactSupport.of_support_subset_isCompact (hsR.prod hsη)
    intro p hp
    exact ⟨subset_tsupport R (mul_ne_zero_iff.mp hp).2,subset_tsupport η (mul_ne_zero_iff.mp hp).1⟩
  have hvg : ∀ p, g p≠0 → p.2∈Ioo a b := by
    intro p hp
    by_contra hn
    have hz : f p=0 := by by_contra hh; exact hn (hv p hh)
    have hzη : η p.2=0 := image_eq_zero_of_notMem_tsupport (fun hh => hn (hvη hh))
    exact hp (by simp [g,hz,hzη])
  have hzg : ∀ x, (∫ t in a..b, g (x,t))=0 := by
    intro x
    rw [show (fun t => g (x,t))=(fun t => f (x,t)-η t*R x) from rfl,
      intervalIntegral.integral_sub (f := fun t => f (x,t)) (g := fun t => η t*R x)
        ((hf.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
        ((hη.continuous.mul continuous_const).intervalIntegrable a b)]
    rw [intervalIntegral.integral_mul_const,hiη,one_mul]
    exact sub_self _
  refine ⟨fiberPrimitive a g,fiberPrimitive_smooth a hg,(fiberPrimitive_compact hg.continuous hsg hvg hzg).1,?_,?_⟩
  · intro p
    rw [fiberPrimitive_derivative a hg]
    exact sub_add_cancel _ _
  · apply ((fiberPrimitive_compact hg.continuous hsg hvg hzg).2).trans
    intro p hp
    refine ⟨?_,hp.2⟩
    obtain ⟨q,hq,hqp⟩ := hp.1
    by_contra hn
    have hfg : Function.support g⊆(Prod.fst '' tsupport f) ×ˢ univ := by
      intro y hy
      refine ⟨?_,mem_univ _⟩
      by_contra hyf
      have hz : f y=0 := by
        by_contra h
        exact hyf ⟨y,subset_tsupport f h,rfl⟩
      have hzR : R y.1=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hyf ((compactFiberMarginal_support hs).2 h))
      exact hy (by simp [g,hz,hzR])
    have hts := closure_minimal hfg ((hs.image continuous_fst).isClosed.prod isClosed_univ)
    exact hn (hqp ▸ (hts hq).1)

end

open Set MeasureTheory

lemma smooth_unit_interval_trace {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {a : ℝ} (ha : a∈Icc (0:ℝ) 1) :
    (q a)^2≤2*unitAverage (fun t => (q t)^2)+
      2*unitAverage (fun t => (deriv q t)^2) := by
  have hd := hq.continuous_deriv (by simp)
  have hp (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      (q a)^2≤2*(q t)^2+2*unitAverage (fun t => (deriv q t)^2) := by
    have hh : (q a-q t)^2≤unitAverage (fun t => (deriv q t)^2) := by
      rcases le_total t a with h|h
      · have hb := smooth_interval_poincare_point hq h
        have hi : (∫ s in t..a, (deriv q s)^2)≤unitAverage (fun s => (deriv q s)^2) := by
          rw [unitAverage_eq_interval]
          exact intervalIntegral.integral_mono_interval ht.1 h ha.2
            (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) ((hd.pow 2).intervalIntegrable 0 1)
        have hpos : 0≤∫ s in t..a, (deriv q s)^2 :=
          intervalIntegral.integral_nonneg h (fun _ _ => sq_nonneg _)
        have hlen : a-t≤1 := by linarith [ht.1,ha.2]
        nlinarith [mul_nonneg (sub_nonneg.mpr hlen) hpos]
      · have hb := smooth_interval_poincare_point hq h
        have hi : (∫ s in a..t, (deriv q s)^2)≤unitAverage (fun s => (deriv q s)^2) := by
          rw [unitAverage_eq_interval]
          exact intervalIntegral.integral_mono_interval ha.1 h ht.2
            (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) ((hd.pow 2).intervalIntegrable 0 1)
        have hpos : 0≤∫ s in a..t, (deriv q s)^2 :=
          intervalIntegral.integral_nonneg h (fun _ _ => sq_nonneg _)
        have hlen : t-a≤1 := by linarith [ha.1,ht.2]
        nlinarith [mul_nonneg (sub_nonneg.mpr hlen) hpos]
    nlinarith [sq_nonneg (q a-2*q t)]
  have hh := unitAverage_mono (continuous_const : Continuous (fun _ : ℝ => (q a)^2))
    ((continuous_const.mul (hq.continuous.pow 2)).add continuous_const) hp
  change unitAverage (fun _ : ℝ => (q a)^2)≤
    unitAverage (fun t => 2*(q t)^2+2*unitAverage (fun t => (deriv q t)^2)) at hh
  rw [unitAverage_const,unitAverage_add (f := fun t => 2*(q t)^2)
      (g := fun _ => 2*unitAverage (fun t => (deriv q t)^2))
      (continuous_const.mul (hq.continuous.pow 2)) continuous_const,
    unitAverage_mul,unitAverage_const] at hh
  exact hh

theorem smooth_unit_face_trace {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {a : ℝ} (ha : a∈Icc (0:ℝ) 1) :
    unitSquareAverage (fun y => (f (y,a))^2)≤
      2*unitCubeAverage (fun z => (f z)^2)+
        2*unitCubeAverage (fun z => (cubePartial f ((0,0),1) z)^2) := by
  have hd := continuous_cubePartial hf ((0,0),1)
  have hp (y : ℝ×ℝ) : (f (y,a))^2≤2*unitAverage (fun t => (f (y,t))^2)+
      2*unitAverage (fun t => (cubePartial f ((0,0),1) (y,t))^2) := by
    have hh := smooth_unit_interval_trace
      (hf.comp (contDiff_const.prodMk contDiff_id) :
        ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ => f (y,t))) ha
    have he (t : ℝ) : deriv (fun s : ℝ => f (y,s)) t=cubePartial f ((0,0),1) (y,t) := by
      exact ((((hf.differentiable (by simp)) (y,t)).hasFDerivAt).comp_hasDerivAt t
        ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))).deriv
    change (f (y,a))^2≤2*unitAverage (fun t => (f (y,t))^2)+
      2*unitAverage (fun t => (deriv (fun s => f (y,s)) t)^2) at hh
    simpa only [he] using hh
  have hh := unitSquareAverage_mono
    ((hf.continuous.comp (continuous_id.prodMk continuous_const)).pow 2)
    ((continuous_const.mul (continuous_unitAverage (hf.continuous.pow 2))).add
      (continuous_const.mul (continuous_unitAverage (hd.pow 2))))
    (fun y _ x _ => hp (y,x))
  change unitSquareAverage (fun y => (f (y,a))^2)≤
    unitSquareAverage (fun y => 2*unitAverage (fun t => (f (y,t))^2)+
      2*unitAverage (fun t => (cubePartial f ((0,0),1) (y,t))^2)) at hh
  rw [unitSquareAverage_add
      (f := fun y => 2*unitAverage (fun t => (f (y,t))^2))
      (g := fun y => 2*unitAverage (fun t => (cubePartial f ((0,0),1) (y,t))^2))
      (continuous_const.mul (continuous_unitAverage (hf.continuous.pow 2)))
      (continuous_const.mul (continuous_unitAverage (hd.pow 2))),
    unitSquareAverage_mul,unitSquareAverage_mul] at hh
  exact hh

end ScalarConductivity

end

end OAI
