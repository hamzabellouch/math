import Mathlib
import OAI.Geometry.BallPacking.Necessity.PlanarEnergy

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

def planeSquare (c : Plane) (r : ℝ) : Set Plane :=
  Icc (c.1-r,c.2-r) (c.1+r,c.2+r)

def squareEnergy {n : ℕ} (v : Plane → Phase n) (c : Plane) (r : ℝ) : ℝ :=
  ∫ z in planeSquare c r, planarDirichlet v z

theorem planeSquare_compact (c : Plane) (r : ℝ) : IsCompact (planeSquare c r) := isCompact_Icc

theorem planeSquare_mono (c : Plane) {r s : ℝ} (hrs : r ≤ s) : planeSquare c r ⊆ planeSquare c s := by
  intro z hz
  exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,
    ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩

theorem squareEnergy_nonneg {n : ℕ} (v : Plane → Phase n) (c : Plane) (r : ℝ) :
    0 ≤ squareEnergy v c r := integral_nonneg (fun z => planarDirichlet_nonneg v z)

theorem squareEnergy_mono {n : ℕ} {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    (c : Plane) {r s : ℝ} (hrs : r ≤ s) : squareEnergy v c r ≤ squareEnergy v c s := by
  exact setIntegral_mono_set ((planarDirichlet_continuous hv).continuousOn.integrableOn_Icc)
    (Eventually.of_forall fun z => planarDirichlet_nonneg v z) (planeSquare_mono c hrs).eventuallyLE

theorem rectangle_integral_eq_iterated {f : Plane → ℝ} (hf : Continuous f)
    {a b : Plane} (hab : a ≤ b) :
    (∫ z in Icc a b, f z) = ∫ x in a.1..b.1, ∫ y in a.2..b.2, f (x,y) := by
  have hi : IntegrableOn f (Icc a b) := hf.continuousOn.integrableOn_Icc
  rw [← Icc_prod_Icc,Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod f hi]
  simp_rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab.1,
    ←intervalIntegral.integral_of_le hab.2]

theorem rectangle_integral_eq_iterated_swap {f : Plane → ℝ} (hf : Continuous f)
    {a b : Plane} (hab : a ≤ b) :
    (∫ z in Icc a b, f z) = ∫ y in a.2..b.2, ∫ x in a.1..b.1, f (x,y) := by
  rw [rectangle_integral_eq_iterated hf hab]
  apply intervalIntegral_intervalIntegral_swap
  have hi : IntegrableOn f (Icc a b) := hf.continuousOn.integrableOn_Icc
  apply hi.mono_set
  intro z hz
  rw [uIoc_of_le hab.1,uIoc_of_le hab.2] at hz
  exact ⟨⟨hz.1.1.le,hz.2.1.le⟩,⟨hz.1.2,hz.2.2⟩⟩

theorem exists_interval_mean {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ t ∈ Icc a b, (b-a)*f t = ∫ x in a..b, f x := by
  obtain ⟨t,ht,he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (μ := volume) hf.continuousOn (continuous_const.intervalIntegrable a b)
    (fun _ _ => (by norm_num : (0:ℝ) ≤ 1))
  refine ⟨t,by simpa only [uIcc_of_le hab] using ht,?_⟩
  simpa [intervalIntegral.integral_const,mul_comm] using he.symm

theorem horizontal_integral_continuous {f : Plane → ℝ} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun y => ∫ x in a..b, f (x,y)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hf.comp continuous_swap

theorem vertical_integral_continuous {f : Plane → ℝ} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun x => ∫ y in a..b, f (x,y)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hf

theorem planar_energy_rectangle_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    {a b : Plane} (hab : a ≤ b) {d : ℝ}
    (h1 : b.1-a.1 ≤ d) (h2 : b.2-a.2 ≤ d) :
    (∫ z in Icc a b, planarDirichlet v z) ≤ 2*C*d*rectangleBoundaryEnergy v a b := by
  have hA : Continuous (fun z => standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) := by
    simpa only [stdOmega_apply,Function.comp_def] using
      (((stdOmega n).continuous.comp (planar_partial_continuous hv (1,0))).clm_apply
        (planar_partial_continuous hv (0,1)))
  have hi : (∫ z in Icc a b, planarDirichlet v z) ≤
      ∫ z in Icc a b, C * standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)) :=
    integral_mono ((planarDirichlet_continuous hv).continuousOn.integrableOn_Icc)
      ((hA.const_mul C).continuousOn.integrableOn_Icc) hE
  rw [integral_const_mul] at hi
  have hb := mul_le_mul_of_nonneg_left (standard_area_rectangle_le_boundaryEnergy hv hab h1 h2) hC
  nlinarith

 

theorem exists_low_energy_rectangle {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (c : Plane) {r : ℝ} (hr : 0 < r) :
    ∃ a b : Plane, a ≤ b ∧ planeSquare c (r/2) ⊆ Icc a b ∧
      Icc a b ⊆ planeSquare c r ∧ b.1-a.1 ≤ 2*r ∧ b.2-a.2 ≤ 2*r ∧
      r*rectangleBoundaryEnergy v a b ≤
        16 * (∫ z in planeSquare c r \ planeSquare c (r/2), planarDirichlet v z) := by
  let e := planarDirichlet v
  let A := ∫ z in planeSquare c r \ planeSquare c (r/2), e z
  have he : Continuous e := planarDirichlet_continuous hv
  have he0 (z : Plane) : 0 ≤ e z := planarDirichlet_nonneg v z
  have hi : IntegrableOn e (planeSquare c r \ planeSquare c (r/2)) :=
    he.continuousOn.integrableOn_Icc.mono_set sdiff_subset
  have hset {a b : Plane} (hsub : Icc a b ⊆ planeSquare c r \ planeSquare c (r/2)) :
      (∫ z in Icc a b, e z) ≤ A :=
    setIntegral_mono_set hi (Eventually.of_forall he0) hsub.eventuallyLE
  have hH (l u : ℝ) (hlu : l ≤ u)
      (hsub : Icc (c.1-r,l) (c.1+r,u) ⊆ planeSquare c r \ planeSquare c (r/2)) :
      ∃ y ∈ Icc l u, (u-l)*(∫ x in c.1-r..c.1+r, e (x,y)) ≤ A := by
    obtain ⟨y,hy,hm⟩ := exists_interval_mean (horizontal_integral_continuous he (c.1-r) (c.1+r)) hlu
    refine ⟨y,hy,?_⟩
    rw [hm,←rectangle_integral_eq_iterated_swap he (show (c.1-r,l) ≤ (c.1+r,u) from ⟨by linarith,hlu⟩)]
    exact hset hsub
  have hV (l u : ℝ) (hlu : l ≤ u)
      (hsub : Icc (l,c.2-r) (u,c.2+r) ⊆ planeSquare c r \ planeSquare c (r/2)) :
      ∃ x ∈ Icc l u, (u-l)*(∫ y in c.2-r..c.2+r, e (x,y)) ≤ A := by
    obtain ⟨x,hx,hm⟩ := exists_interval_mean (vertical_integral_continuous he (c.2-r) (c.2+r)) hlu
    refine ⟨x,hx,?_⟩
    rw [hm,←rectangle_integral_eq_iterated he (show (l,c.2-r) ≤ (u,c.2+r) from ⟨hlu,by linarith⟩)]
    exact hset hsub
  have hlowH : Icc (c.1-r,c.2-r) (c.1+r,c.2-3*r/4) ⊆
      planeSquare c r \ planeSquare c (r/2) := by
    intro z hz
    refine ⟨⟨hz.1,⟨hz.2.1,by linarith [hz.2.2]⟩⟩,?_⟩
    intro hh
    linarith [hz.2.2,hh.1.2]
  have hhighH : Icc (c.1-r,c.2+3*r/4) (c.1+r,c.2+r) ⊆
      planeSquare c r \ planeSquare c (r/2) := by
    intro z hz
    refine ⟨⟨⟨hz.1.1,by linarith [hz.1.2]⟩,hz.2⟩,?_⟩
    intro hh
    linarith [hz.1.2,hh.2.2]
  have hlowV : Icc (c.1-r,c.2-r) (c.1-3*r/4,c.2+r) ⊆
      planeSquare c r \ planeSquare c (r/2) := by
    intro z hz
    refine ⟨⟨hz.1,⟨by linarith [hz.2.1],hz.2.2⟩⟩,?_⟩
    intro hh
    linarith [hz.2.1,hh.1.1]
  have hhighV : Icc (c.1+3*r/4,c.2-r) (c.1+r,c.2+r) ⊆
      planeSquare c r \ planeSquare c (r/2) := by
    intro z hz
    refine ⟨⟨⟨by linarith [hz.1.1],hz.1.2⟩,hz.2⟩,?_⟩
    intro hh
    linarith [hz.1.1,hh.2.1]
  obtain ⟨a2,ha2,hEa2⟩ := hH (c.2-r) (c.2-3*r/4) (by linarith) hlowH
  obtain ⟨b2,hb2,hEb2⟩ := hH (c.2+3*r/4) (c.2+r) (by linarith) hhighH
  obtain ⟨a1,ha1,hEa1⟩ := hV (c.1-r) (c.1-3*r/4) (by linarith) hlowV
  obtain ⟨b1,hb1,hEb1⟩ := hV (c.1+3*r/4) (c.1+r) (by linarith) hhighV
  have h1 : a1 ≤ b1 := by linarith [ha1.2,hb1.1]
  have h2 : a2 ≤ b2 := by linarith [ha2.2,hb2.1]
  refine ⟨(a1,a2),(b1,b2),⟨h1,h2⟩,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact ⟨⟨by linarith [ha1.2,hz.1.1],by linarith [ha2.2,hz.1.2]⟩,
      ⟨by linarith [hb1.1,hz.2.1],by linarith [hb2.1,hz.2.2]⟩⟩
  · intro z hz
    exact ⟨⟨ha1.1.trans hz.1.1,ha2.1.trans hz.1.2⟩,
      ⟨hz.2.1.trans hb1.2,hz.2.2.trans hb2.2⟩⟩
  · dsimp; linarith [ha1.1,hb1.2]
  · dsimp; linarith [ha2.1,hb2.2]
  · have hhb (y : ℝ) : (∫ x in a1..b1, e (x,y)) ≤ ∫ x in c.1-r..c.1+r, e (x,y) :=
      intervalIntegral.integral_mono_interval ha1.1 h1 hb1.2 (Eventually.of_forall fun x => he0 (x,y))
        ((he.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
    have hvb (x : ℝ) : (∫ y in a2..b2, e (x,y)) ≤ ∫ y in c.2-r..c.2+r, e (x,y) :=
      intervalIntegral.integral_mono_interval ha2.1 h2 hb2.2 (Eventually.of_forall fun y => he0 (x,y))
        ((he.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    have hh0 := mul_le_mul_of_nonneg_left (hhb a2) hr.le
    have hh1 := mul_le_mul_of_nonneg_left (hhb b2) hr.le
    have hh2 := mul_le_mul_of_nonneg_left (hvb a1) hr.le
    have hh3 := mul_le_mul_of_nonneg_left (hvb b1) hr.le
    change r*((∫ x in a1..b1, e (x,a2))+(∫ x in a1..b1, e (x,b2))+
      (∫ y in a2..b2, e (a1,y))+(∫ y in a2..b2, e (b1,y))) ≤ 16*A
    nlinarith

 
theorem square_energy_hole_filling {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    squareEnergy v c (r/2) ≤ 64*C*(squareEnergy v c r-squareEnergy v c (r/2)) := by
  obtain ⟨a,b,hab,hinner,houter,h1,h2,hbd⟩ := exists_low_energy_rectangle hv c hr
  have hi : squareEnergy v c (r/2) ≤ ∫ z in Icc a b, planarDirichlet v z :=
    setIntegral_mono_set ((planarDirichlet_continuous hv).continuousOn.integrableOn_Icc)
      (Eventually.of_forall fun z => planarDirichlet_nonneg v z) hinner.eventuallyLE
  have hrect := planar_energy_rectangle_bound hv hC hE hab h1 h2
  have hAnn : (∫ z in planeSquare c r \ planeSquare c (r/2), planarDirichlet v z) =
      squareEnergy v c r-squareEnergy v c (r/2) := by
    exact setIntegral_sdiff measurableSet_Icc
      ((planarDirichlet_continuous hv).continuousOn.integrableOn_Icc)
      (planeSquare_mono c (by linarith))
  rw [hAnn] at hbd
  have hh := mul_le_mul_of_nonneg_left hbd hC
  nlinarith

def decayRatio (C : ℝ) : ℝ := 64*C/(1+64*C)

theorem decayRatio_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ decayRatio C :=
  div_nonneg (by positivity) (by positivity)

theorem decayRatio_lt_one {C : ℝ} (hC : 0 ≤ C) : decayRatio C < 1 := by
  unfold decayRatio
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem square_energy_decay_half {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    squareEnergy v c (r/2) ≤ decayRatio C * squareEnergy v c r := by
  have h := square_energy_hole_filling hv hC hE c hr
  unfold decayRatio
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem square_energy_decay_dyadic {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    (c : Plane) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    squareEnergy v c (r*(1/2:ℝ)^k) ≤ (decayRatio C)^k * squareEnergy v c r := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := square_energy_decay_half hv hC hE c
      (show 0 < r*(1/2:ℝ)^k by positivity)
    have he : r*(1/2:ℝ)^(k+1) = (r*(1/2:ℝ)^k)/2 := by rw [pow_succ]; ring
    rw [he]
    exact h.trans (by simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using
      mul_le_mul_of_nonneg_left ih (decayRatio_nonneg hC))


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def lineMean (f : ℝ → ℝ) (a b : ℝ) : ℝ := (∫ x in a..b, f x)/(b-a)

def rectangleMean (f : Plane → ℝ) (a b : Plane) : ℝ :=
  lineMean (fun y => lineMean (fun x => f (x,y)) a.1 b.1) a.2 b.2

def squareMean (f : Plane → ℝ) (c : Plane) (r : ℝ) : ℝ :=
  rectangleMean f (c.1-r,c.2-r) (c.1+r,c.2+r)

theorem lineMean_const (d : ℝ) {a b : ℝ} (hab : a < b) :
    lineMean (fun _ => d) a b = d := by
  simp only [lineMean,intervalIntegral.integral_const,smul_eq_mul]
  field_simp [sub_ne_zero.mpr hab.ne']

theorem lineMean_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ) :
    lineMean (fun x => f x-g x) a b = lineMean f a b-lineMean g a b := by
  simp [lineMean,intervalIntegral.integral_sub (hf.intervalIntegrable a b) (hg.intervalIntegrable a b),sub_div]

theorem lineMean_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a < b) (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    lineMean f a b ≤ lineMean g a b := by
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hab).le
  exact intervalIntegral.integral_mono_on hab.le (hf.intervalIntegrable a b)
    (hg.intervalIntegrable a b) hfg

theorem lineMean_abs_le (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    |lineMean f a b| ≤ lineMean (fun x => |f x|) a b := by
  simp only [lineMean,abs_div,abs_of_pos (sub_pos.mpr hab)]
  exact div_le_div_of_nonneg_right (intervalIntegral.abs_integral_le_integral_abs hab.le)
    (sub_pos.mpr hab).le

theorem exists_lineMean_eq {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Icc a b, lineMean f a b = f x := by
  obtain ⟨x,hx,he⟩ := exists_interval_mean hf hab.le
  refine ⟨x,hx,?_⟩
  unfold lineMean
  rw [←he]
  field_simp [sub_ne_zero.mpr hab.ne']

theorem lineMean_horizontal_continuous {f : Plane → ℝ} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun y => lineMean (fun x => f (x,y)) a b) :=
  (horizontal_integral_continuous hf a b).div_const _

theorem lineMean_vertical_continuous {f : Plane → ℝ} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun x => lineMean (fun y => f (x,y)) a b) :=
  (vertical_integral_continuous hf a b).div_const _

theorem rectangleMean_eq_integral {f : Plane → ℝ} (hf : Continuous f)
    {a b : Plane} (hab : a ≤ b) :
    rectangleMean f a b = (∫ z in Icc a b, f z)/((b.1-a.1)*(b.2-a.2)) := by
  rw [rectangle_integral_eq_iterated_swap hf hab]
  simp only [rectangleMean,lineMean,intervalIntegral.integral_div,div_div]

theorem rectangleMean_swap {f : Plane → ℝ} (hf : Continuous f)
    {a b : Plane} (hab : a ≤ b) :
    rectangleMean f a b = lineMean (fun x => lineMean (fun y => f (x,y)) a.2 b.2) a.1 b.1 := by
  rw [rectangleMean_eq_integral hf hab,rectangle_integral_eq_iterated hf hab]
  simp only [lineMean,intervalIntegral.integral_div,div_div,mul_comm]

theorem real_displacement_le_integral {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    |f b-f a| ≤ ∫ x in a..b, |g x| := by
  rw [←intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hg.intervalIntegrable a b)]
  exact intervalIntegral.abs_integral_le_integral_abs hab

theorem real_displacement_le_integral_outer {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x-f y| ≤ ∫ s in a..b, |g s| := by
  wlog hxy : y ≤ x generalizing x y
  · rw [abs_sub_comm]
    exact this hy hx (le_of_not_ge hxy)
  have h := real_displacement_le_integral hf hg hxy
  exact h.trans (intervalIntegral.integral_mono_interval hy.1 hxy hx.2
    (Eventually.of_forall fun s => abs_nonneg (g s)) (hg.abs.intervalIntegrable a b))

theorem lineMean_oscillation {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    {a b l u s t : ℝ} (hlu : l < u) (hst : s < t)
    (hl : a ≤ l) (hu : u ≤ b) (hs : a ≤ s) (ht : t ≤ b) :
    |lineMean f l u-lineMean f s t| ≤ ∫ x in a..b, |g x| := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  obtain ⟨x,hx,hxe⟩ := exists_lineMean_eq hc hlu
  obtain ⟨y,hy,hye⟩ := exists_lineMean_eq hc hst
  rw [hxe,hye]
  exact real_displacement_le_integral_outer hf hg ⟨hl.trans hx.1,hx.2.trans hu⟩
    ⟨hs.trans hy.1,hy.2.trans ht⟩

theorem rectangle_integral_sq_le {f : Plane → ℝ} (hf : Continuous f)
    {a b : Plane} (hab : a ≤ b) :
    (∫ z in Icc a b, f z)^2 ≤
      ((b.1-a.1)*(b.2-a.2)) * (∫ z in Icc a b, (f z)^2) := by
  rw [rectangle_integral_eq_iterated_swap hf hab,
    rectangle_integral_eq_iterated_swap (f := fun z => (f z)^2) (hf.pow 2) hab]
  have h1 := interval_integral_sq_le (horizontal_integral_continuous hf a.1 b.1) hab.2
  have h2 := intervalIntegral.integral_mono_on (μ := volume) hab.2
    ((horizontal_integral_continuous hf a.1 b.1).pow 2 |>.intervalIntegrable _ _)
    ((horizontal_integral_continuous (hf.pow 2) a.1 b.1).const_mul (b.1-a.1) |>.intervalIntegrable _ _)
    (fun y _ => interval_integral_sq_le (hf.comp (continuous_id.prodMk continuous_const)) hab.1)
  rw [intervalIntegral.integral_const_mul] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hab.2)
  exact h1.trans (by simpa only [Pi.pow_apply,mul_assoc,mul_comm,mul_left_comm] using h3)

theorem square_integral_abs_le {f e : Plane → ℝ} (hf : Continuous f) (he : Continuous e)
    (hfe : ∀ z, (f z)^2 ≤ e z) (c : Plane) {r : ℝ} (hr : 0 < r) :
    (∫ z in planeSquare c r, |f z|) ≤
      2*r*Real.sqrt (∫ z in planeSquare c r, e z) := by
  have hab : (c.1-r,c.2-r) ≤ (c.1+r,c.2+r) := ⟨by linarith,by linarith⟩
  have h0 : 0 ≤ ∫ z in planeSquare c r, e z :=
    integral_nonneg (fun z => (sq_nonneg (f z)).trans (hfe z))
  have h1 := rectangle_integral_sq_le hf.abs hab
  simp only [sq_abs] at h1
  have h2 := integral_mono (μ := volume.restrict (planeSquare c r)) ((hf.pow 2).continuousOn.integrableOn_Icc)
    (he.continuousOn.integrableOn_Icc) hfe
  have h3 := mul_le_mul_of_nonneg_left h2
    (show 0 ≤ ((c.1+r)-(c.1-r))*((c.2+r)-(c.2-r)) from
      mul_nonneg (by linarith) (by linarith))
  have hs := Real.sq_sqrt h0
  have ht : 0 ≤ 2*r*Real.sqrt (∫ z in planeSquare c r, e z) := by positivity
  change (∫ z in planeSquare c r, |f z|)^2 ≤
    ((c.1+r)-(c.1-r))*((c.2+r)-(c.2-r))*(∫ z in planeSquare c r, (f z)^2) at h1
  change ((c.1+r)-(c.1-r))*((c.2+r)-(c.2-r))*(∫ z in planeSquare c r, (f z)^2) ≤ _ at h3
  have hh := h1.trans h3
  apply (sq_le_sq₀ (integral_nonneg (fun z => abs_nonneg (f z))) ht).mp
  calc
    _ ≤ ((c.1+r)-(c.1-r))*((c.2+r)-(c.2-r))*(∫ z in planeSquare c r, e z) := hh
    _ = (2*r*Real.sqrt (∫ z in planeSquare c r, e z))^2 := by rw [mul_pow,hs]; ring

theorem squareMean_half_bound {f dx dy e : Plane → ℝ}
    (hf : Continuous f) (hdx : Continuous dx) (hdy : Continuous dy) (he : Continuous e)
    (hfX : ∀ x y, HasDerivAt (fun s => f (s,y)) (dx (x,y)) x)
    (hfY : ∀ x y, HasDerivAt (fun s => f (x,s)) (dy (x,y)) y)
    (hxE : ∀ z, (dx z)^2 ≤ e z) (hyE : ∀ z, (dy z)^2 ≤ e z)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    |squareMean f c (r/2)-squareMean f c r| ≤
      4*Real.sqrt (∫ z in planeSquare c r, e z) := by
  let F : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (c.1-r/2) (c.1+r/2)
  let G : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (c.1-r) (c.1+r)
  let H : ℝ → ℝ := fun y => ∫ x in c.1-r..c.1+r, |dx (x,y)|
  let V : ℝ → ℝ := fun x => ∫ y in c.2-r..c.2+r, |dy (x,y)|
  have hF : Continuous F := lineMean_horizontal_continuous hf _ _
  have hG : Continuous G := lineMean_horizontal_continuous hf _ _
  have hH : Continuous H := horizontal_integral_continuous hdx.abs _ _
  have hV : Continuous V := vertical_integral_continuous hdy.abs _ _
  have hH0 (y : ℝ) : 0 ≤ H y := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => abs_nonneg _)
  have hab : (c.1-r,c.2-r) ≤ (c.1+r,c.2+r) := ⟨by linarith,by linarith⟩
  have hFG (y : ℝ) : |F y-G y| ≤ H y :=
    lineMean_oscillation (fun x => hfX x y) (hdx.comp (continuous_id.prodMk continuous_const))
      (by linarith) (by linarith) (by linarith) (by linarith) le_rfl le_rfl
  have hstep1 : |lineMean F (c.2-r/2) (c.2+r/2)-lineMean G (c.2-r/2) (c.2+r/2)| ≤
      (∫ z in planeSquare c r, |dx z|)/r := by
    rw [←lineMean_sub hF hG]
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hF.sub hG).abs hH (by linarith) (fun y _ => hFG y)).trans
    have hm := intervalIntegral.integral_mono_interval (μ := volume) (by linarith : c.2-r ≤ c.2-r/2)
      (by linarith : c.2-r/2 ≤ c.2+r/2) (by linarith : c.2+r/2 ≤ c.2+r)
      (Eventually.of_forall hH0) (hH.intervalIntegrable (c.2-r) (c.2+r))
    change (∫ y in c.2-r/2..c.2+r/2, H y)/((c.2+r/2)-(c.2-r/2)) ≤ _
    rw [show (c.2+r/2)-(c.2-r/2)=r by ring]
    apply div_le_div_of_nonneg_right _ hr.le
    exact hm.trans_eq (rectangle_integral_eq_iterated_swap hdx.abs hab).symm
  let L : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (c.2-r/2) (c.2+r/2)
  let M : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (c.2-r) (c.2+r)
  have hL : Continuous L := lineMean_vertical_continuous hf _ _
  have hM : Continuous M := lineMean_vertical_continuous hf _ _
  have hLM (x : ℝ) : |L x-M x| ≤ V x :=
    lineMean_oscillation (fun y => hfY x y) (hdy.comp (continuous_const.prodMk continuous_id))
      (by linarith) (by linarith) (by linarith) (by linarith) le_rfl le_rfl
  have hstep2 : |lineMean G (c.2-r/2) (c.2+r/2)-squareMean f c r| ≤
      (∫ z in planeSquare c r, |dy z|)/(2*r) := by
    have hs1 : lineMean G (c.2-r/2) (c.2+r/2) = lineMean L (c.1-r) (c.1+r) :=
      rectangleMean_swap (a := (c.1-r,c.2-r/2)) (b := (c.1+r,c.2+r/2)) hf ⟨by dsimp; linarith,by dsimp; linarith⟩
    have hs2 : squareMean f c r = lineMean M (c.1-r) (c.1+r) := rectangleMean_swap hf hab
    rw [hs1,hs2,←lineMean_sub hL hM]
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hL.sub hM).abs hV (by linarith) (fun x _ => hLM x)).trans
    change (∫ x in c.1-r..c.1+r, V x)/((c.1+r)-(c.1-r)) ≤ _
    rw [show (c.1+r)-(c.1-r)=2*r by ring]
    exact le_of_eq (congrArg (fun v : ℝ => v/(2*r)) (rectangle_integral_eq_iterated hdy.abs hab).symm)
  have hX := square_integral_abs_le hdx he hxE c hr
  have hY := square_integral_abs_le hdy he hyE c hr
  have hX' : (∫ z in planeSquare c r, |dx z|)/r ≤
      2*Real.sqrt (∫ z in planeSquare c r, e z) := by
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have hY' : (∫ z in planeSquare c r, |dy z|)/(2*r) ≤
      Real.sqrt (∫ z in planeSquare c r, e z) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have ht := abs_sub_le (squareMean f c (r/2))
    (lineMean G (c.2-r/2) (c.2+r/2)) (squareMean f c r)
  change |squareMean f c (r/2)-lineMean G (c.2-r/2) (c.2+r/2)| ≤ _ at hstep1
  linarith [Real.sqrt_nonneg (∫ z in planeSquare c r, e z)]

theorem exists_squareMean_eq {f : Plane → ℝ} (hf : Continuous f)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ planeSquare c r, squareMean f c r = f z := by
  obtain ⟨y,hy,hey⟩ := exists_lineMean_eq (lineMean_horizontal_continuous hf (c.1-r) (c.1+r))
    (show c.2-r < c.2+r by linarith)
  obtain ⟨x,hx,hex⟩ := exists_lineMean_eq (hf.comp (continuous_id.prodMk continuous_const))
    (show c.1-r < c.1+r by linarith)
  exact ⟨(x,y),⟨⟨hx.1,hy.1⟩,⟨hx.2,hy.2⟩⟩,hey.trans hex⟩

theorem planeSquare_dist_le {c z : Plane} {r : ℝ} (hz : z ∈ planeSquare c r) :
    dist z c ≤ r := by
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  exact max_le (abs_le.mpr ⟨by linarith [hz.1.1],by linarith [hz.2.1]⟩)
    (abs_le.mpr ⟨by linarith [hz.1.2],by linarith [hz.2.2]⟩)

theorem squareMean_tendsto {f : Plane → ℝ} (hf : Continuous f) (c : Plane)
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hl : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => squareMean f c (r k)) atTop (𝓝 (f c)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
  filter_upwards [(tendsto_order.mp hl).2 δ hδ] with k hk
  obtain ⟨z,hz,he⟩ := exists_squareMean_eq hf c (hr k)
  rw [he]
  exact hfδ ((planeSquare_dist_le hz).trans_lt hk)

def morreyConstant (C : ℝ) : ℝ := 4/(1-Real.sqrt (decayRatio C))

theorem morreyConstant_pos {C : ℝ} (hC : 0 ≤ C) : 0 < morreyConstant C := by
  have hs : Real.sqrt (decayRatio C) < 1 := (Real.sqrt_lt' (by norm_num)).mpr
    (by simpa using decayRatio_lt_one hC)
  unfold morreyConstant
  positivity

theorem squareMean_point_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    {f dx dy : Plane → ℝ} (hf : Continuous f) (hdx : Continuous dx) (hdy : Continuous dy)
    (hfX : ∀ x y, HasDerivAt (fun s => f (s,y)) (dx (x,y)) x)
    (hfY : ∀ x y, HasDerivAt (fun s => f (x,s)) (dy (x,y)) y)
    (hxE : ∀ z, (dx z)^2 ≤ planarDirichlet v z)
    (hyE : ∀ z, (dy z)^2 ≤ planarDirichlet v z)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    |f c-squareMean f c r| ≤ morreyConstant C * Real.sqrt (squareEnergy v c r) := by
  let s := Real.sqrt (decayRatio C)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using decayRatio_lt_one hC)
  have hpow (k : ℕ) : Real.sqrt ((decayRatio C)^k) = s^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) k),ih,pow_succ]
  have hsd (k : ℕ) : Real.sqrt (squareEnergy v c (r*(1/2:ℝ)^k)) ≤
      s^k * Real.sqrt (squareEnergy v c r) := by
    have hh := Real.sqrt_le_sqrt (square_energy_decay_dyadic hv hC hE c hr k)
    rwa [Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) k),hpow k] at hh
  let m : ℕ → ℝ := fun k => squareMean f c (r*(1/2:ℝ)^k)
  have hstep (k : ℕ) : dist (m k) (m (k+1)) ≤
      (4*Real.sqrt (squareEnergy v c r))*s^k := by
    have hh := squareMean_half_bound hf hdx hdy (planarDirichlet_continuous hv)
      hfX hfY hxE hyE c (show 0 < r*(1/2:ℝ)^k by positivity)
    have hh2 := mul_le_mul_of_nonneg_left (hsd k) (by norm_num : (0:ℝ) ≤ 4)
    have he : r*(1/2:ℝ)^(k+1) = (r*(1/2:ℝ)^k)/2 := by rw [pow_succ]; ring
    simpa only [m,Real.dist_eq,abs_sub_comm,he,squareEnergy,mul_assoc,mul_comm,mul_left_comm]
      using hh.trans hh2
  have hl : Tendsto m atTop (𝓝 (f c)) := by
    apply squareMean_tendsto hf c (fun k => by positivity)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul r
  have hh := dist_le_tsum_of_dist_le_of_tendsto₀
    (fun k => (4*Real.sqrt (squareEnergy v c r))*s^k) hstep
    ((summable_geometric_of_lt_one hs0 hs1).mul_left _) hl
  rw [tsum_mul_left,tsum_geometric_of_lt_one hs0 hs1] at hh
  simpa only [m,pow_zero,mul_one,Real.dist_eq,abs_sub_comm,morreyConstant,div_eq_mul_inv,
    mul_assoc,mul_comm,mul_left_comm] using hh


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem squareMean_translate_bound {f dx dy e : Plane → ℝ}
    (hf : Continuous f) (hdx : Continuous dx) (hdy : Continuous dy) (he : Continuous e)
    (hfX : ∀ x y, HasDerivAt (fun s => f (s,y)) (dx (x,y)) x)
    (hfY : ∀ x y, HasDerivAt (fun s => f (x,s)) (dy (x,y)) y)
    (hxE : ∀ z, (dx z)^2 ≤ e z) (hyE : ∀ z, (dy z)^2 ≤ e z)
    (hi : Integrable e) {D : ℝ} (hD : (∫ z, e z) ≤ D)
    (c : Plane) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    |squareMean f c r-squareMean f 0 r| ≤ 2*(R+r)/r*Real.sqrt D := by
  let L := R+r
  have hL : 0 < L := by dsimp [L]; linarith
  have hc1' := abs_le.mp hc1
  have hc2' := abs_le.mp hc2
  let F : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (c.1-r) (c.1+r)
  let G : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (-r) r
  let H : ℝ → ℝ := fun y => ∫ x in -L..L, |dx (x,y)|
  let V : ℝ → ℝ := fun x => ∫ y in -L..L, |dy (x,y)|
  have hF : Continuous F := lineMean_horizontal_continuous hf _ _
  have hG : Continuous G := lineMean_horizontal_continuous hf _ _
  have hH : Continuous H := horizontal_integral_continuous hdx.abs _ _
  have hV : Continuous V := vertical_integral_continuous hdy.abs _ _
  have hH0 (y : ℝ) : 0 ≤ H y := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => abs_nonneg _)
  have hV0 (x : ℝ) : 0 ≤ V x := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => abs_nonneg _)
  have hFG (y : ℝ) : |F y-G y| ≤ H y :=
    lineMean_oscillation (fun x => hfX x y) (hdx.comp (continuous_id.prodMk continuous_const))
      (by linarith) (by linarith) (by dsimp [L]; linarith) (by dsimp [L]; linarith)
      (by dsimp [L]; linarith) (by dsimp [L]; linarith)
  have hab : (-L,-L) ≤ (L,L) := ⟨by linarith,by linarith⟩
  have hsquare : Icc (-L,-L) (L,L) = planeSquare 0 L := by simp [planeSquare]
  have hstep1 : |lineMean F (c.2-r) (c.2+r)-lineMean G (c.2-r) (c.2+r)| ≤
      (∫ z in planeSquare 0 L, |dx z|)/(2*r) := by
    rw [←lineMean_sub hF hG]
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hF.sub hG).abs hH (by linarith) (fun y _ => hFG y)).trans
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (by dsimp [L]; linarith : -L ≤ c.2-r) (by linarith : c.2-r ≤ c.2+r)
      (by dsimp [L]; linarith : c.2+r ≤ L) (Eventually.of_forall hH0) (hH.intervalIntegrable (-L) L)
    change (∫ y in c.2-r..c.2+r, H y)/((c.2+r)-(c.2-r)) ≤ _
    rw [show (c.2+r)-(c.2-r)=2*r by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact hm.trans_eq (by rw [←rectangle_integral_eq_iterated_swap hdx.abs hab,hsquare])
  let F' : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (c.2-r) (c.2+r)
  let G' : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (-r) r
  have hF' : Continuous F' := lineMean_vertical_continuous hf _ _
  have hG' : Continuous G' := lineMean_vertical_continuous hf _ _
  have hFG' (x : ℝ) : |F' x-G' x| ≤ V x :=
    lineMean_oscillation (fun y => hfY x y) (hdy.comp (continuous_const.prodMk continuous_id))
      (by linarith) (by linarith) (by dsimp [L]; linarith) (by dsimp [L]; linarith)
      (by dsimp [L]; linarith) (by dsimp [L]; linarith)
  have hstep2 : |lineMean G (c.2-r) (c.2+r)-squareMean f 0 r| ≤
      (∫ z in planeSquare 0 L, |dy z|)/(2*r) := by
    have hs1 : lineMean G (c.2-r) (c.2+r) = lineMean F' (-r) r :=
      rectangleMean_swap (a := (-r,c.2-r)) (b := (r,c.2+r)) hf ⟨by dsimp; linarith,by dsimp; linarith⟩
    have hs2 : squareMean f 0 r = lineMean G' (-r) r := by
      simpa only [squareMean,Prod.fst_zero,Prod.snd_zero,zero_sub,zero_add] using
        rectangleMean_swap (a := (-r,-r)) (b := (r,r)) hf ⟨by dsimp; linarith,by dsimp; linarith⟩
    rw [hs1,hs2,←lineMean_sub hF' hG']
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hF'.sub hG').abs hV (by linarith) (fun x _ => hFG' x)).trans
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (by dsimp [L]; linarith : -L ≤ -r) (by linarith : -r ≤ r)
      (by dsimp [L]; linarith : r ≤ L) (Eventually.of_forall hV0) (hV.intervalIntegrable (-L) L)
    change (∫ x in -r..r, V x)/(r-(-r)) ≤ _
    rw [show r-(-r)=2*r by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact hm.trans_eq (by rw [←rectangle_integral_eq_iterated hdy.abs hab,hsquare])
  have he0 (z : Plane) : 0 ≤ e z := (sq_nonneg (dx z)).trans (hxE z)
  have hE : (∫ z in planeSquare 0 L, e z) ≤ D :=
    (setIntegral_le_integral hi (Eventually.of_forall he0)).trans hD
  have hX := (square_integral_abs_le hdx he hxE 0 hL).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by positivity : 0 ≤ 2*L))
  have hY := (square_integral_abs_le hdy he hyE 0 hL).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by positivity : 0 ≤ 2*L))
  have hX' : (∫ z in planeSquare 0 L, |dx z|)/(2*r) ≤ L/r*Real.sqrt D := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ 2*L*Real.sqrt D := hX
      _ = L/r*Real.sqrt D*(2*r) := by field_simp
  have hY' : (∫ z in planeSquare 0 L, |dy z|)/(2*r) ≤ L/r*Real.sqrt D := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ 2*L*Real.sqrt D := hY
      _ = L/r*Real.sqrt D*(2*r) := by field_simp
  have ht := abs_sub_le (squareMean f c r) (lineMean G (c.2-r) (c.2+r)) (squareMean f 0 r)
  change |squareMean f c r-lineMean G (c.2-r) (c.2+r)| ≤ _ at hstep1
  calc
    _ ≤ L/r*Real.sqrt D+L/r*Real.sqrt D :=
      ht.trans (add_le_add (hstep1.trans hX') (hstep2.trans hY'))
    _ = 2*(R+r)/r*Real.sqrt D := by dsimp [L]; ring


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def phaseProjection {n : ℕ} (a : Phase n) : Phase n →L[ℝ] ℝ :=
  (euclideanNorm a)⁻¹ • stdDot n a

theorem phaseProjection_self {n : ℕ} (a : Phase n) :
    phaseProjection a a = euclideanNorm a := by
  change (euclideanNorm a)⁻¹ * stdDot n a a = _
  rw [←euclideanNorm_sq]
  by_cases h : euclideanNorm a = 0
  · simp [h]
  · field_simp

theorem phaseProjection_sq_le {n : ℕ} (a v : Phase n) :
    (phaseProjection a v)^2 ≤ stdDot n v v := by
  change ((euclideanNorm a)⁻¹ * stdDot n a v)^2 ≤ _
  by_cases h : euclideanNorm a = 0
  · simpa [h] using stdDot_nonneg v
  · have hp : 0 < (euclideanNorm a)^2 := sq_pos_of_ne_zero h
    have hh := stdDot_standardForm_sq_le a v
    have hb : (stdDot n a v)^2 ≤ (euclideanNorm a)^2 * stdDot n v v := by
      rw [euclideanNorm_sq]
      nlinarith [sq_nonneg (standardForm a v)]
    rw [mul_pow,inv_pow]
    calc
      _ ≤ ((euclideanNorm a)^2)⁻¹ * ((euclideanNorm a)^2 * stdDot n v v) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hp.le)
      _ = stdDot n v v := by rw [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]

theorem projection_abs_le {n : ℕ} (ℓ : Phase n →L[ℝ] ℝ)
    (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a) (a : Phase n) :
    |ℓ a| ≤ euclideanNorm a := by
  apply (sq_le_sq₀ (abs_nonneg _) (euclideanNorm_nonneg _)).mp
  simpa only [sq_abs,euclideanNorm_sq] using hℓ a

theorem projection_point_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    (ℓ : Phase n →L[ℝ] ℝ) (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    |ℓ (v c)-squareMean (fun z => ℓ (v z)) c r| ≤
      morreyConstant C * Real.sqrt (squareEnergy v c r) := by
  apply squareMean_point_bound hv hC hE (ℓ.continuous.comp hv.continuous)
    (ℓ.continuous.comp (planar_partial_continuous hv (1,0)))
    (ℓ.continuous.comp (planar_partial_continuous hv (0,1)))
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt x
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt y
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_right (stdDot_nonneg _))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_left (stdDot_nonneg _))
  · exact hr

theorem projection_translate_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (ℓ : Phase n →L[ℝ] ℝ)
    (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a)
    (hi : Integrable (planarDirichlet v)) {D : ℝ} (hD : (∫ z, planarDirichlet v z) ≤ D)
    (c : Plane) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    |squareMean (fun z => ℓ (v z)) c r-squareMean (fun z => ℓ (v z)) 0 r| ≤
      2*(R+r)/r*Real.sqrt D := by
  apply squareMean_translate_bound (ℓ.continuous.comp hv.continuous)
    (ℓ.continuous.comp (planar_partial_continuous hv (1,0)))
    (ℓ.continuous.comp (planar_partial_continuous hv (0,1))) (planarDirichlet_continuous hv)
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt x
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt y
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_right (stdDot_nonneg _))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_left (stdDot_nonneg _))
  · exact hi
  · exact hD
  · exact hR
  · exact hr
  · exact hc1
  · exact hc2

theorem lineMean_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ) :
    lineMean (fun x => f x+g x) a b = lineMean f a b+lineMean g a b := by
  simp [lineMean,intervalIntegral.integral_add (hf.intervalIntegrable a b) (hg.intervalIntegrable a b),add_div]

theorem squareMean_add {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g)
    (c : Plane) (r : ℝ) :
    squareMean (fun z => f z+g z) c r = squareMean f c r+squareMean g c r := by
  unfold squareMean rectangleMean
  have hrow (y : ℝ) := lineMean_add (f := fun x => f (x,y)) (g := fun x => g (x,y))
    (hf.comp (continuous_id.prodMk continuous_const))
    (hg.comp (continuous_id.prodMk continuous_const)) (c.1-r) (c.1+r)
  simp_rw [hrow]
  exact lineMean_add (lineMean_horizontal_continuous hf _ _) (lineMean_horizontal_continuous hg _ _) _ _

theorem squareMean_sub {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g)
    (c : Plane) (r : ℝ) :
    squareMean (fun z => f z-g z) c r = squareMean f c r-squareMean g c r := by
  unfold squareMean rectangleMean
  have hrow (y : ℝ) := lineMean_sub (f := fun x => f (x,y)) (g := fun x => g (x,y))
    (hf.comp (continuous_id.prodMk continuous_const))
    (hg.comp (continuous_id.prodMk continuous_const)) (c.1-r) (c.1+r)
  simp_rw [hrow]
  exact lineMean_sub (lineMean_horizontal_continuous hf _ _) (lineMean_horizontal_continuous hg _ _) _ _

theorem lineMean_linear (a b c : ℝ) {r : ℝ} (hr : 0 < r) :
    lineMean (fun x => a*x+b) (c-r) (c+r) = a*c+b := by
  rw [lineMean_add (f := fun x => a*x) (g := fun _ => b) (continuous_const.mul continuous_id) continuous_const,
    lineMean_const b (by linarith)]
  change (∫ x in c-r..c+r, a*x)/((c+r)-(c-r))+b = a*c+b
  rw [intervalIntegral.integral_const_mul,integral_id]
  have hn : (c+r)-(c-r) ≠ 0 := by linarith
  field_simp
  ring

theorem squareMean_affine_scalar (a b : ℝ) (c : Plane) {r : ℝ} (hr : 0 < r) :
    squareMean (fun z => a*z.1+b*z.2) c r = a*c.1+b*c.2 := by
  unfold squareMean rectangleMean
  simp_rw [lineMean_linear a _ c.1 hr]
  have he : (fun y : ℝ => a*c.1+b*y) = fun y => b*y+a*c.1 := by funext y; ring
  rw [he,lineMean_linear b _ c.2 hr]
  ring

theorem realCurve_affine_eq {n : ℕ} (a : Phase n) (z : Plane) :
    realCurve (fun ζ : ℂ => ζ • a) z = z.1 • a+z.2 • (Complex.I • a) := by
  ext i
  simp only [realCurve,Function.comp_apply,Complex.equivRealProdCLM_symm_apply,
    Pi.smul_apply,Pi.add_apply,smul_eq_mul,Complex.real_smul]
  ring

theorem projection_squareMean_affine {n : ℕ} (ℓ : Phase n →L[ℝ] ℝ)
    (a : Phase n) (c : Plane) {r : ℝ} (hr : 0 < r) :
    squareMean (fun z => ℓ (realCurve (fun ζ : ℂ => ζ • a) z)) c r =
      ℓ (realCurve (fun ζ : ℂ => ζ • a) c) := by
  simp only [realCurve_affine_eq,map_add,map_smul,smul_eq_mul]
  have he : (fun z : Plane => z.1*ℓ a+z.2*ℓ (Complex.I • a)) =
      fun z => ℓ a*z.1+ℓ (Complex.I • a)*z.2 := by funext z; ring
  rw [he,squareMean_affine_scalar _ _ c hr]
  ring

end HigherDimensionalBallPacking.Rigidity

end

end OAI
