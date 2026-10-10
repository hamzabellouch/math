import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.Geometry
import OAI.Analysis.CoulombIonization.RadialBounds.RetainedNeighborhoodBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierRetainedFinite_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAnalysis

lemma sup_pair_values (a b : ℝ) :
    ({0,1} : Finset (Fin 2)).sup' (by simp) (fun i => if i = 0 then a else b) = max a b := by
  rw [Finset.sup'_insert (by simp),Finset.sup'_singleton]
  simp

lemma sup_triple_values (a b c : ℝ) :
    ({0,1,2} : Finset (Fin 3)).sup' (by simp)
      (fun i => if i = 0 then a else if i = 1 then b else c) = max (max a b) c := by
  rw [Finset.sup'_insert (by simp),Finset.sup'_insert (by simp),Finset.sup'_singleton]
  simp [max_assoc]

 theorem nuclear_retained_max_two {U : Set TFSpace} (hU : IsOpen U) (Z : ℝ)
    {R κ ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {u v h₁ h₂ g χ : TFSpace → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hh₁ : LocallyIntegrable h₁) (hh₂ : LocallyIntegrable h₂)
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < R → χ x = 0)
    (hw₁ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u x) h₁)
    (hw₂ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v x) h₂)
    (hdom₁ : ∀ᵐ x, x ∈ U → max (u x) (v x)-u x < 2*ε →
      g x+χ x*reaction κ (nuclearField Z x+u x) ≤ h₁ x)
    (hdom₂ : ∀ᵐ x, x ∈ U → max (u x) (v x)-v x < 2*ε →
      g x+χ x*reaction κ (nuclearField Z x+v x) ≤ h₂ x) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+max (u x) (v x))
      (fun x => g x+χ x*reaction κ (nuclearField Z x+max (u x) (v x))) := by
  have hw := nuclear_retained_weak_maximum ({0,1} : Finset (Fin 2)) (by simp) hU Z hR
    (fun i x => if i = 0 then u x else v x) (fun i x => if i = 0 then h₁ x else h₂ x)
    (by
      intro i _
      fin_cases i
      · simpa using hu
      · simpa using hv)
    (by
      intro i _
      fin_cases i
      · simpa using hh₁
      · simpa using hh₂)
    hg hχ hbχ hzero hε
    (by
      intro i _
      fin_cases i
      · simpa using hw₁
      · simpa using hw₂)
    (by
      filter_upwards [hdom₁,hdom₂] with x hx₁ hx₂
      intro i _ hx hi
      rw [sup_pair_values] at hi
      fin_cases i
      · simpa using hx₁ hx (by simpa using hi)
      · simpa using hx₂ hx (by simpa using hi))
  simpa only [sup_pair_values] using hw

 theorem nuclear_retained_max_three {U : Set TFSpace} (hU : IsOpen U) (Z : ℝ)
    {R κ ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {u v b h₁ h₂ h₃ g χ : TFSpace → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hb : Continuous b)
    (hh₁ : LocallyIntegrable h₁) (hh₂ : LocallyIntegrable h₂) (hh₃ : LocallyIntegrable h₃)
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < R → χ x = 0)
    (hw₁ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u x) h₁)
    (hw₂ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v x) h₂)
    (hw₃ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+b x) h₃)
    (hdom₁ : ∀ᵐ x, x ∈ U → max (max (u x) (v x)) (b x)-u x < 2*ε →
      g x+χ x*reaction κ (nuclearField Z x+u x) ≤ h₁ x)
    (hdom₂ : ∀ᵐ x, x ∈ U → max (max (u x) (v x)) (b x)-v x < 2*ε →
      g x+χ x*reaction κ (nuclearField Z x+v x) ≤ h₂ x)
    (hdom₃ : ∀ᵐ x, x ∈ U → max (max (u x) (v x)) (b x)-b x < 2*ε →
      g x+χ x*reaction κ (nuclearField Z x+b x) ≤ h₃ x) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+max (max (u x) (v x)) (b x))
      (fun x => g x+χ x*reaction κ (nuclearField Z x+max (max (u x) (v x)) (b x))) := by
  have hw := nuclear_retained_weak_maximum ({0,1,2} : Finset (Fin 3)) (by simp) hU Z hR
    (fun i x => if i = 0 then u x else if i = 1 then v x else b x)
    (fun i x => if i = 0 then h₁ x else if i = 1 then h₂ x else h₃ x)
    (by
      intro i _
      fin_cases i
      · simpa using hu
      · simpa using hv
      · simpa using hb)
    (by
      intro i _
      fin_cases i
      · simpa using hh₁
      · simpa using hh₂
      · simpa using hh₃)
    hg hχ hbχ hzero hε
    (by
      intro i _
      fin_cases i
      · simpa using hw₁
      · simpa using hw₂
      · simpa using hw₃)
    (by
      filter_upwards [hdom₁,hdom₂,hdom₃] with x hx₁ hx₂ hx₃
      intro i _ hx hi
      rw [sup_triple_values] at hi
      fin_cases i
      · simpa using hx₁ hx (by simpa using hi)
      · simpa using hx₂ hx (by simpa using hi)
      · simpa using hx₃ hx (by simpa using hi))
  simpa only [sup_triple_values] using hw

end Work_BarrierRetainedFinite_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

structure OutwardCalibration (κ B C M lam1 lam2 e ξ hl hh : ℝ) : Prop where
  k_nonneg : 0 ≤ κ
  B_pos : 0 < B
  C_nonneg : 0 ≤ C
  B_le_C : B ≤ C
  M_large : 2 < M
  xi_nonneg : 0 ≤ ξ
  low_shift : ξ < lam2
  shift_order : lam2 ≤ lam1
  shift_small : lam1 < barrierGap B
  gap : 16*ξ+2*e < lam1-lam2
  e_pos : 0 < e
  e_small : 2*e*(2*M)^4 < B/4
  cap_shift : C/M^4 < lam2
  height_low : hl < B/4
  height_high : C < hh
  subsolution : 4*Real.pi*κ*Real.sqrt B ≤ 19/2

def outwardRegionOffset (good radial : Prop) [Decidable good] [Decidable radial]
    (a h : TFSpace → ℝ) (Z B R lam1 lam2 : ℝ) (x : TFSpace) : ℝ :=
  max (max (a x-lam1/R^4) (if good then h x-lam2/R^4 else a x-lam1/R^4))
    (if radial then outerOffset Z B R x else a x-lam1/R^4)

lemma outwardRegionOffset_inner (good : Prop) [Decidable good]
    (a h : TFSpace → ℝ) (Z B R lam1 lam2 : ℝ) :
    outwardRegionOffset good False a h Z B R lam1 lam2 = shiftedCandidates good a h R lam1 lam2 := by
  funext x
  by_cases hg : good <;> simp [outwardRegionOffset,shiftedCandidates,hg]

lemma outwardRegionOffset_middle (good : Prop) [Decidable good]
    (a h : TFSpace → ℝ) (Z B R lam1 lam2 : ℝ) :
    outwardRegionOffset good True a h Z B R lam1 lam2 =
      fun x => max (shiftedCandidates good a h R lam1 lam2 x) (outerOffset Z B R x) := by
  funext x
  by_cases hg : good <;> simp [outwardRegionOffset,shiftedCandidates,hg]

theorem outward_region_weak (good radial : Prop) [Decidable good] [Decidable radial]
    {Z B C R M κ lam1 lam2 e ξ Cinv hl hh : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh) (hR : 0 < R)
    {U : Set TFSpace} (hU : IsOpen U) (hUbound : ∀ x ∈ U, ‖x‖ < 2*M*R)
    (hUrad : radial → ∀ x ∈ U, R < ‖x‖)
    {a h μ p : TFSpace → ℝ} (ha : Continuous a) (hhc : Continuous h)
    (hμ : LocallyIntegrable μ) (hp : LocallyIntegrable p)
    (hμn : ∀ x, 0 ≤ μ x) (hpn : ∀ x, 0 ≤ p x)
    (hlo : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hhcap : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h x ≤ C/‖x‖^4)
    (hinv : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R →
      InverseComparisonAt ‖x‖ (nuclearField Z x+h x) (μ x) κ hl hh ξ Cinv)
    (hwlo : ∀ x ∈ U, R ≤ ‖x‖ → outerBarrier B R x ≤
      nuclearField Z x+outwardRegionOffset good radial a h Z B R lam1 lam2 x)
    (hwa : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource (R/2) μ p x+outerCoefficient (R/2) x*reaction κ (nuclearField Z x+a x)))
    (hwh : good → WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+h x) (fun x => 4*Real.pi*μ x)) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+outwardRegionOffset good radial a h Z B R lam1 lam2 x)
      (fun x => innerSource R μ (addedError good R μ p) x+
        outerCoefficient R x*reaction κ (nuclearField Z x+outwardRegionOffset good radial a h Z B R lam1 lam2 x)) := by
  let v₁ := fun x => a x-lam1/R^4
  let v₂ := fun x => if good then h x-lam2/R^4 else v₁ x
  let b := outerOffset Z B R
  let v₃ := fun x => if radial then b x else v₁ x
  let s₁ := fun x => innerSource (R/2) μ p x+outerCoefficient (R/2) x*reaction κ (nuclearField Z x+a x)
  let s₂ := fun x => if good then 4*Real.pi*μ x else s₁ x
  let sb := fun x => outerCoefficient R x*reaction κ (nuclearField Z x+b x)
  let s₃ := fun x => if radial then sb x else s₁ x
  let g := innerSource R μ (addedError good R μ p)
  have hv₁ : Continuous v₁ := ha.sub continuous_const
  have hv₂ : Continuous v₂ := by
    dsimp [v₂]; split_ifs; exact hhc.sub continuous_const; exact hv₁
  have hb : Continuous b := outerOffset_continuous Z B hR
  have hv₃ : Continuous v₃ := by dsimp [v₃]; split_ifs; exact hb; exact hv₁
  have hs₁ : LocallyIntegrable s₁ := nuclear_source_locallyIntegrable Z κ (by linarith : 0 < R/2)
    (innerSource_locallyIntegrable hμ hp (R/2)) (outerCoefficient_measurable (R/2))
    (outerCoefficient_bound (R/2)) (outerCoefficient_zero (R/2)) ha
  have hs₂ : LocallyIntegrable s₂ := by
    dsimp [s₂]; split_ifs; exact hμ.smul (4*Real.pi); exact hs₁
  have hsb : LocallyIntegrable sb := by
    simpa only [zero_add] using nuclear_source_locallyIntegrable Z κ hR
      (locallyIntegrable_zero (X := TFSpace) (ε'' := ℝ)) (outerCoefficient_measurable R)
      (outerCoefficient_bound R) (outerCoefficient_zero R) hb
  have hs₃ : LocallyIntegrable s₃ := by dsimp [s₃]; split_ifs; exact hsb; exact hs₁
  have hg : LocallyIntegrable g := innerSource_locallyIntegrable hμ (addedError_locallyIntegrable good hμ hp R) R
  have hw₁ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v₁ x) s₁ := by
    have hw := (hwa.sub_const ((nuclearField_locallyIntegrable Z).add ha.locallyIntegrable) (lam1/R^4)).mono_set
      (subset_univ U)
    simpa only [v₁,add_sub_assoc] using hw
  have hw₂ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v₂ x) s₂ := by
    by_cases hgood : good
    · have hw := ((hwh hgood).sub_const ((nuclearField_locallyIntegrable Z).add hhc.locallyIntegrable)
        (lam2/R^4)).mono_set (subset_univ U)
      simpa only [v₂,s₂,ite_eq_left hgood,add_sub_assoc] using hw
    · simpa only [v₂,s₂,ite_eq_right hgood] using hw₁
  have hw₃ : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v₃ x) s₃ := by
    by_cases hrad : radial
    · have hw := (outerOffset_weak_nuclear cal.B_pos hR cal.k_nonneg cal.subsolution Z).mono_set (hUrad hrad)
      have hw' : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+b x) sb :=
        hw.congr_source (fun x hx => by simp only [sb,outerCoefficient,ite_eq_left (hUrad hrad x hx).le,one_mul,b])
      simpa only [v₃,s₃,ite_eq_left hrad] using hw'
    · simpa only [v₃,s₃,ite_eq_right hrad] using hw₁
  have hd₁ (x : TFSpace) (_hx : x ∈ U)
      (hn : max (max (v₁ x) (v₂ x)) (v₃ x)-v₁ x < 2*(e/R^4)) :
      g x+outerCoefficient R x*reaction κ (nuclearField Z x+v₁ x) ≤ s₁ x := by
    apply outward_old_retained_dom good cal.B_pos hR cal.k_nonneg
      (cal.xi_nonneg.trans (cal.low_shift.le.trans cal.shift_order)) cal.xi_nonneg cal.gap
      cal.height_low cal.height_high hlo hhi
      (fun hgood y hy hy' => hinv hgood y hy (by nlinarith [cal.M_large]))
      (h := h) (p := p) (w := max (max (v₁ x) (v₂ x)) (v₃ x))
    · intro hgood
      have hh : v₂ x ≤ max (max (v₁ x) (v₂ x)) (v₃ x) :=
        (le_max_right _ _).trans (le_max_left _ _)
      simpa only [v₂,ite_eq_left hgood] using hh
    · exact hn
  have hd₂ (x : TFSpace) (hx : x ∈ U)
      (hn : max (max (v₁ x) (v₂ x)) (v₃ x)-v₂ x < 2*(e/R^4)) :
      g x+outerCoefficient R x*reaction κ (nuclearField Z x+v₂ x) ≤ s₂ x := by
    by_cases hgood : good
    · simp only [v₂,ite_eq_left hgood] at hn ⊢
      simp only [s₂,ite_eq_left hgood]
      exact outward_field_retained_dom good cal.B_pos hR cal.e_pos cal.xi_nonneg cal.low_shift
        (cal.xi_nonneg.trans cal.low_shift.le) cal.height_low cal.height_high cal.e_small hpn hμn
        (hUbound x hx) (fun hy => hinv hgood x (by linarith) (hUbound x hx))
        (fun hy => hhcap hgood x (by linarith) (hUbound x hx)) (hwlo x hx) (by simpa only [outwardRegionOffset,v₁,v₂,v₃,b,ite_eq_left hgood] using hn)
    · simp only [v₂,ite_eq_right hgood] at hn ⊢
      simpa only [s₂,ite_eq_right hgood] using hd₁ x hx (by simpa only [v₂,ite_eq_right hgood] using hn)
  have hd₃ (x : TFSpace) (hx : x ∈ U)
      (hn : max (max (v₁ x) (v₂ x)) (v₃ x)-v₃ x < 2*(e/R^4)) :
      g x+outerCoefficient R x*reaction κ (nuclearField Z x+v₃ x) ≤ s₃ x := by
    by_cases hrad : radial
    · have hrx := hUrad hrad x hx
      have hp' := addedError_nonneg good (R := R) hμn hpn x
      have hπ : 0 < 4*Real.pi := by positivity
      simp only [v₃,s₃,g,sb,ite_eq_left hrad,innerSource,ite_eq_right (not_lt_of_ge hrx.le),zero_sub]
      nlinarith
    · simpa only [v₃,s₃,ite_eq_right hrad] using hd₁ x hx (by simpa only [v₃,ite_eq_right hrad] using hn)
  exact nuclear_retained_max_three hU Z hR (div_pos cal.e_pos (pow_pos hR 4)) hv₁ hv₂ hv₃
    hs₁ hs₂ hs₃ hg (outerCoefficient_measurable R) (outerCoefficient_bound R) (outerCoefficient_zero R)
    hw₁ hw₂ hw₃ (ae_of_all _ hd₁) (ae_of_all _ hd₂) (ae_of_all _ hd₃)

end CoulombBarrier

end

end OAI
