import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierDataSelectionBarrier

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set Metric
open scoped Topology
namespace CoulombAnalysis
open CoulombAtom

lemma tfDilation_exterior_mass {s : ℝ} (hs : 0 < s) (R : ℝ) (μ : TFSpace → ℝ) :
    (∫ x in {x : TFSpace | R < ‖x‖}, tfDilation s μ x) =
      s^3*(∫ x in {x : TFSpace | s*R < ‖x‖}, μ x) := by
  have hE : MeasurableSet {x : TFSpace | R < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  have hEs : MeasurableSet {x : TFSpace | s*R < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  rw [←integral_indicator hE,←integral_indicator hEs,←tfDilation_mass hs]
  congr 1
  funext x
  have hx : s*R < ‖s • x‖ ↔ R < ‖x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hs.le,mul_lt_mul_iff_right₀ hs]
  change {x : TFSpace | R < ‖x‖}.indicator (tfDilation s μ) x = s^6*{x : TFSpace | s*R < ‖x‖}.indicator μ (s • x)
  by_cases hh : R < ‖x‖
  · rw [indicator_of_mem (show x ∈ {x : TFSpace | R < ‖x‖} from hh),
      indicator_of_mem (show s • x ∈ {x : TFSpace | s*R < ‖x‖} from hx.mpr hh)]
    rfl
  · rw [indicator_of_notMem (show x ∉ {x : TFSpace | R < ‖x‖} from hh),
      indicator_of_notMem (show s • x ∉ {x : TFSpace | s*R < ‖x‖} from fun h => hh (hx.mp h)),mul_zero]

end CoulombAnalysis
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

def selectedDyadicIndex (r t : ℝ) : ℕ := by
  classical
  exact if h : @Exists ℕ (fun J => (2:ℝ)^J*r ≤ t ∧ t < 2*((2:ℝ)^J*r)) then Classical.choose h else 0

lemma selectedDyadicIndex_spec {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t) :
    (2:ℝ)^(selectedDyadicIndex r t)*r ≤ t ∧
      t < 2*((2:ℝ)^(selectedDyadicIndex r t)*r) := by
  have h : ∃ J : ℕ, (2:ℝ)^J*r ≤ t ∧ t < 2*((2:ℝ)^J*r) := by
    obtain ⟨J,hJ,hJ'⟩ := exists_nat_pow_near ((one_le_div hr).mpr hrt) (by norm_num : (1:ℝ) < 2)
    refine ⟨J,(le_div_iff₀ hr).mp hJ,?_⟩
    have hh := (div_lt_iff₀ hr).mp hJ'
    rw [pow_succ] at hh
    nlinarith only [hh]
  simpa only [selectedDyadicIndex,dite_eq_left h] using Classical.choose_spec h

lemma selectedDyadicIndex_radius {r s l : ℝ} (hr : 0 < r) (hs : 0 < s) (hl : 1 ≤ l)
    (hrs : r ≤ s/l) :
    let u := (2:ℝ)^(selectedDyadicIndex r (s/l))*r
    0 < u ∧ u ≤ s ∧ 1/(2*l) ≤ u/s ∧ u/s ≤ l⁻¹ ∧ s*l ≤ (2*l^2)*u := by
  let u := (2:ℝ)^(selectedDyadicIndex r (s/l))*r
  have hspec := selectedDyadicIndex_spec hr hrs
  have hlp : 0 < l := zero_lt_one.trans_le hl
  have hu : 0 < u := mul_pos (pow_pos (by norm_num) _) hr
  have hlu : l*u ≤ s := by nlinarith [(le_div_iff₀ hlp).mp hspec.1]
  have hslu : s < 2*l*u := by nlinarith [(div_lt_iff₀ hlp).mp hspec.2]
  refine ⟨hu,?_,?_,?_,?_⟩
  · exact hspec.1.trans (div_le_self hs.le hl)
  · apply (le_div_iff₀ hs).mpr
    have hh : s/(2*l) ≤ u := (div_le_iff₀ (show 0 < 2*l by positivity)).mpr (by nlinarith only [hslu])
    simpa only [u,one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  · exact (div_le_iff₀ hs).mpr (by simpa only [one_div,mul_comm,div_eq_mul_inv] using hspec.1)
  · nlinarith [mul_nonneg hlp.le (sub_nonneg.mpr hslu.le)]

lemma fixed_target_nuclear_radius_eventually {ι : Type*} {F : Filter ι} {Z s : ι → ℝ}
    (hZ : ∀ i, 0 < Z i) (hs : ∀ i, 0 < s i)
    (hscale : Tendsto (fun i => Z i*(s i)^3) F atTop)
    {ε l : ℝ} (hε : 0 < ε) (hl : 0 < l) :
    ∀ᶠ i in F, ε*(Z i)^(-1/3:ℝ) ≤ s i/l := by
  filter_upwards [hscale.eventually_ge_atTop (ε^3*l^3)] with i hi
  apply (pow_le_pow_iff_left₀
    (mul_nonneg hε.le (Real.rpow_nonneg (hZ i).le _))
    (div_nonneg (hs i).le hl.le) (by norm_num : 3 ≠ 0)).mp
  apply (mul_le_mul_iff_right₀ (hZ i)).mp
  rw [nuclear_radius_relation (hZ i),div_pow,←mul_div_assoc]
  exact (le_div_iff₀ (pow_pos hl 3)).mpr hi

end CoulombBarrier

end

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace CoulombAtom

lemma oneBody_coordinate_derivative {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (i j : Fin N) (a : Fin 3) (x : Configuration N) :
    lineDeriv ℝ (fun y : Configuration N => p.value (y i)) x (direction j a) =
      if j = i then lineDeriv ℝ p.value (x i) (spaceDirections a) else 0 := by
  exact spatial_coordinate_derivative (fun _ : Fin 2 => p) 0 i j a x

def SmoothMultiplier.oneBody {N : ℕ} (p : SmoothMultiplier spaceDirections) (i : Fin N) :
    SmoothMultiplier (sectorDirections N) where
  value := fun x => p.value (x i)
  regular := p.regular.comp (electronProjection i).contDiff
  bound := by obtain ⟨C,hC⟩ := p.bound; exact ⟨C,fun x => hC (x i)⟩
  gradient_bound := by
    intro j
    obtain ⟨C,hC⟩ := p.gradient_bound j.2
    refine ⟨max C 0, fun x => ?_⟩
    change |lineDeriv ℝ (fun y : Configuration N => p.value (y i)) x (direction j.1 j.2)| ≤ _
    rw [oneBody_coordinate_derivative]
    split_ifs
    · exact (hC (x i)).trans (le_max_left _ _)
    · exact (by simpa only [abs_zero] using (le_max_right C 0))

def oneBodySquareTotal {N : ℕ} (p : SmoothMultiplier spaceDirections) :
    FermionMultiplier N where
  toSmoothMultiplier := SmoothMultiplier.sumSquares p.oneBody
  symmetric := by
    intro π x
    change (∑ i, p.value ((x ∘ π) i)^2) = ∑ i,p.value (x i)^2
    exact Equiv.sum_comp π (fun i => p.value (x i)^2)

lemma oneBodySquareTotal_value {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (x : Configuration N) : (oneBodySquareTotal p).value x = ∑ i,p.value (x i)^2 := rfl

lemma oneBodySquareTotal_component {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (s : Spins N) (k : Option (Fin N × Fin 3)) :
    graphComponent s k ((oneBodySquareTotal p).apply F) =
      ∑ i, ((p.oneBody i).apply ((p.oneBody i).apply (F.val s))).val k := by
  change ((SmoothMultiplier.sumSquares p.oneBody).apply (F.val s)).val k = _
  rw [SmoothMultiplier.sumSquares_apply, weakGraph_sum_component]

lemma SmoothMultiplier.square_integrable (p : SmoothMultiplier spaceDirections)
    {N : ℕ} (i : Fin N) {f : Configuration N → ℝ} (hf : Integrable f) :
    Integrable (fun x => p.value (x i)^2*f x) := by
  obtain ⟨C,hC⟩ := p.bound
  apply weighted_integrable hf ((p.regular.continuous.comp (continuous_apply i)).pow 2)
  intro x
  change ‖p.value (x i)^2‖ ≤ C^2
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hC (x i)) 2

lemma oneBodySquareTotal_integral {N : ℕ} (p : SmoothMultiplier spaceDirections)
    {f : Configuration N → ℝ} (hf : Integrable f) :
    (∫ x, (oneBodySquareTotal p).value x*f x) = ∑ i, ∫ x,p.value (x i)^2*f x := by
  simp only [oneBodySquareTotal_value, Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => p.square_integrable i hf)

lemma oneBody_pairing_off {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : weakGraph (sectorDirections N)) (i j : Fin N) (hij : i ≠ j) (a : Fin 3) :
    (⟪((p.oneBody i).apply ((p.oneBody i).apply F)).val (some (j,a)),
      F.val (some (j,a))⟫_ℂ).re = ∫ x,p.value (x i)^2*‖F.val (some (j,a)) x‖^2 := by
  apply l2_real_weight_pairing
  have hd (x : Configuration N) : lineDeriv ℝ (p.oneBody i).value x
      (sectorDirections N (j,a)) = 0 := by
    simp only [SmoothMultiplier.oneBody,sectorDirections,oneBody_coordinate_derivative,
      ite_eq_right (Ne.symm hij)]
  filter_upwards [(p.oneBody i).apply_gradient ((p.oneBody i).apply F) (j,a),
    (p.oneBody i).apply_gradient F (j,a)] with x hx hy
  rw [hd,Complex.ofReal_zero,zero_mul,add_zero] at hx hy
  rw [hx,hy]
  simp only [SmoothMultiplier.oneBody,Complex.ofReal_pow]
  ring

lemma oneBody_kinetic_error {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : weakGraph (sectorDirections N)) (i : Fin N) :
    -(∑ a : Fin 3, ∫ x, (lineDeriv ℝ p.value (x i) (spaceDirections a))^2*
      ‖F.val none x‖^2) ≤ ∑ a : Fin 3,
      (⟪((p.oneBody i).apply ((p.oneBody i).apply F)).val (some (i,a)),
        F.val (some (i,a))⟫_ℂ).re := by
  have hi (a : Fin 3) : ‖((p.oneBody i).apply F).val (some (i,a))‖^2 -
      (⟪((p.oneBody i).apply ((p.oneBody i).apply F)).val (some (i,a)),
        F.val (some (i,a))⟫_ℂ).re =
      ∫ x, (lineDeriv ℝ p.value (x i) (spaceDirections a))^2*‖F.val none x‖^2 := by
    have hh := l2_ims_identity (p.oneBody i).value
      (fun x => lineDeriv ℝ (p.oneBody i).value x (sectorDirections N (i,a)))
      (F.val (some (i,a))) (F.val none) (((p.oneBody i).apply F).val (some (i,a)))
      (((p.oneBody i).apply ((p.oneBody i).apply F)).val (some (i,a)))
      ((p.oneBody i).apply_gradient F (i,a))
    have hh' := hh (by
      filter_upwards [(p.oneBody i).apply_gradient ((p.oneBody i).apply F) (i,a),
        (p.oneBody i).apply_value F] with x hx hy
      rw [hx,hy])
    simpa only [SmoothMultiplier.oneBody,sectorDirections,oneBody_coordinate_derivative,
      ite_eq_left rfl,ite_true] using hh'
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun a _ => hi a)
  have hn : 0 ≤ ∑ a : Fin 3, ‖((p.oneBody i).apply F).val (some (i,a))‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Finset.sum_sub_distrib] at hs
  linarith

lemma oneBody_kinetic_lower {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : weakGraph (sectorDirections N)) (i : Fin N) :
    (∑ j,∑ a,∫ x,p.value (x i)^2*‖F.val (some (j,a)) x‖^2) -
      (∑ a,∫ x,p.value (x i)^2*‖F.val (some (i,a)) x‖^2) -
      (∑ a,∫ x,(lineDeriv ℝ p.value (x i) (spaceDirections a))^2*‖F.val none x‖^2) ≤
    ∑ j,∑ a,(⟪((p.oneBody i).apply ((p.oneBody i).apply F)).val (some (j,a)),
      F.val (some (j,a))⟫_ℂ).re := by
  classical
  let A (j : Fin N) := ∑ a,∫ x,p.value (x i)^2*‖F.val (some (j,a)) x‖^2
  let B (j : Fin N) := ∑ a,(⟪((p.oneBody i).apply ((p.oneBody i).apply F)).val
    (some (j,a)),F.val (some (j,a))⟫_ℂ).re
  have he : (∑ j,if j ≠ i then B j else 0) = ∑ j,if j ≠ i then A j else 0 := by
    apply Finset.sum_congr rfl; intro j _
    split_ifs with hji
    · apply Finset.sum_congr rfl; intro a _
      exact oneBody_pairing_off p F i j hji.symm a
    · rfl
  have ha := sum_excluding_add i A
  have hb := sum_excluding_add i B
  have hp := oneBody_kinetic_error p F i
  change -_ ≤ B i at hp
  change (∑ j,A j)-A i-_ ≤ ∑ j,B j
  rw [he] at hb
  linarith

end CoulombAtom

end

end OAI
