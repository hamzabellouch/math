import OAI.Probability.LatticePassage.PlanarCalibration
import OAI.Probability.LatticePassage.HilbertWeakCompactness
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology

noncomputable abbrev CalibrationL2 := Lp ℝ 2 environmentLaw

noncomputable def passageL2 (x y : Vertex) : CalibrationL2 :=
  (passageTime_memLp_two x y).toLp (fun ω => passageTime ω x y)

noncomputable def approxL2 (d a b : Vertex) (n : ℕ) (x y : Vertex) : CalibrationL2 :=
  (planarTargetCocycle_memLp_two d a b x y ((n+1)*(n+1)) (n+1)
    (by nlinarith) (by omega)).toLp (fun ω => calibrationApprox d a b n ω x y)

lemma coe_passageL2 (x y : Vertex) : passageL2 x y =ᵐ[environmentLaw] fun ω => passageTime ω x y :=
  MemLp.coeFn_toLp _

lemma coe_approxL2 (d a b : Vertex) (n : ℕ) (x y : Vertex) :
    approxL2 d a b n x y =ᵐ[environmentLaw] fun ω => calibrationApprox d a b n ω x y :=
  MemLp.coeFn_toLp _

theorem approxL2_norm_le (d a b : Vertex) (n : ℕ) (x y : Vertex) :
    ‖approxL2 d a b n x y‖ ≤ ‖passageL2 x y‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coe_approxL2 d a b n x y, coe_passageL2 x y,
    planarTargetCocycle_dominated d a b ((n+1)*(n+1)) (n+1) (by nlinarith) (by omega)] with ω hc hp hd
  rw [hc, hp, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hd x y).trans (le_abs_self _)

theorem approxL2_add (d a b : Vertex) (n : ℕ) (x y z : Vertex) :
    approxL2 d a b n x z = approxL2 d a b n x y + approxL2 d a b n y z := by
  apply Lp.ext
  filter_upwards [coe_approxL2 d a b n x z, coe_approxL2 d a b n x y,
    coe_approxL2 d a b n y z, Lp.coeFn_add (approxL2 d a b n x y) (approxL2 d a b n y z)]
    with ω hx hy hz ha
  rw [hx, ha, Pi.add_apply, hy, hz]
  exact planarTargetCocycle_add d a b _ _ ω x y z

noncomputable def translationL2 (a : Vertex) : CalibrationL2 →L[ℝ] CalibrationL2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ (environmentTranslation a)
    (environmentTranslation_preserving a)).toContinuousLinearMap

lemma coe_translationL2 (a : Vertex) (f : CalibrationL2) :
    translationL2 a f =ᵐ[environmentLaw] fun ω => f (environmentTranslation a ω) :=
  Lp.coeFn_compMeasurePreserving f (environmentTranslation_preserving a)

theorem approxL2_shift_norm_le (d a b : Vertex) (n : ℕ) (x y : Vertex) :
    ‖translationL2 a (approxL2 d a b n x y) - approxL2 d a b n (a+x) (a+y)‖ ≤
      (2/(n+1))*‖passageL2 (a+x) (a+y)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hcomp := (environmentTranslation_preserving a).quasiMeasurePreserving.ae
    (coe_approxL2 d a b n x y)
  filter_upwards [coe_translationL2 a (approxL2 d a b n x y), hcomp,
    coe_approxL2 d a b n (a+x) (a+y), coe_passageL2 (a+x) (a+y),
    Lp.coeFn_sub (translationL2 a (approxL2 d a b n x y)) (approxL2 d a b n (a+x) (a+y)),
    planarTargetCocycle_shift_bound d a b x y ((n+1)*(n+1)) (n+1) (by nlinarith) (by omega)]
    with ω ht hc he hp hs hb
  rw [hs, Pi.sub_apply, ht, hc, he, hp, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    _ ≤ 2*passageTime ω (a+x) (a+y)/(n+1) := by exact_mod_cast hb
    _ ≤ (2/(n+1))*|passageTime ω (a+x) (a+y)| := by
      calc
        _ = (2/((n : ℝ)+1))*passageTime ω (a+x) (a+y) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)

theorem approxL2_shift_tendsto (d a b x y : Vertex) :
    Tendsto (fun n : ℕ => translationL2 a (approxL2 d a b n x y) -
      approxL2 d a b n (a+x) (a+y)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => approxL2_shift_norm_le d a b n x y)
  have h := ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp
    (tendsto_add_atTop_nat 1)).mul_const ‖passageL2 (a+x) (a+y)‖
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, zero_mul] using h

theorem exists_calibration_weak_limit (d a b : Vertex) :
    ∃ (B : Vertex → Vertex → CalibrationL2) (l : Filter ℕ), l.NeBot ∧ l ≤ atTop ∧
      ∀ x y, Tendsto (fun n => toWeakSpace ℝ CalibrationL2 (approxL2 d a b n x y)) l
        (𝓝 (toWeakSpace ℝ CalibrationL2 (B x y))) := by
  obtain ⟨u,l,hl,hle,hu⟩ := exists_weak_product_limit
    (fun n (p : Vertex × Vertex) => approxL2 d a b n p.1 p.2)
    (fun p => ‖passageL2 p.1 p.2‖) (fun n p => approxL2_norm_le d a b n p.1 p.2)
  refine ⟨fun x y => (toWeakSpace ℝ CalibrationL2).symm (u (x,y)), l, hl, hle, ?_⟩
  intro x y
  exact (continuous_apply (x,y)).tendsto (u) |>.comp hu

end CompanionFPP

end OAI
