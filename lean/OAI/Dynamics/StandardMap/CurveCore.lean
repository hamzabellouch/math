import OAI.Dynamics.StandardMap.LiftDynamics

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
abbrev CurvePlane := ℝ × ℝ

structure ControlledCurve (ε : ℝ) where
  map : ℝ → CurvePlane
  velocity : ℝ → CurvePlane
  hasDeriv : ∀ t, HasDerivAt map (velocity t) t
  continuous_velocity : Continuous velocity
  speed : ∀ t ∈ Icc (0:ℝ) 1, ‖velocity t‖ ≤ ε
  variation : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
    ‖velocity s-velocity t‖ ≤ ε*|s-t|

def affineParameter (a b t : ℝ) : ℝ := a+(b-a)*t
lemma affineParameter_mem (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : affineParameter a b t∈Icc (0:ℝ) 1 := by
  dsimp [affineParameter]
  rcases ht with ⟨ht0,ht1⟩
  constructor <;> nlinarith
lemma affineParameter_mem_interval (a b : ℝ) (hab : a≤b)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : affineParameter a b t∈Icc a b := by
  dsimp [affineParameter]
  rcases ht with ⟨ht0,ht1⟩
  constructor <;> nlinarith
lemma hasDerivAt_affineParameter (a b t : ℝ) :
    HasDerivAt (affineParameter a b) (b-a) t := by
  convert! ((hasDerivAt_id t).const_mul (b-a)).const_add a using 1 ; simp
lemma affineParameter_range (a b : ℝ) (hab : a≤b) :
    affineParameter a b '' Icc (0:ℝ) 1=Icc a b := by
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩; exact affineParameter_mem_interval a b hab ht
  · intro hx
    by_cases h : a=b
    · subst b; have : x=a := le_antisymm hx.2 hx.1
      subst x; exact ⟨0,by norm_num,by simp [affineParameter]⟩
    · have hba : 0<b-a := sub_pos.mpr (lt_of_le_of_ne hab h)
      refine ⟨(x-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hx.1) hba.le,?_⟩,?_⟩
      · exact (div_le_one hba).mpr (by linarith [hx.2])
      · dsimp [affineParameter]; field_simp; ring
lemma curve_displacement (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (B : ℝ) (hB : ∀t∈Icc (0:ℝ) 1, ‖v t‖≤B)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    ‖g b-g a‖≤B*|b-a| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht=>(hv t).hasDerivWithinAt) hB ha hb
lemma curve_linear_error (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (ε : ℝ) (hε : ∀t∈Icc (0:ℝ) 1, ‖v t-v 0‖≤ε)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    ‖g b-g a-(b-a) • v 0‖≤ε*|b-a| := by
  have h := curve_displacement (fun t=>g t-t • v 0) (fun t=>v t-v 0)
    (fun t=>by
      convert! (hv t).sub ((hasDerivAt_id t).smul_const (v 0)) using 1 ; simp) ε hε ha hb
  convert h using 1 ; congr 1 ; simp only [sub_smul] ; abel
lemma curve_chord_lower (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (ε : ℝ) (hε : ∀t∈Icc (0:ℝ) 1, ‖v t-v 0‖≤ε)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    (‖v 0‖-ε)*|b-a|≤‖g b-g a‖ := by
  have he := curve_linear_error g v hv ε hε ha hb
  have hn := norm_sub_le (g b-g a) (g b-g a-(b-a) • v 0)
  rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs] at hn
  nlinarith
end StandardMapEntropy

end OAI
