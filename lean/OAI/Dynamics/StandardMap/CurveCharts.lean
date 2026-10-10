import OAI.Dynamics.StandardMap.CurveCore

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
structure CurveInterval where
  left : ℝ
  right : ℝ
  left_nonneg : 0≤left
  ordered : left≤right
  right_le : right≤1
namespace CurveInterval
def length (I : CurveInterval) : ℝ:=I.right-I.left
def parameter (I : CurveInterval) : ℝ → ℝ:=affineParameter I.left I.right
lemma length_nonneg (I : CurveInterval) : 0≤I.length := sub_nonneg.mpr I.ordered
lemma length_le_one (I : CurveInterval) : I.length≤1 := by dsimp [length]; linarith [I.left_nonneg,I.right_le]
lemma parameter_mem (I : CurveInterval) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    I.parameter t∈Icc (0:ℝ) 1 := affineParameter_mem _ _ I.left_nonneg I.ordered I.right_le ht
lemma parameter_range (I : CurveInterval) : I.parameter '' Icc (0:ℝ) 1=Icc I.left I.right :=
  affineParameter_range _ _ I.ordered
lemma parameter_sub (I : CurveInterval) (s t : ℝ) :
    I.parameter s-I.parameter t=I.length*(s-t) := by dsimp [parameter,affineParameter,length]; ring
lemma parameter_abs_sub (I : CurveInterval) (s t : ℝ) :
    |I.parameter s-I.parameter t|=I.length*|s-t| := by
  rw [I.parameter_sub,abs_mul,abs_of_nonneg I.length_nonneg]
def velocity (I : CurveInterval) (v : ℝ → CurvePlane) (t : ℝ) : CurvePlane:=I.length • v (I.parameter t)
lemma velocity_norm (I : CurveInterval) (v : ℝ → CurvePlane) (t : ℝ) :
    ‖I.velocity v t‖=I.length*‖v (I.parameter t)‖ := by
  rw [velocity,norm_smul,Real.norm_eq_abs,abs_of_nonneg I.length_nonneg]
lemma velocity_continuous (I : CurveInterval) {v : ℝ → CurvePlane} (hv : Continuous v) :
    Continuous (I.velocity v) := by
  have hp : Continuous I.parameter := by unfold parameter affineParameter; fun_prop
  exact (continuous_const : Continuous (fun _ : ℝ => I.length)).smul (hv.comp hp)
lemma hasDeriv (I : CurveInterval) {g v : ℝ → CurvePlane} (h : ∀t,HasDerivAt g (v t) t) (t : ℝ) :
    HasDerivAt (g ∘ I.parameter) (I.velocity v t) t := by
  convert! (h (I.parameter t)).scomp t (hasDerivAt_affineParameter I.left I.right t) using 1
lemma variation (I : CurveInterval) {v : ℝ → CurvePlane} {B : ℝ}
    (hB : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,‖v s-v t‖≤B*|s-t|)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    ‖I.velocity v s-I.velocity v t‖≤(I.length^2*B)*|s-t| := by
  rw [velocity,velocity,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg I.length_nonneg]
  calc
    _ ≤ I.length*(B*|I.parameter s-I.parameter t|) :=
      mul_le_mul_of_nonneg_left (hB _ (I.parameter_mem hs) _ (I.parameter_mem ht)) I.length_nonneg
    _ = _ := by rw [I.parameter_abs_sub]; ring
end CurveInterval

lemma curve_compact_hull (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (ε δ : ℝ) (hε : 0≤ε) (hδ : 3*δ≤ε)
    (hvar : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,‖v s-v t‖≤ε*|s-t|)
    (hfast : 2*ε<‖v 0‖) (S : Set ℝ) (hS : IsCompact S)
    (hne : S.Nonempty) (hsub : S⊆Icc (0:ℝ) 1)
    (hdiam : ∀s∈S,∀t∈S,‖g s-g t‖≤δ) :
    ∃I:CurveInterval, S⊆Icc I.left I.right ∧
      ∀t∈Icc (0:ℝ) 1,‖I.velocity v t‖≤ε := by
  obtain ⟨a,ha,hmin⟩:=hS.exists_isLeast hne
  obtain ⟨b,hb,hmax⟩:=hS.exists_isGreatest hne
  have hab:a≤b := hmin hb
  let I:CurveInterval:=⟨a,b,(hsub ha).1,hab,(hsub hb).2⟩
  have hclose:∀t∈Icc (0:ℝ) 1,‖v t-v 0‖≤ε := by
    intro t ht
    have h:=hvar t ht 0 (by norm_num)
    simp only [sub_zero,abs_of_nonneg ht.1] at h
    exact h.trans (mul_le_of_le_one_right hε ht.2)
  have hchord: (‖v 0‖-ε)*(b-a)≤δ := by
    have h:=curve_chord_lower g v hv ε hclose (hsub ha) (hsub hb)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    exact h.trans (hdiam b hb a ha)
  refine ⟨I,fun t ht=>⟨hmin ht,hmax ht⟩,?_⟩
  intro t ht
  have hs:‖v (I.parameter t)‖≤‖v 0‖+ε := by
    have h:=norm_sub_le (v (I.parameter t)-v 0) (-v 0)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at h
    have hc:=hclose _ (I.parameter_mem ht)
    linarith
  rw [I.velocity_norm]
  calc
    _ ≤ (b-a)*(‖v 0‖+ε) := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hab)
    _ ≤ 3*δ := by
      have h:=mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hfast.le)
      nlinarith
    _ ≤ ε := hδ
end StandardMapEntropy

end OAI
