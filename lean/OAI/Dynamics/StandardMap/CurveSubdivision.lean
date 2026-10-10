import OAI.Dynamics.StandardMap.CurveCharts

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
noncomputable def subdivisionInterval (N : ℕ) (hN : 0<N) (i : Fin N) : CurveInterval where
  left := (i:ℝ)/N
  right := ((i:ℝ)+1)/N
  left_nonneg := by positivity
  ordered := by apply div_le_div_of_nonneg_right; linarith; positivity
  right_le := by
    have hNr:0<(N:ℝ) := by exact_mod_cast hN
    apply (div_le_one hNr).mpr
    exact_mod_cast (Nat.succ_le_of_lt i.isLt)
lemma subdivisionInterval_length (N : ℕ) (hN : 0<N) (i : Fin N) :
    (subdivisionInterval N hN i).length=1/(N:ℝ) := by
  dsimp [CurveInterval.length,subdivisionInterval]; ring
lemma subdivisionInterval_cover (N : ℕ) (hN : 0<N) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    ∃i:Fin N,x∈Icc (subdivisionInterval N hN i).left (subdivisionInterval N hN i).right := by
  have hNr:0<(N:ℝ) := by exact_mod_cast hN
  let q:=⌊(N:ℝ)*x⌋₊
  have hq0:(q:ℝ)≤N*x := Nat.floor_le (mul_nonneg hNr.le hx.1)
  have hq1:(N:ℝ)*x<(q:ℝ)+1 := Nat.lt_floor_add_one _
  by_cases hq:q<N
  · refine ⟨⟨q,hq⟩,?_⟩
    change (q:ℝ)/N≤x ∧ x≤((q:ℝ)+1)/N
    exact ⟨(div_le_iff₀ hNr).mpr (by nlinarith), (le_div_iff₀ hNr).mpr (by nlinarith)⟩
  · have hq2:(N:ℝ)≤q := by exact_mod_cast (show N≤q by omega)
    have hx1:x=1 := by nlinarith [hx.2]
    subst x
    refine ⟨⟨N-1,by omega⟩,?_⟩
    have he:((N-1:ℕ):ℝ)+1=N := by exact_mod_cast (show N-1+1=N by omega)
    change ((N-1:ℕ):ℝ)/N≤1 ∧ 1≤(((N-1:ℕ):ℝ)+1)/N
    constructor
    · apply (div_le_one hNr).mpr; linarith
    · rw [he,div_self hNr.ne']
noncomputable def pointCurveInterval : CurveInterval:=⟨0,0,le_rfl,le_rfl,by norm_num⟩
lemma pointCurveInterval_speed (ε : ℝ) (hε : 0≤ε) (v : ℝ → CurvePlane) (t : ℝ) :
    ‖pointCurveInterval.velocity v t‖≤ε := by simpa [CurveInterval.velocity,CurveInterval.length,pointCurveInterval] using hε
lemma restricted_controlled_curve (ε : ℝ) (hε : 0≤ε) (g v : ℝ → CurvePlane)
    (hv : ∀t,HasDerivAt g (v t) t) (hc : Continuous v)
    (hvar : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,‖v s-v t‖≤ε*|s-t|)
    (I : CurveInterval) (hs : ∀t∈Icc (0:ℝ) 1,‖I.velocity v t‖≤ε) :
    ∃C:ControlledCurve ε,C.map=g ∘ I.parameter ∧ C.velocity=I.velocity v := by
  refine ⟨⟨g ∘ I.parameter,I.velocity v,I.hasDeriv hv,I.velocity_continuous hc,hs,?_⟩,rfl,rfl⟩
  intro s hs t ht
  apply (I.variation hvar hs ht).trans
  have hsq:I.length^2≤1 := by nlinarith [I.length_nonneg,I.length_le_one]
  exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)

lemma curve_small_target_cover (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (ε δ : ℝ) (hε : 0≤ε) (hδ : 3*δ≤ε)
    (hvar : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,‖v s-v t‖≤ε*|s-t|)
    (S : Set ℝ) (hS : IsCompact S) (hsub : S⊆Icc (0:ℝ) 1)
    (hdiam : ∀s∈S,∀t∈S,‖g s-g t‖≤δ) :
    ∃I:Fin 4→CurveInterval,
      (∀s∈S,∃i,s∈Icc (I i).left (I i).right) ∧
      (∀i,∀t∈Icc (0:ℝ) 1,‖(I i).velocity v t‖≤ε) := by
  by_cases hne:S.Nonempty
  · by_cases hf:2*ε<‖v 0‖
    · obtain ⟨J,hJ,hs⟩:=curve_compact_hull g v hv ε δ hε hδ hvar hf S hS hne hsub hdiam
      exact ⟨fun _=>J,fun s hs=>⟨0,hJ hs⟩,fun _=>hs⟩
    · refine ⟨subdivisionInterval 4 (by norm_num),fun s hs=>subdivisionInterval_cover 4 (by norm_num) (hsub hs),?_⟩
      intro i t ht
      rw [CurveInterval.velocity_norm,subdivisionInterval_length]
      have hp: (subdivisionInterval 4 (by norm_num) i).parameter t∈Icc (0:ℝ) 1 := CurveInterval.parameter_mem _ ht
      have hv0:=hvar _ hp 0 (by norm_num)
      simp only [sub_zero,abs_of_nonneg hp.1] at hv0
      have hn:=norm_sub_le_norm_sub_add_norm_sub (v ((subdivisionInterval 4 (by norm_num) i).parameter t)) (v 0) 0
      simp only [sub_zero] at hn
      have he:=mul_le_of_le_one_right hε hp.2
      norm_num at *
      linarith
  · exact ⟨fun _=>pointCurveInterval,fun s hs=>(hne ⟨s,hs⟩).elim,
      fun _ t _=>pointCurveInterval_speed ε hε v t⟩
end StandardMapEntropy

end OAI
