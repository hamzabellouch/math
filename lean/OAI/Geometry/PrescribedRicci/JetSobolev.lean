import Mathlib
import OAI.Geometry.PrescribedPotential.CoreBounds
import OAI.Geometry.PrescribedRicci.JetTrim

namespace OAI

/-! Jet Sobolev. -/

section

 

noncomputable section
open Set Finset MeasureTheory LineDeriv TemperedDistribution
open scoped ContDiff Classical BigOperators ENNReal SchwartzMap
namespace TameInterpolation
open SobolevChart EllipticKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι κ : Type*}

lemma cdir_schwartz (v : E) (f : 𝓢(E,ℂ)) : cdir v f = (∂_{v} f : 𝓢(E,ℂ)) := by
  funext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

lemma cword_schwartz (e : ι → E) (f : 𝓢(E,ℂ)) (ws : List ι) :
    cword e f ws = (schwartzWord (ws.map e) f : E → ℂ) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change cdir (e a) (cword e f ws) = _
    rw [ih,cdir_schwartz]
    rfl

lemma cjet_schwartz (e : ι → E) (f : 𝓢(E,ℂ)) {j : ℕ} (w : Fin j → ι) :
    cjet e f w = (schwartzWord ((List.ofFn w).map e) f : E → ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [cjet,List.ofFn_succ,List.map_cons,schwartzWord,ContinuousLinearMap.comp_apply]
    rw [ih,cdir_schwartz]
    rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lpNorm_schwartz_zero (f : 𝓢(E,ℂ)) : lpNorm (f : E → ℂ) 2 volume = ‖schwartzCoord 0 f‖ := by
  have he : schwartzCoord 0 f = f.toLp 2 volume := by
    apply l2_injective
    simpa [realize] using realize_schwartzCoord 0 f
  rw [he,SchwartzMap.norm_toLp,toReal_eLpNorm]

lemma lpNorm_realComponent_le (f : E → ℂ) {p : ℝ≥0∞} (hf : MemLp f p volume) (b : Bool) :
    lpNorm (fun x => if b then (f x).im else (f x).re) p volume ≤ lpNorm f p volume := by
  apply (lpNorm_mono_real hf.norm (fun x => ?_)).trans_eq (lpNorm_norm hf.aestronglyMeasurable p)
  cases b
  · exact Complex.abs_re_le_norm (f x)
  · exact Complex.abs_im_le_norm (f x)

variable [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

theorem familyJetNorm_sobolev_bound (e : ι → E) (j : ℕ) (s : ℝ) (hs : (j:ℝ) ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : κ → 𝓢(E,ℂ),
      familyJetNorm e (realComponents (fun i => (F i : E → ℂ))) j 2 ≤
        C*∑ i, ‖schwartzCoord s (F i)‖ := by
  have hb (w : Fin j → ι) : CoreBound s 0 (schwartzWord ((List.ofFn w).map e)) :=
    coreBound_word _ (by simpa using sub_nonneg.mpr hs)
  choose C hC hbound using hb
  refine ⟨∑ w, C w,Finset.sum_nonneg fun w _ => hC w,fun F => ?_⟩
  obtain ⟨⟨i,b⟩,ha⟩ := familyJetNorm_attained e (realComponents (fun i => (F i : E → ℂ))) j 2
  obtain ⟨w,hw⟩ := jetNorm_attained e (realComponents (fun i => (F i : E → ℂ)) (i,b)) j 2
  rw [ha,hw]
  have he : jet e (realComponents (fun i => (F i : E → ℂ)) (i,b)) w =
      fun x => if b then (cjet e (F i) w x).im else (cjet e (F i) w x).re := by
    cases b
    · exact cjet_real_map e (F i).smooth' Complex.reCLM w
    · exact cjet_real_map e (F i).smooth' Complex.imCLM w
  rw [he]
  have hmem : MemLp (cjet e (F i) w) 2 volume := by rw [cjet_schwartz]; exact (schwartzWord _ _).memLp _ _
  apply (lpNorm_realComponent_le _ hmem b).trans
  rw [cjet_schwartz,lpNorm_schwartz_zero]
  apply (hbound w (F i)).trans
  exact mul_le_mul (Finset.single_le_sum (fun w _ => hC w) (Finset.mem_univ w))
    (Finset.single_le_sum (f:=fun i => ‖schwartzCoord s (F i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    (norm_nonneg _) (Finset.sum_nonneg fun w _ => hC w)

def initialSchwartz (e : ι → E) (F : κ → 𝓢(E,ℂ)) (q : κ × Option ι) : 𝓢(E,ℂ) :=
  match q.2 with
  | none => F q.1
  | some a => ∂_{e a} (F q.1)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ] in
lemma initialSchwartz_coe (e : ι → E) (F : κ → 𝓢(E,ℂ)) (q : κ × Option ι) :
    (initialSchwartz e F q : E → ℂ) = initialJet e (fun i => (F i : E → ℂ)) q := by
  rcases q with ⟨i,q⟩; cases q
  · rfl
  · exact (cdir_schwartz _ _).symm

theorem initialJet_sobolev_bound (e : ι → E) (j : ℕ) (s : ℝ) (hs : (j:ℝ)+1 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : κ → 𝓢(E,ℂ),
      familyJetNorm e (realComponents (initialJet e (fun i => (F i : E → ℂ)))) j 2 ≤
        C*∑ i, ‖schwartzCoord s (F i)‖ := by
  obtain ⟨B,hB,hb⟩ := familyJetNorm_sobolev_bound (κ:=κ×Option ι) e j (j:ℝ) le_rfl
  have hq (q : Option ι) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(E,ℂ),
      ‖schwartzCoord (j:ℝ) (initialSchwartz e (fun _ : κ => f) (Classical.choice inferInstance,q))‖ ≤
        C*‖schwartzCoord s f‖ := by
    cases q with
    | none => exact CoreBound.id (by linarith)
    | some a => exact coreBound_deriv (e a) (by linarith)
  choose C hC hcb using hq
  refine ⟨B*∑ q : κ×Option ι, C q.2,mul_nonneg hB (Finset.sum_nonneg fun q _ => hC q.2),fun F => ?_⟩
  have he : (fun q => (initialSchwartz e F q : E → ℂ)) = initialJet e (fun i => (F i : E → ℂ)) :=
    funext (initialSchwartz_coe e F)
  rw [← he]
  apply (hb (initialSchwartz e F)).trans
  rw [mul_assoc,Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ hB
  apply Finset.sum_le_sum
  intro q _
  have hqq := hcb q.2 (F q.1)
  have heq : initialSchwartz e (fun _ : κ => F q.1) (Classical.choice inferInstance,q.2) = initialSchwartz e F q := by
    cases q with
    | mk i a => cases a <;> rfl
  rw [heq] at hqq
  exact hqq.trans (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f:=fun i => ‖schwartzCoord s (F i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ q.1)) (hC q.2))
end TameInterpolation

end
end

end OAI
