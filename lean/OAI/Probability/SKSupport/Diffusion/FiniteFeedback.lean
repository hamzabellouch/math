import Mathlib
import OAI.Probability.SKSupport.Backward.GaussianBackwardShapes
import OAI.Probability.SKSupport.Diffusion.PicardDiffusion

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat

lemma Heat.BoundedSmoothFamily.uniform_lipschitz {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (F t) := by
  obtain ⟨L,hL⟩ := hF.deriv.bound
  exact ⟨L,fun t => lipschitzWith_of_nnnorm_deriv_le
    ((hF.regular t).smooth.differentiable (by simp)) (fun x => hL t x)⟩

def Heat.BoundedSmoothFamily.toDrift {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) : BoundedLipschitzDrift where
  f := F
  bound := hF.bound.choose
  lip := hF.uniform_lipschitz.choose
  measurable := hF.measurable
  bounded := hF.bound.choose_spec
  lipschitz := hF.uniform_lipschitz.choose_spec

def rightCoeff (c : ℕ → ℝ≥0) (h : ℝ≥0) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | N+1, i, t => if t < h then c i else rightCoeff c h N (i+1) (t-h)

lemma rightCoeff_measurable (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : Measurable (rightCoeff c h N i) := by
  induction N generalizing i with
  | zero => exact measurable_const
  | succ N ih =>
    exact Measurable.ite (measurableSet_lt (f := id) (g := fun _ : ℝ => (h:ℝ)) measurable_id measurable_const)
      measurable_const ((ih (i+1)).comp (measurable_id.sub_const (h:ℝ)))

lemma rightCoeff_bounds (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ C : ℝ≥0, ∀ t, 0 ≤ rightCoeff c h N i t ∧ rightCoeff c h N i t ≤ C := by
  induction N generalizing i with
  | zero => exact ⟨0,fun _ => ⟨le_rfl,le_rfl⟩⟩
  | succ N ih =>
    obtain ⟨C,hC⟩ := ih (i+1)
    refine ⟨c i+C,fun t => ?_⟩
    dsimp only [rightCoeff]
    split_ifs with ht
    · exact ⟨(c i).coe_nonneg,by simp only [NNReal.coe_add];linarith [C.coe_nonneg]⟩
    · exact ⟨(hC _).1,by simp only [NNReal.coe_add];linarith [(hC (t-h)).2,(c i).coe_nonneg]⟩

lemma rightCoeff_family (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    BoundedSmoothFamily (fun t (_ : ℝ) => rightCoeff c h N i t) := by
  obtain ⟨C,hC⟩ := rightCoeff_bounds c h N i
  exact BoundedSmoothFamily.timeConst (rightCoeff_measurable c h N i)
    (fun t => by simpa only [abs_of_nonneg (hC t).1] using (hC t).2)

def finiteFeedbackFun (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (t x : ℝ) :=
  rightCoeff c h N i t*deriv (finiteValue c h f N i t) x

lemma finiteFeedback_family {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : BoundedSmoothFamily (finiteFeedbackFun c h f N i) :=
  (rightCoeff_family c h N i).mul (finiteGradient_family hf hLip c h N i)

def finiteFeedback {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : BoundedLipschitzDrift :=
  (finiteFeedback_family hf hLip c h N i).toDrift

lemma finiteValue_shift {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N j : ℕ} (hj : j ≤ N) (i : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    finiteValue c h f N i ((j:ℝ)*h+t)=finiteValue c h f (N-j) (i+j) t := by
  induction j generalizing N i with
  | zero => simp
  | succ j ih =>
    cases N with
    | zero => omega
    | succ N =>
      have hh : (h:ℝ) ≤ ((j+1:ℕ):ℝ)*h+t := by push_cast;nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) h.coe_nonneg]
      rw [finiteValue_tail_of_le hf hLip c h N i hh]
      have he : ((j+1:ℕ):ℝ)*(h:ℝ)+t-h=(j:ℝ)*h+t := by push_cast;ring
      rw [he,ih (by omega)]
      rw [show (N+1)-(j+1)=N-j by omega,show i+1+j=i+(j+1) by omega]

lemma rightCoeff_shift (c : ℕ → ℝ≥0) (h : ℝ≥0) {N j : ℕ} (hj : j ≤ N)
    (i : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    rightCoeff c h N i ((j:ℝ)*h+t)=rightCoeff c h (N-j) (i+j) t := by
  induction j generalizing N i with
  | zero => simp
  | succ j ih =>
    cases N with
    | zero => omega
    | succ N =>
      have hh : ¬((j+1:ℕ):ℝ)*(h:ℝ)+t<h := by push_cast;nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) h.coe_nonneg]
      rw [rightCoeff,ite_eq_right hh]
      have he : ((j+1:ℕ):ℝ)*(h:ℝ)+t-h=(j:ℝ)*h+t := by push_cast;ring
      rw [he,ih (by omega)]
      rw [show (N+1)-(j+1)=N-j by omega,show i+1+j=i+(j+1) by omega]

lemma finiteFeedback_step {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N j : ℕ} (hj : j < N) {t : ℝ}
    (ht : t ∈ Ico ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h)) (x : ℝ) :
    (finiteFeedback hf hLip c h N 0).f t x =
      (c j:ℝ)*deriv (varianceLogHeat (c j) (((j+1:ℕ):ℝ)*h-t)
        (backwardBoundary c h f N (j+1))) x := by
  let τ := t-(j:ℝ)*h
  have hτ : 0 ≤ τ := sub_nonneg.mpr ht.1
  have hτh : τ < h := by dsimp [τ];have hh := ht.2;push_cast at hh;linarith
  have he : t=(j:ℝ)*h+τ := by dsimp [τ];ring
  change rightCoeff c h N 0 t*deriv (finiteValue c h f N 0 t) x=_
  rw [he,rightCoeff_shift c h hj.le 0 hτ,finiteValue_shift hf hLip c h hj.le 0 hτ]
  have hn : N-j=(N-(j+1))+1 := by omega
  simp only [Nat.zero_add,hn,rightCoeff,ite_eq_left hτh,finiteValue_head f c h (N-(j+1)) j hτh.le]
  have he' : (h:ℝ)-τ=((j+1:ℕ):ℝ)*h-((j:ℝ)*h+τ) := by push_cast;ring
  change (c j:ℝ)*deriv (varianceLogHeat (c j) ((h:ℝ)-τ) (cascade c h f (N-(j+1)) (j+1))) x=_
  rw [he']
  rfl

end ZeroTemperatureSK

end
end

end OAI
