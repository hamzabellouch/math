import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MachineHalting
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveGluing

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Recorder Coding BalancedTransport.Geometry
open scoped Classical

lemma computable_rationalWord {S : Type*} [Primcodable S] [Fintype S] [Inhabited S]
    {B : ℕ} (digit : S → Fin B) : Computable (Coding.rationalWord digit) := by
  have h : Computable (fun w : List S => w.reverse.foldl
      (fun q a => (B : ℚ)⁻¹ * ((digit a : ℚ) + q)) 0) :=
    computable_foldl Primrec.list_reverse.to_comp (Computable.const 0)
      (computable_rat_mul.comp (Computable.const ((B : ℚ)⁻¹))
        (computable_rat_add.comp
          ((Primrec.dom_finite (fun a : S => (digit a : ℚ))).to_comp.comp
            (Computable.snd.comp Computable.snd))
          (Computable.fst.comp Computable.snd))).to₂
  apply h.of_eq
  intro w
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [List.reverse_cons,List.foldl_append,List.foldl_cons,
      List.foldl_nil, Coding.rationalWord] using
      (congrArg (fun q => (B : ℚ)⁻¹ * ((digit a : ℚ) + q)) ih)

lemma computable_rationalTailCode {S : Type*} [Primcodable S] [Fintype S] [Inhabited S]
    {B : ℕ} (digit : S → Fin B) (a : S) :
    Computable (fun w => Coding.rationalTailCode digit w a) :=
  computable_rat_add.comp (computable_rationalWord digit)
    (computable_rat_mul.comp
      (computable_rat_pow.comp (Computable.const ((B : ℚ)⁻¹)) Computable.list_length)
      (Computable.const ((digit a : ℚ) / ((B : ℚ) - 1))))

lemma computable_rationalInitial (N : FiniteMachine) :
    Computable (Recorder.Checkpoint.rationalInitial N.normalized (some N.initial)) := by
  let S := Recorder.Letter (Option (Fin (N.states+1))) (Fin (N.symbols+1))
  let : Primcodable S := Primcodable.ofEquiv (Fin (Fintype.card S)) (Fintype.equivFin S)
  let : Inhabited S := ⟨.boundary⟩
  have hwork : Primrec (fun a : Fin (N.symbols+1) => (Letter.work a : S)) := Primrec.dom_finite _
  have hh : Computable (fun w : Input N => w.headD N.blank) := by
    exact (Primrec.option_getD.comp Primrec.list_head? (Primrec.const N.blank)).to_comp.of_eq
      (fun w => by cases w <;> rfl)
  have hw : Computable (fun w : Input N =>
      (Letter.work (w.headD N.blank) : S) :: (w.tail.map Letter.work ++ [Letter.boundary])) :=
    Primrec.list_cons.to_comp.comp (hwork.to_comp.comp hh)
      (Primrec.list_append.to_comp.comp
        ((Primrec.list_map Primrec.list_tail (hwork.comp Primrec.snd).to₂).to_comp)
        (Computable.const [Letter.boundary]))
  apply computable_fin_lam
  intro i
  fin_cases i
  · exact Computable.const _
  · exact (computable_rationalTailCode (Recorder.digit (Q := Option (Fin (N.states+1)))
      (Γ := Fin (N.symbols+1))) (Letter.work N.blank)).comp hw
  · exact Computable.const _

lemma rationalInitial_bounded (N : FiniteMachine) :
    ∃ C : ℕ, ∀ w : Input N, ∀ i,
      |(Recorder.Checkpoint.rationalInitial N.normalized (some N.initial) w i : ℝ)| ≤ C := by
  let k := Recorder.placement N.normalized (.ready (some N.initial))
  refine ⟨4*k+1, ?_⟩
  intro w i
  have he := congrFun (Recorder.Checkpoint.rationalInitial_cast N.normalized (some N.initial) w) i
  change (Recorder.Checkpoint.rationalInitial N.normalized (some N.initial) w i : ℝ) = _ at he
  rw [he]
  change |Coding.origin k i + Coding.stream Recorder.digit _| ≤ _
  have hh := Coding.stream_mem_unit Recorder.digit
    (((Recorder.Checkpoint.initial N.normalized (some N.initial) w).expand N.normalized).stacks i)
  have ho : 0 ≤ Coding.origin k i ∧ Coding.origin k i ≤ 4*(k : ℝ) := by
    fin_cases i <;> dsimp [Coding.origin] <;> constructor <;>
      first | positivity | exact le_rfl
  rw [abs_of_nonneg (add_nonneg ho.1 hh.1)]
  push_cast
  linarith [hh.2, ho.2]

lemma fixedLabel_bound (i : Fin 3) : |fixedLabel i| ≤ (4 : ℝ) := by
  fin_cases i <;> norm_num [fixedLabel]

lemma loadingSupport_ball {z : Space} {C : ℕ} (hz : ∀i, |z i| ≤ C) :
    loadingSupport z 1 ⊆ Metric.closedBall (0 : Space) (C+6 : ℕ) := by
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_le]
  have hh := (mem_closedEnlargement _ _ _ x).mp hx i
  have h₀ := (abs_le.mp (fixedLabel_bound i))
  have hz' := abs_le.mp (hz i)
  have hlo : -(C : ℝ)-4 ≤ min (fixedLabel i) (z i) := le_min (by linarith) (by linarith)
  have hhi : max (fixedLabel i) (z i) ≤ (C : ℝ)+4 := max_le (by linarith) (by linarith)
  push_cast
  constructor <;> linarith [hh.1,hh.2]

end BalancedTransport.Effectivity
end

end OAI
