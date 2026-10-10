import OAI.Probability.DilutedSpin.PhysicalMarkerControl

namespace OAI

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance overlapDepthAverageDecidableEq (β : Type) :
    DecidableEq β := Classical.decEq β
noncomputable local instance overlapDepthAveragePropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_option (D : (Option α → Fin L) → Prop) (F : (Option α → Fin L) → ℝ) :
    average D F=(FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t =>
      average (fun q => D ((fun i => Option.elim i t q))) (fun q => F ((fun i => Option.elim i t q)))) := by
  rw [average_split none D F]
  apply FiniteLaw.expect_congr
  intro t
  let e : α → {j : Option α // j≠none} := fun i => ⟨some i,by simp⟩
  have he : Function.Injective e := by intro a b hab; exact Option.some_injective _ (congrArg Subtype.val hab)
  have hi (rest : {j : Option α // j≠none} → Fin L) :
      insertCoordinate none t rest=(fun i => Option.elim i t (coordinateProjection e (fun _ => Equiv.refl _) rest)) := by
    funext i
    cases i with
    | none => exact insertCoordinate_self _ _ _
    | some a => exact insertCoordinate_other none t rest (e a)
  unfold average
  simp_rw [hi]
  exact depthLaw_projection e he (fun _ => Equiv.refl _)
    (fun q => if D ((fun i => Option.elim i t q)) then F ((fun i => Option.elim i t q)) else 0)

lemma average_option_product (D : (α → Fin L) → Prop) (E : Fin L → Prop)
    (F : (α → Fin L) → ℝ) :
    average (fun Q : Option α → Fin L => D (fun i => Q (some i)) ∧ E (Q none))
      (fun Q => F (fun i => Q (some i))) =
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t => if E t then 1 else 0) * average D F := by
  rw [average_option]
  have he (t : Fin L) :
      average (fun q : α → Fin L => D q ∧ E t) F=(if E t then 1 else 0)*average D F := by
    by_cases ht : E t
    · simp [ht]
    · simp [ht,average]
  simp only [Option.elim_some,Option.elim_none,he]
  exact (FiniteLaw.expect_mul_right _ _ _)

lemma uniform_interval (r : ℕ) (hr : 2*r<L) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun t => if r<t.val ∧ t.val≤2*r then (1:ℝ) else 0) =
      (r:ℝ)/(L:ℝ) := by
  unfold FiniteLaw.expect FiniteLaw.uniform
  rw [← Finset.mul_sum]
  have he : (Finset.univ.filter (fun t : Fin L => r<t.val ∧ t.val≤2*r)).card=r := by
    have hv : Finset.univ.filter (fun t : Fin L => r<t.val ∧ t.val≤2*r)=
        Finset.Ioc (⟨r,by omega⟩ : Fin L) ⟨2*r,hr⟩ := by ext t; simp [Fin.lt_def,Fin.le_def]
    rw [hv]
    simp
    omega
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,Fintype.card_fin,nsmul_eq_mul,mul_one,he]
  rw [div_eq_mul_inv,mul_comm]

end DilutedSpinGlass.DepthAverage

end

end OAI
