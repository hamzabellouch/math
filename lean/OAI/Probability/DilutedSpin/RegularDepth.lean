import OAI.Probability.DilutedSpin.JointRootLaw
import OAI.Probability.DilutedSpin.SpinRootData

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

theorem fullRoot_variance_eq
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*k+D*n) :
    variance (packRoot F) (fullRootLaw ξ μ ν r s) =
      ∫ h, ∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y,
        (F h k x n y-(∫ h', ∫ k' : ℕ, ∫ x', ∫ n' : ℕ, ∫ y', F h' k' x' n' y'
          ∂rootLaw n' (fun _ => ν) ∂poissonMeasure s ∂rootLaw k' (fun _ => μ)
            ∂poissonMeasure r ∂rootLaw M ξ))^2
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)
          ∂poissonMeasure r ∂rootLaw M ξ := by
  have hk (k : ℕ) : C*k ≤ C+C*(k:ℝ)^2 := by
    have h : (k:ℝ) ≤ 1+(k:ℝ)^2 := by nlinarith [sq_nonneg ((k:ℝ)-(1:ℝ)/2)]
    nlinarith [mul_le_mul_of_nonneg_left h hC]
  have hn (n : ℕ) : D*n ≤ D+D*(n:ℝ)^2 := by
    have h : (n:ℝ) ≤ 1+(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-(1:ℝ)/2)]
    nlinarith [mul_le_mul_of_nonneg_left h hD]
  have hbq h k x n y : |F h k x n y| ≤ (B+C+D)+C*(k:ℝ)^2+D*(n:ℝ)^2 := by
    linarith [hb h k x n y,hk k,hn n]
  have he := integral_fullRootLaw_quadratic ξ μ ν r s hF hbq
  let center := ∫ z, packRoot F z ∂fullRootLaw ξ μ ν r s
  have hsq h k x n y : |(F h k x n y-center)^2| ≤
      3*(|B|+|center|)^2+3*C^2*(k:ℝ)^2+3*D^2*(n:ℝ)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hbd : |F h k x n y-center| ≤ (|B|+|center|)+C*k+D*n := by
      have hh := abs_sub (F h k x n y) center
      linarith [hb h k x n y,le_abs_self B]
    have ha := abs_nonneg (F h k x n y-center)
    have hh : (F h k x n y-center)^2 ≤ ((|B|+|center|)+C*k+D*n)^2 := by
      nlinarith [sq_abs (F h k x n y-center)]
    nlinarith [sq_nonneg ((|B|+|center|)-C*k),sq_nonneg ((|B|+|center|)-D*n),
      sq_nonneg (C*k-D*n)]
  rw [variance_eq_integral (measurable_packRoot hF).aemeasurable]
  change (∫ z, packRoot (fun h k x n y => (F h k x n y-center)^2) z ∂fullRootLaw ξ μ ν r s) = _
  rw [integral_fullRootLaw_quadratic ξ μ ν r s
    (fun k n => ((hF k n).sub measurable_const).pow_const 2) hsq]
  dsimp only [center]
  rw [he]

end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance regularDepthPropDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {L : ℕ} [NeZero L]

noncomputable def normalized (q : Fin L) : ℝ := (q.val:ℝ)/(L:ℝ)

/-- Exactly the separated, interior distinct-coordinate domain of
`decor:average-definition`. Ancestry/order restrictions may further restrict it. -/
def Regular (η : ℝ) (q : α → Fin L) : Prop :=
  (∀ i, η < normalized (q i) ∧ normalized (q i) < 1-η) ∧
  ∀ i j, i ≠ j → η < |normalized (q i)-normalized (q j)|

noncomputable def shiftPerm (s : Bool) : Equiv.Perm (Fin L) :=
  if s then finRotate L else Equiv.refl _

lemma rotate_val_of_room (q : Fin L) (hq : q.val+1 < L) :
    (finRotate L q).val=q.val+1 := by
  cases L with
  | zero => exact q.elim0
  | succ n =>
    rcases q with ⟨v,hv⟩
    change v+1<n+1 at hq
    have hn : v<n := by omega
    exact congrArg Fin.val (finRotate_of_lt hn)

omit [Fintype α] [DecidableEq α] in
lemma regular_room {η : ℝ} (hlarge : 1 < η*(L:ℝ)) {q : α → Fin L}
    (hq : Regular η q) (i : α) : (q i).val+1 < L := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hi := (div_lt_iff₀ hL).mp (hq.1 i).2
  have hh : ((q i).val:ℝ)+1 < (L:ℝ) := by nlinarith
  exact_mod_cast hh

lemma normalized_shift_bounds (s : Bool) (q : Fin L) (hq : q.val+1<L) :
    normalized q ≤ normalized (shiftPerm s q) ∧
    normalized (shiftPerm s q) ≤ normalized q + 1/(L:ℝ) := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  cases s with
  | false =>
    simp only [shiftPerm,Bool.false_eq_true,ite_false,Equiv.refl_apply]
    constructor
    · exact le_rfl
    · linarith [one_div_pos.mpr hL]
  | true =>
    simp only [shiftPerm,ite_true,normalized,rotate_val_of_room q hq,Nat.cast_add,Nat.cast_one]
    constructor
    · exact div_le_div_of_nonneg_right (by linarith) hL.le
    · rw [add_div]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Positive shifts of any subset of retained coordinates are truly +1,
not modular wraparound, and send the regular domain into η/2 regularity.
The fixed numerical threshold is deliberately generous and uniform. -/
theorem regular_shift_restrict {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L:ℝ))
    (e : β → α) (he : Function.Injective e) (s : β → Bool)
    {q : α → Fin L} (hq : Regular η q) :
    Regular (η/2) (coordinateProjection e (fun i => shiftPerm (s i)) q) := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hstep : 1/(L:ℝ)<η/4 := (div_lt_iff₀ hL).mpr (by nlinarith)
  have hb (i : β) := normalized_shift_bounds (s i) (q (e i))
    (regular_room (by linarith : 1<η*(L:ℝ)) hq (e i))
  constructor
  · intro i
    change η/2 < normalized (shiftPerm (s i) (q (e i))) ∧
      normalized (shiftPerm (s i) (q (e i))) < 1-η/2
    have hi := hq.1 (e i)
    constructor <;> linarith [hb i]
  · intro i j hij
    change η/2 < |normalized (shiftPerm (s i) (q (e i)))-
      normalized (shiftPerm (s j) (q (e j)))|
    have hi := hb i
    have hj := hb j
    have hold := hq.2 (e i) (e j) (fun heq => hij (he heq))
    have htri := abs_sub_le (normalized (q (e i)))
      (normalized (shiftPerm (s i) (q (e i)))) (normalized (q (e j)))
    have htri2 := abs_sub_le (normalized (shiftPerm (s i) (q (e i))))
      (normalized (shiftPerm (s j) (q (e j)))) (normalized (q (e j)))
    have hd1 : |normalized (q (e i))-normalized (shiftPerm (s i) (q (e i)))| ≤ 1/(L:ℝ) :=
      abs_le.mpr ⟨by linarith,by linarith⟩
    have hd2 : |normalized (shiftPerm (s j) (q (e j)))-normalized (q (e j))| ≤ 1/(L:ℝ) :=
      abs_le.mpr ⟨by linarith,by linarith⟩
    linarith

/-- Concrete regular-depth fiber estimate, including arbitrary unused
coordinates and independently shifted retained depths. -/
theorem regular_fiber_fourthRoot_bound {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L:ℝ))
    (e : β → α) (he : Function.Injective e) (s : β → Bool)
    (D : (α → Fin L) → Prop) (hD : ∀ q, D q → Regular η q)
    (F : (β → Fin L) → ℝ) (hF : ∀ q, 0≤F q) :
    average D (fun q => Real.sqrt (Real.sqrt
      (F (coordinateProjection e (fun i => shiftPerm (s i)) q)))) ≤
      Real.sqrt (Real.sqrt (average (Regular (η/2)) F)) := by
  exact fiber_fourthRoot_bound e he (fun i => shiftPerm (s i)) D (Regular (η/2))
    (fun q hq => regular_shift_restrict hη hlarge e he s (hD q hq)) F hF

end DilutedSpinGlass.DepthAverage
end

end

end OAI
