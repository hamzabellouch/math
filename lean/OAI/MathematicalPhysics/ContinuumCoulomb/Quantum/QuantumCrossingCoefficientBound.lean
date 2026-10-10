import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathPolynomialBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalCrossing

namespace OAI

/-! Polynomial coefficient envelopes for the actual rational crossing layer.
The bounds include its scalar counterterms. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaCrossingWeight_abs_le {J K L : ℝ} (hL : 1 ≤ L)
    (hJ : |J| ≤ L) (hK : |K| ≤ L) (a : Fin 4) :
    |qmaCrossingWeight J K a| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ L^2 := by nlinarith
  have hprod := mul_le_mul hJ hK (abs_nonneg K) hL0
  fin_cases a <;> simp [qmaCrossingWeight,abs_mul] <;> nlinarith

theorem qmaCrossingAmplitude_abs_le {R J K L : ℝ} (hL : 1 ≤ L)
    (hR : |R| ≤ L) (hJ : |J| ≤ L) (hK : |K| ≤ L) (a : Fin 4) :
    |qmaCrossingAmplitude R J K a| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ L^2 := by nlinarith
  have hprodJ := mul_le_mul hR hJ (abs_nonneg J) hL0
  have hprodK := mul_le_mul hR hK (abs_nonneg K) hL0
  fin_cases a <;> simp [qmaCrossingAmplitude,abs_mul] <;> nlinarith

theorem qmaCrossingOffset_abs_le {J K L : ℝ} (hL : 1 ≤ L)
    (hJ : |J| ≤ L) (hK : |K| ≤ L) :
    |qmaCrossingOffset J K| ≤ 8*L^2 := by
  have hJ2 : J^2 ≤ L^2 := by nlinarith [sq_abs J,mul_self_le_mul_self (abs_nonneg J) hJ]
  have hK2 : K^2 ≤ L^2 := by nlinarith [sq_abs K,mul_self_le_mul_self (abs_nonneg K) hK]
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  rw [abs_of_nonneg (by unfold qmaCrossingOffset; positivity)]
  unfold qmaCrossingOffset
  linarith

def qmaCrossingBudget (m r L : ℝ) : ℝ :=
  3*m*L+L+6*r*(1+2*L)+12*r*(1+2*L)^2+1

def qmaCrossingRadiusBound (m r L T : ℝ) : ℝ :=
  L+16*(qmaCrossingBudget m r L)^3*T+4*qmaCrossingBudget m r L+1

def qmaCrossingCoefficientBound (m r L T : ℝ) : ℝ :=
  1+L+(11*r+2)*(qmaCrossingRadiusBound m r L T)^2

namespace QMARationalCrossingLayer
variable {r : ℕ} (C : QMARationalCrossingLayer r)

theorem scale_abs_bound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card C.base.Edge:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : C.base.CoefficientBound L)
    (hJ : ∀ i, |(C.J i:ℝ)| ≤ L) (hK : ∀ i, |(C.K i:ℝ)| ≤ L) :
    |(C.scale N:ℝ)| ≤ qmaCrossingRadiusBound m r L T := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ (N:ℝ) := by exact_mod_cast hN
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hret : (∑ e, |(C.base.weight e:ℝ)|) ≤ m*L := by
    calc
      _ ≤ ∑ _e : C.base.Edge, L := Finset.sum_le_sum (fun e _ => hc.2 e)
      _ = (Fintype.card C.base.Edge:ℝ)*L := by simp
      _ ≤ m*L := mul_le_mul_of_nonneg_right hm hL0
  have ha : (∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)) ≤ r*(1+2*L) := by
    calc
      _ ≤ ∑ _i : Fin r, (1+2*L) := Finset.sum_le_sum (fun i _ => by linarith [hJ i,hK i])
      _ = (r:ℝ)*(1+2*L) := by simp [mul_add]
  have hd : (∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)^2) ≤ r*(1+2*L)^2 := by
    calc
      _ ≤ ∑ _i : Fin r, (1+2*L)^2 := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (by positivity) (by linarith [hJ i,hK i]) 2)
      _ = (r:ℝ)*(1+2*L)^2 := by simp
  let A := 6*∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)
  let D := 3*(∑ e, |(C.base.weight e:ℝ)|)+|(C.base.constant:ℝ)|+
    12*∑ i, (1+|(C.J i:ℝ)|+|(C.K i:ℝ)|)^2
  have hAD0 : 0 ≤ A+D+1 := by dsimp [A,D]; positivity
  have hAD : A+D+1 ≤ qmaCrossingBudget m r L := by
    dsimp [A,D,qmaCrossingBudget]
    linarith [hc.1]
  have hcube := pow_le_pow_left₀ hAD0 hAD 3
  have hnT : (N:ℝ) ≤ T := by simpa only [abs_of_nonneg hn0] using hT
  have hprod := mul_le_mul hcube hnT hn0 (pow_nonneg (hAD0.trans hAD) 3)
  rw [C.scale_cast]
  change |16*(A+D+1)^3*(N:ℝ)+4*(A+D+1)+1| ≤ _
  rw [abs_of_nonneg (by positivity)]
  dsimp [qmaCrossingRadiusBound]
  nlinarith

theorem output_weight_abs_le (N : ℚ) {L : ℝ} (hL : 1 ≤ L)
    (hR : |(C.scale N:ℝ)| ≤ L) (hw : ∀ e, |(C.base.weight e:ℝ)| ≤ L)
    (hJ : ∀ i, |(C.J i:ℝ)| ≤ L) (hK : ∀ i, |(C.K i:ℝ)| ≤ L)
    (e : (C.output N).Edge) : |((C.output N).weight e:ℝ)| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ L^2 := by nlinarith
  rcases e with (e | ⟨i,a⟩) | (i | ⟨i,a⟩)
  · exact (hw e).trans (by nlinarith)
  · change |(QuantumRoutingCode.coefficients (C.scale N,C.J i,C.K i) ⟨a.val+5,by omega⟩:ℝ)| ≤ _
    rw [QuantumRoutingCode.coefficients_perimeter]
    exact qmaCrossingWeight_abs_le hL (hJ i) (hK i) a
  · change |(((C.scale N)^2:ℚ):ℝ)| ≤ _
    push_cast
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (C.scale N:ℝ),mul_self_le_mul_self (abs_nonneg _) hR]
  · change |(QuantumRoutingCode.coefficients (C.scale N,C.J i,C.K i) ⟨a.val+1,by omega⟩:ℝ)| ≤ _
    rw [QuantumRoutingCode.coefficients_spoke]
    exact qmaCrossingAmplitude_abs_le hL hR (hJ i) (hK i) a

theorem output_constant_abs_le (N : ℚ) {L : ℝ} (hL : 1 ≤ L)
    (hR : |(C.scale N:ℝ)| ≤ L) (hJ : ∀ i, |(C.J i:ℝ)| ≤ L)
    (hK : ∀ i, |(C.K i:ℝ)| ≤ L) :
    |((C.output N).constant:ℝ)| ≤ |(C.base.constant:ℝ)|+11*(r:ℝ)*L^2 := by
  have hR2 : (C.scale N:ℝ)^2 ≤ L^2 := by
    nlinarith [sq_abs (C.scale N:ℝ),mul_self_le_mul_self (abs_nonneg _) hR]
  have hs : |∑ i, qmaCrossingOffset (C.J i:ℝ) (C.K i:ℝ)| ≤ (r:ℝ)*(8*L^2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _i : Fin r, 8*L^2 := Finset.sum_le_sum (fun i _ =>
        qmaCrossingOffset_abs_le hL (hJ i) (hK i))
      _ = _ := by simp
  have ha := abs_add_le (C.base.constant:ℝ) (∑ i, qmaCrossingOffset (C.J i:ℝ) (C.K i:ℝ))
  have hb := abs_add_le ((C.base.constant:ℝ)+∑ i, qmaCrossingOffset (C.J i:ℝ) (C.K i:ℝ))
    (3*(r:ℝ)*(C.scale N:ℝ)^2)
  rw [abs_of_nonneg (by positivity : 0 ≤ 3*(r:ℝ)*(C.scale N:ℝ)^2)] at hb
  change |((((C.base.constant+∑ i, (3/2+3*(C.J i)^2+3*(C.K i)^2))+
    3*(r:ℚ)*(C.scale N)^2):ℚ):ℝ)| ≤ _
  push_cast
  change |((C.base.constant:ℝ)+∑ i, qmaCrossingOffset (C.J i:ℝ) (C.K i:ℝ))+
    3*(r:ℝ)*(C.scale N:ℝ)^2| ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hR2 (by positivity : 0 ≤ (r:ℝ))]

theorem output_coefficientBound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card C.base.Edge:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : C.base.CoefficientBound L)
    (hJ : ∀ i, |(C.J i:ℝ)| ≤ L) (hK : ∀ i, |(C.K i:ℝ)| ≤ L) :
    (C.output N).CoefficientBound (qmaCrossingCoefficientBound m r L T) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hbudget : 0 ≤ qmaCrossingBudget m r L := by unfold qmaCrossingBudget; positivity
  have hrad : L ≤ qmaCrossingRadiusBound m r L T := by
    unfold qmaCrossingRadiusBound
    have h : 0 ≤ 16*(qmaCrossingBudget m r L)^3*T := by positivity
    linarith
  have hr1 : 1 ≤ qmaCrossingRadiusBound m r L T := hL.trans hrad
  have hr := C.scale_abs_bound hN hm hL hT hc hJ hK
  have hj : ∀ i, |(C.J i:ℝ)| ≤ qmaCrossingRadiusBound m r L T := fun i => (hJ i).trans hrad
  have hk : ∀ i, |(C.K i:ℝ)| ≤ qmaCrossingRadiusBound m r L T := fun i => (hK i).trans hrad
  constructor
  · have h := C.output_constant_abs_le N hr1 hr hj hk
    unfold qmaCrossingCoefficientBound
    nlinarith [hc.1,sq_nonneg (qmaCrossingRadiusBound m r L T)]
  · intro e
    have h := C.output_weight_abs_le N hr1 hr (fun e => (hc.2 e).trans hrad) hj hk e
    unfold qmaCrossingCoefficientBound
    nlinarith [sq_nonneg (qmaCrossingRadiusBound m r L T),
      mul_nonneg (Nat.cast_nonneg r : (0:ℝ) ≤ r) (sq_nonneg (qmaCrossingRadiusBound m r L T))]

end QMARationalCrossingLayer
end ContinuumCoulomb

end

end OAI
