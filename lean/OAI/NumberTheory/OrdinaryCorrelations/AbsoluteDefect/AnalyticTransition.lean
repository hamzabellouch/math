import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinQ
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Threshold

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryChainScales
open Finset OrdinaryNarrowGrid OrdinaryExponentialBudgets

noncomputable def analyticTransition (A : ℝ) (k : ℕ) (V W : ℝ) : ℝ :=
  (W^2/V^(2*k))*(A*(2+((k:ℝ)+Real.log 2)^2)*(2:ℝ)^k*(k.factorial:ℝ)*Real.exp ((k:ℝ)+Real.exp 1-1))

lemma card_exp {B H s j : ℕ} (hB : 2*H+s+30≤B) :
    ((grid (binQ B H s j) (binStart B H s j) (binWidth B s j)).card:ℝ)≤
      Real.exp (2*(mesh B H s j:ℝ)) := by
  have hh := bin_card_bound (j:=j) hB
  have hr : ((grid (binQ B H s j) (binStart B H s j) (binWidth B s j)).card:ℝ)≤(2:ℝ)^(2*mesh B H s j) := by exact_mod_cast hh
  apply hr.trans
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using two_pow_exp (2*mesh B H s j)

lemma double_sum_bound {α β : Type*} (I : Finset α) (J : Finset β)
    (cost : α → β → ℝ) {c : ℝ} (hcost : ∀i∈I,∀a∈J,cost i a≤c) :
    (I.card:ℝ)*(∑i∈I,∑a∈J,cost i a)≤(I.card:ℝ)^2*(J.card:ℝ)*c := by
  calc
    _ ≤ (I.card:ℝ)*(∑i∈I,∑a∈J,c) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact sum_le_sum (fun i hi => sum_le_sum (fun a ha => hcost i hi a ha))
    _ = _ := by simp; ring

attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier

lemma transition_total {A : ℝ} (hA0 : 0≤A) {B H s j K : ℕ}
    (hA : A+Real.exp 1+10≤(2:ℝ)^K)
    (hB : H+4*s+K+70≤B) (hB' : 2*H+s+30≤B) :
    ((grid (binQ B H s (j+1)) (binStart B H s (j+1)) (binWidth B s (j+1))).card:ℝ)*
      ∑i∈grid (binQ B H s (j+1)) (binStart B H s (j+1)) (binWidth B s (j+1)),
      ∑a∈grid (binQ B H s j) (binStart B H s j) (binWidth B s j),
        analyticTransition A (amplifier (binLog B H s j a) (binLog B H s (j+1) i))
          (threshold H j (binLog B H s j a)) (threshold H (j+1) (binLog B H s (j+1) i))
        ≤ Real.exp (-993*(mesh B H s (j+1):ℝ)) := by
  have hB0 : H+10≤B := by omega
  have hh := double_sum_bound
    (grid (binQ B H s (j+1)) (binStart B H s (j+1)) (binWidth B s (j+1)))
    (grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
    (fun i a => analyticTransition A (amplifier (binLog B H s j a) (binLog B H s (j+1) i))
      (threshold H j (binLog B H s j a)) (threshold H (j+1) (binLog B H s (j+1) i)))
    (c:=Real.exp (-999*(mesh B H s (j+1):ℝ)))
    (fun i hi a ha => transition_saving (B:=B) (H:=H) (s:=s) (j:=j) (K:=K) hA0 hA hB
      (bin_log_range (B:=B) (H:=H) (s:=s) (j:=j) hB0 ha).1 (bin_log_range (B:=B) (H:=H) (s:=s) (j:=j) hB0 ha).2.le
      (bin_log_range (B:=B) (H:=H) (s:=s) (j:=j+1) hB0 hi).1 (bin_log_range (B:=B) (H:=H) (s:=s) (j:=j+1) hB0 hi).2.le)
  apply hh.trans
  have hi := card_exp (j:=j+1) hB'
  have ha : ((grid (binQ B H s j) (binStart B H s j) (binWidth B s j)).card:ℝ)≤
      Real.exp (2*(mesh B H s (j+1):ℝ)) := by
    apply (card_exp (j:=j) hB').trans
    apply Real.exp_le_exp.mpr
    have hm : (mesh B H s j:ℝ)≤(mesh B H s (j+1):ℝ) := by exact_mod_cast mesh_mono B H s (show j≤j+1 by omega)
    linarith only [hm]
  calc
    _ ≤ (Real.exp (2*(mesh B H s (j+1):ℝ)))^2*Real.exp (2*(mesh B H s (j+1):ℝ))*
        Real.exp (-999*(mesh B H s (j+1):ℝ)) := by gcongr
    _ = _ := by rw [←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]; congr 1; norm_num; ring

end OrdinaryChainScales

end

end OAI
