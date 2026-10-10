import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AeNotNatTranslate

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
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryTwistWidth
open OrdinaryCorrelations OrdinaryInitialWidth OrdinaryLocalAdditive OrdinarySharpWindow Finset Filter MeasureTheory

lemma forward_integrableOn (f : ℕ→ℂ) (α : ℝ) {D X : ℝ} (hD : 0≤D) :
    IntegrableOn (forwardSum f α D) (Set.Ioc 0 X) := by
  let N : ℕ := ⌈max 0 (X+D)⌉₊
  have hXN : X+D≤(N:ℝ) := (le_max_right _ _).trans (Nat.le_ceil _)
  have hi := ((sharpWindow_integrable (Ioc 0 N) (fun n=>f n*phase (α*n))
    (fun n=>(n:ℝ)) D).comp_add_right D).integrableOn (s:=Set.Ioc 0 X)
  apply hi.congr_fun_ae
  change ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioc 0 X),
    sharpWindow (Ioc 0 N) (fun n=>f n*phase (α*n)) (fun n=>(n:ℝ)) D (y+D)=
      forwardSum f α D y
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [ae_not_nat_translate 0,ae_not_nat_translate D] with y hy hyD
  intro hyX
  exact (forward_eq_prefix α hyX.1.le hD (by linarith [hyX.2])
    (by simpa only [add_zero] using hy) hyD).symm

lemma forwardSum_sub (f g : ℕ→ℂ) (α D y : ℝ) :
    forwardSum (fun n=>f n-g n) α D y=
      forwardSum f α D y-forwardSum g α D y := by
  simp only [forwardSum,sub_mul,sum_sub_distrib]

lemma forward_integral_continuity {f g : ℕ→ℂ} {δ D X : ℝ}
    (hfg : ∀n,‖f n-g n‖≤δ) (hδ : 0≤δ) (hD : 0≤D) (hX : 1≤X) (hDX : D≤X)
    (α : ℝ) :
    (∫y in Set.Ioc 0 X,‖forwardSum f α D y‖) ≤
      (∫y in Set.Ioc 0 X,‖forwardSum g α D y‖)+3*δ*D*X := by
  let N : ℕ := ⌊X+D⌋₊+1
  have hXN : X+D≤(N:ℝ) := by
    dsimp [N];push_cast;exact (Nat.lt_floor_add_one _).le
  have hNX : (N:ℝ)≤3*X := by
    have ht := Nat.floor_le (show 0≤X+D by linarith)
    dsimp [N];push_cast;linarith
  have hs : (∑n∈Ioc 0 N,‖(f n-g n)*phase (α*n)‖)≤δ*N := by
    calc
      _ ≤∑n∈Ioc 0 N,δ := by
        apply sum_le_sum
        intro n _
        simpa only [norm_mul,norm_phase,mul_one] using hfg n
      _ = _ := by simp [mul_comm]
  have hdif := (forward_integral_le_prefix (fun n=>f n-g n) α hD hXN).trans
    ((sharpWindow_l1_mass _ _ _ hD).trans (mul_le_mul_of_nonneg_left hs hD))
  have hf := (forward_integrableOn f α (X:=X) hD).norm
  have hg := (forward_integrableOn g α (X:=X) hD).norm
  have hdiff := (forward_integrableOn (fun n=>f n-g n) α (X:=X) hD).norm
  calc
    _ ≤∫y in Set.Ioc 0 X, ‖forwardSum g α D y‖+‖forwardSum (fun n=>f n-g n) α D y‖ := by
      apply integral_mono hf (hg.add hdiff)
      intro y
      change ‖forwardSum f α D y‖≤‖forwardSum g α D y‖+‖forwardSum (fun n=>f n-g n) α D y‖
      rw [forwardSum_sub]
      have he : forwardSum f α D y = forwardSum g α D y+
        (forwardSum f α D y-forwardSum g α D y) := by abel
      calc
        _ = ‖forwardSum g α D y+(forwardSum f α D y-forwardSum g α D y)‖ := congrArg norm he
        _ ≤ _ := norm_add_le _ _
    _ = (∫y in Set.Ioc 0 X, ‖forwardSum g α D y‖)+
        ∫y in Set.Ioc 0 X, ‖forwardSum (fun n=>f n-g n) α D y‖ := integral_add hg hdiff
    _ ≤_ := by
      apply _root_.add_le_add le_rfl
      have hmul := mul_le_mul_of_nonneg_left hNX (mul_nonneg hδ hD)
      nlinarith only [hdif,hmul]

end OrdinaryTwistWidth

end

end OAI
