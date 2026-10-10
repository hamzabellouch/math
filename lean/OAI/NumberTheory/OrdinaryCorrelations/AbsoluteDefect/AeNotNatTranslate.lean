import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ForwardSum
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrefixEnergy

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

namespace OrdinaryInitialWidth
open OrdinaryCorrelations OrdinaryLocalAdditive OrdinarySharpWindow Finset Filter MeasureTheory

lemma ae_not_nat_translate (t : ℝ) : ∀ᵐ y : ℝ, ∀ n : ℕ, y+t≠(n:ℝ) := by
  rw [ae_all_iff]
  intro n
  apply ae_iff.mpr
  have he : {y : ℝ | ¬y+t≠(n:ℝ)}={((n:ℝ)-t)} := by
    ext y
    simp only [Set.mem_ofPred_eq,not_not,Set.mem_singleton_iff]
    constructor <;> intro hy <;> linarith
  rw [he]
  exact measure_singleton _

lemma forward_eq_prefix {f : ℕ→ℂ} (α : ℝ) {D y : ℝ} {N : ℕ}
    (hy : 0≤y) (hD : 0≤D) (hN : y+D≤(N:ℝ))
    (hyN : ∀ n : ℕ, y≠(n:ℝ)) (hyDN : ∀ n : ℕ, y+D≠(n:ℝ)) :
    forwardSum f α D y = sharpWindow (Ioc 0 N)
      (fun n=>f n*phase (α*n)) (fun n=>(n:ℝ)) D (y+D) := by
  classical
  have hfbd : ⌊y+D⌋₊≤N := by
    exact_mod_cast (Nat.floor_le (add_nonneg hy hD)).trans hN
  have hsub : Finset.Ioc ⌊y⌋₊ ⌊y+D⌋₊ ⊆ Finset.Ioc 0 N := by
    intro n hn
    obtain ⟨hn1,hn2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega,hn2.trans hfbd⟩
  have hiff (n : ℕ) : n∈Finset.Ioc ⌊y⌋₊ ⌊y+D⌋₊ ↔ y+D-(n:ℝ)∈Set.Ioc 0 D := by
    rw [Finset.mem_Ioc,Nat.floor_lt hy,Nat.le_floor_iff (add_nonneg hy hD)]
    change (y<(n:ℝ) ∧ (n:ℝ)≤y+D) ↔ (0<y+D-n ∧ y+D-n≤D)
    have h1 := hyN n
    have h2 := hyDN n
    constructor
    · rintro ⟨ha,hb⟩
      have hb' : (n:ℝ)<y+D := lt_of_le_of_ne hb (Ne.symm h2)
      constructor <;> linarith
    · rintro ⟨ha,hb⟩
      have hyy : y≤(n:ℝ) := by linarith
      have hyy' := lt_of_le_of_ne hyy h1
      constructor <;> linarith
  unfold forwardSum sharpWindow
  calc
    _ = ∑ n ∈ Ioc ⌊y⌋₊ ⌊y+D⌋₊, (f n*phase (α*n))*(box D (y+D-n):ℂ) := by
      apply sum_congr rfl
      intro n hn
      rw [OrdinarySharpWindow.box,Set.indicator_of_mem ((hiff n).mp hn)]
      simp
    _ = _ := by
      apply sum_subset hsub
      intro n hn hnot
      rw [OrdinarySharpWindow.box,Set.indicator_of_notMem (fun hh=>hnot ((hiff n).mpr hh))]
      simp

lemma forward_integral_le_prefix (f : ℕ→ℂ) (α : ℝ) {D X : ℝ} {N : ℕ}
    (hD : 0≤D) (hX : X+D≤(N:ℝ)) :
    (∫y in Set.Ioc 0 X, ‖forwardSum f α D y‖) ≤
      prefixEnergy (fun n=>f n*phase (α*n)) D N := by
  have he : (∫y in Set.Ioc 0 X, ‖forwardSum f α D y‖) =
      ∫y in Set.Ioc 0 X, ‖sharpWindow (Ioc 0 N) (fun n=>f n*phase (α*n))
        (fun n=>(n:ℝ)) D (y+D)‖ := by
    apply setIntegral_congr_ae measurableSet_Ioc
    filter_upwards [ae_not_nat_translate 0,ae_not_nat_translate D] with y hy hyD
    intro hyX
    congr 1
    apply forward_eq_prefix α hyX.1.le hD (by linarith [hyX.2])
      (by simpa only [add_zero] using hy) hyD
  rw [he]
  calc
    _ ≤ ∫y : ℝ, ‖sharpWindow (Ioc 0 N) (fun n=>f n*phase (α*n))
        (fun n=>(n:ℝ)) D (y+D)‖ :=
      setIntegral_le_integral ((sharpWindow_integrable _ _ _ _).norm.comp_add_right D)
        (ae_of_all _ (fun _=>norm_nonneg _))
    _ = _ := integral_add_right_eq_self
      (fun y : ℝ=>‖sharpWindow (Ioc 0 N) (fun n=>f n*phase (α*n))
        (fun n=>(n:ℝ)) D y‖) D

end OrdinaryInitialWidth

end

end OAI
