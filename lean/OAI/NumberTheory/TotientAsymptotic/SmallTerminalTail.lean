import OAI.NumberTheory.TotientAsymptotic.SmallTerminalCount
import OAI.NumberTheory.TotientAsymptotic.GaussianTail

namespace OAI

/-! Summing the bounded-terminal classes with the same Gaussian exponent. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem small_terminal_tail_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Ψ : ℕ,∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧ x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧
      (v:ℝ) ≤ x ∧ 2 < fordPrimeCoordinate (n v) 0 ∧
      fordPrimeCoordinate (n v) (m x-Ψ) ≤ 2 ∧
      (∀ i ≤ m x-Ψ,fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
        xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i))) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  classical
  obtain ⟨A,hA,hcount⟩ := small_terminal_row_count
  let q : ℝ := Real.exp (-1/4:ℝ)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨A/(1-q),div_pos hA (sub_pos.mpr hq),?_⟩
  filter_upwards [hcount,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro Ψ Q n hQ
  let I := Finset.Icc 1 (m x-Ψ)
  let R (j : ℕ) := Q.filter (fun v => 2 < fordPrimeCoordinate (n v) (j-1) ∧
    fordPrimeCoordinate (n v) j ≤ 2)
  have hcover : Q ⊆ I.biUnion R := by
    intro v hv
    obtain ⟨_,_,_,_,hhead,htail,_⟩ := hQ v hv
    obtain ⟨j,hj,hjL,hprev,hcur⟩ := first_small_terminal_exists hhead htail
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_Icc.mpr ⟨hj,hjL⟩,
      Finset.mem_filter.mpr ⟨hv,hprev,hcur⟩⟩
  have hcard : (Q.card:ℝ) ≤ ∑ j ∈ I,((R j).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrow (j : ℕ) (hj : j ∈ I) : (R j).card ≤
      A*(x/Real.log x)*G x (m x)*Real.exp (-((m x-j:ℕ):ℝ)^2/4) := by
    obtain ⟨hj,hjL⟩ := Finset.mem_Icc.mp hj
    apply hx j hj (hjL.trans (Nat.sub_le _ _)) (R j) n
    intro v hv
    obtain ⟨hv,hprev,hcur⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hlarge,hvx,_,_,hrows⟩ := hQ v hv
    exact ⟨hn,hφ,hlarge,hvx,hprev,hcur,fun i hi => hrows i (by omega)⟩
  have hinj : Set.InjOn (fun j => m x-j) ↑I := by
    intro j hj l hl he
    have hjm := (Finset.mem_Icc.mp hj).2
    have hlm := (Finset.mem_Icc.mp hl).2
    change m x-j=m x-l at he
    omega
  have hsum : (∑ j ∈ I,Real.exp (-((m x-j:ℕ):ℝ)^2/4)) ≤
      Real.exp (-(Ψ:ℝ)^2/4)/(1-q) := by
    have he : (∑ k ∈ I.image (fun j => m x-j),Real.exp (-(k:ℝ)^2/4)) =
        ∑ j ∈ I,Real.exp (-((m x-j:ℕ):ℝ)^2/4) := Finset.sum_image hinj
    rw [← he]
    apply finite_gaussian_tail
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have hjm := (Finset.mem_Icc.mp hj).2
    have hj1 := (Finset.mem_Icc.mp hj).1
    omega
  have hfac : 0 ≤ A*(x/Real.log x)*G x (m x) :=
    mul_nonneg (mul_nonneg hA.le (div_nonneg (by linarith) (Real.log_pos hx1).le)) (G_pos hB _).le
  calc
    _ ≤ ∑ j ∈ I,((R j).card:ℝ) := hcard
    _ ≤ ∑ j ∈ I,A*(x/Real.log x)*G x (m x)*Real.exp (-((m x-j:ℕ):ℝ)^2/4) :=
      Finset.sum_le_sum hrow
    _ = (A*(x/Real.log x)*G x (m x))*(∑ j ∈ I,Real.exp (-((m x-j:ℕ):ℝ)^2/4)) := by
      rw [Finset.mul_sum]
    _ ≤ (A*(x/Real.log x)*G x (m x))*(Real.exp (-(Ψ:ℝ)^2/4)/(1-q)) :=
      mul_le_mul_of_nonneg_left hsum hfac
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
