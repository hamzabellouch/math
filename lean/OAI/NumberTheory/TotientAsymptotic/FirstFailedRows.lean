import OAI.NumberTheory.TotientAsymptotic.FirstFailedRowBound
import OAI.NumberTheory.TotientAsymptotic.GaussianTail

namespace OAI

/-! Summing the first-failed-row classes without losing the Gaussian exponent. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def fordRowHolds (x : ℝ) (n i : ℕ) : Prop :=
  fordRowSum (m x) (fordPrimeCoordinate n) i ≤
    xi x i*(if i=0 then B x else fordPrimeCoordinate n i)

def FirstFailedRowAt (x : ℝ) (n j : ℕ) : Prop :=
  (∀ i < j,fordRowHolds x n i) ∧ ¬fordRowHolds x n j

lemma first_failed_row_exists {x : ℝ} {n J : ℕ}
    (h0 : fordRowHolds x n 0)
    (hfail : ∃ j, j ≤ J ∧ ¬fordRowHolds x n j) :
    ∃ j, 1 ≤ j ∧ j ≤ J ∧ FirstFailedRowAt x n j := by
  classical
  let hex : ∃ j, ¬fordRowHolds x n j := by
    obtain ⟨j,_,hj⟩ := hfail
    exact ⟨j,hj⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  change ¬fordRowHolds x n j at hj
  have hj0 : j≠0 := by
    intro he
    exact hj (by simpa only [he] using h0)
  refine ⟨j,by omega,?_,?_,hj⟩
  · obtain ⟨l,hl,he⟩ := hfail
    exact (Nat.find_min' hex he).trans hl
  · intro i hi
    exact Classical.byContradiction (fun h => Nat.find_min hex hi h)

theorem first_failed_rows_tail_bound : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ Ψ : ℕ, ∀ Q : Finset ℕ, ∀ n : ℕ → ℕ,
      (∀ v ∈ Q, 0 < n v ∧ (n v).totient=v ∧
        x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
        ∃ j,1 ≤ j ∧ j ≤ m x-Ψ ∧ FirstFailedRowAt x (n v) j) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  classical
  obtain ⟨A,hA,hcount⟩ := first_failed_row_bound
  let q : ℝ := Real.exp (-1/4:ℝ)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨A/(1-q),div_pos hA (sub_pos.mpr hq),?_⟩
  filter_upwards [hcount,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro Ψ Q n hQ
  let I := Finset.Icc 1 (m x-Ψ)
  let R (j : ℕ) := Q.filter (fun v => FirstFailedRowAt x (n v) j)
  have hcover : Q ⊆ I.biUnion R := by
    intro v hv
    obtain ⟨_,_,_,_,j,hj,hjm,hfirst⟩ := hQ v hv
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_Icc.mpr ⟨hj,hjm⟩,
      Finset.mem_filter.mpr ⟨hv,hfirst⟩⟩
  have hcard : (Q.card:ℝ) ≤ ∑ j ∈ I,((R j).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrow (j : ℕ) (hj : j ∈ I) : (R j).card ≤
      A*(x/Real.log x)*G x (m x)*Real.exp (-((m x-j:ℕ):ℝ)^2/4) := by
    obtain ⟨hj,hjm⟩ := Finset.mem_Icc.mp hj
    apply hx j hj (hjm.trans (Nat.sub_le _ _)) (R j) n
    intro v hv
    obtain ⟨hv,hfirst⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hhead,hvx,_⟩ := hQ v hv
    refine ⟨hn,hφ,hhead,hvx,hfirst.1,?_⟩
    have hh := not_le.mp hfirst.2
    simpa only [fordRowHolds,ite_eq_right (by omega : j≠0)] using hh
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
