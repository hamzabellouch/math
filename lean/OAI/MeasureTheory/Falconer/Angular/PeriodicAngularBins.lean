import OAI.MeasureTheory.Falconer.Angular.AngularBinSelection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set
open scoped ContDiff Topology

noncomputable def periodicAngularBin (n j : ℕ) (θ : ℝ) : ℝ :=
  angularBinSelection (fun k => (k % (n : ℤ)).toNat = j) ((n : ℝ)/(2*Real.pi)*θ)

theorem angularBinSelection_periodic (p : ℤ → Prop) (n : ℤ)
    (hp : ∀ k, p (k+n) ↔ p k) : Function.Periodic (angularBinSelection p) (n : ℝ) := by
  intro t
  unfold angularBinSelection
  rw [← (Equiv.addRight n).tsum_eq]
  apply tsum_congr
  intro k
  change (if p (k+n) then angularBinKernel (t+(n:ℝ)-(k+n : ℤ)) else 0) = _
  rw [show t+(n:ℝ)-(k+n : ℤ) = t-k by push_cast; ring]
  simp only [hp]

theorem periodicAngularBin_periodic (n j : ℕ) :
    Function.Periodic (periodicAngularBin n j) (2*Real.pi) := by
  have hp := angularBinSelection_periodic (fun k => (k % (n : ℤ)).toNat = j) (n : ℤ)
    (fun k => by simp)
  intro θ
  unfold periodicAngularBin
  convert hp ((n : ℝ)/(2*Real.pi)*θ) using 1
  congr 1
  push_cast
  field_simp

theorem periodicAngularBin_contDiff (n j : ℕ) : ContDiff ℝ ∞ (periodicAngularBin n j) :=
  (angularBinSelection_contDiff _).comp (contDiff_const.mul contDiff_id)

theorem periodicAngularBin_bounds (n j : ℕ) (θ : ℝ) :
    0 ≤ periodicAngularBin n j θ ∧ periodicAngularBin n j θ ≤ 1 :=
  angularBinSelection_bounds _ _

theorem angularBinResidue_lt {n : ℕ} (hn : 0 < n) (k : ℤ) :
    (k % (n : ℤ)).toNat < n := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have h0 := Int.emod_nonneg k hn'.ne'
  have h1 := Int.emod_lt_of_pos k hn'
  have he := Int.toNat_of_nonneg h0
  have ht : ((k % (n : ℤ)).toNat : ℤ) < n := by rwa [he]
  exact_mod_cast ht

theorem periodicAngularBin_partition {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    ∑ j ∈ Finset.range n, periodicAngularBin n j θ = 1 := by
  have hsum (k : ℤ) (w : ℝ) :
      (∑ j ∈ Finset.range n, if (k % (n : ℤ)).toNat = j then w else 0) = w := by
    calc
      _ = if (k % (n : ℤ)).toNat ∈ Finset.range n then w else 0 :=
        Finset.sum_ite_eq _ _ (fun _ => w)
      _ = _ := by simp [angularBinResidue_lt hn]
  unfold periodicAngularBin
  simp_rw [angularBinSelection_two_terms]
  rw [Finset.sum_add_distrib]
  let t := (n : ℝ)/(2*Real.pi)*θ
  convert (congrArg₂ (fun a b : ℝ => a+b)
    (hsum ⌊t⌋ (angularBinKernel (t-(⌊t⌋ : ℤ))))
    (hsum (⌊t⌋+1) (angularBinKernel (t-(⌊t⌋+1 : ℤ))))).trans
      (angularBinKernel_floor_partition t) using 1
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> split_ifs <;> rfl

theorem periodicAngularBin_nonzero_labels (n : ℕ) (θ : ℝ) :
    {j ∈ Finset.range n | periodicAngularBin n j θ ≠ 0} ⊆
      {(⌊(n : ℝ)/(2*Real.pi)*θ⌋ % (n : ℤ)).toNat,
       ((⌊(n : ℝ)/(2*Real.pi)*θ⌋+1) % (n : ℤ)).toNat} := by
  intro j hj
  have hj := (Finset.mem_filter.mp hj).2
  by_contra h
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact hj (by simp [periodicAngularBin, angularBinSelection_two_terms, Ne.symm h.1, Ne.symm h.2])

theorem periodicAngularBin_overlap (n : ℕ) (θ : ℝ) :
    {j ∈ Finset.range n | periodicAngularBin n j θ ≠ 0}.card ≤ 2 := by
  have hp (a b : ℕ) : ({a,b} : Finset ℕ).card ≤ 2 := by
    by_cases h : a = b <;> simp [h]
  exact (Finset.card_le_card (periodicAngularBin_nonzero_labels n θ)).trans
    (hp _ _)

theorem periodicAngularBin_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n k θ,
      ‖iteratedDeriv j (periodicAngularBin n k) θ‖ ≤ C * ((n : ℝ)/(2*Real.pi))^j := by
  obtain ⟨C,hC0,hC⟩ := angularBinSelection_derivative_bound j
  refine ⟨C,hC0,?_⟩
  intro n k θ
  unfold periodicAngularBin
  rw [iteratedDeriv_comp_const_mul ((angularBinSelection_contDiff _).of_le
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)/(2*Real.pi))]
  simpa only [mul_comm, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left (hC _ _) (by positivity :
    0 ≤ ((n : ℝ)/(2*Real.pi))^j)

end PlanarFalconer

end OAI
