import OAI.MeasureTheory.Falconer.Angular.PeriodicAngularBins

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open scoped ContDiff Topology

theorem periodicAngularBin_sum (n : ℕ) (S : Finset ℕ) :
    (fun θ => ∑ j ∈ S, periodicAngularBin n j θ) =
      fun θ => angularBinSelection (fun k => (k % (n : ℤ)).toNat ∈ S)
        ((n : ℝ)/(2*Real.pi)*θ) := by
  funext θ
  have hsum (q : ℕ) (w : ℝ) :
      (∑ j ∈ S, if q = j then w else 0) = if q ∈ S then w else 0 :=
    Finset.sum_ite_eq _ _ (fun _ => w)
  simp only [periodicAngularBin, angularBinSelection_two_terms, Finset.sum_add_distrib]
  let t := (n : ℝ)/(2*Real.pi)*θ
  convert congrArg₂ (fun a b : ℝ => a+b)
    (hsum (⌊t⌋ % (n : ℤ)).toNat (angularBinKernel (t-(⌊t⌋ : ℤ))))
    (hsum ((⌊t⌋+1) % (n : ℤ)).toNat (angularBinKernel (t-(⌊t⌋+1 : ℤ)))) using 1
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> split_ifs <;> rfl
  congr 1 <;> split_ifs <;> rfl

theorem selectedAngularBins_bounds (n : ℕ) (S : Finset ℕ) (θ : ℝ) :
    0 ≤ ∑ j ∈ S, periodicAngularBin n j θ ∧
      (∑ j ∈ S, periodicAngularBin n j θ) ≤ 1 := by
  have he := congrFun (periodicAngularBin_sum n S) θ
  rw [he]
  exact angularBinSelection_bounds _ _

theorem selectedAngularBins_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (S : Finset ℕ) θ,
      ‖iteratedDeriv j (fun φ => ∑ k ∈ S, periodicAngularBin n k φ) θ‖ ≤
        C * ((n : ℝ)/(2*Real.pi))^j := by
  obtain ⟨C,hC0,hC⟩ := angularBinSelection_derivative_bound j
  refine ⟨C,hC0,?_⟩
  intro n S θ
  rw [periodicAngularBin_sum, iteratedDeriv_comp_const_mul
    ((angularBinSelection_contDiff _).of_le
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)/(2*Real.pi))]
  simpa only [mul_comm, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left (hC _ _)
    (by positivity : 0 ≤ ((n : ℝ)/(2*Real.pi))^j)

noncomputable def angularBinCount (δ : ℝ) : ℕ := ⌈2*Real.pi/δ⌉₊

theorem angularBinCount_pos {δ : ℝ} (hδ : 0 < δ) : 0 < angularBinCount δ := by
  exact Nat.ceil_pos.mpr (by positivity)

theorem angularBinCount_bounds {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi) :
    2*Real.pi/(angularBinCount δ : ℝ) ≤ δ ∧
      (angularBinCount δ : ℝ)/(2*Real.pi) ≤ 2/δ := by
  have hn : (0 : ℝ) < angularBinCount δ := by exact_mod_cast angularBinCount_pos hδ
  have hlo := Nat.le_ceil (2*Real.pi/δ)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 2*Real.pi/δ by positivity)
  change 2*Real.pi/δ ≤ (angularBinCount δ : ℝ) at hlo
  change (angularBinCount δ : ℝ) < 2*Real.pi/δ+1 at hhi
  constructor
  · apply (div_le_iff₀ hn).mpr
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlo
  · apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    have hbase : 1 ≤ 2*Real.pi/δ := (le_div_iff₀ hδ).mpr (by simpa using hcap)
    calc
      _ ≤ 2*(2*Real.pi/δ) := by linarith
      _ = _ := by ring

theorem selectedAngularBins_scale_derivatives (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ, 0 < δ → δ ≤ 2*Real.pi → ∀ (S : Finset ℕ) θ,
      ‖iteratedDeriv j (fun φ => ∑ k ∈ S, periodicAngularBin (angularBinCount δ) k φ) θ‖ ≤
        C * δ⁻¹^j := by
  obtain ⟨C,hC0,hC⟩ := selectedAngularBins_derivative_bound j
  refine ⟨C*2^j, by positivity, ?_⟩
  intro δ hδ hcap S θ
  apply (hC _ S θ).trans
  calc
    _ ≤ C*(2/δ)^j := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (angularBinCount_bounds hδ hcap).2 j) hC0
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

end PlanarFalconer

end OAI
