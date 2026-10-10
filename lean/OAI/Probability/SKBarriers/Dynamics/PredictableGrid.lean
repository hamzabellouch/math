import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.FiniteProduct
import OAI.Probability.SKBarriers.SpinGlass.FiniteIndicators
import OAI.Probability.SKBarriers.Dynamics.GreedyRecursion
import OAI.Probability.SKBarriers.Dynamics.GridThreshold

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

def gridThresholds (n p : ℕ) (t ρ : ℝ) (z : Fin p → Fin n) (j : ℕ) : ℝ :=
  if h : j<p then thresholdGrid n (t+4*j*ρ) ρ (z ⟨j,h⟩) else t+4*j*ρ

theorem gridThresholds_prefix (n p j : ℕ) (t ρ : ℝ) (z : Fin p → Fin n) (hj : j<p) :
    ∀ i<j, gridThresholds n p t ρ z i =
      gridThresholds n j t ρ (fun a => z ⟨a.val,a.isLt.trans hj⟩) i := by
  intro i hij
  simp only [gridThresholds,dite_eq_left hij,dite_eq_left (hij.trans hj)]

theorem gridThresholds_good_mass {n : ℕ} (hn : 0<n) (μ : ProbabilityMeasure ℝ)
    (p : ℕ) (t ρ : ℝ) (hρ : 0<ρ) :
    ((FiniteLaw.uniformFin n hn).iid (Fin p)).prob (fun z => ∃ i : Fin p,
      ρ^4 < (μ:Measure ℝ).real (Icc (thresholdGrid n (t+4*i.val*ρ) ρ (z i)-2*ρ^8)
        (thresholdGrid n (t+4*i.val*ρ) ρ (z i)+2*ρ^8))) ≤
      p*((4*ρ^8/ρ+1/(n:ℝ))/ρ^4) := by
  classical
  let P := FiniteLaw.uniformFin n hn
  refine (FiniteLaw.prob_exists _ _).trans ?_
  calc
    _ ≤ ∑ i : Fin p, (4*ρ^8/ρ+1/(n:ℝ))/ρ^4 := by
      apply Finset.sum_le_sum
      intro i _
      rw [P.iid_prob_single i (fun u => ρ^4 < (μ:Measure ℝ).real
        (Icc (thresholdGrid n (t+4*i.val*ρ) ρ u-2*ρ^8) (thresholdGrid n (t+4*i.val*ρ) ρ u+2*ρ^8)))]
      have HM := P.markov (fun u => (μ:Measure ℝ).real
          (Icc (thresholdGrid n (t+4*i.val*ρ) ρ u-2*ρ^8) (thresholdGrid n (t+4*i.val*ρ) ρ u+2*ρ^8)))
        (fun _ => measureReal_nonneg) (ρ^4) (pow_pos hρ _)
      have HE := thresholdGrid_mass_expect hn μ hρ (by positivity : 0≤2*ρ^8) (t+4*i.val*ρ)
      apply (le_div_iff₀ (pow_pos hρ 4)).mpr
      have HR : 2*(2*ρ^8)/ρ=4*ρ^8/ρ := by ring
      rw [HR] at HE
      simpa only [mul_comm] using HM.trans HE
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem prod_block_marker (B s : ℕ) (hB : 0<B) (γ : ℝ) :
    (∏ i : Fin (B*s), if i.val%B=0 then γ else 1)=γ^s := by
  classical
  let : NeZero B := ⟨hB.ne'⟩
  have hfirst : (∏ i : Fin B, if i.val%B=0 then γ else 1)=γ := by
    have he (i : Fin B) : i.val%B=0 ↔ i=0 := by rw [Nat.mod_eq_of_lt i.isLt]; exact (Fin.ext_iff (a := i) (b := (0:Fin B))).symm
    simp only [he]
    simp
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.mul_succ,Fin.prod_univ_add]
    simp only [Fin.val_castAdd,Fin.val_natAdd]
    rw [show (∏ i : Fin B, if ((B*s)+i.val)%B=0 then γ else 1)=γ from by
      simpa only [Nat.add_mod,Nat.mul_mod_right,zero_add,Nat.mod_mod] using hfirst]
    rw [ih,pow_succ]

theorem greedy_grid_windows_bound {n : ℕ} (hn : 0<n) (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n) (x : ℕ → Config n)
    (B s m : ℕ) (hB : 0<B) (t ρ b w : ℝ) (hρ : 0<ρ) (hw : 0≤w) (k : ℕ) :
    ((FiniteLaw.uniformFin n hn).iid (Fin (B*s))).prob (fun z => ∀ i : Fin (B*s), i.val%B=0 →
      |overlap (greedyReference base pick x (gridThresholds n (B*s) t ρ z) b m i.val) (x k)-
        thresholdGrid n (t+4*i.val*ρ) ρ (z i)|≤w) ≤ (2*w/ρ+1/(n:ℝ))^s := by
  classical
  let P := FiniteLaw.uniformFin n hn
  let γ := 2*w/ρ+1/(n:ℝ)
  let E (j : ℕ) (z : Fin j → Fin n) (u : Fin n) := j%B=0 →
    |overlap (greedyReference base pick x (gridThresholds n j t ρ z) b m j) (x k)-
      thresholdGrid n (t+4*j*ρ) ρ u|≤w
  have hE (j : ℕ) (z : Fin j → Fin n) : P.prob (E j z) ≤ if j%B=0 then γ else 1 := by
    by_cases hj : j%B=0
    · rw [ite_eq_left hj]
      have H := thresholdGrid_window hn hρ hw (t+4*j*ρ)
        (overlap (greedyReference base pick x (gridThresholds n j t ρ z) b m j) (x k))
      simpa only [E,hj,true_implies,abs_sub_comm] using H
    · exact (P.prob_le_one _).trans_eq (ite_eq_right hj).symm
  have H := P.iid_predictable_bound E (fun j => if j%B=0 then γ else 1)
    (fun j => by dsimp only [γ]; split_ifs <;> positivity) hE (B*s)
  rw [prod_block_marker B s hB] at H
  refine (FiniteLaw.prob_mono _ (fun z hz i hi => ?_)).trans H
  have hr := gridThresholds_prefix n (B*s) i.val t ρ z i.isLt
  have he := greedyReference_predictable base pick x (gridThresholds n (B*s) t ρ z)
      (gridThresholds n i.val t ρ (fun a => z ⟨a.val,a.isLt.trans i.isLt⟩)) b m i.val hr
  rw [← he]
  exact hz i hi

end SK.Analytic

end
end

end OAI
