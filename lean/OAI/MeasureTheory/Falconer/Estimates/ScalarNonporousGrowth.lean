import OAI.MeasureTheory.Falconer.Estimates.ScalarNonporousPowers

namespace OAI

/-! Actual nonporous blocks, including skipped levels, produce a large
 separated subset of a fixed-fold sumset of the original leaf centers. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_nonporous_growth {B M copies J L C : ℕ} {U : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (branch n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (branch i) (n i))
    (t : ℕ) (g : ℕ → ℕ) (hg : ∀ i < t, g i < g (i+1)) (hgM : ∀ i < t, g i < M)
    (hbranch : ∀ i < t, branch (g i) ≠ 0)
    (hpor : ∀ i < t, B*(g i+1) ≤ n (g i)+C)
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hcopies : (2*L+1)*J ≤ copies) :
    ∃ E : Finset ℝ, E ⊆ copies • Q.image scalarPathCenter ∧ E.card = (J+1)^t ∧
      ∀ x ∈ E, ∀ y ∈ E, x ≠ y → (1/2:ℝ)^(B*M) ≤ |x-y| := by
  by_cases ht0 : t = 0
  · have hA : (Q.image scalarPathCenter).Nonempty := hne.image scalarPathCenter
    have hsum : (copies • Q.image scalarPathCenter).Nonempty := hA.nsmul
    obtain ⟨x,hx⟩ := hsum
    refine ⟨{x},Finset.singleton_subset_iff.mpr hx,by simp [ht0],?_⟩
    intro y hy z hz hyz
    exact False.elim (hyz ((Finset.mem_singleton.mp hy).trans (Finset.mem_singleton.mp hz).symm))
  have hU0 : 0 ≤ U := (by positivity : (0:ℝ) ≤ 18*(2:ℝ)^C).trans hU
  have hW : 0 ≤ 1+2*(J:ℝ)*U := by positivity
  have hscale := scalarSelectedScale_contract hW B t g hg hcontract
  have hlower : ∀ i < t,
      2*scalarSelectedScale B g (i+1) ≤ 6*(1/2:ℝ)^(n (g i)) := by
    intro i hi
    rw [scalarSelectedScale_succ]
    have hn := (hlevel (g i) (hgM i hi)).level_hi
    have hp : (1/2:ℝ)^(B*(g i+1)) ≤ (1/2:ℝ)^(n (g i)) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have hp0 : 0 ≤ (1/2:ℝ)^(n (g i)) := by positivity
    linarith
  have hupper : ∀ i < t,
      18*(1/2:ℝ)^(n (g i)) ≤ U*scalarSelectedScale B g (i+1) := by
    intro i hi
    rw [scalarSelectedScale_succ]
    have hh := scalar_dyadic_shift (B*(g i+1)) (n (g i)) C (hpor i hi)
    calc
      _ ≤ 18*((2:ℝ)^C*(1/2:ℝ)^(B*(g i+1))) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = (18*(2:ℝ)^C)*(1/2:ℝ)^(B*(g i+1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hU (by positivity)
  obtain ⟨E,hE,hcard,hsep⟩ := scalar_selected_fork_sumset Q hQ hne t
    (fun i => B*g i) (fun i => B*(g i+1)) (fun i => branch (g i)) (fun i => n (g i))
    (fun i _ => Nat.mul_le_mul_left B (Nat.le_succ _))
    (fun i hi => Nat.mul_le_mul_left B (by have := hg i hi; omega))
    (fun i hi => Nat.mul_le_mul_left B (by have := hgM i hi; omega))
    (fun i hi => hlevel (g i) (hgM i hi)) hbranch
    (scalarSelectedScale B g) (fun i _ => scalarSelectedScale_pos B g i) hJ hscale hL hcopies hlower hupper
  refine ⟨E,hE,hcard,?_⟩
  have hfinal : (1/2:ℝ)^(B*M) ≤ scalarSelectedScale B g t := by
    rw [scalarSelectedScale,ite_eq_right ht0]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.mul_le_mul_left B (by have := hgM (t-1) (by omega); omega))
  exact fun x hx y hy hxy => hfinal.trans (hsep x hx y hy hxy)

end Falconer.Regularization

end OAI
