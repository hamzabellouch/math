import OAI.InformationTheory.AmplitudeDamping.OutputEntropy

namespace OAI

noncomputable section

section
open scoped BigOperators
namespace GAD

/-- Binary Shannon entropy is concave, including the endpoints. -/
theorem concaveOn_binEntropy : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) Real.binEntropy := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro p hp q hq a b ha hb hab
  have h₀ := Real.concaveOn_negMulLog.2 hp.1 hq.1 ha hb hab
  have h₁ := Real.concaveOn_negMulLog.2 (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2) ha hb hab
  have heq : 1-(a*p+b*q)=a*(1-p)+b*(1-q) := by nlinarith only [hab]
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,smul_eq_mul,heq] at *
  linarith

theorem weighted_conditional_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)*(b/(a+b))=b := by
  by_cases h : a+b=0
  · have : b=0 := by linarith
    simp [this]
  · exact mul_div_cancel₀ _ h

theorem conditional_mem (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    b/(a+b) ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨div_nonneg hb (add_nonneg ha hb), ?_⟩
  by_cases h : a+b=0
  · simp [h]
  · exact (div_le_one (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h))).mpr (by linarith)

theorem negMulLog_split (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog a+Real.negMulLog b =
      Real.negMulLog (a+b)+(a+b)*Real.binEntropy (b/(a+b)) := by
  have hb' := weighted_conditional_eq a b ha hb
  have ha' : (a+b)*(1-b/(a+b))=a := by nlinarith only [hb']
  have hA := Real.negMulLog_mul (a+b) (1-b/(a+b))
  have hB := Real.negMulLog_mul (a+b) (b/(a+b))
  rw [ha'] at hA
  rw [hb'] at hB
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  nlinarith only [hA,hB]

def distPopulation {n : ℕ} (q : Basis n → ℝ) (j : Fin n) : ℝ :=
  ∑ i, if i j=1 then q i else 0

theorem classical_entropy_le_sum_binary (n : ℕ) (q : Basis n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1) :
    ∑ i, Real.negMulLog (q i) ≤ ∑ j, Real.binEntropy (distPopulation q j) := by
  induction n with
  | zero =>
      have hq1 (i : Basis 0) : q i = 1 := by
        rw [Fintype.sum_unique] at hs
        convert hs using 1
        exact congrArg q (Subsingleton.elim _ _)
      simp only [hq1,Real.negMulLog_one,Finset.sum_const_zero,Fintype.sum_empty,le_refl]
  | succ n ih =>
      let t : Basis n → ℝ := fun i ↦ q (Fin.cons 0 i)+q (Fin.cons 1 i)
      have ht (i) : 0 ≤ t i := add_nonneg (hq _) (hq _)
      have ht1 : ∑ i, t i = 1 := by
        rw [sum_fin_cons] at hs
        simpa only [Fin.sum_univ_two,← Finset.sum_add_distrib,t] using hs
      have hsplit : (∑ i, Real.negMulLog (q i)) =
          (∑ i, Real.negMulLog (t i)) +
            ∑ i, t i*Real.binEntropy (q (Fin.cons 1 i)/t i) := by
        rw [sum_fin_cons,Fin.sum_univ_two,← Finset.sum_add_distrib]
        simp only [negMulLog_split _ _ (hq _) (hq _),Finset.sum_add_distrib,t]
      have hmean : (∑ i, t i*(q (Fin.cons 1 i)/t i)) = distPopulation q 0 := by
        simp only [t,weighted_conditional_eq _ _ (hq _) (hq _)]
        unfold distPopulation
        rw [sum_fin_cons]
        simp
      have hJ : (∑ i, t i*Real.binEntropy (q (Fin.cons 1 i)/t i)) ≤
          Real.binEntropy (distPopulation q 0) := by
        rw [← hmean]
        exact concaveOn_binEntropy.le_map_sum (fun i _ ↦ ht i) ht1
          (fun i _ ↦ conditional_mem _ _ (hq _) (hq _))
      have hpop (j : Fin n) : distPopulation t j = distPopulation q j.succ := by
        unfold distPopulation
        rw [sum_fin_cons]
        simp [Fin.sum_univ_two,t,← Finset.sum_add_distrib,ite_add_ite]
      calc
        (∑ i, Real.negMulLog (q i)) = _ := hsplit
        _ ≤ (∑ j, Real.binEntropy (distPopulation t j))+Real.binEntropy (distPopulation q 0) :=
          add_le_add (ih t ht ht1) hJ
        _ = _ := by simp only [hpop,Fin.sum_univ_succ]; ring

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem entropy_le_sum_populations {n : ℕ} {P : QMatrix n} (hP : IsState P) :
    entropy P ≤ ∑ j, Real.binEntropy (matrixPopulation P j) := by
  have hdiag (i : Basis n) : 0 ≤ (P i i).re := (Complex.nonneg_iff.mp hP.1.diag_nonneg).1
  have hs : ∑ i, (P i i).re=1 := by
    simpa only [Matrix.trace,Matrix.diag,Complex.re_sum,Complex.one_re] using congrArg Complex.re hP.2
  exact (entropy_le_diagonal hP.1).trans (classical_entropy_le_sum_binary n _ hdiag hs)

theorem output_entropy_upper (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} {P : QMatrix n} (hP : IsState P) :
    entropy (channel γ ν n P) ≤ ∑ j, Real.binEntropy ((1-γ)*matrixPopulation P j+γ*ν) := by
  simpa only [channel_population γ ν hγ hν hP] using
    entropy_le_sum_populations (channel_state γ ν hγ hν n hP)

theorem ensemble_nats_upper (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (E : Ensemble n) {p : ℝ} (hp : Maximizes γ ν p) :
    entropy (∑ a, (E.weight a : ℂ) • channel γ ν n (E.signal a)) -
      (∑ a, E.weight a * entropy (channel γ ν n (E.signal a))) ≤
    (n : ℝ)*objective γ ν p := by
  let P := ∑ a, E.weight a • E.signal a
  have hP : IsState P := state_mixture E.weight E.signal E.weight_nonneg E.weight_sum E.signal_state
  have hpop (j) : (∑ a, E.weight a*matrixPopulation (E.signal a) j) = matrixPopulation P j :=
    (matrixPopulation_mixture E.weight E.signal j).symm
  have hJ (j) : g (v γ ν (matrixPopulation P j)) ≤
      ∑ a, E.weight a*g (v γ ν (matrixPopulation (E.signal a) j)) := by
    rw [← hpop]
    exact (convexOn_output_entropy hγ hν).map_sum_le
      (fun a _ ↦ E.weight_nonneg a) E.weight_sum
      (fun a _ ↦ matrixPopulation_mem (E.signal_state a) j)
  have hlow : (∑ j, g (v γ ν (matrixPopulation P j))) ≤
      ∑ a, E.weight a*entropy (channel γ ν n (E.signal a)) := by
    calc
      _ ≤ ∑ j, ∑ a, E.weight a*g (v γ ν (matrixPopulation (E.signal a) j)) :=
        Finset.sum_le_sum (fun j _ ↦ hJ j)
      _ = ∑ a, E.weight a * ∑ j, g (v γ ν (matrixPopulation (E.signal a) j)) := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun a _ ↦ mul_le_mul_of_nonneg_left
        (mixed_output_entropy_bound γ ν hγ hν n (E.signal_state a)) (E.weight_nonneg a))
  have hu := output_entropy_upper γ ν hγ hν hP
  have hv : (∑ j, objective γ ν (matrixPopulation P j)) ≤ (n:ℝ)*objective γ ν p := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hp.2 _ (matrixPopulation_mem hP j))
  have heq : (∑ a, (E.weight a : ℂ) • channel γ ν n (E.signal a)) = channel γ ν n P := by
    simp only [Complex.coe_smul, P,channel_mixture]
  rw [heq]
  simp only [objective,Finset.sum_sub_distrib] at hv
  dsimp only [objective]
  linarith

theorem ensembleValue_upper (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (E : Ensemble n) {p : ℝ} (hp : Maximizes γ ν p) :
    ensembleValue γ ν E ≤ (n : ℝ)/Real.log 2 * objective γ ν p := by
  unfold ensembleValue
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := div_le_div_of_nonneg_right (ensemble_nats_upper γ ν hγ hν E hp) hlog.le
  calc
    _ ≤ (n:ℝ)*objective γ ν p / Real.log 2 := h
    _ = _ := by ring

end GAD

end

end OAI
