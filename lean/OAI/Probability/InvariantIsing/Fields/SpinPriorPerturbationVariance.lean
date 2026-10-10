import OAI.Probability.InvariantIsing.Fields.SpinPriorProfileVariance
import OAI.Probability.InvariantIsing.Arrays.FullPerturbationVariance

namespace OAI

/-! Uniform concentration of the actual finite perturbation for a deterministic
spin constraint, with the cascade retained as quenched disorder. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

theorem spinPriorPerturbation_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m n : ℕ, ∀ π : Measure (Spin N), IsProbabilityMeasure π →
    ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, |u j|≤2) →
    ∀ v : Fin m → ℝ, (∀ a, |v a|≤2) → ∀ t : ℝ, |t|≤1 →
    ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
      let d := fun j : Fin N => enumeratedSpectralDegree m j
      let r := fun j : Fin N => enumeratedTreeDegree m j
      let F := spinPriorProfileLog π (diagonalPerturbedEigenvalues eig I v t) c I d
        (tensorPerturbationAmplitude N u) (fun i => tensorPathProfile I d n r h i)
      MemLp F 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ∧
        variance F ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ≤
          N*(4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
            ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+C*(K+4*m+8)^2) := by
  obtain ⟨C,hC,hvar⟩ := spinPriorProfileLog_variance hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m n π hπ b hb eig c K hK heig I u hu v hv t ht h hh h0 H hH d r F
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure π := hπ
  have hNp : 0<N := by omega
  have hNr : (0 : ℝ)<N := by exact_mod_cast hNp
  let a := tensorPerturbationAmplitude N u
  let L := (K+4*m)*N + 2*(∑ i : Fin (n+1), ∑ j : Fin N,
    (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2*∑ b, (d j b : ℝ))
  have hp := hvar N hN μ hμ hμinv π hπ m N n
    (diagonalPerturbedEigenvalues eig I v t) c (K+4*m) (by positivity)
    (diagonalPerturbedEigenvalues_abs_le hNp eig I v hv t ht K heig) I d a b hb
    (fun i => varianceIncrement h i) (fun i j => varianceIncrement (monomialPath n (r j)) i)
  have hsum := tensorPerturbationAmplitude_square_sum_le N u hu
  have hsmall := perturbationScale_sq_le_one hNp
  have hsum' : (∑ j : Fin N, a j^2) ≤ 4*N :=
    hsum.trans ((mul_le_mul_of_nonneg_left hsmall (by positivity : 0≤4*(N : ℝ))).trans_eq (mul_one _))
  have hG : (∑ i : Fin (n+1), ((varianceIncrement h i : ℝ)*N+
      ∑ j : Fin N, (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2)) ≤ (H+4)*N := by
    rw [Finset.sum_add_distrib,← Finset.sum_mul,varianceIncrement_sum hh h0,Finset.sum_comm]
    have hm : (∑ j : Fin N, ∑ i : Fin (n+1),
        (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2) ≤ ∑ j : Fin N, a j^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [← Finset.sum_mul]
      exact (mul_le_mul_of_nonneg_right (monomialVarianceIncrement_sum_le n (r j))
        (sq_nonneg _)).trans_eq (one_mul _)
    have hhN := mul_le_mul_of_nonneg_right hH hNr.le
    linarith
  have hdeg : ∀ j : Fin N, (∑ b, (d j b : ℝ)) ≤ 1*((j : ℝ)+1) := by
    intro j
    simpa only [one_mul] using enumeratedSpectralDegree_real_sum_le m j
  have hrot := (tensorPathProfile_rotation_cap d a n r).trans
    (tensorPerturbationAmplitude_degree_sum_le u hu d 1 zero_le_one hdeg)
  have hrot' : (∑ i : Fin (n+1), ∑ j : Fin N,
      (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2*∑ b, (d j b : ℝ)) ≤ 4*N := by
    apply hrot.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (by positivity : 0≤4*(N : ℝ))
  have hL0 : 0≤L := by dsimp only [L]; positivity
  have hL : L≤N*(K+4*m+8) := by dsimp only [L]; linarith
  have hLsq := pow_le_pow_left₀ hL0 hL 2
  let T := 4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
    ∂(rawCascadeLaw n b : Measure (RawTree n)))
  have hT : 0 ≤ T := mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)
  have hroot : (varianceIncrement h 0 : ℝ)*N+
      ∑ j : Fin N, (varianceIncrement (monomialPath n (r j)) 0 : ℝ)*a j^2 ≤ (H+4)*N := by
    apply le_trans ?_ hG
    exact Finset.single_le_sum
      (f := fun i : Fin (n+1) => (varianceIncrement h i : ℝ)*N+
        ∑ j : Fin N, (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2)
      (fun i _ => add_nonneg (by positivity) (Finset.sum_nonneg fun j _ => by positivity))
      (Finset.mem_univ (0 : Fin (n+1)))
  have hroot' : T+(varianceIncrement h 0 : ℝ)*N+
      ∑ j : Fin N, (varianceIncrement (monomialPath n (r j)) 0 : ℝ)*a j^2 ≤ T+(H+4)*N := by
    linarith
  have hvar' := hp.2.trans (add_le_add hroot' 
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLsq hC.le) hNr.le))
  refine ⟨hp.1, ?_⟩
  have he : C*(N*(K+4*m+8))^2/N = N*(C*(K+4*m+8)^2) := by
    field_simp [hNr.ne']
  rw [he] at hvar'
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hTN : T ≤ N*T := by nlinarith
  change variance F ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ≤
    T+(H+4)*N+N*(C*(K+4*m+8)^2) at hvar'
  change variance F _ ≤ N*(T+H+4+C*(K+4*m+8)^2)
  linarith

end InvariantIsing

end

end OAI
