import OAI.Probability.InvariantIsing.Fields.SpinPriorHaarMean

namespace OAI

/-! Haar concentration combined with the proved constrained root/cascade
estimate. All constants are independent of the spin constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

theorem spinPriorJointFlatLog_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ π : Measure (Spin N), IsProbabilityMeasure π →
    ∀ m k n : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin k → Fin m → ℕ, ∀ amp : Fin k → ℝ,
    ∀ b : ℕ → ℝ, CascadeExponents n b → ∀ site : ℕ → ℝ≥0, ∀ monomial : ℕ → Fin k → ℝ≥0,
      let v := fun i => tensorVarianceProfile I degree (site i) (monomial i)
      let P := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
      let F := spinPriorJointFlatLog π eig c I degree amp (fun i => v i)
      let L := K*N+2*(∑ i : Fin (n+1), ∑ j, (monomial i j : ℝ)*amp j^2*∑ a, (degree j a : ℝ))
      MemLp F 2 P ∧ variance F P ≤
        4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)))+
          (site 0 : ℝ)*N+∑ j, (monomial 0 j : ℝ)*amp j^2+C*L^2/N := by
  obtain ⟨C,hC,hvar⟩ := haar_frobeniusLipschitz_variance hhaar
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv π hπ m k n eig c K hK heig I degree amp b hb site monomial v P F L
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure π := hπ
  let τ := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates
  let G := fun q : SpecialOrthogonal N × (LabeledTree n × (ℕ → ℝ)) => F ((q.1,q.2.1),q.2.2)
  let M := fun U => ∫ p, G (U,p) ∂τ
  have hmG : Measurable G := (measurable_spinPriorJointFlatLog π eig c I degree amp _).comp
    (show Measurable (fun q : SpecialOrthogonal N × (LabeledTree n × (ℕ → ℝ)) =>
      ((q.1,q.2.1),q.2.2)) from by fun_prop)
  have hm : Measurable M := hmG.stronglyMeasurable.integral_prod_right'.measurable
  have hsec U := spinPriorFlatLog_variance hgauss (by omega : 0<N) π eig (specialRotation U) c
    I degree amp n b site monomial hb
  have hmi U : Integrable (fun p => G (U,p)) τ := (hsec U).1.integrable (by norm_num)
  have hL : 0 < L := by
    dsimp only [L]
    exact add_pos_of_pos_of_nonneg (mul_pos hK (by exact_mod_cast (show 0<N by omega))) (by positivity)
  have hLip : ∀ U V, |M U-M V| ≤ L*frobeniusDistance U V := fun U V =>
    spinPriorFlatMean_rotation_bound hgauss (by omega) π eig c K hK.le heig
      I degree amp n b hb site monomial U V

  have hM := haar_frobeniusLipschitz_memLp_two hhaar N hN μ hμinv M hm L hL hLip
  have hg := variance_of_conditional_center μ τ hmG hM
    (fun U => ((hsec U).1.sub (memLp_const (M U))).integrable_sq) (fun _ => rfl)
    (fun U => by
      have he := variance_eq_integral (hsec U).1.aemeasurable
      change variance (fun p => G (U,p)) τ = ∫ p, (G (U,p)-M U)^2 ∂τ at he
      rw [← he]
      exact (hsec U).2)
  have hp := (measurePreserving_prodAssoc μ (labeledCascadeLaw n b : Measure (LabeledTree n))
    gaussianCoordinates)
  let φ := fun p : TensorFlatDisorder N n => (p.1.1,p.1.2,p.2)
  have hφ : MeasurePreserving φ P (μ.prod τ) := hp
  have hFG : G ∘ φ = F := rfl
  have hF : MemLp F 2 P := by
    have hh : MemLp (G ∘ φ) 2 P := hg.1.comp_measurePreserving hφ
    exact hFG ▸ hh
  have hvarF : variance F P = variance G (μ.prod τ) :=
    (congrArg (fun f => variance f P) hFG).symm.trans (hφ.variance_fun_comp hmG.aemeasurable)
  exact ⟨hF, hvarF.trans_le (hg.2.trans
    (add_le_add le_rfl (hvar N hN μ hμ hμinv M hm L hL hLip)))⟩

end InvariantIsing

end

end OAI
