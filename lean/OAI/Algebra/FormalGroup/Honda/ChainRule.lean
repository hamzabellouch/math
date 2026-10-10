import Mathlib

namespace OAI

noncomputable section

namespace HeightThree.OriginalDifferentialSupport
open MvPowerSeries.WithPiTopology
section ChainRule
variable {R σ τ : Type*} [CommRing R] [Fintype σ]

omit [Fintype σ] in

theorem continuous_pderiv [TopologicalSpace R] [IsTopologicalRing R]
    (i : σ) : Continuous (MvPowerSeries.pderiv (R := R) i) := by
  apply continuous_pi
  intro n
  exact (MvPowerSeries.WithPiTopology.continuous_coeff R (n + Finsupp.single i 1)).mul_const _

theorem pderiv_subst_polynomial (g : σ → MvPowerSeries τ R)
    (hg : MvPowerSeries.HasSubst g) (i : τ) (f : MvPolynomial σ R) :
    MvPowerSeries.pderiv i (MvPowerSeries.subst g (f : MvPowerSeries σ R)) =
      ∑ j, MvPowerSeries.subst g (MvPowerSeries.pderiv j (f : MvPowerSeries σ R)) *
        MvPowerSeries.pderiv i (g j) := by
  classical
  have hz : MvPowerSeries.subst g (0 : MvPowerSeries σ R) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hg]
    exact map_zero _
  have ho : MvPowerSeries.subst g (1 : MvPowerSeries σ R) = 1 := by
    rw [← MvPowerSeries.coe_substAlgHom hg]
    exact map_one _
  induction f using MvPolynomial.induction_on with
  | C r => simp [hz]
  | add f h hf hh =>
    simp only [MvPolynomial.coe_add, MvPowerSeries.subst_add hg, map_add,
      hf, hh, add_mul, Finset.sum_add_distrib]
  | mul_X f j hf =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X,
      MvPowerSeries.subst_X hg,
      Derivation.leibniz, smul_eq_mul, hf,
      MvPowerSeries.subst_add hg, MvPowerSeries.subst_mul hg, add_mul]
    rw [Finset.sum_add_distrib]
    have h1 : (∑ j_1, (MvPowerSeries.subst g (f : MvPowerSeries σ R) *
        MvPowerSeries.subst g (MvPowerSeries.pderiv (R := R) j_1 (MvPowerSeries.X j))) *
          MvPowerSeries.pderiv i (g j_1)) =
        MvPowerSeries.subst g (f : MvPowerSeries σ R) * MvPowerSeries.pderiv i (g j) := by
      simp [MvPowerSeries.pderiv_X, Pi.single_apply, apply_ite,
        hz, ho]
    rw [h1]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring

theorem pderiv_subst (g : σ → MvPowerSeries τ R)
    (hg : MvPowerSeries.HasSubst g) (i : τ) (f : MvPowerSeries σ R) :
    MvPowerSeries.pderiv i (MvPowerSeries.subst g f) =
      ∑ j, MvPowerSeries.subst g (MvPowerSeries.pderiv j f) *
        MvPowerSeries.pderiv i (g j) := by
  let : UniformSpace R := ⊥
  let : DiscreteUniformity R := ⟨rfl⟩
  have hc₁ : Continuous (fun f : MvPowerSeries σ R =>
      MvPowerSeries.pderiv i (MvPowerSeries.subst g f)) :=
    (continuous_pderiv i).comp (MvPowerSeries.continuous_subst hg)
  have hc₂ : Continuous (fun f : MvPowerSeries σ R =>
      ∑ j, MvPowerSeries.subst g (MvPowerSeries.pderiv j f) *
        MvPowerSeries.pderiv i (g j)) := by
    exact continuous_finsetSum _ fun j _ =>
      ((MvPowerSeries.continuous_subst hg).comp (continuous_pderiv j)).mul_const _
  exact congrFun (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer
    hc₁ hc₂ (by funext f; exact pderiv_subst_polynomial g hg i f)) f

end ChainRule

variable {R : Type*} [CommRing R]
theorem constantCoeff_subst_zero_axis {σ τ : Type*} (a : σ → MvPowerSeries τ R)
    (ha : MvPowerSeries.HasSubst a) (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  have hz := MvPowerSeries.constantCoeff_subst_eq_zero ha h0
    (f := f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) (by simp)
  have hs : MvPowerSeries.subst a (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) =
      MvPowerSeries.subst a f - MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sub]
    rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply,
      MvPowerSeries.subst_C]
  rw [hs, map_sub, MvPowerSeries.constantCoeff_C, sub_eq_zero] at hz
  exact hz

theorem constantCoeff_derivative_eq (f : PowerSeries R) :
    PowerSeries.constantCoeff (PowerSeries.derivative f) = PowerSeries.coeff 1 f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_derivative]
  simp

theorem coeff_one_formal_add (F : FormalGroup R) (a b : PowerSeries R)
    (ha : PowerSeries.constantCoeff a = 0) (hb : PowerSeries.constantCoeff b = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst ![a,b] F.toPowerSeries) =
      PowerSeries.coeff 1 a + PowerSeries.coeff 1 b := by
  have hs : MvPowerSeries.HasSubst (![a,b] : Fin 2 → PowerSeries R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
    intro i
    fin_cases i
    · exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
    · exact PowerSeries.HasSubst.of_constantCoeff_zero' hb
  have h := congrArg (PowerSeries.constantCoeff (R := R)) (pderiv_subst _ hs () F.toPowerSeries)
  change PowerSeries.constantCoeff (PowerSeries.derivative _) = _ at h
  rw [constantCoeff_derivative_eq] at h
  simp only [Fin.sum_univ_two, map_add, map_mul] at h
  have hc (i : Fin 2) :
      PowerSeries.constantCoeff (MvPowerSeries.subst ![a,b] (MvPowerSeries.pderiv i F.toPowerSeries)) = 1 := by
    change MvPowerSeries.constantCoeff (MvPowerSeries.subst ![a,b] (MvPowerSeries.pderiv i F.toPowerSeries)) = 1
    rw [constantCoeff_subst_zero_axis _ hs (by intro j; fin_cases j; exact ha; exact hb),
      ← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_pderiv]
    fin_cases i <;> simp [F.lin_coeff_X, F.lin_coeff_Y]
  rw [hc, hc] at h
  simp only [one_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  change _ = PowerSeries.constantCoeff (PowerSeries.derivative a) +
    PowerSeries.constantCoeff (PowerSeries.derivative b) at h
  simpa only [constantCoeff_derivative_eq] using h

end HeightThree.OriginalDifferentialSupport

end

end OAI
