import OAI.Probability.InvariantIsing.Magnetic.MagneticVariationalBounds
import OAI.Probability.InvariantIsing.Core.TrialGridApproximation

namespace OAI

/-! Lower finite-grid trials preserve the magnetic entropy bound and
approximate the finite-spectrum magnetic variational infimum. -/
noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators
namespace InvariantIsing

lemma magneticEntropyFunctional_mono {A : Type*} [Fintype A]
    (γ mag : A → ℝ) {p q : OverlapPath} (hpq : p.val ≤ᵐ[pathMeasure] q.val) :
    magneticEntropyFunctional γ mag p ≤ magneticEntropyFunctional γ mag q := by
  apply iSup_mono
  intro h
  apply EReal.coe_le_coe_iff.mpr
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply integral_mono_ae (integrable_path_mul_field p h) (integrable_path_mul_field q h)
  filter_upwards [hpq] with s hs
  exact mul_le_mul_of_nonneg_right hs (fieldFunction_nonneg h s)

lemma lowerGridPath_magneticEntropy_le {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (p : OverlapPath) (n : ℕ) :
    magneticEntropyFunctional γ mag (lowerGridPath p n) ≤ magneticEntropyFunctional γ mag p :=
  magneticEntropyFunctional_mono γ mag (lowerGridPath_le p n)

theorem exists_finiteMagneticEntropy_trial {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a| ≤ 1) {ε : ℝ} (hε : 0<ε) :
    ∃ p : OverlapPath, ∃ S : ℝ, magneticEntropyFunctional γ mag p=(S : EReal) ∧
      S+spectralFunctional (finiteR ρ eig hρ hsum) p <
        (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal+ε := by
  have hf := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ mag hγ hγsum hmag
  have hlt : magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag <
      ((magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal+ε : ℝ) := by
    rw [← EReal.coe_toReal hf.1 hf.2]
    exact_mod_cast (show (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal <
      (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal+ε by linarith)
  obtain ⟨p,hp⟩ := iInf_lt_iff.mp hlt
  have htop : magneticEntropyFunctional γ mag p ≠ ⊤ := by
    intro he
    simp only [he,EReal.top_add_coe,not_top_lt] at hp
  have hbot : magneticEntropyFunctional γ mag p ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (magneticEntropyFunctional_lower γ mag hγ hγsum hmag p)
  refine ⟨p,(magneticEntropyFunctional γ mag p).toReal,(EReal.coe_toReal htop hbot).symm,?_⟩
  rw [← EReal.coe_toReal htop hbot,← EReal.coe_add] at hp
  exact_mod_cast hp

end InvariantIsing

end

end OAI
