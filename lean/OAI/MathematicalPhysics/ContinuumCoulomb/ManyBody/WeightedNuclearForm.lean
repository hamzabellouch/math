import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.WeightedNuclearCross
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.BoundedFormCross

namespace OAI

/-! Polarization and graph bounds for the actual nuclear error potential,
including its Coulomb singularities. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def nuclearErrorEnergy {n : ℕ} (F : Position → ℝ) (u : Coulomb.H1Vector n) : ℝ :=
  ∑ s, ∑ i, ∫ x, F (Coulomb.position x i)*‖u.value s x‖^2

theorem nuclearErrorEnergy_eq_cross {n : ℕ} (F : Position → ℝ) (u : Coulomb.H1Vector n) :
    nuclearErrorEnergy F u = nuclearErrorCross F u u := by
  simp only [nuclearErrorEnergy,nuclearErrorCross,real_inner_self_eq_norm_sq]

theorem nuclearErrorCross_comm {n : ℕ} (F : Position → ℝ) (u v : Coulomb.H1Vector n) :
    nuclearErrorCross F u v = nuclearErrorCross F v u := by
  simp only [nuclearErrorCross,real_inner_comm]

theorem nuclearErrorCross_add_left {n : ℕ} (F : Position → ℝ) (hF : Measurable F)
    (hI : ∀ (w : Coulomb.H1Vector n) s i,
      Integrable (fun x => |F (Coulomb.position x i)| * ‖w.value s x‖^2))
    (u v w : Coulomb.H1Vector n) :
    nuclearErrorCross F (u.add v) w = nuclearErrorCross F u w+nuclearErrorCross F v w := by
  simp only [nuclearErrorCross,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  have hi (z : Coulomb.H1Vector n) := (weighted_inner_pairing volume
    (fun x => F (Coulomb.position x i)) (z.value s) (w.value s)
    (hF.comp (Coulomb.positionCLM i).continuous.measurable).aemeasurable
    (z.value_L2 s).aestronglyMeasurable (w.value_L2 s).aestronglyMeasurable (hI z s i) (hI w s i)).1
  change (∫ x, F (Coulomb.position x i)*inner ℝ (u.value s x+v.value s x) (w.value s x)) = _
  simp only [inner_add_left,mul_add]
  exact integral_add (hi u) (hi v)

theorem nuclearErrorCross_add_right {n : ℕ} (F : Position → ℝ) (hF : Measurable F)
    (hI : ∀ (w : Coulomb.H1Vector n) s i,
      Integrable (fun x => |F (Coulomb.position x i)| * ‖w.value s x‖^2))
    (u v w : Coulomb.H1Vector n) :
    nuclearErrorCross F u (v.add w) = nuclearErrorCross F u v+nuclearErrorCross F u w := by
  rw [nuclearErrorCross_comm,nuclearErrorCross_add_left F hF hI,
    nuclearErrorCross_comm F v,nuclearErrorCross_comm F w]

theorem nuclearErrorEnergy_add {n : ℕ} (F : Position → ℝ) (hF : Measurable F)
    (hI : ∀ (w : Coulomb.H1Vector n) s i,
      Integrable (fun x => |F (Coulomb.position x i)| * ‖w.value s x‖^2))
    (u v : Coulomb.H1Vector n) :
    nuclearErrorEnergy F (u.add v) = nuclearErrorEnergy F u+nuclearErrorEnergy F v+
      2*nuclearErrorCross F u v := by
  simp only [nuclearErrorEnergy_eq_cross,nuclearErrorCross_add_left F hF hI,
    nuclearErrorCross_add_right F hF hI]
  rw [nuclearErrorCross_comm F v u]
  ring

theorem nuclearErrorEnergy_abs_le {n : ℕ} (F : Position → ℝ) (u : Coulomb.H1Vector n) :
    |nuclearErrorEnergy F u| ≤ nuclearAbsoluteError F u := by
  have hi (s : SpinConfiguration n) (i : Fin n) :
      |∫ x, F (Coulomb.position x i)*‖u.value s x‖^2| ≤
        ∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2 := by
    have h := norm_integral_le_integral_norm (μ := volume)
      (fun x => F (Coulomb.position x i)*‖u.value s x‖^2)
    simpa only [norm_mul,Real.norm_eq_abs,abs_pow,abs_norm] using h
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun s _ => (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i _ => hi s i)))

theorem nuclearErrorEnergy_graph_bound {n : ℕ} (hn : 1 ≤ n)
    (F : Position → ℝ) {B : ℝ} (hB : 0 ≤ B) (u : Coulomb.H1Vector n)
    (hb : ∀ s i, (∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2) ≤
      B*((∫ x, ‖u.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) :
    |nuclearErrorEnergy F u| ≤ B*n*(Coulomb.mass u+2*Coulomb.kinetic u) := by
  apply (nuclearErrorEnergy_abs_le F u).trans ((nuclearAbsoluteError_bound F B u hb).trans ?_)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hk := mul_le_mul_of_nonneg_right hnR (Coulomb.kinetic_nonneg u)
  nlinarith only [mul_le_mul_of_nonneg_left hk hB]

end ContinuumCoulomb

end

end OAI
