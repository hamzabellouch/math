import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearCutoff
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteOverlap

namespace OAI

/-! The singular near-node term has a localized form bound uniform over all
weak-H1 states. No smoothness of the state or orbital restriction is imposed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def electronBall {n : ℕ} (i : Fin n) (a : Position) (r : ℝ) : Set (Configuration n) :=
  {x | ‖Coulomb.position x i-a‖ ≤ r}

theorem electronBall_measurable {n : ℕ} (i : Fin n) (a : Position) (r : ℝ) :
    MeasurableSet (electronBall i a r) :=
  isClosed_le (((Coulomb.positionCLM i).continuous.sub continuous_const).norm)
    continuous_const |>.measurableSet

theorem nuclear_near_form_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (a : Position) (r : ℝ), 0 < r →
      (∫ x in electronBall i a r,
        Coulomb.coulombKernel (Coulomb.position x i-a)*‖u.value s x‖^2) ≤
      (24*C^2/r)*(∫ x in electronBall i a (2*r), ‖u.value s x‖^2)+
        8*r*(∑ k : Fin 3, ∫ x in electronBall i a (2*r), ‖u.gradient s (i,k) x‖^2) := by
  obtain ⟨C,hC,hder⟩ := nuclearBump_derivative_bound
  refine ⟨C,hC,fun n u s i a r hr => ?_⟩
  have hzero (x : Configuration n) (hx : x ∉ electronBall i a (2*r)) :
      nuclearCutoff r a i x = 0 ∧ fderiv ℝ (nuclearCutoff r a i) x = 0 :=
    nuclearCutoff_outside hr a i x (lt_of_not_ge hx)
  have hb := localized_nuclear_hardy u s i a hr (nuclearCutoff r a i)
    (nuclearCutoff_contDiff r a i) (nuclearCutoff_abs_le_one r a i)
    (nuclearCutoff_partial_bound hder hr a i) (electronBall i a r) (electronBall i a (2*r))
    (electronBall_measurable i a r) (electronBall_measurable i a (2*r))
    (fun _ hx => hx) (fun x hx => nuclearCutoff_one hr a i x hx)
    (fun x hx => (hzero x hx).1)
    (fun k x hx => by rw [(hzero x hx).2]; rfl)
  convert hb using 1
  field_simp

theorem nuclear_near_sum_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (R : Fin m → Position) (r M : ℝ), 0 < r →
      (∀ x : Configuration n, (∑ a, if x ∈ electronBall i (R a) (2*r) then (1:ℝ) else 0) ≤ M) →
      (∑ a, ∫ x in electronBall i (R a) r,
        Coulomb.coulombKernel (Coulomb.position x i-R a)*‖u.value s x‖^2) ≤
      M*((24*C^2/r)*(∫ x, ‖u.value s x‖^2)+
        8*r*(∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) := by
  obtain ⟨C,hC,hnear⟩ := nuclear_near_form_bound
  refine ⟨C,hC,fun m n u s i R r M hr hoverlap => ?_⟩
  have hm := finite_overlap_integral (fun a => electronBall i (R a) (2*r))
    (fun a => electronBall_measurable i (R a) (2*r)) (fun x => ‖u.value s x‖^2)
    ((u.value_L2 s).integrable_norm_pow (p := 2) (by decide)) (fun _ => sq_nonneg _) M hoverlap
  have hg (k : Fin 3) := finite_overlap_integral (fun a => electronBall i (R a) (2*r))
    (fun a => electronBall_measurable i (R a) (2*r)) (fun x => ‖u.gradient s (i,k) x‖^2)
    ((u.partial_L2 s (i,k)).integrable_norm_pow (p := 2) (by decide)) (fun _ => sq_nonneg _) M hoverlap
  have hgall := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hg k)
  simp only [← Finset.mul_sum] at hgall
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin m))) =>
    hnear n u s i (R a) r hr)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  apply hs.trans
  rw [Finset.sum_comm]
  calc
    _ ≤ (24*C^2/r)*(M*∫ x, ‖u.value s x‖^2)+
        8*r*(M*∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
        (mul_le_mul_of_nonneg_left hgall (by positivity))
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
