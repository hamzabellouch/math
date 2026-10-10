import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.WeightedSourcePairing
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.H1BoundedForm

namespace OAI

/-! Absolute nuclear form errors control mixed terms on the full complex,
spinful weak-H1 domain. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem weighted_inner_pairing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℝ) (f g : X → ℂ) (hF : AEMeasurable F μ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfi : Integrable (fun x => |F x| * ‖f x‖^2) μ)
    (hgi : Integrable (fun x => |F x| * ‖g x‖^2) μ) :
    Integrable (fun x => F x*inner ℝ (f x) (g x)) μ ∧
      |∫ x, F x*inner ℝ (f x) (g x) ∂μ|^2 ≤
        (∫ x, |F x| * ‖f x‖^2 ∂μ)*(∫ x, |F x| * ‖g x‖^2 ∂μ) := by
  obtain ⟨hi,hsq⟩ := weighted_real_pairing μ (fun x => |F x|) (fun x => ‖f x‖) (fun x => ‖g x‖)
    hF.abs hf.norm.aemeasurable hg.norm.aemeasurable
    (by simpa only [abs_abs] using hfi) (by simpa only [abs_abs] using hgi)
  have hb (x : X) : ‖F x*inner ℝ (f x) (g x)‖ ≤ |F x| * ‖f x‖*‖g x‖ := by
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (f x) (g x)) (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm
  have hI : Integrable (fun x => F x*inner ℝ (f x) (g x)) μ :=
    hi.mono' (hF.aestronglyMeasurable.mul (hf.inner hg)) (Filter.Eventually.of_forall hb)
  refine ⟨hI,?_⟩
  have he : |∫ x, F x*inner ℝ (f x) (g x) ∂μ| ≤ ∫ x, |F x| * ‖f x‖*‖g x‖ ∂μ := by
    apply (show |∫ x, F x*inner ℝ (f x) (g x) ∂μ| ≤ ∫ x, ‖F x*inner ℝ (f x) (g x)‖ ∂μ from
      by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (fun x => F x*inner ℝ (f x) (g x))).trans
    exact integral_mono hI.norm hi hb
  apply (pow_le_pow_left₀ (abs_nonneg _) he 2).trans
  simpa only [sq_abs,abs_abs] using hsq

def nuclearErrorCross {n : ℕ} (F : Position → ℝ) (u v : Coulomb.H1Vector n) : ℝ :=
  ∑ s, ∑ i, ∫ x, F (Coulomb.position x i)*inner ℝ (u.value s x) (v.value s x)

def nuclearAbsoluteError {n : ℕ} (F : Position → ℝ) (u : Coulomb.H1Vector n) : ℝ :=
  ∑ s, ∑ i, ∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2

theorem nuclearErrorCross_square_bound {n : ℕ} (F : Position → ℝ) (hF : Measurable F)
    (u v : Coulomb.H1Vector n)
    (hu : ∀ s i, Integrable (fun x => |F (Coulomb.position x i)| * ‖u.value s x‖^2))
    (hv : ∀ s i, Integrable (fun x => |F (Coulomb.position x i)| * ‖v.value s x‖^2)) :
    (nuclearErrorCross F u v)^2 ≤ nuclearAbsoluteError F u*nuclearAbsoluteError F v := by
  let A := fun s i => ∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2
  let B := fun s i => ∫ x, |F (Coulomb.position x i)| * ‖v.value s x‖^2
  let c := fun s i => ∫ x, F (Coulomb.position x i)*inner ℝ (u.value s x) (v.value s x)
  have hA s i : 0 ≤ A s i := integral_nonneg (fun _ => by positivity)
  have hB s i : 0 ≤ B s i := integral_nonneg (fun _ => by positivity)
  have hc s i : (c s i)^2 ≤ A s i*B s i := by
    have h := (weighted_inner_pairing volume (fun x => F (Coulomb.position x i))
      (u.value s) (v.value s) (hF.comp (Coulomb.positionCLM i).continuous.measurable).aemeasurable
      (u.value_L2 s).aestronglyMeasurable (v.value_L2 s).aestronglyMeasurable (hu s i) (hv s i)).2
    simpa only [sq_abs] using h
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun s _ => Finset.sum_nonneg (fun i _ => hA s i))
    (fun s _ => Finset.sum_nonneg (fun i _ => hB s i))
    (fun s _ => Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => hA s i) (fun i _ => hB s i) (fun i _ => hc s i))

theorem nuclearAbsoluteError_bound {n : ℕ} (F : Position → ℝ) (B : ℝ)
    (u : Coulomb.H1Vector n)
    (hb : ∀ s i, (∫ x, |F (Coulomb.position x i)| * ‖u.value s x‖^2) ≤
      B*((∫ x, ‖u.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) :
    nuclearAbsoluteError F u ≤ B*((n:ℝ)*Coulomb.mass u+2*Coulomb.kinetic u) := by
  apply (Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun i _ => hb s i))).trans_eq
  simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  simp only [Coulomb.mass,Coulomb.kinetic,Fintype.sum_prod_type,← Finset.mul_sum]
  ring

theorem nuclearErrorCross_graph_square_bound {n : ℕ} (F : Position → ℝ) (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (u v : Coulomb.H1Vector n)
    (hb : ∀ (w : Coulomb.H1Vector n) s i,
      Integrable (fun x => |F (Coulomb.position x i)| * ‖w.value s x‖^2) ∧
      (∫ x, |F (Coulomb.position x i)| * ‖w.value s x‖^2) ≤
        B*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2)) :
    (nuclearErrorCross F u v)^2 ≤ B^2*
      ((n:ℝ)*Coulomb.mass u+2*Coulomb.kinetic u)*
      ((n:ℝ)*Coulomb.mass v+2*Coulomb.kinetic v) := by
  have h := nuclearErrorCross_square_bound F hF u v
    (fun s i => (hb u s i).1) (fun s i => (hb v s i).1)
  have hu := nuclearAbsoluteError_bound F B u (fun s i => (hb u s i).2)
  have hv := nuclearAbsoluteError_bound F B v (fun s i => (hb v s i).2)
  apply h.trans
  have he := mul_le_mul hu hv
    (show 0 ≤ nuclearAbsoluteError F v from Finset.sum_nonneg (fun s _ =>
      Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => by positivity))))
    (show 0 ≤ B*((n:ℝ)*Coulomb.mass u+2*Coulomb.kinetic u) by
      exact mul_nonneg hB (add_nonneg (mul_nonneg (Nat.cast_nonneg n) (Coulomb.mass_nonneg u))
        (mul_nonneg (by norm_num) (Coulomb.kinetic_nonneg u))))
  convert he using 1
  ring

end ContinuumCoulomb

end

end OAI
