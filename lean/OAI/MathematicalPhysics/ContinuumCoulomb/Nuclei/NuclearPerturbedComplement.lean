import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.WeightedNuclearForm
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.CoerciveComplementLower

namespace OAI

/-! Complement elimination with the actual singular nuclear error form.
The general form error enters quadratically through its mixed term. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def nuclearPerturbedForm {n : ℕ} (V : Configuration n → ℝ) (F : Position → ℝ)
    (u : Coulomb.H1Vector n) : ℝ := boundedPotentialForm V u+nuclearErrorEnergy F u

theorem nuclearPerturbedForm_add {n : ℕ} (V : Configuration n → ℝ)
    (hV : Continuous V) (D : ℝ) (hD : ∀ x, |V x| ≤ D)
    (F : Position → ℝ) (hF : Measurable F)
    (hI : ∀ (w : Coulomb.H1Vector n) s i,
      Integrable (fun x => |F (Coulomb.position x i)| * ‖w.value s x‖^2))
    (u v : Coulomb.H1Vector n) :
    nuclearPerturbedForm V F (u.add v) = nuclearPerturbedForm V F u+nuclearPerturbedForm V F v+
      2*(graphBoundedCross (BoundedPotential.operator V hV D hD) (h1Coordinates u) (h1Coordinates v)+
        nuclearErrorCross F u v) := by
  simp only [nuclearPerturbedForm,boundedPotentialForm_add V hV D hD,
    nuclearErrorEnergy_add F hF hI]
  ring

theorem nuclearPerturbed_coercive_complement {n : ℕ} (hn : 1 ≤ n)
    (V : Configuration n → ℝ) (F : Position → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (q : Coulomb.H1Vector n) (E a g₀ g : ℝ)
    (herror : ∀ s i, (∫ x, |F (Coulomb.position x i)| * ‖q.value s x‖^2) ≤
      B*((∫ x, ‖q.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖q.gradient s (i,k) x‖^2))
    (hgap : g₀*(Coulomb.mass q+2*Coulomb.kinetic q) ≤
      boundedPotentialForm V q-E*Coulomb.mass q)
    (hsmall : B*n+|a|+g ≤ g₀) :
    (E+a)*Coulomb.mass q+g*(Coulomb.mass q+2*Coulomb.kinetic q) ≤
      nuclearPerturbedForm V F q := by
  have he := (abs_le.mp (nuclearErrorEnergy_graph_bound hn F hB q herror)).1
  have hm := Coulomb.mass_nonneg q
  have hk := Coulomb.kinetic_nonneg q
  have hgraph : Coulomb.mass q ≤ Coulomb.mass q+2*Coulomb.kinetic q := by linarith
  have ham := mul_le_mul_of_nonneg_right (le_abs_self a) hm
  have hag := mul_le_mul_of_nonneg_left hgraph (abs_nonneg a)
  have hs := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ Coulomb.mass q+2*Coulomb.kinetic q by positivity)
  unfold nuclearPerturbedForm
  nlinarith only [he,hgap,ham,hag,hs]

theorem nuclearPerturbed_interacting_lower {n : ℕ} (hn : 1 ≤ n)
    (V : Configuration n → ℝ) (hV : Continuous V) (D : ℝ) (hD : ∀ x, |V x| ≤ D)
    (F : Position → ℝ) (hF : Measurable F) (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ (w : Coulomb.H1Vector n) s i,
      Integrable (fun x => |F (Coulomb.position x i)| * ‖w.value s x‖^2) ∧
      (∫ x, |F (Coulomb.position x i)| * ‖w.value s x‖^2) ≤
        B*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2))
    (p q : Coulomb.H1Vector n) (E a g A K t : ℝ)
    (hg : 0 < g) (hA : 0 ≤ A) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hfinite : (E+a)*Coulomb.mass p ≤ nuclearPerturbedForm V F p+t*Coulomb.pairEnergy p)
    (hcomp : (E+a)*Coulomb.mass q+g*(Coulomb.mass q+2*Coulomb.kinetic q) ≤ nuclearPerturbedForm V F q)
    (hkin : Coulomb.kinetic p ≤ K*Coulomb.mass p)
    (hcross : (graphBoundedCross (BoundedPotential.operator V hV D hD)
      (h1Coordinates p) (h1Coordinates q))^2 ≤ A*Coulomb.mass p*Coulomb.mass q) :
    (E+a-3*(A+t^2*(8*(n:ℝ)^3*K)+B^2*((n:ℝ)+2*K)*n)/g)*
      (Coulomb.mass p+Coulomb.mass q) ≤
      nuclearPerturbedForm V F (p.add q)+t*Coulomb.pairEnergy (p.add q) := by
  have hmp := Coulomb.mass_nonneg p
  have hmq := Coulomb.mass_nonneg q
  have hkp0 := Coulomb.kinetic_nonneg p
  have hkq0 := Coulomb.kinetic_nonneg q
  let Q := Coulomb.mass q+2*Coulomb.kinetic q
  have hQ : 0 ≤ Q := add_nonneg (Coulomb.mass_nonneg q) (by positivity)
  have hmQ : Coulomb.mass q ≤ Q := by dsimp [Q]; linarith [Coulomb.kinetic_nonneg q]
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hkp : (n:ℝ)*Coulomb.mass p+2*Coulomb.kinetic p ≤ ((n:ℝ)+2*K)*Coulomb.mass p := by
    nlinarith only [hkin]
  have hkq : (n:ℝ)*Coulomb.mass q+2*Coulomb.kinetic q ≤ (n:ℝ)*Q := by
    have h := mul_le_mul_of_nonneg_right hnR (Coulomb.kinetic_nonneg q)
    dsimp [Q]
    nlinarith only [h]
  have hnuc := nuclearErrorCross_graph_square_bound F hF hB p q herror
  have hnuc' : (nuclearErrorCross F p q)^2 ≤
      (B^2*((n:ℝ)+2*K)*n)*Coulomb.mass p*Q := by
    have h := mul_le_mul hkp hkq
      (add_nonneg (by positivity) (by positivity)) (by positivity)
    have h' := mul_le_mul_of_nonneg_left h (sq_nonneg B)
    apply hnuc.trans
    convert h' using 1 <;> ring
  have hres : (graphBoundedCross (BoundedPotential.operator V hV D hD)
      (h1Coordinates p) (h1Coordinates q))^2 ≤ A*Coulomb.mass p*Q :=
    hcross.trans (mul_le_mul_of_nonneg_left hmQ (mul_nonneg hA (Coulomb.mass_nonneg p)))
  have hrep : (t*repulsionCross p q)^2 ≤ (t^2*(8*(n:ℝ)^3*K))*Coulomb.mass p*Q := by
    have h := (repulsionCross_square_bound p q).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkin (by positivity : 0 ≤ 8*(n:ℝ)^3)) (Coulomb.mass_nonneg q))
    have h' : (repulsionCross p q)^2 ≤ (8*(n:ℝ)^3*K)*Coulomb.mass p*Q := by
      apply h.trans
      nlinarith only [mul_le_mul_of_nonneg_left hmQ
        (show 0 ≤ (8*(n:ℝ)^3*K)*Coulomb.mass p by positivity)]
    have h'' := mul_le_mul_of_nonneg_left h' (sq_nonneg t)
    convert h'' using 1 <;> ring
  have hc := three_mixed_square_bound hres hrep hnuc'
  apply coercive_complement_scalar_lower (a := E+a) (g := g)
    (C := 3*(A+t^2*(8*(n:ℝ)^3*K)+B^2*((n:ℝ)+2*K)*n))
    (P := nuclearPerturbedForm V F p+t*Coulomb.pairEnergy p)
    (Q := nuclearPerturbedForm V F q+t*Coulomb.pairEnergy q)
    (c := graphBoundedCross (BoundedPotential.operator V hV D hD) (h1Coordinates p) (h1Coordinates q)+
      t*repulsionCross p q+nuclearErrorCross F p q)
    (Coulomb.mass_nonneg p) (Coulomb.mass_nonneg q) hQ hg (by positivity) _ hfinite _ hc
  · rw [nuclearPerturbedForm_add V hV D hD F hF (fun w s i => (herror w s i).1),pairEnergy_add]
    ring_nf
    exact le_rfl
  · have h := mul_nonneg ht (Coulomb.pairEnergy_nonneg q)
    linarith only [hcomp,h]

end ContinuumCoulomb

end

end OAI
