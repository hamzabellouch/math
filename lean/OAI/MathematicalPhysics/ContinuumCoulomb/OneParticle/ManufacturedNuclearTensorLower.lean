import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedTensorDiagonal
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorVariationalLower
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearPerturbedComplement

namespace OAI

/-! Singular nuclear perturbations of the actual manufactured tensor projection.
The differential residual and kinetic bounds are discharged from the orbitals. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem manufacturedTensor_nuclear_interacting_lower
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq η D R ε : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H)
    (hfreq : 1 ≤ freq) (hrelation : freq^2 = 4*Real.pi*rho)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) (hscale : 0 ≤ scale) {m n : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hD : 2 ≤ D) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η)
    (hε : 0 ≤ ε)
    (herr : (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j,
      manufacturedOrbitalSquaredError rho H S freq η D R u j) ≤ ε^2)
    (F : Position → ℝ) (hF : Measurable F) (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ (z : Coulomb.H1Vector (n+1)) s i,
      Integrable (fun x => |F (Coulomb.position x i)| * ‖z.value s x‖^2) ∧
      (∫ x, |F (Coulomb.position x i)| * ‖z.value s x‖^2) ≤
        B*((∫ x, ‖z.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖z.gradient s (i,k) x‖^2))
    (w : Coulomb.H1Vector (n+1)) (a g t : ℝ) (hg : 0 < g) (ht : 0 ≤ t) :
    let hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
    let p : Coulomb.H1Vector (n+1) := finiteTensorProjection (localizedSpinMode freq u)
      (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
      (localizedSpinMode_partial_memLp hf u) w
    let q : Coulomb.H1Vector (n+1) := w.add (Coulomb.H1Vector.scale (-1) p)
    let V : Configuration (n+1) → ℝ := fun x => ∑ i,
      manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
    let E : ℝ := (n+1:ℝ)*((-1/2:ℝ)+freq/2)
    let K : ℝ := (n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
      ((-1/2:ℝ)+freq/2))+ε
    (E+a)*Coulomb.mass p ≤ nuclearPerturbedForm V F p+t*Coulomb.pairEnergy p →
    (E+a)*Coulomb.mass q+g*(Coulomb.mass q+2*Coulomb.kinetic q) ≤ nuclearPerturbedForm V F q →
    (E+a-3*(ε^2+t^2*(8*(n+1:ℝ)^3*K)+B^2*((n+1:ℝ)+2*K)*(n+1))/g)*Coulomb.mass w ≤
      nuclearPerturbedForm V F w+t*Coulomb.pairEnergy w := by
  let hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  let p : Coulomb.H1Vector (n+1) := finiteTensorProjection (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) w
  let q : Coulomb.H1Vector (n+1) := w.add (Coulomb.H1Vector.scale (-1) p)
  let V : Configuration (n+1) → ℝ := fun x => ∑ i,
    manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
  let E : ℝ := (n+1:ℝ)*((-1/2:ℝ)+freq/2)
  let K : ℝ := (n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
    ((-1/2:ℝ)+freq/2))+ε
  change (E+a)*Coulomb.mass p ≤ nuclearPerturbedForm V F p+t*Coulomb.pairEnergy p →
    (E+a)*Coulomb.mass q+g*(Coulomb.mass q+2*Coulomb.kinetic q) ≤ nuclearPerturbedForm V F q → _
  intro hfinite hcomp
  have hV : Continuous V := continuous_finsetSum _ (fun i _ =>
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u).comp
      (Coulomb.positionCLM i).continuous)
  obtain ⟨Vbound,hVbound⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hsum (x : Configuration (n+1)) : |V x| ≤ (n+1:ℝ)*Vbound := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one] using Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => hVbound (Coulomb.position x i))
  have hc := manufacturedTensorProjection_mixed_square_bound hdensity hrho hH hS hf hrelation
    hR hRH hRS scale u hsep hs hη hcoeff ((n+1:ℝ)*Vbound) hsum w
  have hc' : (graphBoundedCross (BoundedPotential.operator V hV _ hsum)
      (h1Coordinates p) (h1Coordinates q))^2 ≤ ε^2*Coulomb.mass p*Coulomb.mass q :=
    hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right herr (Coulomb.mass_nonneg p)) (Coulomb.mass_nonneg q))
  have hk : Coulomb.kinetic p ≤ K*Coulomb.mass p :=
    localizedTensorState_kinetic_bound hdensity hrho hH hS hSH hf hrelation hR hRH hRS
      scale hscale u hD hsep hs hη hcoeff hε herr (Coulomb.orbitalCoefficient w (localizedSpinMode freq u))
  have hK : 0 ≤ K := by
    have he : 0 ≤ (-1/2:ℝ)+freq/2 := by linarith only [hfreq]
    have hw := PlanarSobolev.wellBound_nonnegative
    dsimp only [K]
    positivity
  have he := nuclearPerturbed_interacting_lower (show 1 ≤ n+1 by omega)
    V hV _ hsum F hF B hB herror p q E a g (ε^2) K t hg (sq_nonneg ε) hK ht
    hfinite hcomp hk hc'
  have hpq : p.add q = w := finiteTensorProjection_add_remainder
    (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) w
  have hm : Coulomb.mass w = Coulomb.mass p+Coulomb.mass q :=
    finiteTensorProjection_mass_decomposition (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) (fun i j => by
        have h := localizedSpinMode_inner hf u hsep hs i j
        by_cases hij : i=j <;> simpa only [hij,ite_true,ite_false] using h) w
  rw [hpq,← hm] at he
  simpa only [E,K,V,Nat.cast_add,Nat.cast_one] using he

end ContinuumCoulomb

end

end OAI
