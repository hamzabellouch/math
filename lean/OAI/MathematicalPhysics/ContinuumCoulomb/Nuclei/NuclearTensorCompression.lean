import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockOneBodyIntegral
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.WeightedNuclearForm
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.FullSpinTensorCoefficients

namespace OAI

/-! The singular nuclear form of the full spinful finite tensor state is
the actual finite CAR one-body form, including every spin component. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem nuclearErrorEnergy_cube {n : ℕ} (F : Position → ℝ) (u : Coulomb.H1Vector n)
    (hI : ∀ s i, Integrable (fun x => F (Coulomb.position x i)*‖u.value s x‖^2)) :
    (nuclearErrorEnergy F u : ℂ) =
      ∫ z, (∑ i, (F (WithLp.toLp 2 (z i).2) : ℂ))*
        (star (Coulomb.cubeState u z)*Coulomb.cubeState u z)
        ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure) := by
  have hn (z : ℂ) : ((‖z‖^2:ℝ):ℂ) = star z*z := by
    simpa only [starRingEnd_apply,Complex.ofReal_pow] using (Complex.conj_mul' z).symm
  have h := spinConfiguration_complex_integral
    (fun s x => ((∑ i, F (Coulomb.position x i)*‖u.value s x‖^2 : ℝ):ℂ))
    (fun s => (integrable_finsetSum Finset.univ (fun i _ => hI s i)).ofReal)
  have he (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
      ((∑ i, F (Coulomb.position (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2) i)*
          ‖u.value ((Coulomb.spinCubeEquiv n) z).1
            (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2)‖^2 : ℝ):ℂ) =
        (∑ i, (F (WithLp.toLp 2 (z i).2) : ℂ))*
          (star (Coulomb.cubeState u z)*Coulomb.cubeState u z) := by
    simp only [Complex.ofReal_sum,Complex.ofReal_mul,hn,Finset.sum_mul]
    rfl
  simp_rw [he] at h
  rw [h]
  simp only [integral_complex_ofReal,← Complex.ofReal_sum]
  congr 1
  unfold nuclearErrorEnergy
  apply Finset.sum_congr rfl
  intro s _
  exact (integral_finsetSum Finset.univ (fun i _ => hI s i)).symm

theorem finiteTensorState_cubeState {n Q : ℕ}
    (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (c : Laughlin.State n Q) (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
    Coulomb.cubeState (finiteTensorState v hv hL2 hpartial c) z =
      FockSlaterTensor.tensorValue (fun a => Coulomb.flatSpinOrbital (v a)) c z := rfl

theorem finiteTensorState_nuclear_compression {n Q : ℕ}
    (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (c : Laughlin.State (n+1) Q) (hc : Laughlin.Antisymmetric c) (F : Position → ℝ)
    (hentry : ∀ a b, Integrable (fun z : Fin 2 × (Fin 3 → ℝ) =>
      (F (WithLp.toLp 2 z.2) : ℂ)*
        (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z))
        Coulomb.spinSpaceMeasure)
    (hI : ∀ s i, Integrable (fun x => F (Coulomb.position x i)*
      ‖(finiteTensorState v hv hL2 hpartial c).value s x‖^2)) :
    (nuclearErrorEnergy F (finiteTensorState v hv hL2 hpartial c) : ℂ) =
      Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+1) Q c)
        (HubbardGlobal.oneBodyOperator (fun a b =>
          ∫ z : Fin 2 × (Fin 3 → ℝ), (F (WithLp.toLp 2 z.2) : ℂ)*
            (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z)
            ∂Coulomb.spinSpaceMeasure)
          (Laughlin.Fock.normalizedTensorExterior (n+1) Q c)) := by
  rw [nuclearErrorEnergy_cube F _ hI]
  simp_rw [finiteTensorState_cubeState]
  apply FockOneBodyIntegral.tensorValue_oneBody_integral _
    (fun a => Coulomb.flatSpinOrbital_memLp (v a) (hL2 a)) _ _ hentry c c hc hc
  intro a b
  rw [Coulomb.flatSpinOrbital_inner _ _ (hL2 a) (hL2 b)]
  exact ho a b

end ContinuumCoulomb

end

end OAI
