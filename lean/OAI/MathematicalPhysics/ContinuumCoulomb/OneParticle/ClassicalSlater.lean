import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalTensor

namespace OAI

/-! Finite Slater determinants of C1 decaying orbitals are actual spinful
antisymmetric weak-H1 states. Orthonormal orbitals give unit mass on the
full continuum configuration space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem slaterConfiguration_C1 {n : ℕ} (v : Fin n → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s)) (s : SpinConfiguration n) :
    ContDiff ℝ 1 (Coulomb.slaterConfiguration v s) := by
  rw [Coulomb.slaterConfiguration_expansion]
  apply contDiff_const.mul
  exact ContDiff.sum (fun p _ => contDiff_const.mul (tensorOrbital_C1 v hv p s))

theorem slaterConfiguration_memLp {n : ℕ} (v : Fin n → Position → Fin 2 → ℂ)
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2) (s : SpinConfiguration n) :
    MemLp (Coulomb.slaterConfiguration v s) 2 := by
  have ht (p : Equiv.Perm (Fin n)) : MemLp
      (fun x => (((p.sign : ℤ) : ℂ)) * Coulomb.tensorOrbital v p s x) 2 volume :=
    (Coulomb.tensorOrbital_memLp v hL2 p s).const_mul _
  have hs : MemLp (fun x => ∑ p : Equiv.Perm (Fin n),
      (((p.sign : ℤ) : ℂ)) * Coulomb.tensorOrbital v p s x) 2 volume :=
    memLp_finsetSum Finset.univ (fun p _ => ht p)
  have hc : MemLp (fun x => (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
      ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) * Coulomb.tensorOrbital v p s x) 2 volume :=
    hs.const_mul _
  simpa only [Coulomb.slaterConfiguration_expansion] using hc

theorem slaterConfiguration_partial_memLp {n : ℕ} (v : Fin n → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1)) 2)
    (s : SpinConfiguration n) (i : Fin n) (b : Fin 3) :
    MemLp (fun x => fderiv ℝ (Coulomb.slaterConfiguration v s) x (EuclideanSpace.single (i,b) 1)) 2 := by
  have ht (p : Equiv.Perm (Fin n)) (x : Configuration n) :
      DifferentiableAt ℝ (Coulomb.tensorOrbital v p s) x := (tensorOrbital_C1 v hv p s).differentiable (by norm_num) x
  have he (x : Configuration n) :
      fderiv ℝ (Coulomb.slaterConfiguration v s) x (EuclideanSpace.single (i,b) 1) =
      (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
        ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) *
          fderiv ℝ (Coulomb.tensorOrbital v p s) x (EuclideanSpace.single (i,b) 1) := by
    rw [Coulomb.slaterConfiguration_expansion, fderiv_const_mul
      (DifferentiableAt.fun_sum (fun p _ => (ht p x).const_mul _)),
      fderiv_fun_sum (fun p _ => (ht p x).const_mul _)]
    simp only [smul_apply, smul_eq_mul, sum_apply, fderiv_const_mul (ht _ x)]
  have htL (p : Equiv.Perm (Fin n)) : MemLp (fun x => (((p.sign : ℤ) : ℂ)) *
      fderiv ℝ (Coulomb.tensorOrbital v p s) x (EuclideanSpace.single (i,b) 1)) 2 volume :=
    (tensorOrbital_partial_memLp v hv hL2 hpartial p s i b).const_mul _
  have hs : MemLp (fun x => ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) *
      fderiv ℝ (Coulomb.tensorOrbital v p s) x (EuclideanSpace.single (i,b) 1)) 2 volume :=
    memLp_finsetSum Finset.univ (fun p _ => htL p)
  have hc : MemLp (fun x => (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
      ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) *
        fderiv ℝ (Coulomb.tensorOrbital v p s) x (EuclideanSpace.single (i,b) 1)) 2 volume :=
    hs.const_mul _
  simpa only [he] using hc

def classicalSlaterState {n : ℕ} (v : Fin n → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1)) 2) :
    Coulomb.H1Vector n :=
  classicalH1State (Coulomb.slaterConfiguration v) (slaterConfiguration_C1 v hv)
    (slaterConfiguration_memLp v hL2) (fun s a => slaterConfiguration_partial_memLp v hv hL2 hpartial s a.1 a.2)

theorem classicalSlaterState_antisymmetric {n : ℕ} (v : Fin n → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1)) 2) :
    Coulomb.Antisymmetric (classicalSlaterState v hv hL2 hpartial) := by
  intro p s
  filter_upwards [] with x
  change Coulomb.slaterConfiguration v (s ∘ p) (Coulomb.permute p x) = _ * Coulomb.slaterConfiguration v s x
  have he : (fun i => ((s ∘ p) i, Coulomb.position (Coulomb.permute p x) i)) =
      (fun i => (s i, Coulomb.position x i)) ∘ p := by
    funext i
    simp only [Function.comp_apply, Coulomb.position_permute]
  simp only [Coulomb.slaterConfiguration, Coulomb.slaterWave, he, Coulomb.determinantWave_permute]
  ring

theorem classicalSlaterState_normalized {n : ℕ} (v : Fin n → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1)) 2)
    (ho : ∀ i j, (∑ s : Fin 2, ∫ x : Position, star (v i x s) * v j x s) =
      if i = j then (1 : ℂ) else 0) : Coulomb.mass (classicalSlaterState v hv hL2 hpartial) = 1 := by
  rw [← Coulomb.cubeState_full_mass]
  change (∫ x, ‖Coulomb.slaterWave (fun i => Coulomb.flatSpinOrbital (v i)) x‖ ^ 2
    ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) = 1
  apply Coulomb.slaterWave_normalized (fun i => Coulomb.flatSpinOrbital (v i))
    (fun i => Coulomb.flatSpinOrbital_memLp (v i) (hL2 i))
  intro i j
  rw [Coulomb.flatSpinOrbital_inner (v i) (v j) (hL2 i) (hL2 j)]
  exact ho i j

end ContinuumCoulomb

end

end OAI
