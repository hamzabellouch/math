import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalSlater
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SlaterOccupation
import OAI.Analysis.CoulombRadii.FieldAnalysis.TsumFixed

namespace OAI

/-! Arbitrary complex occupation amplitudes give actual antisymmetric
weak-H1 continuum states. Their continuum mass equals the finite Fock norm,
so this construction treats every state of the fixed-particle mode space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open SlaterOccupation

def selectedSpatialSpinOrbitals {Q n : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (S : Occupied Q n) : Fin n → Position → Fin 2 → ℂ :=
  fun i => v (selection S i)

def slaterSynthesisValue {Q n : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (c : EuclideanSpace ℂ (Occupied Q n)) (s : SpinConfiguration n) (x : Configuration n) : ℂ :=
  ∑ S, c S * Coulomb.slaterConfiguration (selectedSpatialSpinOrbitals v S) s x

theorem slaterSynthesisValue_C1 {Q n : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ 1 (fun x => v i x s))
    (c : EuclideanSpace ℂ (Occupied Q n)) (s : SpinConfiguration n) :
    ContDiff ℝ 1 (slaterSynthesisValue v c s) :=
  ContDiff.sum (fun S _ => contDiff_const.mul
    (slaterConfiguration_C1 (selectedSpatialSpinOrbitals v S) (fun i s => hv (selection S i) s) s))

theorem slaterSynthesisValue_memLp {Q n : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hL2 : ∀ i s, MemLp (fun x => v i x s) 2)
    (c : EuclideanSpace ℂ (Occupied Q n)) (s : SpinConfiguration n) :
    MemLp (slaterSynthesisValue v c s) 2 := by
  have ht (S : Occupied Q n) : MemLp (fun x =>
      c S * Coulomb.slaterConfiguration (selectedSpatialSpinOrbitals v S) s x) 2 volume :=
    (slaterConfiguration_memLp (selectedSpatialSpinOrbitals v S)
      (fun i s => hL2 (selection S i) s) s).const_mul (c S)
  exact memLp_finsetSum Finset.univ (fun S _ => ht S)

theorem slaterSynthesisValue_fderiv {Q n : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ 1 (fun x => v i x s))
    (c : EuclideanSpace ℂ (Occupied Q n)) (s : SpinConfiguration n) (x e : Configuration n) :
    fderiv ℝ (slaterSynthesisValue v c s) x e =
      ∑ S, c S * fderiv ℝ (Coulomb.slaterConfiguration (selectedSpatialSpinOrbitals v S) s) x e := by
  have hd (S : Occupied Q n) :
      DifferentiableAt ℝ (Coulomb.slaterConfiguration (selectedSpatialSpinOrbitals v S) s) x :=
    (slaterConfiguration_C1 _ (fun i s => hv (selection S i) s) s).differentiable (by norm_num) x
  unfold slaterSynthesisValue
  rw [fderiv_fun_sum (fun S _ => (hd S).const_mul (c S))]
  simp only [sum_apply, fderiv_const_mul (hd _), smul_apply, smul_eq_mul]

theorem slaterSynthesisValue_partial_memLp {Q n : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ 1 (fun x => v i x s))
    (hL2 : ∀ i s, MemLp (fun x => v i x s) 2)
    (hpartial : ∀ i s b, MemLp (fun x => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)) 2)
    (c : EuclideanSpace ℂ (Occupied Q n)) (s : SpinConfiguration n) (a : Fin n × Fin 3) :
    MemLp (fun x => fderiv ℝ (slaterSynthesisValue v c s) x (EuclideanSpace.single a 1)) 2 := by
  have ht (S : Occupied Q n) : MemLp (fun x => c S *
      fderiv ℝ (Coulomb.slaterConfiguration (selectedSpatialSpinOrbitals v S) s) x
        (EuclideanSpace.single a 1)) 2 volume :=
    (slaterConfiguration_partial_memLp _ (fun i s => hv (selection S i) s)
      (fun i s => hL2 (selection S i) s) (fun i s b => hpartial (selection S i) s b) s a.1 a.2).const_mul (c S)
  have hs : MemLp (fun x => ∑ S, c S *
      fderiv ℝ (Coulomb.slaterConfiguration (selectedSpatialSpinOrbitals v S) s) x
        (EuclideanSpace.single a 1)) 2 volume :=
    memLp_finsetSum Finset.univ (fun S _ => ht S)
  simpa only [slaterSynthesisValue_fderiv v hv] using hs

def classicalSlaterSynthesis {Q n : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ 1 (fun x => v i x s))
    (hL2 : ∀ i s, MemLp (fun x => v i x s) 2)
    (hpartial : ∀ i s b, MemLp (fun x => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)) 2)
    (c : EuclideanSpace ℂ (Occupied Q n)) : Coulomb.H1Vector n :=
  classicalH1State (slaterSynthesisValue v c) (slaterSynthesisValue_C1 v hv c)
    (slaterSynthesisValue_memLp v hL2 c) (slaterSynthesisValue_partial_memLp v hv hL2 hpartial c)

theorem slaterConfiguration_permute {n : ℕ} (v : Fin n → Position → Fin 2 → ℂ)
    (p : Equiv.Perm (Fin n)) (s : SpinConfiguration n) (x : Configuration n) :
    Coulomb.slaterConfiguration v (s ∘ p) (Coulomb.permute p x) =
      (((p.sign : ℤ) : ℂ)) * Coulomb.slaterConfiguration v s x := by
  have he : (fun i => ((s ∘ p) i, Coulomb.position (Coulomb.permute p x) i)) =
      (fun i => (s i, Coulomb.position x i)) ∘ p := by
    funext i
    simp only [Function.comp_apply, Coulomb.position_permute]
  simp only [Coulomb.slaterConfiguration, Coulomb.slaterWave, he, Coulomb.determinantWave_permute]
  ring

theorem classicalSlaterSynthesis_antisymmetric {Q n : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ 1 (fun x => v i x s))
    (hL2 : ∀ i s, MemLp (fun x => v i x s) 2)
    (hpartial : ∀ i s b, MemLp (fun x => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)) 2)
    (c : EuclideanSpace ℂ (Occupied Q n)) :
    Coulomb.Antisymmetric (classicalSlaterSynthesis v hv hL2 hpartial c) := by
  intro p s
  filter_upwards [] with x
  change slaterSynthesisValue v c (s ∘ p) (Coulomb.permute p x) = _ * slaterSynthesisValue v c s x
  unfold slaterSynthesisValue
  simp only [slaterConfiguration_permute, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem classicalSlaterSynthesis_cubeState {Q n : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ 1 (fun x => v i x s))
    (hL2 : ∀ i s, MemLp (fun x => v i x s) 2)
    (hpartial : ∀ i s b, MemLp (fun x => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)) 2)
    (c : EuclideanSpace ℂ (Occupied Q n)) (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
    Coulomb.cubeState (classicalSlaterSynthesis v hv hL2 hpartial c) z =
      ∑ S, c S * wave (fun i => Coulomb.flatSpinOrbital (v i)) S z := rfl

theorem classicalSlaterSynthesis_mass {Q n : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ 1 (fun x => v i x s))
    (hL2 : ∀ i s, MemLp (fun x => v i x s) 2)
    (hpartial : ∀ i s b, MemLp (fun x => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)) 2)
    (ho : ∀ i j, (∑ s : Fin 2, ∫ x, star (v i x s) * v j x s) = if i=j then (1 : ℂ) else 0)
    (c : EuclideanSpace ℂ (Occupied Q n)) :
    Coulomb.mass (classicalSlaterSynthesis v hv hL2 hpartial c) = ‖c‖^2 := by
  have hV (i : Fin (Q+1)) : MemLp (Coulomb.flatSpinOrbital (v i)) 2 Coulomb.spinSpaceMeasure :=
    Coulomb.flatSpinOrbital_memLp (v i) (hL2 i)
  have hO (i j : Fin (Q+1)) : (∫ a, star (Coulomb.flatSpinOrbital (v i) a) *
      Coulomb.flatSpinOrbital (v j) a ∂Coulomb.spinSpaceMeasure) = if i=j then (1 : ℂ) else 0 := by
    rw [Coulomb.flatSpinOrbital_inner (v i) (v j) (hL2 i) (hL2 j)]
    exact ho i j
  rw [← Coulomb.cubeState_full_mass]
  simp only [classicalSlaterSynthesis_cubeState]
  have h := Coulomb.orbital_sum_sq (fun S : Occupied Q n => wave (fun i => Coulomb.flatSpinOrbital (v i)) S)
    (wave_memLp _ hV) (by
      intro S T
      by_cases h : S=T
      · simpa only [h, ite_true] using wave_overlap _ hV hO S T
      · simpa only [h, ite_false] using wave_overlap _ hV hO S T)
    Finset.univ (fun S => c S)
  simpa only [EuclideanSpace.norm_sq_eq] using h

end ContinuumCoulomb

end

end OAI
