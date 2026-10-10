import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalSlaterKinetic

namespace OAI

/-! Spin lifting of real C1 orbitals into the actual fermionic weak-H1
domain. Any injective list of occupied orthonormal spatial/spin modes
gives a normalized antisymmetric state on the full configuration space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def realSpinOrbital (f : Position → ℝ) (σ : Fin 2) (x : Position) (s : Fin 2) : ℂ :=
  if s = σ then (f x : ℂ) else 0

theorem realSpinOrbital_C1 (f : Position → ℝ) (hf : ContDiff ℝ 1 f) (σ s : Fin 2) :
    ContDiff ℝ 1 (fun x => realSpinOrbital f σ x s) := by
  by_cases h : s = σ
  · simpa only [realSpinOrbital, h, ite_true, Function.comp_def, Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hf
  · simpa only [realSpinOrbital, h, ite_false] using (contDiff_const : ContDiff ℝ 1 (fun _ : Position => (0 : ℂ)))

theorem realSpinOrbital_memLp (f : Position → ℝ) (hf : MemLp f 2) (σ s : Fin 2) :
    MemLp (fun x => realSpinOrbital f σ x s) 2 := by
  by_cases h : s = σ
  · simp only [realSpinOrbital, h, ite_true]
    exact hf.ofReal
  · simp only [realSpinOrbital, h, ite_false]
    exact MemLp.zero

theorem realSpinOrbital_fderiv (f : Position → ℝ) (hf : ContDiff ℝ 1 f)
    (σ s : Fin 2) (x e : Position) :
    fderiv ℝ (fun y => realSpinOrbital f σ y s) x e =
      if s = σ then (fderiv ℝ f x e : ℂ) else 0 := by
  by_cases h : s = σ
  · simp only [realSpinOrbital, h, ite_true]
    exact congrArg (fun L : Position →L[ℝ] ℂ => L e)
      (Complex.ofRealCLM.hasFDerivAt.comp x (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv
  · simp [realSpinOrbital, h]

theorem realSpinOrbital_partial_memLp (f : Position → ℝ) (hf : ContDiff ℝ 1 f)
    (hd : ∀ b : Fin 3, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single b 1)) 2)
    (σ s : Fin 2) (b : Fin 3) :
    MemLp (fun x => fderiv ℝ (fun y => realSpinOrbital f σ y s) x (EuclideanSpace.single b 1)) 2 := by
  simp_rw [realSpinOrbital_fderiv f hf]
  by_cases h : s = σ
  · simp only [h, ite_true]
    exact (hd b).ofReal
  · simp only [h, ite_false]
    exact MemLp.zero

theorem realSpinOrbital_inner (f g : Position → ℝ) (σ τ : Fin 2) :
    (∑ s : Fin 2, ∫ x, star (realSpinOrbital f σ x s) * realSpinOrbital g τ x s) =
      if σ = τ then (↑(∫ x, f x * g x) : ℂ) else 0 := by
  by_cases h : σ = τ
  · subst τ
    have hp (s : Fin 2) :
        (∫ x, star (realSpinOrbital f σ x s) * realSpinOrbital g σ x s) =
          if s=σ then (↑(∫ x, f x*g x) : ℂ) else 0 := by
      by_cases hs : s=σ
      · subst s
        simp only [realSpinOrbital, ite_true, Complex.star_def, Complex.conj_ofReal,
          ← Complex.ofReal_mul, integral_complex_ofReal]
      · simp [realSpinOrbital, hs]
    simp only [hp, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · have hz (s : Fin 2) (x : Position) : star (realSpinOrbital f σ x s) * realSpinOrbital g τ x s = 0 := by
      by_cases hs : s = σ
      · subst s
        simp [realSpinOrbital, h]
      · simp [realSpinOrbital, hs]
    simp only [hz, integral_zero, Finset.sum_const_zero, h, ite_false]

theorem selectedRealSpinOrbitals_orthonormal {α : Type*} {n : ℕ}
    (f : α → Position → ℝ)
    (ho : ∀ i j, (∫ x, f i x * f j x) = if i = j then (1 : ℝ) else 0)
    (p : Fin n → α × Fin 2) (hp : Function.Injective p) (i j : Fin n) :
    (∑ s : Fin 2, ∫ x, star (realSpinOrbital (f (p i).1) (p i).2 x s) *
      realSpinOrbital (f (p j).1) (p j).2 x s) = if i = j then (1 : ℂ) else 0 := by
  classical
  rw [realSpinOrbital_inner, ho]
  by_cases hij : i = j
  · subst j
    simp
  · by_cases hs : (p i).2 = (p j).2
    · have hf : (p i).1 ≠ (p j).1 := by
        intro hf
        exact hij (hp (Prod.ext hf hs))
      simp only [hs, hf, hij, ite_true, ite_false, Complex.ofReal_zero]
    · simp only [hs, hij, ite_false]

def selectedRealSlaterState {α : Type*} {n : ℕ} (f : α → Position → ℝ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hL2 : ∀ i, MemLp (f i) 2)
    (hd : ∀ i b, MemLp (fun x => fderiv ℝ (f i) x (EuclideanSpace.single b 1)) 2)
    (p : Fin n → α × Fin 2) : Coulomb.H1Vector n :=
  classicalSlaterState (fun i => realSpinOrbital (f (p i).1) (p i).2)
    (fun i s => realSpinOrbital_C1 _ (hf (p i).1) _ s)
    (fun i s => realSpinOrbital_memLp _ (hL2 (p i).1) _ s)
    (fun i s b => realSpinOrbital_partial_memLp _ (hf (p i).1) (hd (p i).1) _ s b)

theorem selectedRealSlaterState_antisymmetric {α : Type*} {n : ℕ}
    (f : α → Position → ℝ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (hL2 : ∀ i, MemLp (f i) 2)
    (hd : ∀ i b, MemLp (fun x => fderiv ℝ (f i) x (EuclideanSpace.single b 1)) 2)
    (p : Fin n → α × Fin 2) : Coulomb.Antisymmetric (selectedRealSlaterState f hf hL2 hd p) :=
  classicalSlaterState_antisymmetric _ _ _ _

theorem selectedRealSlaterState_normalized {α : Type*} {n : ℕ}
    (f : α → Position → ℝ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (hL2 : ∀ i, MemLp (f i) 2)
    (hd : ∀ i b, MemLp (fun x => fderiv ℝ (f i) x (EuclideanSpace.single b 1)) 2)
    (ho : ∀ i j, (∫ x, f i x * f j x) = if i = j then (1 : ℝ) else 0)
    (p : Fin n → α × Fin 2) (hp : Function.Injective p) :
    Coulomb.mass (selectedRealSlaterState f hf hL2 hd p) = 1 :=
  classicalSlaterState_normalized _ _ _ _ (selectedRealSpinOrbitals_orthonormal f ho p hp)

end ContinuumCoulomb

end

end OAI
