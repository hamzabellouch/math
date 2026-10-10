import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorComplementBound
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalBasisExtension

namespace OAI

/-! The complement occupation bound for a finite family requires no choice
of ambient basis in its statement. The auxiliary basis is constructed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finite_orbital_complement_bound {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [SecondCountableTopology (Lp ℂ 2 μ)] {m n : ℕ}
    (v : Fin m → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ x, star (v i x)*v j x ∂μ) = if i=j then (1:ℂ) else 0)
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : Coulomb.ProductAntisymmetric (μ := μ) f)
    (hzero : ∀ b : Fin (n+1) → Fin m, Coulomb.scalarCoefficient (μ := μ) f v b = 0) :
    (n+1:ℕ)*(∑ a, ∫ y, ‖Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f) y‖^2
      ∂(Measure.pi fun _ : Fin n => μ)) ≤
      (n:ℝ)*(∫ x, ‖f x‖^2 ∂(Measure.pi fun _ : Fin (n+1) => μ)) := by
  obtain ⟨J,b,e,hJ,he⟩ := finite_orbitals_basis_extension
    (fun i => (hv i).toLp (v i)) (Coulomb.orbital_orthonormal v hv (by
      intro i j
      by_cases hij : i=j <;> simpa only [hij,ite_true,ite_false] using ho i j))
  let : Countable J := hJ
  let w (j : J) : A → ℂ := b j
  have hw (j : J) : MemLp (w j) 2 μ := Lp.memLp (b j)
  have hwo (i j : J) : (∫ x, star (w i x)*w j x ∂μ) = if i=j then (1:ℂ) else 0 := by
    calc
      _ = inner ℂ (b i) (b j) := by
        simpa only [w,Lp.toLp_coeFn] using (Coulomb.inner_toLp_complex (hw i) (hw j)).symm
      _ = _ := (orthonormal_iff_ite.mp b.orthonormal) i j
  have hwc : Coulomb.CompleteOrbitals μ w := Coulomb.HilbertBasis_completeOrbitals b
  have heq (i : Fin m) : w (e i) =ᵐ[μ] v i := by
    change (b (e i) : A → ℂ) =ᵐ[μ] v i
    rw [he i]
    exact (hv i).coeFn_toLp
  let T := Finset.univ.image e
  have hz (q : Fin (n+1) → J) (hq : ∀ i, q i ∈ T) :
      Coulomb.scalarCoefficient (μ := μ) f w q = 0 := by
    have hpre (i : Fin (n+1)) : ∃ j, e j = q i := by
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (hq i)
      exact ⟨j,hj⟩
    choose a ha' using hpre
    have hcoeff : Coulomb.scalarCoefficient (μ := μ) f w q =
        Coulomb.scalarCoefficient (μ := μ) f v a := by
      unfold Coulomb.scalarCoefficient
      apply integral_congr_ae
      have hp := Measure.ae_eq_pi (μ := fun _ : Fin (n+1) => μ)
        (fun i => show w (q i) =ᵐ[μ] v (a i) by rw [← ha' i]; exact heq (a i))
      filter_upwards [hp] with x hx
      congr 2
      apply Finset.prod_congr rfl
      intro i _
      exact congrFun hx i
    rw [hcoeff,hzero a]
  have h := first_fiber_complement_bound w hw (by
    intro i j
    by_cases hij : i=j <;> simpa only [hij,ite_true,ite_false] using hwo i j) hwc f hf ha T hz
  have hfiber (a : Fin m) (y : Fin n → A) :
      Coulomb.fiberContract (μ := μ) (w (e a)) (Coulomb.firstFiber f) y =
      Coulomb.fiberContract (μ := μ) (v a) (Coulomb.firstFiber f) y := by
    unfold Coulomb.fiberContract
    apply integral_congr_ae
    filter_upwards [heq a] with x hx
    rw [hx]
  dsimp [T] at h
  rw [Finset.sum_image e.injective.injOn] at h
  simpa only [hfiber] using h

end ContinuumCoulomb

end

end OAI
