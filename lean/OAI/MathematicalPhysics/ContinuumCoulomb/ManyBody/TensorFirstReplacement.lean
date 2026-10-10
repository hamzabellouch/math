import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedCrossBound
import OAI.Analysis.CoulombRadii.FormDomain.OrbitalHilbertBasis
import OAI.Analysis.CoulombRadii.FieldAnalysis.TsumFixed

namespace OAI

/-! Replacing one orbital in a finite tensor expansion costs the squared
L2 size of the replacement family, without an exponential dimension factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def tensorCoefficientSlice {A ι : Type*} [Fintype ι] {n : ℕ}
    (v : ι → A → ℂ) (c : ι → (Fin n → ι) → ℂ) (a : ι) (y : Fin n → A) : ℂ :=
  ∑ b, c a b*(∏ i, v (b i) (y i))

def tensorFirstReplacement {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : ι → (Fin n → ι) → ℂ) (z : (Fin n → A) × A) : ℂ :=
  ∑ a, tensorCoefficientSlice v c a z.1*r a z.2

theorem tensorCoefficientSlice_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ)
    (c : ι → (Fin n → ι) → ℂ) (a : ι) :
    MemLp (tensorCoefficientSlice v c a) 2 (Measure.pi fun _ : Fin n => μ) := by
  unfold tensorCoefficientSlice
  exact memLp_finsetSum Finset.univ (fun b _ =>
    (Coulomb.scalarTensor_memLp v hv b).const_mul (c a b))

theorem tensorCoefficientSlice_norm {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (c : ι → (Fin n → ι) → ℂ) (a : ι) :
    (∫ y, ‖tensorCoefficientSlice v c a y‖^2 ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ b, ‖c a b‖^2 := by
  have ht : ∀ b : Fin n → ι,
      MemLp (fun y : Fin n → A => ∏ i, v (b i) (y i)) 2
        (Measure.pi fun _ : Fin n => μ) :=
    Coulomb.scalarTensor_memLp (μ := μ) v hv
  simpa only [tensorCoefficientSlice] using
    (Coulomb.orbital_sum_sq (μ := Measure.pi fun _ : Fin n => μ)
      (fun (b : Fin n → ι) (y : Fin n → A) => ∏ i, v (b i) (y i)) ht
      (fun b d => by
        have h := Coulomb.scalarTensor_orthonormal (μ := μ) v ho b d
        by_cases hd : b=d <;> simpa only [hd,ite_true,ite_false] using h)
      Finset.univ (c a))

theorem tensorFirstReplacement_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (c : ι → (Fin n → ι) → ℂ) :
    MemLp (tensorFirstReplacement v r c) 2 ((Measure.pi fun _ : Fin n => μ).prod μ) := by
  unfold tensorFirstReplacement
  exact memLp_finsetSum Finset.univ (fun a _ =>
    Coulomb.tensorPair_memLp (tensorCoefficientSlice_memLp v hv c a) (hr a))

theorem tensorFirstReplacement_pointwise {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : ι → (Fin n → ι) → ℂ) (z : (Fin n → A) × A) :
    ‖tensorFirstReplacement v r c z‖^2 ≤
      (∑ a, ‖tensorCoefficientSlice v c a z.1‖^2)*(∑ a, ‖r a z.2‖^2) := by
  have ht : ‖tensorFirstReplacement v r c z‖ ≤
      ∑ a, ‖tensorCoefficientSlice v c a z.1‖*‖r a z.2‖ := by
    simpa only [tensorFirstReplacement,norm_mul] using norm_sum_le Finset.univ
      (fun a => tensorCoefficientSlice v c a z.1*r a z.2)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _)

theorem tensorFirstReplacement_L2_bound {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (c : ι → (Fin n → ι) → ℂ) :
    (∫ z, ‖tensorFirstReplacement v r c z‖^2 ∂((Measure.pi fun _ : Fin n => μ).prod μ)) ≤
      (∑ a, ∫ x, ‖r a x‖^2 ∂μ)*(∑ a, ∑ b, ‖c a b‖^2) := by
  have hG : Integrable (fun y => ∑ a, ‖tensorCoefficientSlice v c a y‖^2)
      (Measure.pi fun _ : Fin n => μ) :=
    integrable_finsetSum _ (fun a _ => (tensorCoefficientSlice_memLp v hv c a).norm.integrable_sq)
  have hR : Integrable (fun x => ∑ a, ‖r a x‖^2) μ :=
    integrable_finsetSum _ (fun a _ => (hr a).norm.integrable_sq)
  calc
    _ ≤ ∫ z, (∑ a, ‖tensorCoefficientSlice v c a z.1‖^2)*(∑ a, ‖r a z.2‖^2)
        ∂((Measure.pi fun _ : Fin n => μ).prod μ) :=
      integral_mono (tensorFirstReplacement_memLp v r hv hr c).norm.integrable_sq
        (hG.mul_prod hR) (tensorFirstReplacement_pointwise v r c)
    _ = (∫ y, ∑ a, ‖tensorCoefficientSlice v c a y‖^2 ∂(Measure.pi fun _ : Fin n => μ))*
        (∫ x, ∑ a, ‖r a x‖^2 ∂μ) :=
      integral_prod_mul (μ := Measure.pi fun _ : Fin n => μ) (ν := μ)
        (fun y => ∑ a, ‖tensorCoefficientSlice v c a y‖^2)
        (fun x => ∑ a, ‖r a x‖^2)
    _ = _ := by
      rw [integral_finsetSum _ (fun a _ => (tensorCoefficientSlice_memLp v hv c a).norm.integrable_sq),
        integral_finsetSum _ (fun a _ => (hr a).norm.integrable_sq)]
      simp only [tensorCoefficientSlice_norm v hv ho c]
      ring

theorem sum_cons_coefficient_norm {ι : Type*} [Fintype ι] {n : ℕ}
    (c : (Fin (n+1) → ι) → ℂ) :
    (∑ a, ∑ b : Fin n → ι, ‖c (Fin.cons a b)‖^2) = ∑ b, ‖c b‖^2 := by
  calc
    _ = ∑ p : ι × (Fin n → ι), ‖c (Fin.cons p.1 p.2)‖^2 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := (Fin.consEquiv (fun _ : Fin (n+1) => ι)).sum_comp (fun b => ‖c b‖^2)

end ContinuumCoulomb

end

end OAI
