import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearRounding
import OAI.Analysis.CoulombRadii.FieldAnalysis.Space

namespace OAI

/-! A cutoff Hardy estimate for the near-node part of the nuclear mesh. The
right side is localized, allowing bounded-overlap summation over nuclei. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localized_nuclear_hardy {n : ℕ} (u : Coulomb.H1Vector n)
    (s : SpinConfiguration n) (i : Fin n) (a : Position) {r D : ℝ} (hr : 0 < r)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfB : ∀ x, |f x| ≤ 1)
    (hdfB : ∀ j x, |fderiv ℝ f x (EuclideanSpace.single j 1)| ≤ D)
    (A B : Set (Configuration n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hnear : ∀ x ∈ A, ‖Coulomb.position x i-a‖ ≤ r)
    (hone : ∀ x ∈ A, f x = 1)
    (hzero : ∀ x ∉ B, f x = 0)
    (hdzero : ∀ k x, x ∉ B → fderiv ℝ f x (EuclideanSpace.single (i,k) 1) = 0) :
    (∫ x in A, Coulomb.coulombKernel (Coulomb.position x i-a)*‖u.value s x‖^2) ≤
      24*r*D^2*(∫ x in B, ‖u.value s x‖^2)+
      8*r*(∑ k : Fin 3, ∫ x in B, ‖u.gradient s (i,k) x‖^2) := by
  let v := u.smoothMul f hf 1 D hfB hdfB
  obtain ⟨hvi,hvh⟩ := nuclear_hardy_square v s i a
  have hpoint (x : Configuration n) :
      A.indicator (fun x => Coulomb.coulombKernel (Coulomb.position x i-a)*‖u.value s x‖^2) x ≤
      r*(Coulomb.coulombKernel (Coulomb.position x i-a)^2*‖v.value s x‖^2) := by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have hv : v.value s x = u.value s x := by
        change (f x:ℂ)*u.value s x = _
        rw [hone x hx,Complex.ofReal_one,one_mul]
      rw [hv,← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      by_cases hz : ‖Coulomb.position x i-a‖ = 0
      · simp only [Coulomb.coulombKernel,hz,inv_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
      · have hp : 0 < ‖Coulomb.position x i-a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        have hh := mul_le_mul_of_nonneg_right (hnear x hx) (sq_nonneg ‖Coulomb.position x i-a‖⁻¹)
        have he : ‖Coulomb.position x i-a‖*‖Coulomb.position x i-a‖⁻¹^2 =
            ‖Coulomb.position x i-a‖⁻¹ := by field_simp
        simpa only [Coulomb.coulombKernel,he] using hh
    · rw [Set.indicator_of_notMem hx]
      positivity
  have hnearint : (∫ x in A, Coulomb.coulombKernel (Coulomb.position x i-a)*‖u.value s x‖^2) ≤
      r*(∫ x, Coulomb.coulombKernel (Coulomb.position x i-a)^2*‖v.value s x‖^2) := by
    rw [← integral_indicator hA,← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => by
      apply Set.indicator_nonneg
      intro y _
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sq_nonneg _)))
      (hvi.const_mul r) (Filter.Eventually.of_forall hpoint)
  have hg (k : Fin 3) :
      (∫ x, ‖v.gradient s (i,k) x‖^2) ≤
        2*D^2*(∫ x in B, ‖u.value s x‖^2)+2*(∫ x in B, ‖u.gradient s (i,k) x‖^2) := by
    have hp (x : Configuration n) : ‖v.gradient s (i,k) x‖^2 ≤
        B.indicator (fun x => 2*D^2*‖u.value s x‖^2+2*‖u.gradient s (i,k) x‖^2) x := by
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx]
        have h₁ : ‖(fderiv ℝ f x (EuclideanSpace.single (i,k) 1):ℂ)*u.value s x‖ ≤ D*‖u.value s x‖ := by
          rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hdfB (i,k) x) (norm_nonneg _)
        have h₂ : ‖(f x:ℂ)*u.gradient s (i,k) x‖ ≤ ‖u.gradient s (i,k) x‖ := by
          rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hfB x) (norm_nonneg (u.gradient s (i,k) x))
        have ht := norm_add_le ((fderiv ℝ f x (EuclideanSpace.single (i,k) 1):ℂ)*u.value s x)
          ((f x:ℂ)*u.gradient s (i,k) x)
        change ‖(fderiv ℝ f x (EuclideanSpace.single (i,k) 1):ℂ)*u.value s x+
          (f x:ℂ)*u.gradient s (i,k) x‖^2 ≤ _
        nlinarith [norm_nonneg ((fderiv ℝ f x (EuclideanSpace.single (i,k) 1):ℂ)*u.value s x+
          (f x:ℂ)*u.gradient s (i,k) x),sq_nonneg (D*‖u.value s x‖-‖u.gradient s (i,k) x‖)]
      · rw [Set.indicator_of_notMem hx]
        change ‖(fderiv ℝ f x (EuclideanSpace.single (i,k) 1):ℂ)*u.value s x+
          (f x:ℂ)*u.gradient s (i,k) x‖^2 ≤ 0
        simp only [hdzero k x hx,hzero x hx,Complex.ofReal_zero,zero_mul,add_zero,norm_zero,
          zero_pow (by decide : 2 ≠ 0),le_refl]
    have hu := (u.value_L2 s).integrable_norm_pow (p := 2) (by decide)
    have hd := (u.partial_L2 s (i,k)).integrable_norm_pow (p := 2) (by decide)
    have hb := ((hu.const_mul (2*D^2)).add (hd.const_mul 2)).integrableOn.integrable_indicator hB
    have hi := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg ‖v.gradient s (i,k) x‖))
      hb (Filter.Eventually.of_forall hp)
    rw [integral_indicator hB] at hi
    simp only [Pi.add_apply] at hi
    rw [integral_add (hu.integrableOn.const_mul _) (hd.integrableOn.const_mul _),
      integral_const_mul,integral_const_mul] at hi
    exact hi
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hg k)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,← Finset.mul_sum,Nat.cast_ofNat] at hs
  have hh := mul_le_mul_of_nonneg_left hvh hr.le
  have hsum := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4*r)
  nlinarith only [hnearint,hh,hsum]

end ContinuumCoulomb

end

end OAI
