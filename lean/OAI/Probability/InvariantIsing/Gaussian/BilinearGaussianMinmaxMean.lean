import OAI.Probability.InvariantIsing.Gaussian.BilinearGaussianMinmax

namespace OAI

/-! Removing the auxiliary Gaussian scalar and bounding the comparison's vector term. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

theorem bilinear_gaussian_minmax_mean {N m : ℕ}
    (u : U → EuclideanSpace ℝ (Fin N)) (v : V → EuclideanSpace ℝ (Fin m))
    (hu : ∀ a, ‖u a‖ = 1) (hv : ∀ b, ‖v b‖ = 1) :
    (∫ g, indexedGaussianMaximum (fun a i => u a i) g
      ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1))-Real.sqrt m ≤
    ∫ g, finiteMinmax (fun x : U × V => ∑ ij : Fin N × Fin m, (u x.1 ij.1*v x.2 ij.2)*g ij)
      ∂Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)
  let e : Fin N × Fin m → BilinearGaussianIndex N m := fun ij => .inl (.inl ij)
  let eu : Fin N → BilinearGaussianIndex N m := fun i => .inr (.inl i)
  let ev : Fin m → BilinearGaussianIndex N m := fun j => .inr (.inr j)
  let D : U × V → (Fin N × Fin m) → ℝ := fun x ij => u x.1 ij.1*v x.2 ij.2
  let C := bilinearMatrixCoefficient (fun x : U × V => u x.1) (fun x => v x.2)
  let A := bilinearVectorCoefficient (fun x : U × V => u x.1) (fun x => v x.2)
  have hR := iidGaussian_restrict_hasLaw e (fun _ _ h => Sum.inl.inj (Sum.inl.inj h))
  have hRu := iidGaussian_restrict_hasLaw eu (fun _ _ h => Sum.inl.inj (Sum.inr.inj h))
  have hc : Integrable (fun g : BilinearGaussianIndex N m → ℝ => g (.inl (.inr ()))) μ :=
    (gaussianCoordinate_memLp _).integrable (by norm_num)
  have hzero : (∫ g : BilinearGaussianIndex N m → ℝ, g (.inl (.inr ())) ∂μ) = 0 := by
    simpa only [μ,integral_id_gaussianReal] using
      (measurePreserving_eval (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)
        (.inl (.inr ()))).hasLaw.integral_eq
  have hmatrix (g : BilinearGaussianIndex N m → ℝ) :
      finiteMinmax (fun x => ∑ i, C x i*g i) =
        finiteMinmax (fun x => ∑ ij, D x ij*g (e ij)) + g (.inl (.inr ())) := by
    dsimp only [C]
    simp only [Fintype.sum_sum_type,bilinearMatrixCoefficient,zero_mul,
      one_mul,Finset.sum_const_zero,Fintype.sum_unique,add_zero]
    exact finiteMinmax_add_constant _ _
  have hright : (∫ g, finiteMinmax (fun x => ∑ i, C x i*g i) ∂μ) =
      ∫ g, finiteMinmax (fun x => ∑ ij, D x ij*g ij)
        ∂Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1) := by
    simp_rw [hmatrix]
    change (∫ g, ((fun g => finiteMinmax (fun x => ∑ ij, D x ij*g ij)) ∘
      (fun g : BilinearGaussianIndex N m → ℝ => fun j => g (e j))) g+
      g (.inl (.inr ())) ∂μ) = _
    rw [integral_add (hR.integrable_comp (indexedGaussianMinmax_integrable D)) hc,hzero,add_zero]
    exact hR.integral_comp (indexedGaussianMinmax_integrable D).aestronglyMeasurable
  have himax : Integrable (fun g : BilinearGaussianIndex N m → ℝ =>
      indexedGaussianMaximum (fun a i => u a i) (fun i => g (eu i))) μ := by
    simpa only [Function.comp_def] using
      hRu.integrable_comp (indexedGaussianMaximum_integrable (fun a i => u a i))
  have hinorm := ((gaussianCoordinateVector_memLp ev).integrable (by norm_num)).norm
  have hleft : (∫ g, indexedGaussianMaximum (fun a i => u a i) (fun i => g (eu i)) ∂μ)-
      (∫ g, ‖gaussianCoordinateVector ev g‖ ∂μ) ≤
      ∫ g, finiteMinmax (fun x => ∑ i, A x i*g i) ∂μ := by
    rw [← integral_sub himax hinorm]
    apply integral_mono (himax.sub hinorm) (indexedGaussianMinmax_integrable A)
    intro g
    obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun a => ∑ i, u a i*g (eu i))
    change (Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ i, u a i*g (eu i)))-_ ≤ _
    rw [he]
    apply Finset.le_inf'
    intro b _
    apply Finset.le_sup'_of_le _ (Finset.mem_univ a)
    have hb := abs_real_inner_le_norm (v b) (gaussianCoordinateVector ev g)
    rw [hv,one_mul] at hb
    have hl := neg_le_of_abs_le hb
    change -‖gaussianCoordinateVector ev g‖ ≤ _ at hl
    change (∑ i, u a i*g (eu i)) - ‖gaussianCoordinateVector ev g‖ ≤ ∑ i, A (a,b) i*g i
    dsimp only [A]
    simp only [Fintype.sum_sum_type,bilinearVectorCoefficient,zero_mul,
      Finset.sum_const_zero,zero_add]
    have heq : ⟪v b,gaussianCoordinateVector ev g⟫ = ∑ j, v b j*g (ev j) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,
        gaussianCoordinateVector,mul_comm]
    rw [heq] at hl
    dsimp only [eu,ev] at hl ⊢
    linarith
  have hmaxeq : (∫ g, indexedGaussianMaximum (fun a i => u a i) (fun i => g (eu i)) ∂μ) =
      ∫ g, indexedGaussianMaximum (fun a i => u a i) g
        ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1) := by
    simpa only [Function.comp_def] using hRu.integral_comp
      (indexedGaussianMaximum_integrable (fun a i => u a i)).aestronglyMeasurable
  rw [hmaxeq] at hleft
  have hnorm : (∫ g, ‖gaussianCoordinateVector ev g‖ ∂μ) ≤ Real.sqrt m := by
    simpa only [Fintype.card_fin] using gaussianCoordinateVector_norm_integral_le ev
  have hcomp := bilinear_gaussian_minmax_comparison u v hu hv
  change (∫ g, finiteMinmax (fun x => ∑ i, A x i*g i) ∂μ) ≤
    (∫ g, finiteMinmax (fun x => ∑ i, C x i*g i) ∂μ) at hcomp
  rw [hright] at hcomp
  exact (sub_le_sub_left hnorm _).trans (hleft.trans hcomp)

end InvariantIsing

end

end OAI
