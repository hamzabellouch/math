import OAI.NumberTheory.PrimeGaps.ContourIntegrals

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

section FourierLaplace

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def laplaceFrequency (ℓ : V →L[ℝ] ℝ) (m u : V) : ℂ :=
  (ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem laplaceFrequency_re (ℓ : V →L[ℝ] ℝ) (m u : V) :
    (laplaceFrequency ℓ m u).re = ℓ m := by simp [laplaceFrequency]

noncomputable def rayVector {α : Type*} [Fintype α] (m : α → V) (y : α → ℝ) : V :=
  ∑ i, y i • m i

noncomputable def positiveOrthantMeasure (α : Type*) [Fintype α] : Measure (α → ℝ) :=
  Measure.pi (fun _ : α => volume.restrict (Ioi 0))

instance {α : Type*} [Fintype α] : SigmaFinite (positiveOrthantMeasure α) := by
  unfold positiveOrthantMeasure
  infer_instance

theorem positiveOrthantMeasure_eq_restrict (α : Type*) [Fintype α] :
    positiveOrthantMeasure α = volume.restrict (Set.pi univ (fun _ : α => Ioi (0:ℝ))) := by
  rw [volume_pi,Measure.restrict_pi_pi]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem product_laplace_exp_eq {α : Type*} [Fintype α] (ℓ : V →L[ℝ] ℝ)
    (m : α → V) (u : V) (y : α → ℝ) :
    (∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))) =
      Complex.exp (-(ℓ (rayVector m y):ℂ)-Complex.I*(inner ℝ u (rayVector m y):ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  simp only [rayVector,map_sum,map_smul,smul_eq_mul,inner_sum,inner_smul_right,
    Complex.ofReal_sum,Complex.ofReal_mul]
  rw [← Finset.sum_neg_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold laplaceFrequency
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem norm_product_laplace_exp {α : Type*} [Fintype α] (ℓ : V →L[ℝ] ℝ)
    (m : α → V) (u : V) (y : α → ℝ) :
    ‖∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))‖ =
      ∏ i, Real.exp (-ℓ (m i) * y i) := by
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [Complex.norm_exp,laplaceFrequency]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem integrable_product_laplace_exp {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) (u : V) :
    Integrable (fun y => ∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ)))
      (positiveOrthantMeasure α) := by
  exact Integrable.fintype_prod (f := fun i (y : ℝ) => Complex.exp (-laplaceFrequency ℓ (m i) u * (y:ℂ)))
    (μ := fun _ => volume.restrict (Ioi 0))
    (fun i => integrableOn_exp_mul_complex_Ioi (by simp [hm i]) 0)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem integral_product_laplace_exp {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) (u : V) :
    (∫ y, ∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))
      ∂positiveOrthantMeasure α) = ∏ i, (laplaceFrequency ℓ (m i) u)⁻¹ := by
  rw [positiveOrthantMeasure,integral_fintype_prod_eq_prod
    (fun i (y : ℝ) => Complex.exp (-laplaceFrequency ℓ (m i) u * (y:ℂ)))]
  apply Finset.prod_congr rfl
  intro i _
  simpa using integral_exp_mul_complex_Ioi (a:=-laplaceFrequency ℓ (m i) u)
    (by simp [hm i]) 0

theorem schwartz_product_laplace_integrable {α : Type*} [Fintype α]
    (Ψ : SchwartzMap V ℂ) (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    Integrable (fun z : V × (α → ℝ) => Ψ z.1 *
      ∏ i, Complex.exp (-laplaceFrequency ℓ (m i) z.1 * (z.2 i:ℂ)))
      (volume.prod (positiveOrthantMeasure α)) := by
  have he : Integrable (fun y : α → ℝ => ∏ i, Real.exp (-ℓ (m i)*y i))
      (positiveOrthantMeasure α) := by
    exact Integrable.fintype_prod (f := fun i y => Real.exp (-ℓ (m i)*y))
      (μ := fun _ => volume.restrict (Ioi 0))
      (fun i => integrableOn_exp_mul_Ioi (by linarith [hm i]) 0)
  have hb := (Ψ.integrable (μ := volume)).norm.mul_prod he
  apply hb.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul (Ψ.continuous.comp continuous_fst)
    apply continuous_finsetProd
    intro i _
    unfold laplaceFrequency
    fun_prop
  · filter_upwards [] with z
    rw [norm_mul,norm_product_laplace_exp]

theorem schwartz_product_laplace_interchange {α : Type*} [Fintype α]
    (Ψ : SchwartzMap V ℂ) (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, Ψ u*(∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, (∫ u : V, Ψ u *
        Complex.exp (-(ℓ (rayVector m y):ℂ)-Complex.I*(inner ℝ u (rayVector m y):ℂ)))
        ∂positiveOrthantMeasure α := by
  calc
    _ = ∫ u : V, ∫ y, Ψ u*(∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ)))
        ∂positiveOrthantMeasure α := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_const_mul,integral_product_laplace_exp ℓ m hm]
    _ = ∫ y, (∫ u : V, Ψ u*(∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))))
        ∂positiveOrthantMeasure α :=
      integral_integral_swap (schwartz_product_laplace_integrable Ψ ℓ m hm)
    _ = _ := by simp only [product_laplace_exp_eq]

theorem sourceFourier_product_laplace {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (F : V → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, sourceFourier ℓ F hF hFs u*(∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, F (rayVector m y) ∂positiveOrthantMeasure α := by
  rw [schwartz_product_laplace_interchange _ ℓ m hm]
  simp only [sourceFourier_inversion]

theorem sourceFourier_derivative_laplace {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      (ms.map (fun m => laplaceFrequency ℓ m u)).prod *
      (∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, signedDirections ms F (rayVector m y) ∂positiveOrthantMeasure α := by
  rw [← sourceFourier_product_laplace ℓ (signedDirections ms F)
    (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs) m hm]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sourceFourier_signedDirections ℓ ms F hF hFs u]
  simp only [laplaceFrequency,mul_comm (sourceFourier ℓ F hF hFs u)]

end FourierLaplace

theorem fiberKernel_card_le_two {ι : Type*} (S : Finset ι) (hS : S.card≤2) (w : ι → ℂ) :
    fiberKernel S w = (∏ i∈S, w i)*if S.card=2 then (∑ i∈S, w i)⁻¹ else 1 := by
  classical
  have hc : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases hc with hc|hc|hc
  · have hs : S=∅ := Finset.card_eq_zero.mp hc
    subst S
    simp [fiberKernel,nonemptySubsets]
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc
    simp [fiberKernel_singleton]
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hc
    simp [fiberKernel_pair hij,hij,div_eq_mul_inv]

theorem familyKernel_small_fibers {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (hR : ∀ i, b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2) (w : ι → ℂ) :
    familyKernel (fiberSubsetFamily b R) w =
      (∏ i, w i)*(∏ r∈R.filter (fun r => (Finset.univ.filter fun i => b i=r).card=2),
        (∑ i∈Finset.univ.filter (fun i => b i=r), w i)⁻¹) := by
  classical
  rw [familyKernel_fibers]
  calc
    _ = ∏ r∈R, (∏ i∈Finset.univ.filter (fun i => b i=r), w i)*
        (if (Finset.univ.filter (fun i => b i=r)).card=2 then
          (∑ i∈Finset.univ.filter (fun i => b i=r), w i)⁻¹ else 1) := by
      apply Finset.prod_congr rfl
      intro r hr
      exact fiberKernel_card_le_two _ (hcard r hr) w
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_fiberwise_of_maps_to (fun i _ => hR i)]
      congr 1
      exact (Finset.prod_filter ..).symm

section SmallFiberCoefficient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def coordinateDirectionList (ι : Type*) [Fintype ι] :
    List (EuclideanSpace ℝ ι) := by
  classical
  exact Finset.univ.toList.map (fun i => EuclideanSpace.single i (1:ℝ))

noncomputable def doubleFibers {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) : Finset α := by
  classical
  exact R.filter (fun r => (Finset.univ.filter (fun i => b i=r)).card=2)

noncomputable def fiberRay {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) : EuclideanSpace ℝ ι := by
  classical
  exact ∑ i∈Finset.univ.filter (fun i => b i=r), EuclideanSpace.single i (1:ℝ)

@[simp] theorem laplaceFrequency_coordinate {ι : Type*} [Fintype ι]
    (i : ι) (u : EuclideanSpace ℝ ι) :
    laplaceFrequency (fourierCoordinateSum ι) (EuclideanSpace.single i (1:ℝ)) u =
      frequencyW (u i) := by
  classical
  simp [laplaceFrequency,frequencyW,fourierCoordinateSum_apply,EuclideanSpace.inner_single_right]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceFrequency_sum {α : Type*} (ℓ : V →L[ℝ] ℝ) (S : Finset α)
    (m : α → V) (u : V) :
    laplaceFrequency ℓ (∑ i∈S, m i) u = ∑ i∈S, laplaceFrequency ℓ (m i) u := by
  simp [laplaceFrequency,map_sum,inner_sum,Complex.ofReal_sum,Finset.mul_sum,Finset.sum_add_distrib]

@[simp] theorem laplaceFrequency_fiberRay {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (u : EuclideanSpace ℝ ι) :
    laplaceFrequency (fourierCoordinateSum ι) (fiberRay b r) u =
      ∑ i∈Finset.univ.filter (fun i => b i=r), frequencyW (u i) := by
  classical
  simp [fiberRay,laplaceFrequency_sum]

@[simp] theorem coordinateDirectionList_multiplier {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι) :
    ((coordinateDirectionList ι).map (fun m => laplaceFrequency (fourierCoordinateSum ι) m u)).prod =
      ∏ i, frequencyW (u i) := by
  classical
  simp [coordinateDirectionList,List.map_map,Function.comp_def]

theorem fiberRay_positive {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (r : doubleFibers b R) :
    0 < fourierCoordinateSum ι (fiberRay b r.val) := by
  classical
  have hr : (Finset.univ.filter (fun i => b i=r.val)).card=2 :=
    (Finset.mem_filter.mp r.property).2
  have h := congrArg Complex.re (laplaceFrequency_fiberRay b r.val (0 : EuclideanSpace ℝ ι))
  simp only [laplaceFrequency_re,Complex.re_sum,frequencyW_re,Finset.sum_const] at h
  rw [h,hr]
  norm_num

theorem small_fiber_kernelConstant {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (hR : ∀ i, b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    kernelConstant (sourceFourier (fourierCoordinateSum ι) F hF hFs) (fiberSubsetFamily b R) =
      ∫ y, signedDirections (coordinateDirectionList ι) F
        (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y)
          ∂positiveOrthantMeasure (doubleFibers b R) := by
  classical
  rw [← sourceFourier_derivative_laplace (fourierCoordinateSum ι) (coordinateDirectionList ι)
    F hF hFs (fun r : doubleFibers b R => fiberRay b r.val) (fiberRay_positive b R)]
  unfold kernelConstant
  apply integral_congr_ae
  filter_upwards [] with u
  rw [contourKernel,familyKernel_small_fibers b R hR hcard,coordinateDirectionList_multiplier]
  simp only [laplaceFrequency_fiberRay]
  have hp := Finset.prod_coe_sort (s := doubleFibers b R)
    (f := fun r : α => (∑ i∈Finset.univ.filter (fun i => b i=r), frequencyW (u i))⁻¹)
  rw [hp,mul_assoc]
  rfl

end SmallFiberCoefficient

theorem shiftFamily_nonempty {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    ∀ S∈shiftFamily b, S.Nonempty := by
  intro S hS
  exact ((mem_fiberSubsetFamily b (Finset.univ.image b) S).mp hS).1

theorem residueFamily_nonempty {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) :
    ∀ S∈residueFamily b p, S.Nonempty := by
  intro S hS
  exact ((mem_fiberSubsetFamily _ _ S).mp hS).1

theorem markedResidueFamily_nonempty {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ) :
    ∀ S∈markedResidueFamily b p a, S.Nonempty := by
  intro S hS
  exact ((mem_markedResidueFamily b p a S).mp hS).1

theorem shiftFamily_sign_sum {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    (∑ S∈shiftFamily b, (-1:ℤ)^S.card) = -((Finset.univ.image b).card:ℤ) := by
  apply fiberSubsetFamily_sign_sum
  intro r hr
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hr
  exact ⟨i,hi⟩

theorem unmarked_analyticDensity_uniform_asymptotic {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (t β : ℕ) (hβ : 0<β)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ b : ι → ℤ, shiftFamily b=B → ∀ D : ℕ,
      (∀ i, (b i).natAbs≤D) → 2*D≤densityCutoff β L →
      ‖(L:ℂ)^t*analyticDensity 0 (residueFamily b) L F -
        (singularSeries (Finset.univ.image b):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum ι) F hF hFs) B‖ ≤ E L := by
  obtain ⟨E,hE,hbound⟩ := tupleFourier_integral_uniform_asymptotic
    (sourceFourier (fourierCoordinateSum ι) F hF hFs) B hB
    (2^Fintype.card ι) t β (subsetFamily_card_le B) hβ ht
  refine ⟨E,hE,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with L hbound hL
  intro b hb D hD hDL
  have hA := fun p : Nat.Primes => residueFamily_nonempty b p
  have hR := fun p : Nat.Primes => subsetFamily_card_le (residueFamily b p)
  have hgen : ∀ p : Nat.Primes, densityCutoff β L<(p:ℕ) → residueFamily b p=B := by
    intro p hp
    exact (residueFamily_generic_of_bound b hD (hDL.trans_lt hp)).trans hb
  have h := hbound 0 (by omega) (residueFamily b) hA hR hgen
  rw [← analyticDensity_eq_integral (by omega) (residueFamily b) hL hA hR F hF hFs] at h
  rw [← hb,unmarked_eulerGlobal_zero] at h
  simpa only [hb] using h

theorem marked_analyticDensity_uniform_asymptotic {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (t β : ℕ) (hβ : 0<β)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ b : ι → ℤ, shiftFamily b=B → ∀ a : ℤ,
      (∀ i, b i≠a) → ∀ D : ℕ, (∀ i, (b i).natAbs≤D) → a.natAbs≤D →
      2*D≤densityCutoff β L →
      ‖(L:ℂ)^t*analyticDensity 1 (fun p => markedResidueFamily b p a) L F -
        (singularSeries (insert a (Finset.univ.image b)):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum ι) F hF hFs) B‖ ≤ E L := by
  obtain ⟨E,hE,hbound⟩ := tupleFourier_integral_uniform_asymptotic
    (sourceFourier (fourierCoordinateSum ι) F hF hFs) B hB
    (2^Fintype.card ι) t β (subsetFamily_card_le B) hβ ht
  refine ⟨E,hE,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with L hbound hL
  intro b hb a ha D hD haD hDL
  have hA := fun p : Nat.Primes => markedResidueFamily_nonempty b p a
  have hR := fun p : Nat.Primes => subsetFamily_card_le (markedResidueFamily b p a)
  have hgen : ∀ p : Nat.Primes, densityCutoff β L<(p:ℕ) → markedResidueFamily b p a=B := by
    intro p hp
    exact (markedResidueFamily_generic_of_bound b a ha hD haD (hDL.trans_lt hp)).trans hb
  have h := hbound 1 (by omega) (fun p => markedResidueFamily b p a) hA hR hgen
  rw [← analyticDensity_eq_integral (by omega) (fun p => markedResidueFamily b p a)
    hL hA hR F hF hFs] at h
  rw [← hb,marked_eulerGlobal_zero b a ha] at h
  simpa only [hb] using h

theorem unmarked_average_uniform_asymptotic {n : ℕ}
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i, 0≤v i) → |F v|≤M)
    (B : Finset (Finset (Fin (n+1)))) (hB : ∀ S∈B, S.Nonempty)
    (t β : ℕ) (hβ : 0<β) (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ∀ b : Fin (n+1) → ℕ,
      shiftFamily (fun i => (b i:ℤ))=B → ∀ D : ℕ,
      (∀ i, b i≤D) → 2*D≤densityCutoff β (Real.log X) →
      ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b):ℂ) -
        (singularSeries (Finset.univ.image fun i => (b i:ℤ)):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+1)))
            (fun v => (F v.ofLp:ℂ)) hF hFs) B‖ ≤ E X := by
  obtain ⟨E,hE,hEbound⟩ := unmarked_analyticDensity_uniform_asymptotic
    (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) hF hFs B hB t β hβ ht
  let err : ℝ → ℝ := fun L => (2*M*(1+rho)^n)*L^(n+t)*Real.exp (-(1-rho)*L)
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (n+t:ℕ) (1-rho) (by linarith)).const_mul (2*M*(1+rho)^n)
    simpa only [Real.rpow_natCast,mul_zero,mul_assoc,err] using h
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨fun X => err (Real.log X)+E (Real.log X),?_,?_⟩
  · simpa only [Function.comp_def,add_zero] using (herr.comp hlog).add (hE.comp hlog)
  filter_upwards [hlog.eventually hEbound,eventually_ge_atTop 2,
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with X hEX hX hL
  intro b hb D hD hDL
  have hb' : ∀ i, ((b i:ℤ)).natAbs≤D := by simpa only [Int.natAbs_natCast] using hD
  have hden := hEX (fun i => (b i:ℤ)) hb D hb' hDL
  rw [analyticDensity_eq_unmarkedDensitySum hX hbudget b] at hden
  have hcomp : ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b):ℂ)-
      (Real.log X:ℂ)^t*(unmarkedDensitySum X F rho b:ℂ)‖ ≤ err (Real.log X) := by
    rw [← mul_sub,← Complex.ofReal_sub,norm_mul,norm_pow,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log X)]
    have hh := mul_le_mul_of_nonneg_left
      (unmarked_arithmetic_error_exponential hX hL hrho hbudget hM hbound b)
      (pow_nonneg (by linarith : 0≤Real.log X) t)
    convert hh using 1
    all_goals first | rfl | (simp only [err,pow_add]; ring)
  apply le_trans ?_ (add_le_add hcomp hden)
  simpa only [dist_eq_norm] using (dist_triangle
    ((Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b):ℂ))
    ((Real.log X:ℂ)^t*(unmarkedDensitySum X F rho b:ℂ)) _)

theorem marked_average_uniform_asymptotic (hBV : BombieriVinogradov) {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i, 0≤v i) → |F v|≤M)
    (B : Finset (Finset (Fin n))) (hB : ∀ S∈B, S.Nonempty)
    (t β : ℕ) (hβ : 0<β) (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ))
    (H : ℕ → ℕ) {D₀ B₀ : ℝ} (hD₀ : 0<D₀)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ)≤D₀*(Real.log (X:ℝ))^B₀) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ∀ b : Fin n → ℕ,
      shiftFamily (fun i => (b i:ℤ))=B → ∀ a : ℕ, a≤H X →
      (∀ i, b i≠a) → ∀ D : ℕ, (∀ i, b i≤D) → a≤D →
      2*D≤densityCutoff β (Real.log X) →
      ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ) -
        (singularSeries (insert (a:ℤ) (Finset.univ.image fun i => (b i:ℤ))):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
            (fun v => (F v.ofLp:ℂ)) hF hFs) B‖ ≤ E X := by
  obtain ⟨E,hE,hEbound⟩ := marked_analyticDensity_uniform_asymptotic
    (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) hF hFs B hB t β hβ ht
  let err : ℕ → ℝ := fun X => M*(weightedErrorSum (2^n) X (H X) (powerModulus rho X)/X)*
    (Real.log (X:ℝ))^t
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := (weightedErrorSum_log_decay hBV (2^n) H hrho hrhohalf hD₀ hH t).const_mul M
    simpa only [mul_zero,mul_assoc,err] using h
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨fun X => err X+E (Real.log X),?_,?_⟩
  · simpa only [Function.comp_def,add_zero] using herr.add (hE.comp hlog)
  filter_upwards [hlog.eventually hEbound,eventually_ge_atTop 2] with X hEX hX
  intro b hb a haH ha D hD haD hDL
  have hb' : ∀ i, ((b i:ℤ)).natAbs≤D := by simpa only [Int.natAbs_natCast] using hD
  have ha' : ∀ i, (b i:ℤ)≠(a:ℤ) := fun i he => ha i (by exact_mod_cast he)
  have hden := hEX (fun i => (b i:ℤ)) hb a ha' D hb'
    (by simpa only [Int.natAbs_natCast] using haD) hDL
  rw [analyticDensity_eq_markedDensitySum hX hbudget b a] at hden
  have hXR : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have hY : ⌊Real.exp (rho*Real.log (X:ℝ))⌋₊ = powerModulus rho X := by
    unfold powerModulus
    rw [Real.rpow_def_of_pos hXR,mul_comm rho]
  have he := marked_arithmetic_error hX haH (by linarith : rho≤1) hbudget hM hbound b
  rw [hY] at he
  have he' : |average X (fun m => divisorSum X F m b*theta (m+a))-
      markedDensitySum X F rho b a| ≤
      M/X*weightedErrorSum (2^n) X (H X) (powerModulus rho X) := by
    simpa only [weightedErrorSum,Nat.cast_pow] using he
  have hcomp : ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ)-
      (Real.log X:ℂ)^t*(markedDensitySum X F rho b a:ℂ)‖ ≤ err X := by
    rw [← mul_sub,← Complex.ofReal_sub,norm_mul,norm_pow,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (log_pos_of_two_le hX).le]
    have hh := mul_le_mul_of_nonneg_left he' (pow_nonneg (log_pos_of_two_le hX).le t)
    convert hh using 1
    all_goals first | rfl | (simp only [err]; ring)
  apply le_trans ?_ (add_le_add hcomp hden)
  simpa only [dist_eq_norm] using (dist_triangle
    ((Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ))
    ((Real.log X:ℂ)^t*(markedDensitySum X F rho b a:ℂ)) _)

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def negativeCube {ι : Type*} [Fintype ι] (T : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, -T≤x i ∧ x i≤0}

theorem negativeCube_compact {ι : Type*} [Fintype ι] (T : ℝ) :
    IsCompact (negativeCube (ι:=ι) T) := by
  have h := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := -T) (b := (0:ℝ)))).image
    (PiLp.homeomorph 2 (fun _ : ι => ℝ)).symm.continuous
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨x.ofLp, ?_, ?_⟩
    · simpa only [negativeCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc] using hx
    · rfl
  · rintro ⟨y, hy, rfl⟩
    change ∀ i, -T≤y i ∧ y i≤0
    simpa only [Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc] using hy

noncomputable def cubeIndicator {ι : Type*} [Fintype ι] (T : ℝ) : EuclideanSpace ℝ ι → ℝ :=
  (negativeCube T).indicator (fun _ => 1)

theorem cubeIndicator_compact {ι : Type*} [Fintype ι] (T : ℝ) :
    HasCompactSupport (cubeIndicator (ι:=ι) T) := by
  apply (negativeCube_compact T).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (negativeCube_compact T).isClosed
  exact Set.support_indicator_subset

theorem cubeIndicator_integrable {ι : Type*} [Fintype ι] (T : ℝ) :
    Integrable (cubeIndicator (ι:=ι) T) := by
  apply (integrable_indicator_iff (negativeCube_compact T).measurableSet).mpr
  exact continuous_const.continuousOn.integrableOn_compact (negativeCube_compact T)

end LargePrimeGaps

end OAI
