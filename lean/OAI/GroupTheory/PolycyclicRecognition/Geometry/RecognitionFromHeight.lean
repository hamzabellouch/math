import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoundedPathGrowth
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.DualityEndgame
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TransferredHeight

namespace OAI

/-! # Recognition from a geometric height estimate

Corrected height bounds control intrinsic word growth of finitely generated
subgroups of its kernel. Polynomial bounded-height chain packing gives
elementary amenability, to which the finiteness and duality theorems apply.
-/

noncomputable section

namespace PolycyclicRecognition

universe u v

variable {H : Type u} [Group H] [MetricSpace H] [IsIsometricSMul H H]
variable {X : Type v} [PseudoMetricSpace X]
variable {W : Type u} [NormedAddCommGroup W]

/-- Intrinsic polynomial growth for an injectively parametrized subgroup of the
ambient coarse source. All metric estimates use the ambient source metric. -/
theorem virtuallyNilpotent_of_injective_boundedHeight
    {J : Type u} [Group J] [Group.FG J] [DecidableEq J] [DecidableEq X]
    (gromov : GromovPolynomialGrowthInput J)
    (ι : J →* H) (hι : Function.Injective ι)
    (f : H → X) (π : X → W) (packing : PolynomialBoundedChainPacking π)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C K' C' M : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hM : 0 ≤ M)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hheight : ∀ j, ‖π (f (ι j))‖ ≤ M) : Group.IsVirtuallyNilpotent J := by
  classical
  obtain ⟨T, hsymm, hgen⟩ := exists_symmetric_finite_generating_set (J := J)
  let R : ℝ := ∑ t ∈ T, dist (1 : H) (ι t)
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => dist_nonneg
  have hRbound (t : J) (ht : t ∈ T) : dist (1 : H) (ι t) ≤ R :=
    Finset.single_le_sum (f := fun t : J => dist 1 (ι t)) (fun _ _ => dist_nonneg) ht
  have hstep (j t : J) (ht : t ∈ T) :
      dist (f (ι j)) (f (ι (j * t))) ≤ K * R + C := by
    apply (hupper (ι j) (ι (j * t))).trans
    have hd : dist (ι j) (ι (j * t)) = dist (1 : H) (ι t) := by
      rw [map_mul]
      simpa only [mul_one] using dist_mul_left (ι j) (1 : H) (ι t)
    rw [hd]
    exact add_le_add (mul_le_mul_of_nonneg_left (hRbound t ht) hK) le_rfl
  obtain ⟨N, hN⟩ := exists_uniform_ball_multiplicity (r := 1) f hfinite hK' hlower
  exact virtuallyNilpotent_of_boundedHeight_steps gromov (f ∘ ι) π packing T hsymm hgen
    (add_nonneg (mul_nonneg hK hR) hC) hM hheight hstep N
    (ball_multiplicity_comp_injective f ι hι N 1 hN)

/-- The height-kernel and finite-extension argument, including potentially
infinitely generated kernels and nondiscrete height images. -/
theorem elementaryAmenable_of_corrected_height [DecidableEq X]
    (H₀ : Subgroup H) [H₀.FiniteIndex] (τ : H₀ →* Multiplicative W)
    (gromov : ∀ (J : Subgroup τ.ker) [DecidableEq J], GromovPolynomialGrowthInput J)
    (f : H → X) (π : X → W) (packing : PolynomialBoundedChainPacking π)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C K' C' D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hD : 0 ≤ D)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hheight : ∀ h : H₀, ‖(τ h).toAdd - π (f h)‖ ≤ D) :
    IsElementaryAmenable H := by
  classical
  apply elementaryAmenable_of_finiteIndex H₀
  apply elementaryAmenable_of_height_kernel τ
  intro J hJ
  let _ := hJ
  let ι : J →* H := H₀.subtype.comp (τ.ker.subtype.comp J.subtype)
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  apply virtuallyNilpotent_of_injective_boundedHeight (gromov J) ι hι f π packing
    hfinite hK hC hK' hD hupper hlower
  intro j
  have hj : τ (j.val.val) = 1 := j.val.property
  have he := hheight (j.val.val)
  rw [hj] at he
  change ‖(0 : W) - π (f (ι j))‖ ≤ D at he
  simpa only [zero_sub, norm_neg] using he

variable [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The transferred quasi-action, mean correction, intrinsic subgroup growth,
and finite-extension step form one complete argument after the two geometric
obligations have been supplied. -/
theorem elementaryAmenable_of_transferred_height [DecidableEq X]
    (gromov : ∀ (J : Type u) [Group J] [DecidableEq J], GromovPolynomialGrowthInput J)
    (f : H → X) (r : X → H) (π : X → W)
    (packing : PolynomialBoundedChainPacking π)
    (A : H → W ≃L[ℝ] W) (hπsurj : Function.Surjective π)
    (L K C E B K' C' : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hB : 0 ≤ B) (hK' : 0 ≤ K')
    (hπ : ∀ x y, ‖π x - π y‖ ≤ L * dist x y)
    (hupper : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (hlower : ∀ a b, dist a b ≤ K' * dist (f a) (f b) + C')
    (hrf : ∀ a, dist (r (f a)) a ≤ E)
    (haffine : ∀ h x,
      ‖π (transferredMap f r h x) - (π (f h) + A h (π x))‖ ≤ B)
    (M : ThompsonNonamenability.InvariantMean H) (hA : Set.Finite (Set.range A))
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite) :
    IsElementaryAmenable H := by
  classical
  obtain ⟨H₀, _, hindex, τ, D, hD, hheight, _⟩ :=
    TransferredHeight.exists_normal_finiteIndex_height f r π A hπsurj
      (fun h a b => dist_mul_left h a b) L K C E B hL hK hC hE hB hπ hupper hrf
      haffine M hA
  let _ := hindex
  exact elementaryAmenable_of_corrected_height H₀ τ (fun J => gromov J)
    f π packing hfinite hK hC hK' hD hupper hlower hheight

/-- The corrected geometric height and bounded-height chain packing imply
virtual polycyclicity through the algebraic recognition theorem. -/
theorem virtuallyPolycyclic_of_corrected_height
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    (Γ H : Type) [Group Γ] [Group H] [MetricSpace H] [IsIsometricSMul H H]
    [Group.FG Γ] [Group.FG H]
    {X W : Type} [PseudoMetricSpace X] [DecidableEq X] [NormedAddCommGroup W]
    (H₀ : Subgroup H) [H₀.FiniteIndex] (τ : H₀ →* Multiplicative W)
    (gromov : ∀ (J : Subgroup τ.ker) [DecidableEq J], GromovPolynomialGrowthInput J)
    (f : H → X) (π : X → W) (packing : PolynomialBoundedChainPacking π)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C K' C' D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hK' : 0 ≤ K') (hD : 0 ≤ D)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hheight : ∀ h : H₀, ‖(τ h).toAdd - π (f h)‖ ≤ D)
    (e : GroupCoarseEquivalence Γ H)
    (n : ℕ) (hΓPD : IsIntegralPoincareDualityGroup Γ n) : IsVirtuallyPolycyclic H := by
  have hEA := elementaryAmenable_of_corrected_height H₀ τ gromov f π packing
    hfinite hK hC hK' hD hupper hlower hheight
  exact virtuallyPolycyclic_of_elementaryAmenable_coarse_PD liFP eaFP liPD bieri Γ H e hEA
    n hΓPD

end PolycyclicRecognition

end

end OAI
