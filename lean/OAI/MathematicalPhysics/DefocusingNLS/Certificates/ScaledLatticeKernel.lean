import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightProduct

namespace OAI

/-! # A lattice sampling bound uniform as the mesh tends to zero

The exact Cauchy-kernel integral and the integral test give a one-dimensional
bound.  A twelve-coordinate product then controls the radial kernel.
-/

open Set MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def scaledCauchyKernel (L x : ℝ) : ℝ := (1 + (x / L) ^ 2)⁻¹

theorem scaledCauchyKernel_nonneg (L x : ℝ) : 0 ≤ scaledCauchyKernel L x := by
  unfold scaledCauchyKernel
  positivity

theorem scaledCauchyKernel_even (L x : ℝ) : scaledCauchyKernel L (-x) = scaledCauchyKernel L x := by
  simp only [scaledCauchyKernel, neg_div, even_two.neg_pow]

theorem scaledCauchyKernel_antitone (L : ℝ) (hL : 0 < L) :
    AntitoneOn (scaledCauchyKernel L) (Ici 0) := by
  intro x hx y hy hxy
  unfold scaledCauchyKernel
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  gcongr

theorem scaledCauchyKernel_integrable (L : ℝ) (hL : 0 < L) :
    Integrable (scaledCauchyKernel L) := by
  change Integrable (fun x => (1 + (x / L) ^ 2)⁻¹)
  simpa only [div_eq_inv_mul] using
    integrable_inv_one_add_mul_sq (inv_ne_zero hL.ne')

theorem integral_scaledCauchyKernel (L : ℝ) (hL : 0 < L) :
    (∫ x, scaledCauchyKernel L x) = Real.pi * L := by
  simp only [scaledCauchyKernel, div_eq_inv_mul]
  rw [integral_univ_inv_one_add_mul_sq, abs_inv, abs_of_pos hL, div_inv_eq_mul]

theorem scaledCauchyKernel_integer_sum (L : ℝ) (hL : 1 ≤ L) :
    Summable (fun n : ℤ => scaledCauchyKernel L n) ∧
      (∑' n : ℤ, scaledCauchyKernel L n) ≤ (1 + 2 * Real.pi) * L := by
  have hLp : 0 < L := by linarith
  have ha := scaledCauchyKernel_antitone L hLp
  have hi := (scaledCauchyKernel_integrable L hLp).integrableOn (s := Ioi 0)
  have hp : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ scaledCauchyKernel L x :=
    fun x _ => scaledCauchyKernel_nonneg L x
  have hb : (∫ x in Ioi 0, scaledCauchyKernel L x) ≤ Real.pi * L := by
    rw [← integral_scaledCauchyKernel L hLp]
    exact setIntegral_le_integral (scaledCauchyKernel_integrable L hLp)
      (Filter.Eventually.of_forall (scaledCauchyKernel_nonneg L))
  have hs := ha.summable_of_integrableOn_Ioi_zero hi hp
  have hs1 : Summable (fun n : ℕ => scaledCauchyKernel L (n + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  have hnat : Summable (fun n : ℕ => scaledCauchyKernel L ((n : ℤ) : ℝ)) := by
    simpa only [Int.cast_natCast] using hs
  have hneg : Summable (fun n : ℕ => scaledCauchyKernel L (((-((n : ℤ) + 1)) : ℤ) : ℝ)) := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      scaledCauchyKernel_even] using hs1
  refine ⟨Summable.of_nat_of_neg_add_one hnat hneg, ?_⟩
  rw [tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => scaledCauchyKernel L n) hnat hneg]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, scaledCauchyKernel_even]
  have h0 := (ha.tsum_le_integral hi hp).trans (add_le_add le_rfl hb)
  have h1 := (ha.tsum_add_one_le_integral hi hp).trans hb
  simp only [scaledCauchyKernel, zero_div, zero_pow (by decide : 2 ≠ 0), add_zero, inv_one] at h0
  change (∑' n : ℕ, scaledCauchyKernel L n) ≤ 1 + Real.pi * L at h0
  simp only [Nat.cast_add, Nat.cast_one] at h1
  nlinarith [Real.pi_pos]

private theorem scaled_frequencyCoordinates_injective : Function.Injective frequencyCoordinates := by
  intro n m h
  apply Subtype.ext
  ext j
  have hc := congrFun h j
  exact_mod_cast (frequencyCoordinates_coe n j).symm.trans
    ((congrArg (fun z : ℤ => (z : ℝ)) hc).trans (frequencyCoordinates_coe m j))

theorem sum_scaledCauchyKernel_product (L : ℝ) (hL : 1 ≤ L) (S : Finset frequencyLattice) :
    (∑ n ∈ S, ∏ j : Fin 12, scaledCauchyKernel L (frequencyCoordinates n j)) ≤
      ((1 + 2 * Real.pi) * L) ^ 12 := by
  classical
  let K : ℤ → ℝ := fun z => scaledCauchyKernel L z
  let U : Finset ℤ := S.biUnion (fun n => Finset.univ.image (frequencyCoordinates n))
  let T : Finset (Fin 12 → ℤ) := S.image frequencyCoordinates
  have hTU : T ⊆ Fintype.piFinset (fun _ : Fin 12 => U) := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    simp only [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨hKs, hKb⟩ := scaledCauchyKernel_integer_sum L hL
  have hU : (∑ z ∈ U, K z) ≤ (1 + 2 * Real.pi) * L :=
    (hKs.sum_le_tsum U (fun z _ => scaledCauchyKernel_nonneg L z)).trans hKb
  have hUnonneg : 0 ≤ ∑ z ∈ U, K z :=
    Finset.sum_nonneg (fun z _ => scaledCauchyKernel_nonneg L z)
  calc
    _ = ∑ p ∈ T, ∏ j : Fin 12, K (p j) := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => scaled_frequencyCoordinates_injective h
    _ ≤ ∑ p ∈ Fintype.piFinset (fun _ : Fin 12 => U), ∏ j : Fin 12, K (p j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hTU (fun _ _ _ => by
        apply Finset.prod_nonneg
        intro j _
        exact scaledCauchyKernel_nonneg L _)
    _ = (∑ z ∈ U, K z) ^ 12 := by rw [Finset.sum_prod_piFinset]; simp
    _ ≤ _ := by gcongr

theorem scaledRadialKernel_le_product (L : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    ((1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (12 : ℕ))⁻¹ ≤
      ∏ j : Fin 12, scaledCauchyKernel L (frequencyCoordinates n j) := by
  have hLp : 0 < L := by linarith
  have hn : ‖(L⁻¹ : ℝ) • (n : E)‖ = ‖n‖ / L := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hLp, div_eq_inv_mul,
      Submodule.norm_coe]
  have heach (j : Fin 12) : 1 + ((frequencyCoordinates n j : ℝ) / L) ^ 2 ≤
      1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2 := by
    rw [hn, div_pow, div_pow]
    exact add_le_add le_rfl (div_le_div_of_nonneg_right (frequencyCoordinates_sq_le n j)
      (sq_nonneg L))
  have hprod : (∏ j : Fin 12, (1 + ((frequencyCoordinates n j : ℝ) / L) ^ 2)) ≤
      (1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (12 : ℕ) := by
    calc
      _ ≤ ∏ _ : Fin 12, (1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) := by
        apply Finset.prod_le_prod₀
        · intro j _
          positivity
        · intro j _
          exact heach j
      _ = _ := by simp
  have hpos : 0 < ∏ j : Fin 12, (1 + ((frequencyCoordinates n j : ℝ) / L) ^ 2) :=
    Finset.prod_pos (fun j _ => by positivity)
  simpa only [scaledCauchyKernel, Finset.prod_inv_distrib] using
    (inv_le_inv₀ (by positivity) hpos).mpr hprod

theorem scaledRadialKernel_sum (L : ℝ) (hL : 1 ≤ L) :
    Summable (fun n : frequencyLattice => ((1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (12 : ℕ))⁻¹) ∧
      (∑' n : frequencyLattice, ((1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (12 : ℕ))⁻¹) ≤
        ((1 + 2 * Real.pi) * L) ^ 12 := by
  have hnon (n : frequencyLattice) :
      0 ≤ ((1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (12 : ℕ))⁻¹ := by positivity
  have hb (S : Finset frequencyLattice) :
      (∑ n ∈ S, ((1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (12 : ℕ))⁻¹) ≤
        ((1 + 2 * Real.pi) * L) ^ 12 :=
    (Finset.sum_le_sum (fun n _ => scaledRadialKernel_le_product L hL n)).trans
      (sum_scaledCauchyKernel_product L hL S)
  have hs := summable_of_sum_le hnon hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

end DefocusingNLS

end OAI
