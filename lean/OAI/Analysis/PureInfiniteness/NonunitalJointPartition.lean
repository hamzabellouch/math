import OAI.Analysis.PureInfiniteness.FiniteJointSubalgebra
import OAI.Analysis.PureInfiniteness.JointSpectralPartition
import OAI.Analysis.PureInfiniteness.JointSpectralSecondMoment
import OAI.Analysis.PureInfiniteness.JointSpectralQuadratic

namespace OAI

/-! An actual finite spectral partition in the original nonunital algebra.
The augmentation-kernel calculation removes the origin cells; the mesh error
is retained explicitly for the fixed-cut compression argument. -/

noncomputable section
open scoped BigOperators ComplexOrder IsMulCommutative

namespace WeakPureInfiniteness

section Commutative
variable {D I : Type*} [CommCStarAlgebra D] [Fintype I] [DecidableEq I]

lemma norm_sum_productGridPlateau_subset_le (a : I → D)
    (ha : ∀ i, IsSelfAdjoint (a i)) (r : ℝ) (s : I → Finset ℤ)
    (T : Finset (SpectralGridCell s)) :
    ‖∑ k ∈ T, productGridPlateauElement a r s k‖ ≤ (5 : ℝ) ^ Fintype.card I := by
  apply norm_le_of_spectralCharacters _ _ (by positivity)
  intro χ
  rw [map_sum]
  simp_rw [scalarStarHom_productGridPlateau _ a ha]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  let x (i : I) := (spectralCharacter χ (a i)).re / r
  rw [abs_of_nonneg (Finset.sum_nonneg (fun k _ => (productGridPlateau_bounds s k x).1))]
  calc
    _ ≤ ∑ k : SpectralGridCell s, productGridPlateau s k x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
        (fun k _ _ => (productGridPlateau_bounds s k x).1)
    _ ≤ _ := sum_productGridPlateau_le s x

end Commutative

variable {A I : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype I] [DecidableEq I]

omit [PartialOrder A] [StarOrderedRing A] [Fintype I] [DecidableEq I] in
lemma norm_of_joint_lift (a : I → A) (x : jointSpectralAlgebra a) (v : A)
    (hv : (v : Unitization ℂ A) = (x : Unitization ℂ A)) : ‖v‖ = ‖x‖ := by
  exact (Unitization.norm_inr (𝕜 := ℂ) (a := v)).symm.trans (congrArg norm hv)

omit [PartialOrder A] [StarOrderedRing A] [Fintype I] [DecidableEq I] in
lemma norm_sub_sum_smul_joint_lifts (a : I → A) {J : Type*} [Fintype J]
    (x : jointSpectralAlgebra a) (v : A)
    (hx : (v : Unitization ℂ A) = (x : Unitization ℂ A))
    (u : J → jointSpectralAlgebra a) (w : J → A)
    (hw : ∀ j, (w j : Unitization ℂ A) = (u j : Unitization ℂ A)) (c : J → ℂ) :
    ‖v - ∑ j, c j • w j‖ = ‖x - ∑ j, c j • u j‖ := by
  apply norm_of_joint_lift a
  change (Unitization.inrNonUnitalStarAlgHom ℂ A) (v - ∑ j, c j • w j) =
    (jointSpectralAlgebra a).subtype (x - ∑ j, c j • u j)
  rw [map_sub, map_sum, map_sub, map_sum]
  refine congrArg₂ (fun z w : Unitization ℂ A => z - w) hx ?_
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = c j • (w j : Unitization ℂ A) :=
      (Unitization.inrNonUnitalStarAlgHom ℂ A).map_smul _ _
    _ = c j • (u j : Unitization ℂ A) := congrArg (fun z => c j • z) (hw j)
    _ = _ := (map_smul (jointSpectralAlgebra a).subtype _ _).symm

omit [PartialOrder A] [StarOrderedRing A] [Fintype I] [DecidableEq I] in
lemma joint_lift_mul (a : I → A) (x y : jointSpectralAlgebra a) (v w : A)
    (hv : (v : Unitization ℂ A) = (x : Unitization ℂ A))
    (hw : (w : Unitization ℂ A) = (y : Unitization ℂ A)) :
    ((v * w : A) : Unitization ℂ A) = ((x * y : jointSpectralAlgebra a) : Unitization ℂ A) := by
  change (Unitization.inrNonUnitalStarAlgHom ℂ A) (v * w) =
    (jointSpectralAlgebra a).subtype (x * y)
  rw [map_mul, map_mul]
  exact congrArg₂ (fun z w : Unitization ℂ A => z * w) hv hw

omit [PartialOrder A] [StarOrderedRing A] [Fintype I] [DecidableEq I] in
lemma joint_lift_sampledQuadraticError (a : I → A) (x y : jointSpectralAlgebra a)
    (v w : A) (hv : (v : Unitization ℂ A) = (x : Unitization ℂ A))
    (hw : (w : Unitization ℂ A) = (y : Unitization ℂ A)) (t : ℝ) :
    ((sampledQuadraticError v w t : A) : Unitization ℂ A) =
      ((sampledQuadraticError x y t : jointSpectralAlgebra a) : Unitization ℂ A) := by
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ A
  let ψ := (jointSpectralAlgebra a).subtype.toNonUnitalStarAlgHom
  change φ (sampledQuadraticError v w t) = ψ (sampledQuadraticError x y t)
  calc
    _ = sampledQuadraticError (φ v) (φ w) t := map_sampledQuadraticError φ v w t
    _ = sampledQuadraticError (ψ x) (ψ y) t :=
      congrArg₂ (fun z w : Unitization ℂ A => sampledQuadraticError z w t) hv hw
    _ = _ := (map_sampledQuadraticError ψ x y t).symm

omit [PartialOrder A] [StarOrderedRing A] [Fintype I] [DecidableEq I] in
lemma norm_sum_of_joint_lifts (a : I → A) {J : Type*} [Fintype J]
    (u : J → jointSpectralAlgebra a) (v : J → A)
    (hv : ∀ j, (v j : Unitization ℂ A) = (u j : Unitization ℂ A)) :
    ‖∑ j, v j‖ = ‖∑ j, u j‖ := by
  have he : ((∑ j, v j : A) : Unitization ℂ A) =
      ((∑ j, u j : jointSpectralAlgebra a) : Unitization ℂ A) := by
    change (Unitization.inrNonUnitalStarAlgHom ℂ A) (∑ j, v j) =
      (jointSpectralAlgebra a).subtype (∑ j, u j)
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun j _ => hv j)
  calc
    _ = ‖((∑ j, v j : A) : Unitization ℂ A)‖ := (Unitization.norm_inr (𝕜 := ℂ) (a := ∑ j, v j)).symm
    _ = ‖((∑ j, u j : jointSpectralAlgebra a) : Unitization ℂ A)‖ := congrArg norm he
    _ = _ := rfl

omit [PartialOrder A] [StarOrderedRing A] [Fintype I] [DecidableEq I] in
lemma commute_of_joint_lifts (a : I → A) (x y : jointSpectralAlgebra a) (u v : A)
    (hu : (u : Unitization ℂ A) = (x : Unitization ℂ A))
    (hv : (v : Unitization ℂ A) = (y : Unitization ℂ A)) (hxy : Commute x y) :
    Commute u v := by
  apply Commute.of_map (f := Unitization.inrNonUnitalStarAlgHom ℂ A)
    (Unitization.inr_injective (R := ℂ))
  change Commute (u : Unitization ℂ A) (v : Unitization ℂ A)
  rw [hu, hv]
  exact hxy.map (jointSpectralAlgebra a).subtype

/-- Finite joint spectral localization for commuting positive elements. The
sum-of-plateaux bound is independent of the mesh and of the number of cells. -/
theorem exists_nonunital_joint_partition (a : I → A) (ha : ∀ i, 0 ≤ a i)
    (hc : ∀ i j, Commute (a i) (a j)) (r : ℝ) (hr : 0 < r) :
    ∃ n : ℕ, ∃ f g : Fin n → A, ∃ t : I → Fin n → ℝ,
      (∀ j, 0 ≤ f j ∧ ‖f j‖ ≤ 1 ∧ 0 ≤ g j ∧ ‖g j‖ ≤ 1 ∧ f j * g j = g j) ∧
      ‖∑ j, f j‖ ≤ (5 : ℝ) ^ Fintype.card I ∧ ‖∑ j, g j‖ ≤ 1 ∧
      (∀ i j, 0 ≤ t i j) ∧
      (∀ i, ‖a i - ∑ j, (t i j : ℂ) • g j‖ ≤ r) ∧
      (∀ i j, Commute (a i) (f j) ∧ Commute (a i) (g j)) ∧
      (∀ j k, Commute (f j) (f k) ∧ Commute (f j) (g k) ∧ Commute (g j) (g k)) ∧
      (∀ i, ‖a i * a i - ∑ j, (((t i j) ^ 2 : ℝ) : ℂ) • g j‖ ≤ r ^ 2) ∧
      (∀ i, ‖∑ j, sampledQuadraticError (a i) (f j) (t i j)‖ ≤
        4 * r ^ 2 * (5 : ℝ) ^ Fintype.card I) ∧
      (∀ i j, t i j ≤ (∑ k, ‖a k‖) + 2 * r) := by
  classical
  let D := jointSpectralAlgebra a
  let _ : IsMulCommutative D := jointSpectralAlgebra_commutative a
    (fun i => (ha i).isSelfAdjoint) hc
  let b : I → D := jointSpectralGenerator a
  have hbp (i : I) : 0 ≤ b i := jointSpectralGenerator_nonneg a ha i
  have hbs (i : I) : IsSelfAdjoint (b i) := hbp i |>.isSelfAdjoint
  let N : ℤ := ⌈(∑ i, ‖b i‖) / r⌉
  have hN := jointGrid_bound_at_ceil b hbp r hr
  let S : Finset (SpectralGridCell (jointGrid (I := I) N)) :=
    Finset.univ.filter (retainedSpectralCell _)
  let e : Fin S.card ≃ S := S.equivFin.symm
  let F (j : Fin S.card) : D := productGridPlateauElement b r _ (e j).val
  let G (j : Fin S.card) : D := productGridHatElement b r _ (e j).val
  have hret (j : Fin S.card) : retainedSpectralCell _ (e j).val :=
    (Finset.mem_filter.mp (e j).property).2
  have hF0 (j : Fin S.card) : jointSpectralAugmentation a (F j) = 0 :=
    jointGridPlateau_in_kernel _ b hbs (fun i => jointSpectralAugmentation_generator a i)
      r N _ (hret j)
  have hG0 (j : Fin S.card) : jointSpectralAugmentation a (G j) = 0 :=
    jointGridHat_in_kernel _ b hbs (fun i => jointSpectralAugmentation_generator a i)
      r N _ (hret j)
  let f (j : Fin S.card) := jointOriginalElement (A := A) a (F j)
  let g (j : Fin S.card) := jointOriginalElement (A := A) a (G j)
  let t (i : I) (j : Fin S.card) : ℝ := r * ((e j).val i : ℝ)
  have hf (j) : (f j : Unitization ℂ A) = (F j : Unitization ℂ A) :=
    jointOriginalElement_inr a (F j) (hF0 j)
  have hg (j) : (g j : Unitization ℂ A) = (G j : Unitization ℂ A) :=
    jointOriginalElement_inr a (G j) (hG0 j)
  have hsumF : (∑ j, F j) = ∑ k ∈ S, productGridPlateauElement b r _ k := by
    exact (e.sum_comp (fun k : S => productGridPlateauElement b r _ k.val)).trans
      (Finset.sum_coe_sort S _)
  have hsumG : (∑ j, G j) = ∑ k ∈ S, productGridHatElement b r _ k := by
    exact (e.sum_comp (fun k : S => productGridHatElement b r _ k.val)).trans
      (Finset.sum_coe_sort S _)
  refine ⟨S.card, f, g, t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine ⟨jointOriginalElement_nonneg a (F j) (hF0 j)
      (productGridPlateauElement_nonneg b r _ _), ?_,
      jointOriginalElement_nonneg a (G j) (hG0 j)
      (productGridHatElement_nonneg b r _ _), ?_, ?_⟩
    · rw [jointOriginalElement_norm a (F j) (hF0 j)]
      exact norm_productGridPlateauElement_le_one b hbs r _ _
    · rw [jointOriginalElement_norm a (G j) (hG0 j)]
      exact norm_productGridHatElement_le_one b hbs r _ _
    · apply Unitization.inr_injective (R := ℂ)
      rw [Unitization.inr_mul, hf, hg]
      exact congrArg (fun x : D => (x : Unitization ℂ A))
        (productGridPlateauElement_mul_hat b r _ (e j).val)
  · rw [norm_sum_of_joint_lifts a F f hf, hsumF]
    exact norm_sum_productGridPlateau_subset_le b hbs r _ S
  · rw [norm_sum_of_joint_lifts a G g hg, hsumG]
    exact norm_sum_retained_hats_le b hbs r N hN
  · intro i j
    apply mul_nonneg hr.le
    exact_mod_cast (Finset.mem_Icc.mp ((e j).val i).property).1
  · intro i
    have hs : (∑ j, (t i j : ℂ) • G j) = jointGridReconstruction b r N i := by
      calc
        _ = ∑ k : S, ((r * (k.val i : ℝ) : ℝ) : ℂ) •
            productGridHatElement b r _ k.val := e.sum_comp _
        _ = ∑ k ∈ S, ((r * (k i : ℝ) : ℝ) : ℂ) •
            productGridHatElement b r _ k := Finset.sum_coe_sort S
              (fun (k : SpectralGridCell (jointGrid (I := I) N)) =>
                ((r * (k i : ℝ) : ℝ) : ℂ) • productGridHatElement b r _ k)
        _ = _ := rfl
    rw [norm_sub_sum_smul_joint_lifts a (b i) (a i) rfl G g hg, hs]
    exact norm_jointGridReconstruction_sub_le b hbs r hr N hN i
  · intro i j
    exact ⟨commute_of_joint_lifts a (b i) (F j) (a i) (f j) rfl (hf j) (mul_comm _ _),
      commute_of_joint_lifts a (b i) (G j) (a i) (g j) rfl (hg j) (mul_comm _ _)⟩
  · intro j k
    exact ⟨commute_of_joint_lifts a (F j) (F k) (f j) (f k) (hf j) (hf k) (mul_comm _ _),
      commute_of_joint_lifts a (F j) (G k) (f j) (g k) (hf j) (hg k) (mul_comm _ _),
      commute_of_joint_lifts a (G j) (G k) (g j) (g k) (hg j) (hg k) (mul_comm _ _)⟩
  · intro i
    have hs : (∑ j, (((t i j) ^ 2 : ℝ) : ℂ) • G j) =
        jointGridSquareReconstruction b r N i := by
      calc
        _ = ∑ k : S, (((r * (k.val i : ℝ)) ^ 2 : ℝ) : ℂ) •
            productGridHatElement b r _ k.val := e.sum_comp _
        _ = ∑ k ∈ S, (((r * (k i : ℝ)) ^ 2 : ℝ) : ℂ) •
            productGridHatElement b r _ k := Finset.sum_coe_sort S
              (fun (k : SpectralGridCell (jointGrid (I := I) N)) =>
                (((r * (k i : ℝ)) ^ 2 : ℝ) : ℂ) • productGridHatElement b r _ k)
        _ = _ := rfl
    rw [norm_sub_sum_smul_joint_lifts a (b i * b i) (a i * a i)
      (joint_lift_mul a (b i) (b i) (a i) (a i) rfl rfl) G g hg, hs]
    exact norm_jointGridSquareReconstruction_sub_le b hbs r hr N hN i
  · intro i
    have he (j) : ((sampledQuadraticError (a i) (f j) (t i j) : A) : Unitization ℂ A) =
        (sampledQuadraticError (b i) (F j) (t i j) : D) :=
      joint_lift_sampledQuadraticError a (b i) (F j) (a i) (f j) rfl (hf j) (t i j)
    rw [norm_sum_of_joint_lifts a _ _ he]
    have hs : (∑ j, sampledQuadraticError (b i) (F j) (t i j)) =
        ∑ k ∈ S, sampledQuadraticError (b i) (productGridPlateauElement b r _ k)
          (r * (k i : ℝ)) := by
      exact (e.sum_comp (fun k : S => sampledQuadraticError (b i)
        (productGridPlateauElement b r _ k.val) (r * (k.val i : ℝ)))).trans
        (Finset.sum_coe_sort S (fun (k : SpectralGridCell (jointGrid (I := I) N)) =>
          sampledQuadraticError (b i) (productGridPlateauElement b r _ k) (r * (k i : ℝ))))
    rw [hs]
    exact norm_sum_sampledQuadraticError_le b hbs r hr _ S i
  · intro i j
    have hki : ((e j).val i : ℤ) ≤ N + 1 :=
      (Finset.mem_Icc.mp ((e j).val i).property).2
    have hkiR : (((e j).val i : ℤ) : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hki
    have hnR : (N : ℝ) < (∑ k, ‖b k‖) / r + 1 := Int.ceil_lt_add_one _
    have hNmul : r * (N : ℝ) ≤ (∑ k, ‖b k‖) + r := by
      have ht := mul_le_mul_of_nonneg_left hnR.le hr.le
      rw [mul_add, mul_one, mul_div_cancel₀ _ hr.ne'] at ht
      exact ht
    have hab : (∑ k, ‖b k‖) = ∑ k, ‖a k‖ := by
      apply Finset.sum_congr rfl
      intro k _
      exact Unitization.norm_inr (𝕜 := ℂ) (a := a k)
    change r * (((e j).val i : ℤ) : ℝ) ≤ _
    rw [← hab]
    nlinarith [mul_le_mul_of_nonneg_left hkiR hr.le]

end WeakPureInfiniteness

end

end OAI
