import Mathlib
import OAI.Analysis.LaughlinGap.NormalOrder

namespace OAI

/-! Creation. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma creation_anticommute {n : ℕ} (i j : Fin n) :
    creation i * creation j = -(creation j * creation i) := by
  have h := congrArg (fun T : Module.End ℂ (Hilbert n) => T.adjoint)
    (annihilation_anticommute j i)
  simpa only [adjoint_mul, annihilation_adjoint, map_neg] using h

noncomputable def creationCombination (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] Module.End ℂ (Hilbert n) where
  toFun v := ∑ i, (v i) • creation i
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [smul_smul, Finset.smul_sum]

lemma creationCombination_square (n : ℕ) (v : Fin n → ℂ) :
    creationCombination n v * creationCombination n v = 0 := by
  have h : creationCombination n v * creationCombination n v =
      -(creationCombination n v * creationCombination n v) := by
    simp only [creationCombination, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [creation_anticommute j i, mul_comm (v j) (v i), smul_neg]
  apply LinearMap.ext
  intro x
  ext A
  have he := congrArg (fun T : Module.End ℂ (Hilbert n) => T x A) h
  change (creationCombination n v * creationCombination n v) x A =
    -((creationCombination n v * creationCombination n v) x A) at he
  change (creationCombination n v * creationCombination n v) x A = 0
  linear_combination (1/2 : ℂ) * he

noncomputable def creationExteriorHom (n : ℕ) :
    ExteriorAlgebra ℂ (Fin n → ℂ) →ₐ[ℂ] Module.End ℂ (Hilbert n) :=
  ExteriorAlgebra.lift ℂ ⟨creationCombination n, creationCombination_square n⟩

@[simp] lemma creationCombination_single {n : ℕ} (j : Fin n) :
    creationCombination n (Pi.single j 1) = creation j := by
  classical
  simp [creationCombination, Pi.single_apply, ite_smul]

lemma creationExteriorHom_multi {n N : ℕ} (a : Fin N → Fin n) :
    creationExteriorHom n (ExteriorAlgebra.ιMulti ℂ N (fun i => Pi.single (a i) 1)) =
      (word (List.ofFn a)).adjoint := by
  induction N with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply, word_nil]
  | succ N ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    simp only [creationExteriorHom, ExteriorAlgebra.lift_ι_apply, creationCombination_single]
    change creation (a 0) * creationExteriorHom n
      (ExteriorAlgebra.ιMulti ℂ N (fun i => Pi.single (a i.succ) 1)) = _
    rw [ih]
    simp only [List.ofFn_succ, word_cons, adjoint_mul, annihilation_adjoint]

lemma word_ofFn_swap {n N : ℕ} (a : Fin N → Fin n) (i j : Fin N) (hij : i ≠ j) :
    word (List.ofFn (a ∘ Equiv.swap i j)) = -word (List.ofFn a) := by
  have hh := (ExteriorAlgebra.ιMulti ℂ N (M := Fin n → ℂ)).map_swap
    (fun k => Pi.single (a k) 1) hij
  have he := congrArg (creationExteriorHom n) hh
  simp only [map_neg] at he
  change creationExteriorHom n (ExteriorAlgebra.ιMulti ℂ N
    (fun k => Pi.single ((a ∘ Equiv.swap i j) k) 1)) = _ at he
  rw [creationExteriorHom_multi, creationExteriorHom_multi] at he
  have hf := congrArg (fun T : Module.End ℂ (Hilbert n) => T.adjoint) he
  simpa only [LinearMap.adjoint_adjoint, map_neg] using hf

theorem normalizedReadout_antisymmetric {Q N : ℕ} (x : Hilbert (Q+1)) :
    Antisymmetric (WithLp.ofLp (normalizedReadout (Q+1) N x)) := by
  intro i j hij a
  simp only [normalizedReadout_apply, word_ofFn_swap a i j hij,
    LinearMap.neg_apply, PiLp.neg_apply, mul_neg]

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped BigOperators InnerProduct

lemma Antisymmetric.perm {N Q : ℕ} {ψ : State N Q} (hψ : Antisymmetric ψ)
    (a : Configuration N Q) (σ : Equiv.Perm (Fin N)) :
    ψ (a ∘ σ) = Equiv.Perm.sign σ • ψ a := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap s i j hij ih => simp_all [← Function.comp_assoc, hψ i j hij]

lemma Antisymmetric.eq_zero_of_not_injective {N Q : ℕ} {ψ : State N Q}
    (hψ : Antisymmetric ψ) {a : Configuration N Q} (ha : ¬ Function.Injective a) :
    ψ a = 0 := by
  classical
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp ha
  have he : a ∘ Equiv.swap i j = a := by
    ext k
    by_cases hki : k = i
    · subst k; simp [hij]
    by_cases hkj : k = j
    · subst k; simp [hij]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hh := hψ i j hne a
  rw [he] at hh
  linear_combination (1/2 : ℂ) * hh

lemma Antisymmetric.ext_increasing {N Q : ℕ} {ψ φ : State N Q}
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ)
    (he : ∀ a, StrictMono a → ψ a = φ a) : ψ = φ := by
  funext a
  by_cases hi : Function.Injective a
  · have hs : StrictMono (a ∘ Tuple.sort a) :=
      (Tuple.monotone_sort a).strictMono_of_injective (hi.comp (Tuple.sort a).injective)
    have he' := he (a ∘ Tuple.sort a) hs
    rw [Antisymmetric.perm hψ, Antisymmetric.perm hφ] at he'
    exact (smul_left_cancel _ he')
  · rw [Antisymmetric.eq_zero_of_not_injective hψ hi,
      Antisymmetric.eq_zero_of_not_injective hφ hi]

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

noncomputable def increasingConfiguration {n N : ℕ} (A : BasisLabel n N) : Fin N → Fin n :=
  A.val.orderEmbOfFin A.property

lemma increasingConfiguration_strictMono {n N : ℕ} (A : BasisLabel n N) :
    StrictMono (increasingConfiguration A) := (A.val.orderEmbOfFin A.property).strictMono

lemma ofFn_increasingConfiguration {n N : ℕ} (A : BasisLabel n N) :
    List.ofFn (increasingConfiguration A) = A.val.sort (· ≤ ·) := by
  rw [List.ofFn_eq_map]
  exact A.val.listMap_orderEmbOfFin_finRange A.property

@[simp] lemma normalizedReadout_increasing {n N : ℕ} (x : Hilbert n) (A : BasisLabel n N) :
    normalizedReadout n N x (increasingConfiguration A) =
      ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) * x A.val := by
  rw [normalizedReadout_apply, ofFn_increasingConfiguration]
  rw [show word (A.val.sort (· ≤ ·)) = basisContraction A from rfl,
    basisContraction_apply_empty]

noncomputable def coordinatesFromTensor (Q N : ℕ) : TensorHilbert N Q →ₗ[ℂ]
    ExteriorCoordinates (Q+1) N where
  toFun ψ := WithLp.toLp 2 (fun A => (Real.sqrt (N.factorial : ℝ) : ℂ) *
    ψ (increasingConfiguration A))
  map_add' ψ φ := by ext A; exact mul_add _ _ _
  map_smul' c ψ := by ext A; exact mul_left_comm _ _ _

@[simp] lemma coordinatesFromTensor_apply {Q N : ℕ} (ψ : TensorHilbert N Q)
    (A : BasisLabel (Q+1) N) :
    coordinatesFromTensor Q N ψ A = (Real.sqrt (N.factorial : ℝ) : ℂ) *
      ψ (increasingConfiguration A) := rfl

lemma coordinatesFromTensor_readout {Q N : ℕ} (x : ExteriorCoordinates (Q+1) N) :
    coordinatesFromTensor Q N (normalizedReadout (Q+1) N (sectorInclusion (Q+1) N x)) = x := by
  have hs : (Real.sqrt (N.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos N))
  ext A
  simp only [coordinatesFromTensor_apply, normalizedReadout_increasing,
    sectorInclusion_apply_label]
  field_simp

theorem readout_coordinatesFromTensor {Q N : ℕ} {ψ : TensorHilbert N Q}
    (hψ : Antisymmetric (WithLp.ofLp ψ)) :
    normalizedReadout (Q+1) N (sectorInclusion (Q+1) N (coordinatesFromTensor Q N ψ)) = ψ := by
  classical
  apply (WithLp.equiv 2 _).injective
  apply Antisymmetric.ext_increasing (normalizedReadout_antisymmetric _) hψ
  intro a ha
  let A : BasisLabel (Q+1) N := ⟨Finset.univ.image a, by
    rw [Finset.card_image_of_injective _ ha.injective, Finset.card_fin]⟩
  have he : increasingConfiguration A = a := by
    symm
    exact Finset.orderEmbOfFin_unique A.property (by intro i; exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩) ha
  rw [← he]
  change normalizedReadout (Q+1) N _ (increasingConfiguration A) = ψ (increasingConfiguration A)
  rw [normalizedReadout_increasing, sectorInclusion_apply_label,
    coordinatesFromTensor_apply, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos N))

@[simp] lemma sectorReadout_inclusion {n k : ℕ} (x : ExteriorCoordinates n k) :
    sectorReadout n k (sectorInclusion n k x) = x := by
  ext A
  rw [sectorReadout_apply, sectorInclusion_apply_label]

lemma sectorInclusion_norm_sq {n k : ℕ} (x : ExteriorCoordinates n k) :
    ‖sectorInclusion n k x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    ← LinearMap.adjoint_inner_right, sectorInclusion_adjoint, sectorReadout_inclusion]

noncomputable def exteriorTensorIsometry (Q N : ℕ) :
    ExteriorCoordinates (Q+1) N ≃ₗᵢ[ℂ] SectorHilbert N Q where
  toFun x := ⟨normalizedReadout (Q+1) N (sectorInclusion (Q+1) N x), normalizedReadout_antisymmetric _⟩
  invFun ψ := coordinatesFromTensor Q N ψ.val
  left_inv x := coordinatesFromTensor_readout x
  right_inv ψ := Subtype.ext (readout_coordinatesFromTensor ψ.property)
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp
  norm_map' x := by
    change ‖normalizedReadout (Q+1) N (sectorInclusion (Q+1) N x)‖ = ‖x‖
    have he := normalizedReadout_norm_sq (sectorInclusion_homogeneous x)
    rw [sectorInclusion_norm_sq] at he
    nlinarith [norm_nonneg (normalizedReadout (Q+1) N (sectorInclusion (Q+1) N x)), norm_nonneg x]

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped InnerProduct

lemma unitary_conj_eq_of_quadraticForm {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (A : Module.End ℂ E) (B : Module.End ℂ F)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (h : ∀ x, (inner ℂ (U x) (B (U x))).re = (inner ℂ x (A x)).re) :
    U.symm.toLinearMap ∘ₗ B ∘ₗ U.toLinearMap = A := by
  apply (ext_inner_map _ _).mp
  intro x
  change inner ℂ (U.symm (B (U x))) x = inner ℂ (A x) x
  have hi := U.inner_map_map (U.symm (B (U x))) x
  simp only [LinearIsometryEquiv.apply_symm_apply] at hi
  rw [← hi, ← hB.coe_re_inner_apply_self, ← hA.coe_re_inner_apply_self]
  congr 1
  rw [inner_re_symm, inner_re_symm (𝕜 := ℂ) (A x) x]
  exact h x

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma sum_symmetric_triangle {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin n → Fin n → A) (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) := by
  classical
  have he (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h, hs i j]
  conv_lhs => arg 2; intro i; arg 2; intro j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then f j i else 0)]

lemma orderedPair_contraction (Q p : ℕ) :
    (∑ i : Fin (Q+1), ∑ j : Fin (Q+1), (pairCoefficient Q p i j : ℂ) •
      (annihilation j * annihilation i)) =
    (Real.sqrt 2 : ℂ) • localPair (Q+1) Q p := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  let T : Module.End ℂ (Hilbert (Q+1)) := ∑ i, ∑ j, if i < j then
    (pairCoefficient Q p i j : ℂ) • (annihilation j * annihilation i) else 0
  have he : localPair (Q+1) Q p = (Real.sqrt 2 : ℂ) • T := by
    simp only [localPair, pairAnnihilator, sphericalExteriorPairCoefficient_eq_tensor,
      Complex.star_def, map_mul, Complex.conj_ofReal, Complex.ofReal_mul, mul_smul, T,
      Finset.smul_sum, smul_ite, smul_zero]
  rw [sum_symmetric_triangle, he, smul_smul, hs]
  · change T + T = (2:ℂ) • T
    module
  · intro i j
    rw [pairCoefficient_swap Q p i j, annihilation_anticommute i j]
    simp
  · intro i
    simp [pairCoefficient]

lemma update_cons_cons {N Q : ℕ} (a : Configuration N Q) (u v x y : Fin (Q+1)) :
    Function.update (Function.update (Fin.cons u (Fin.cons v a) : Configuration (N+2) Q) (0 : Fin (N+2)) x)
      (1 : Fin (N+2)) y = (Fin.cons x (Fin.cons y a) : Configuration (N+2) Q) := by
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · simp
  · simp
  · have hk : k.succ.succ ≠ (1 : Fin (N+2)) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_one] at hv
      omega
    simp [Function.update_of_ne hk]

lemma readout_pairAmplitude_head {N Q : ℕ} (x : Hilbert (Q+1)) (p : ℕ)
    (a : Configuration N Q) :
    pairAmplitude (WithLp.ofLp (normalizedReadout (Q+1) (N+2) x))
      0 1 p (Fin.cons 0 (Fin.cons 0 a)) =
      (((Real.sqrt ((N+2).factorial : ℝ))⁻¹ : ℂ) * (Real.sqrt 2 : ℂ)) *
        rawReadout (Q+1) N (localPair (Q+1) Q p x) a := by
  have he := congrArg (fun T : Module.End ℂ (Hilbert (Q+1)) =>
    rawReadout (Q+1) N (T x) a) (orderedPair_contraction Q p)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] at he
  simp only [pairAmplitude, update_cons_cons, normalizedReadout_apply,
    List.ofFn_cons, word_cons, Module.End.mul_apply]
  simp only [rawReadout_apply, Module.End.mul_apply] at he
  change (∑ i : Fin (Q+1), ∑ j : Fin (Q+1), (pairCoefficient Q p i j : ℂ) *
      (((Real.sqrt ((N+2).factorial : ℝ))⁻¹ : ℂ) *
        word (List.ofFn a) (annihilation j (annihilation i x)) ∅)) = _
  calc
    _ = (((Real.sqrt ((N+2).factorial : ℝ))⁻¹ : ℂ)) *
        (∑ i : Fin (Q+1), ∑ j : Fin (Q+1), (pairCoefficient Q p i j : ℂ) *
          word (List.ofFn a) (annihilation j (annihilation i x)) ∅) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [he]; exact (mul_assoc _ _ _).symm

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped BigOperators InnerProduct

noncomputable def pairEnergyAt {N Q : ℕ} (ψ : State N Q) (i j : Fin N) (p : ℕ) : ℝ :=
  ∑ a, if a i = 0 ∧ a j = 0 then ‖pairAmplitude ψ i j p a‖ ^ 2 else 0

lemma sum_head_anchored {N Q : ℕ} (f : Configuration (N+2) Q → ℝ) :
    (∑ a, if a 0 = 0 ∧ a 1 = 0 then f a else 0) =
      ∑ a : Configuration N Q, f (Fin.cons 0 (Fin.cons 0 a)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (N+2) => Fin (Q+1))).sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ x : Fin (Q+1), ∑ a : Configuration (N+1) Q,
    if x = 0 ∧ a 0 = 0 then f (Fin.cons x a) else 0) = _
  simp only [ite_and]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Fin (Q+1))).sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ y : Fin (Q+1), ∑ a : Configuration N Q,
    if y = 0 then f (Fin.cons 0 (Fin.cons y a)) else 0) = _
  simp_rw [Finset.sum_ite_irrel]
  simp

lemma pairAmplitude_perm {N Q : ℕ} {ψ : State N Q} (hψ : Antisymmetric ψ)
    (σ : Equiv.Perm (Fin N)) (i j : Fin N) (p : ℕ) (a : Configuration N Q) :
    pairAmplitude ψ i j p (a ∘ σ) =
      Equiv.Perm.sign σ • pairAmplitude ψ (σ i) (σ j) p a := by
  have hu (x y : Fin (Q+1)) : Function.update (Function.update (a ∘ σ) i x) j y =
      Function.update (Function.update a (σ i) x) (σ j) y ∘ σ := by
    simp only [Function.update_comp_equiv, Equiv.symm_apply_apply]
  simp only [pairAmplitude, hu, Antisymmetric.perm hψ, Finset.smul_sum, mul_smul_comm]

lemma pairEnergyAt_perm {N Q : ℕ} {ψ : State N Q} (hψ : Antisymmetric ψ)
    (σ : Equiv.Perm (Fin N)) (i j : Fin N) (p : ℕ) :
    pairEnergyAt ψ i j p = pairEnergyAt ψ (σ i) (σ j) p := by
  let e : Configuration N Q ≃ Configuration N Q :=
    ⟨fun a => a ∘ σ, fun a => a ∘ σ.symm,
      by intro a; ext k; simp, by intro a; ext k; simp⟩
  unfold pairEnergyAt
  rw [← e.sum_comp]
  change (∑ a, if a (σ i) = 0 ∧ a (σ j) = 0 then
    ‖pairAmplitude ψ i j p (a ∘ σ)‖ ^ 2 else 0) = _
  simp only [pairAmplitude_perm hψ, norm_units_zsmul]

lemma exists_perm_head_pair {N : ℕ} (i j : Fin (N+2)) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (N+2)), σ 0 = i ∧ σ 1 = j := by
  let τ : Equiv.Perm (Fin (N+2)) := Equiv.swap 0 i
  have hτ : τ 0 = i := Equiv.swap_apply_left _ _
  have h10 : (1 : Fin (N+2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_one, Fin.val_zero] at hv
    omega
  have hi : i ≠ τ 1 := by rw [← hτ]; exact fun h => h10 (τ.injective h).symm
  refine ⟨Equiv.swap (τ 1) j * τ, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, hτ]
    exact Equiv.swap_apply_of_ne_of_ne hi hij
  · simp

lemma pairEnergyAt_eq_head {N Q : ℕ} {ψ : State (N+2) Q} (hψ : Antisymmetric ψ)
    (i j : Fin (N+2)) (hij : i ≠ j) (p : ℕ) :
    pairEnergyAt ψ i j p = pairEnergyAt ψ 0 1 p := by
  obtain ⟨σ,h0,h1⟩ := exists_perm_head_pair i j hij
  simpa only [h0,h1] using (pairEnergyAt_perm hψ σ 0 1 p).symm

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

theorem readout_pairEnergyAt_head {N Q : ℕ} {x : Hilbert (Q+1)}
    (hx : Homogeneous (N+2) x) (p : Fin (2*Q-1)) :
    pairEnergyAt (WithLp.ofLp (normalizedReadout (Q+1) (N+2) x)) 0 1 p.val =
      (2 * (N.factorial : ℝ) / ((N+2).factorial : ℝ)) *
        ‖localPair (Q+1) Q p.val x‖ ^ 2 := by
  have hs : 0 < Real.sqrt ((N+2).factorial : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos (N+2))
  have hh : Homogeneous N (localPair (Q+1) Q p.val x) := by
    rw [← physicalPair_contraction]
    exact pairContraction_homogeneous _ hx
  rw [pairEnergyAt, sum_head_anchored]
  simp only [readout_pairAmplitude_head, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs, abs_of_nonneg (Real.sqrt_nonneg 2),
    mul_pow, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ ((N+2).factorial : ℝ)),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), ← Finset.mul_sum,
    ← EuclideanSpace.norm_sq_eq, rawReadout_norm_sq hh]
  ring

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped BigOperators InnerProduct

lemma sum_increasing_positions (N : ℕ) (c : ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, if i < j then c else 0) =
      (N.choose 2 : ℝ) * c := by
  rw [← Fintype.sum_prod_type (f := fun ij : Fin N × Fin N => if ij.1 < ij.2 then c else 0),
    ← Finset.sum_filter, Finset.sum_const,
    Fintype.card_product_filter_lt, Fintype.card_fin, nsmul_eq_mul]

lemma energy_eq_pairEnergyAt_head {N Q : ℕ} {ψ : State (N+2) Q}
    (hψ : Antisymmetric ψ) :
    energy ψ = ((N+2).choose 2 : ℝ) *
      ∑ p : Fin (2*Q-1), pairEnergyAt ψ 0 1 p.val := by
  change (∑ i, ∑ j, if i < j then
    ∑ p ∈ Finset.range (2*Q-1), pairEnergyAt ψ i j p else 0) = _
  have he (i j : Fin (N+2)) :
      (if i < j then ∑ p ∈ Finset.range (2*Q-1), pairEnergyAt ψ i j p else 0) =
      if i < j then ∑ p ∈ Finset.range (2*Q-1), pairEnergyAt ψ 0 1 p else 0 := by
    split_ifs with hij
    · simp_rw [pairEnergyAt_eq_head hψ i j (ne_of_lt hij)]
    · rfl
  simp_rw [he]
  rw [sum_increasing_positions, Fin.sum_univ_eq_sum_range]

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

theorem readout_energy {N Q : ℕ} {x : Hilbert (Q+1)} (hx : Homogeneous (N+2) x) :
    energy (WithLp.ofLp (normalizedReadout (Q+1) (N+2) x)) =
      localPairEnergy (Q+1) (2*Q-1) Q x := by
  rw [energy_eq_pairEnergyAt_head (normalizedReadout_antisymmetric x)]
  simp_rw [readout_pairEnergyAt_head hx]
  rw [← Finset.mul_sum, ← mul_assoc]
  have he : ((N+2).choose 2 : ℝ) * 2 * (N.factorial : ℝ) = ((N+2).factorial : ℝ) := by
    have hn := Nat.choose_mul_factorial_mul_factorial (n := N+2) (k := 2) (by omega)
    norm_num only [Nat.add_sub_cancel, Nat.factorial_two] at hn
    exact_mod_cast hn
  have hpos : ((N+2).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N+2)
  rw [← mul_div_assoc, ← mul_assoc, he, div_self hpos, one_mul]
  rfl

noncomputable def exteriorHamiltonian (N Q : ℕ) :
    Module.End ℂ (ExteriorCoordinates (Q+1) N) :=
  sectorReadout (Q+1) N ∘ₗ physicalOccupationHamiltonian Q ∘ₗ sectorInclusion (Q+1) N

lemma exteriorHamiltonian_positive (N Q : ℕ) : (exteriorHamiltonian N Q).IsPositive := by
  rw [exteriorHamiltonian, ← sectorInclusion_adjoint]
  exact (physicalOccupationHamiltonian_positive Q).adjoint_conj _

lemma exteriorHamiltonian_inner (N Q : ℕ) (x : ExteriorCoordinates (Q+1) N) :
    (inner ℂ x (exteriorHamiltonian N Q x)).re =
      localPairEnergy (Q+1) (2*Q-1) Q (sectorInclusion (Q+1) N x) := by
  change (inner ℂ x (sectorReadout (Q+1) N
    (physicalOccupationHamiltonian Q (sectorInclusion (Q+1) N x)))).re = _
  rw [← sectorInclusion_adjoint, LinearMap.adjoint_inner_right,
    physicalOccupationHamiltonian_inner]

lemma exteriorHamiltonian_inclusion (N Q : ℕ) (x : ExteriorCoordinates (Q+1) N) :
    sectorInclusion (Q+1) N (exteriorHamiltonian N Q x) =
      physicalOccupationHamiltonian Q (sectorInclusion (Q+1) N x) := by
  apply sectorInclusion_readout
  exact pairHamiltonian_preserves_degree _ (sectorInclusion_homogeneous x)

theorem tensor_exteriorHamiltonian (N Q : ℕ) :
    (exteriorTensorIsometry Q (N+2)).symm.toLinearMap ∘ₗ sectorHamiltonian (N+2) Q ∘ₗ
      (exteriorTensorIsometry Q (N+2)).toLinearMap = exteriorHamiltonian (N+2) Q := by
  apply unitary_conj_eq_of_quadraticForm _ _ _
    (exteriorHamiltonian_positive (N+2) Q).isSymmetric
    (sectorHamiltonian_positive (N+2) Q).isSymmetric
  intro x
  rw [sectorHamiltonian_inner, exteriorHamiltonian_inner]
  exact readout_energy (sectorInclusion_homogeneous x)

lemma exteriorTensorIsometry_intertwines (N Q : ℕ) (x : ExteriorCoordinates (Q+1) (N+2)) :
    sectorHamiltonian (N+2) Q (exteriorTensorIsometry Q (N+2) x) =
      exteriorTensorIsometry Q (N+2) (exteriorHamiltonian (N+2) Q x) := by
  have he := congrArg (fun T : Module.End ℂ (ExteriorCoordinates (Q+1) (N+2)) =>
    exteriorTensorIsometry Q (N+2) (T x)) (tensor_exteriorHamiltonian N Q)
  simpa using he

lemma exteriorTensorIsometry_hamiltonian_norm_sq (N Q : ℕ)
    (x : ExteriorCoordinates (Q+1) (N+2)) :
    ‖sectorHamiltonian (N+2) Q (exteriorTensorIsometry Q (N+2) x)‖ ^ 2 =
      ‖physicalOccupationHamiltonian Q (sectorInclusion (Q+1) (N+2) x)‖ ^ 2 := by
  rw [exteriorTensorIsometry_intertwines, LinearIsometryEquiv.norm_map,
    ← exteriorHamiltonian_inclusion, sectorInclusion_norm_sq]

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

theorem sector_square_of_occupation_square {Q : ℕ} (γ : ℝ)
    (h : ∀ x : Hilbert (Q+1), γ * localPairEnergy (Q+1) (2*Q-1) Q x ≤
      ‖physicalOccupationHamiltonian Q x‖ ^ 2) (N : ℕ) (x : SectorHilbert (N+2) Q) :
    γ * energy (WithLp.ofLp x.val) ≤ ‖sectorHamiltonian (N+2) Q x‖ ^ 2 := by
  let y := (exteriorTensorIsometry Q (N+2)).symm x
  have hy : exteriorTensorIsometry Q (N+2) y = x :=
    (exteriorTensorIsometry Q (N+2)).apply_symm_apply x
  rw [← hy, exteriorTensorIsometry_hamiltonian_norm_sq]
  change γ * energy (WithLp.ofLp (normalizedReadout (Q+1) (N+2)
    (sectorInclusion (Q+1) (N+2) y))) ≤ _
  rw [readout_energy (sectorInclusion_homogeneous y)]
  exact h _

theorem mainTarget_of_uniform_occupation_square_estimate
    (h : ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ x : Hilbert (Q+1),
      (1/25 : ℝ) * localPairEnergy (Q+1) (2*Q-1) Q x ≤
        ‖physicalOccupationHamiltonian Q x‖ ^ 2) : MainTarget := by
  obtain ⟨Q₀,hQ₀⟩ := h
  refine ⟨Q₀+2, by omega, ?_⟩
  intro N hN ψ hψ
  have hN2 : 2 ≤ N := by omega
  obtain ⟨n,rfl⟩ : ∃ n, N = n+2 := ⟨N-2, by omega⟩
  exact laughlin_gap_of_sector_square_estimate hN2 (1/25) (by norm_num)
    (sector_square_of_occupation_square _ (hQ₀ _ (by omega)) n) ψ hψ

end LaughlinGap.Occupation

end

end OAI
