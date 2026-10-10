import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.FactorIndependence

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace


open scoped BigOperators
open Set Module

namespace KirchbergRordam.GenericRW

section KernelCharts

variable {J K E : Type*} [Fintype J]


noncomputable def axes (e : J ↪ K) (y : J → ℝ) : K → ℝ := by
  classical
  exact ∑ j, Pi.single (e j) (y j)

lemma axes_apply_pivot (e : J ↪ K) (y : J → ℝ) (j : J) :
    axes e y (e j) = y j := by
  classical
  simp [axes, Finset.sum_apply, Pi.single_apply, e.injective.eq_iff]

lemma axes_apply_off (e : J ↪ K) (y : J → ℝ) {k : K}
    (hk : k ∉ Set.range e) : axes e y k = 0 := by
  classical
  simp only [axes, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  simp only [Pi.single_apply]
  split_ifs with h
  · exact (hk ⟨j, h.symm⟩).elim
  · rfl

lemma axes_zero (e : J ↪ K) : axes e (0 : J → ℝ) = 0 := by
  classical
  simp [axes]

lemma axes_neg (e : J ↪ K) (y : J → ℝ) : axes e (-y) = -axes e y := by
  classical
  simp [axes, Pi.single_neg, Finset.sum_neg_distrib]


abbrev FreeCoordinates (e : J ↪ K) := {k : K // k ∉ Set.range e}

noncomputable def freeVector (e : J ↪ K) (z : FreeCoordinates e → ℝ) : K → ℝ := by
  classical
  exact fun k => if h : k ∈ Set.range e then 0 else z ⟨k, h⟩

lemma freeVector_of_vector (e : J ↪ K) (x : K → ℝ) :
    freeVector e (fun k => x k) = x - axes e (x ∘ e) := by
  classical
  funext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hk
    simp [freeVector, axes_apply_pivot]
  · simp [freeVector, hk, axes_apply_off e _ hk]

variable [Fintype K]

noncomputable instance (e : J ↪ K) : Fintype (FreeCoordinates e) := Fintype.ofFinite _

lemma mulVec_axes [DecidableEq J] (e : J ↪ K) (M : Matrix J K ℝ)
    (hM : ∀ j l, M j (e l) = if j = l then 1 else 0) (y : J → ℝ) :
    M.mulVec (axes e y) = y := by
  classical
  ext j
  simp [axes, Matrix.mulVec_sum, Matrix.mulVec_single, hM]


noncomputable def kernelChart (e : J ↪ K) (M : E → Matrix J K ℝ)
    (q : E × (FreeCoordinates e → ℝ)) : K → ℝ :=
  freeVector e q.2 - axes e ((M q.1).mulVec (freeVector e q.2))

lemma mem_range_kernelChart [DecidableEq J] (e : J ↪ K) (M : E → Matrix J K ℝ)
    (hM : ∀ p j l, M p j (e l) = if j = l then 1 else 0)
    (p : E) (x : K → ℝ) (hx : (M p).mulVec x = 0) :
    x ∈ Set.range (kernelChart e M) := by
  refine ⟨(p, fun k => x k), ?_⟩
  simp only [kernelChart, freeVector_of_vector, Matrix.mulVec_sub,
    mulVec_axes e _ (hM p), hx, zero_sub, axes_neg]
  abel

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiff_freeVector (e : J ↪ K) :
    ContDiff ℝ 1 (freeVector e) := by
  classical
  apply contDiff_pi.mpr
  intro k
  dsimp [freeVector]
  split_ifs
  · exact contDiff_const
  · exact contDiff_apply ℝ ℝ _

lemma contDiff_axes (e : J ↪ K) : ContDiff ℝ 1 (axes e) := by
  classical
  apply contDiff_pi.mpr
  intro k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hk
    simpa only [axes_apply_pivot] using (contDiff_apply ℝ ℝ j :
      ContDiff ℝ 1 (fun y : J → ℝ => y j))
  · simpa only [axes_apply_off e _ hk] using (contDiff_const :
      ContDiff ℝ 1 (fun _ : J → ℝ => (0 : ℝ)))

lemma contDiff_kernelChart (e : J ↪ K) (M : E → Matrix J K ℝ)
    (hM : ∀ j k, ContDiff ℝ 1 (fun p => M p j k)) :
    ContDiff ℝ 1 (kernelChart e M) := by
  classical
  unfold kernelChart
  refine ((contDiff_freeVector e).comp contDiff_snd).sub ?_
  apply (contDiff_axes e).comp
  apply contDiff_pi.mpr
  intro j
  apply ContDiff.sum
  intro k _
  exact ((hM j k).comp contDiff_fst).mul
    ((contDiff_pi.mp (contDiff_freeVector e) k).comp contDiff_snd)

lemma card_freeCoordinates (e : J ↪ K) :
    Fintype.card (FreeCoordinates e) = Fintype.card K - Fintype.card J := by
  classical
  simp only [FreeCoordinates, Fintype.card_subtype_compl]
  rw [Fintype.card_range e]

variable [FiniteDimensional ℝ E]


theorem exists_avoiding_kernels {B : Type*} [Countable B]
    (e : B → J ↪ K) (M : B → E → Matrix J K ℝ) [DecidableEq J]
    (hpivot : ∀ b p j l, M b p j (e b l) = if j = l then 1 else 0)
    (hsmooth : ∀ b j k, ContDiff ℝ 1 (fun p => M b p j k))
    (hdim : finrank ℝ E < Fintype.card J) :
    ∃ x : K → ℝ, ∀ b p, (M b p).mulVec x ≠ 0 := by
  classical
  cases isEmpty_or_nonempty B with
  | inl h => exact ⟨0, fun b => isEmptyElim b⟩
  | inr h =>
    have hJK : Fintype.card J ≤ Fintype.card K :=
      Fintype.card_le_of_embedding (e (Classical.choice h))
    have hD : finrank ℝ E + (Fintype.card K - Fintype.card J) < Fintype.card K :=
      by omega
    let S : Set (K → ℝ) := ⋃ b, Set.range (kernelChart (e b) (M b))
    have hbound : dimH S ≤ (finrank ℝ E + (Fintype.card K - Fintype.card J) : ℕ) := by
      change dimH (⋃ b, Set.range (kernelChart (e b) (M b))) ≤ _
      rw [dimH_iUnion]
      apply iSup_le
      intro b
      simpa only [Module.finrank_prod, Module.finrank_pi, card_freeCoordinates] using
        ((contDiff_kernelChart (e b) (M b) (hsmooth b)).differentiable (by norm_num)).dimH_range_le
    have hsmall : dimH S < finrank ℝ (K → ℝ) := by
      apply hbound.trans_lt
      rw [Module.finrank_pi]
      exact_mod_cast hD
    obtain ⟨x, hx⟩ := (dense_compl_of_dimH_lt_finrank hsmall).nonempty
    refine ⟨x, fun b p hp => hx ?_⟩
    exact Set.mem_iUnion.mpr ⟨b, mem_range_kernelChart (e b) (M b) (hpivot b) p x hp⟩

end KernelCharts

section TensorMatrices

open scoped Classical

variable {N M R : Type*} [Fintype N]


noncomputable def normalizedRow (s : Fin 2 ↪ M) (p : Fin 2 × M → ℝ) :
    Matrix (Fin 2) M ℝ :=
  fun j i => if i = s j then 1 else if i ∈ Set.range s then 0 else p (j, i)

lemma normalizedRow_pivot (s : Fin 2 ↪ M) (p : Fin 2 × M → ℝ) (j k : Fin 2) :
    normalizedRow s p j (s k) = if j = k then 1 else 0 := by
  simp [normalizedRow, s.injective.eq_iff, eq_comm]


def tensorPivot (s : N → Fin 2 ↪ M) (a : R) : (N → Fin 2) ↪ R × (N → M) where
  toFun j := (a, fun l => s l (j l))
  inj' := by
    intro j k h
    funext l
    exact (s l).injective (congrFun (congrArg Prod.snd h) l)


noncomputable def weightedTensorMatrix (s : N → Fin 2 ↪ M) (a : R)
    (p : (N × (Fin 2 × M) → ℝ) × (R → ℝ)) :
    Matrix (N → Fin 2) (R × (N → M)) ℝ :=
  fun j k => (if k.1 = a then 1 else p.2 k.1) *
    ∏ l, normalizedRow (s l) (fun ji => p.1 (l, ji)) (j l) (k.2 l)

lemma weightedTensorMatrix_pivot (s : N → Fin 2 ↪ M) (a : R)
    (p : (N × (Fin 2 × M) → ℝ) × (R → ℝ)) (j k : N → Fin 2) :
    weightedTensorMatrix s a p j (tensorPivot s a k) = if j = k then 1 else 0 := by
  change (if a = a then 1 else p.2 a) *
    (∏ l, normalizedRow (s l) (fun ji => p.1 (l, ji)) (j l) (s l (k l))) = _
  simp only [ite_true, one_mul, normalizedRow_pivot]
  by_cases h : j = k
  · subst k
    simp
  · rw [ite_eq_right h]
    obtain ⟨l, hl⟩ : ∃ l, j l ≠ k l := by
      by_contra! hh
      exact h (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ l) (ite_eq_right hl)

variable [Fintype M] [Fintype R]

lemma contDiff_weightedTensorMatrix (s : N → Fin 2 ↪ M) (a : R)
    (j : N → Fin 2) (k : R × (N → M)) :
    ContDiff ℝ 1 (fun p => weightedTensorMatrix s a p j k) := by
  unfold weightedTensorMatrix
  apply ContDiff.mul
  · split_ifs
    · exact contDiff_const
    · exact (contDiff_apply ℝ ℝ k.1).comp contDiff_snd
  · apply contDiff_prod
    intro l _
    unfold normalizedRow
    split_ifs
    · exact contDiff_const
    · exact contDiff_const
    · exact (contDiff_apply ℝ ℝ (l, (j l, k.2 l))).comp contDiff_fst


theorem exists_tensor_coordinates
    (hdim : Fintype.card N * (2 * Fintype.card M) + Fintype.card R <
      2 ^ Fintype.card N) :
    ∃ x : R × (N → M) → ℝ, ∀ (s : N → Fin 2 ↪ M) (a : R) p,
      (weightedTensorMatrix s a p).mulVec x ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_avoiding_kernels
    (fun b : (N → Fin 2 ↪ M) × R => tensorPivot b.1 b.2)
    (fun b => weightedTensorMatrix b.1 b.2)
    (fun b => weightedTensorMatrix_pivot b.1 b.2)
    (fun b => contDiff_weightedTensorMatrix b.1 b.2) (by
      simpa only [Module.finrank_prod, Module.finrank_pi, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fun] using hdim)
  exact ⟨x, fun s a p => hx (s, a) p⟩

omit [Fintype M] in
lemma normalizedRow_eq (s : Fin 2 ↪ M) (P : Matrix (Fin 2) M ℝ)
    (hP : ∀ j k, P j (s k) = if j = k then 1 else 0) :
    normalizedRow s (fun ji => P ji.1 ji.2) = P := by
  ext j i
  by_cases hi : i ∈ Set.range s
  · obtain ⟨k, rfl⟩ := hi
    exact (normalizedRow_pivot s _ j k).trans (hP j k).symm
  · have hij : i ≠ s j := fun h => hi ⟨j, h.symm⟩
    simp [normalizedRow, hi, hij]


def tensorMatrix (P : N → Matrix (Fin 2) M ℝ) : Matrix (N → Fin 2) (N → M) ℝ :=
  fun j i => ∏ l, P l (j l) (i l)

lemma weightedTensorMatrix_mulVec (s : N → Fin 2 ↪ M) (a : R)
    (P : N → Matrix (Fin 2) M ℝ)
    (hP : ∀ l j k, P l j (s l k) = if j = k then 1 else 0)
    (u : R → ℝ) (hu : u a = 1) (x : R × (N → M) → ℝ) :
    (weightedTensorMatrix s a ((fun p => P p.1 p.2.1 p.2.2), u)).mulVec x =
      ∑ b, u b • (tensorMatrix P).mulVec (fun i => x (b, i)) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, weightedTensorMatrix,
    Fintype.sum_prod_type, normalizedRow_eq _ _ (hP _), tensorMatrix,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hc : (if b = a then 1 else u b) = u b := by split_ifs with h <;> simp_all
  simp only [hc, mul_assoc]


theorem exists_independent_tensor_coordinates
    (hdim : Fintype.card N * (2 * Fintype.card M) + Fintype.card R <
      2 ^ Fintype.card N) :
    ∃ x : R → (N → M) → ℝ, ∀ (s : N → Fin 2 ↪ M)
      (P : N → Matrix (Fin 2) M ℝ),
      (∀ l j k, P l j (s l k) = if j = k then 1 else 0) →
      LinearIndependent ℝ (fun a => (tensorMatrix P).mulVec (x a)) := by
  obtain ⟨x, hx⟩ := exists_tensor_coordinates (N := N) (M := M) (R := R) hdim
  refine ⟨fun a i => x (a, i), fun s P hP => ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  by_contra ha
  let u : R → ℝ := fun b => (g a)⁻¹ * g b
  have hu : u a = 1 := inv_mul_cancel₀ ha
  apply hx s a ((fun p => P p.1 p.2.1 p.2.2), u)
  rw [weightedTensorMatrix_mulVec s a P hP u hu x]
  calc
    ∑ b, u b • (tensorMatrix P).mulVec (fun i => x (b, i)) =
        (g a)⁻¹ • ∑ b, g b • (tensorMatrix P).mulVec (fun i => x (b, i)) := by
      simp only [Finset.smul_sum, smul_smul, u]
    _ = 0 := by rw [hg, smul_zero]

end TensorMatrices


lemma exists_tensor_exponent (m r : ℕ) : ∃ n ≥ 1, n * (2 * m) + r < 2 ^ n := by
  refine ⟨2 * (2 * m + r + 1), by omega, ?_⟩
  have h := Nat.two_mul_sq_add_one_le_two_pow_two_mul (2 * m + r + 1)
  nlinarith


section TensorCoordinates

open scoped Classical
open PiTensorProduct
open scoped TensorProduct

variable {N M R : Type*} [Fintype N] [Fintype M] [Fintype R]


noncomputable def tensorBasis (N M : Type*) [Fintype N] [Fintype M] :
    Basis (N → M) ℝ (⨂[ℝ] _ : N, (M → ℝ)) :=
  Basis.piTensorProduct (fun _ : N => Pi.basisFun ℝ M)

lemma tensorBasis_map_coordinates
    (P : N → (M → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (x : ⨂[ℝ] _ : N, (M → ℝ)) :
    (tensorBasis N (Fin 2)).equivFun (PiTensorProduct.map P x) =
      (tensorMatrix (fun l j i => P l (Pi.single i 1) j)).mulVec
        ((tensorBasis N M).equivFun x) := by
  classical
  conv_lhs => rw [← (tensorBasis N M).sum_equivFun x]
  ext j
  simp only [map_sum, map_smul, tensorBasis, Basis.piTensorProduct_apply,
    Pi.basisFun_apply, PiTensorProduct.map_tprod, Basis.equivFun_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Basis.piTensorProduct_repr_tprod_apply, Pi.basisFun_repr,
    Matrix.mulVec, dotProduct, tensorMatrix]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _


theorem exists_labels_normalized
    (hdim : Fintype.card N * (2 * Fintype.card M) + Fintype.card R <
      2 ^ Fintype.card N) :
    ∃ x : R → (⨂[ℝ] _ : N, (M → ℝ)),
      ∀ (s : N → Fin 2 ↪ M) (P : N → (M → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)),
      (∀ l j k, P l (Pi.single (s l k) 1) j = if j = k then 1 else 0) →
      LinearIndependent ℝ (fun a => PiTensorProduct.map P (x a)) := by
  obtain ⟨x, hx⟩ := exists_independent_tensor_coordinates (N := N) (M := M) (R := R) hdim
  refine ⟨fun a => (tensorBasis N M).equivFun.symm (x a), fun s P hP => ?_⟩
  apply LinearIndependent.of_comp (tensorBasis N (Fin 2)).equivFun.toLinearMap
  have h := hx s (fun l j i => P l (Pi.single i 1) j) hP
  simpa only [LinearEquiv.coe_coe, Function.comp_def, tensorBasis_map_coordinates,
    LinearEquiv.apply_symm_apply] using h


theorem normalize_surjection (P : (M → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (hP : Function.Surjective P) :
    ∃ (s : Fin 2 ↪ M) (L : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)),
      ∀ j k, L (P (Pi.single (s k) 1)) j = if j = k then 1 else 0 := by
  have hspan : Submodule.span ℝ (Set.range (fun i => P (Pi.single i 1))) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hP y
    rw [← (Pi.basisFun ℝ M).sum_repr x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    rw [Pi.basisFun_apply]
    exact Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨κ, a, ha, hsp, hli⟩ :=
    exists_linearIndependent' ℝ (fun i => P (Pi.single i 1))
  let : Fintype κ := Fintype.ofInjective a ha
  let b : Basis κ ℝ (Fin 2 → ℝ) := Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card (Fin 2) = Fintype.card κ := by
    rw [← Module.finrank_pi ℝ, Module.finrank_eq_card_basis b]
  let e : Fin 2 ≃ κ := Fintype.equivOfCardEq hcard
  let d : Basis (Fin 2) ℝ (Fin 2 → ℝ) := b.reindex e.symm
  let s : Fin 2 ↪ M := ⟨a ∘ e, ha.comp e.injective⟩
  refine ⟨s, d.equivFun, ?_⟩
  intro j k
  have hcol : P (Pi.single (s k) 1) = d k := by
    simp [d, s, b]
  rw [hcol, Basis.equivFun_self]
  simp only [eq_comm]


theorem exists_labels_surjective
    (hdim : Fintype.card N * (2 * Fintype.card M) + Fintype.card R <
      2 ^ Fintype.card N) :
    ∃ x : R → (⨂[ℝ] _ : N, (M → ℝ)),
      ∀ (P : N → (M → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)),
      (∀ l, Function.Surjective (P l)) →
      LinearIndependent ℝ (fun a => PiTensorProduct.map P (x a)) := by
  obtain ⟨x, hx⟩ := exists_labels_normalized (N := N) (M := M) (R := R) hdim
  refine ⟨x, fun P hP => ?_⟩
  choose s L hL using fun l => normalize_surjection (P l) (hP l)
  apply LinearIndependent.of_comp (PiTensorProduct.map (fun l => (L l).toLinearMap))
  have h := hx s (fun l => (L l).toLinearMap.comp (P l)) hL
  simpa only [PiTensorProduct.map_comp, LinearMap.coe_comp, Function.comp_def] using h

end TensorCoordinates

section RankReduction

open scoped Classical

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W]


theorem exists_plane_quotient (hV : 2 ≤ finrank ℝ V) :
    ∃ Q : V →ₗ[ℝ] (Fin 2 → ℝ), Function.Surjective Q := by
  let b := Module.finBasis ℝ V
  let s : Fin 2 ↪ Fin (finrank ℝ V) :=
    ⟨Fin.castLE hV, Fin.castLE_injective hV⟩
  let Q : V →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.pi (fun j => b.coord (s j))
  refine ⟨Q, fun y => ⟨b.equivFun.symm (axes s y), ?_⟩⟩
  ext j
  change b.repr (b.equivFun.symm (axes s y)) (s j) = y j
  change b.equivFun (b.equivFun.symm (axes s y)) (s j) = y j
  rw [LinearEquiv.apply_symm_apply, axes_apply_pivot]


theorem exists_surjective_postcomposition (P : V →ₗ[ℝ] W)
    (hP : 2 ≤ finrank ℝ (LinearMap.range P)) :
    ∃ Q : W →ₗ[ℝ] (Fin 2 → ℝ), Function.Surjective (Q.comp P) := by
  obtain ⟨q, hq⟩ := exists_plane_quotient (V := LinearMap.range P) hP
  obtain ⟨Q, hQ⟩ := q.exists_extend
  refine ⟨Q, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hq y
  obtain ⟨v, hv⟩ := z.property
  refine ⟨v, ?_⟩
  change Q (P v) = y
  rw [hv]
  change (Q.comp (LinearMap.range P).subtype) z = y
  rw [hQ, hz]

end RankReduction


open scoped TensorProduct

universe u v

theorem tensor_real_labels
    (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hV : 2 ≤ Module.finrank ℝ V) (r : ℕ) (hr : 1 ≤ r) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ x : Fin r → (⨂[ℝ] _ : Fin n, V),
      ∀ (E : Fin n → Type v) [∀ j, AddCommGroup (E j)] [∀ j, Module ℝ (E j)]
        (P : ∀ j, V →ₗ[ℝ] E j),
        (∀ j, 2 ≤ Module.finrank ℝ (LinearMap.range (P j))) →
        LinearIndependent ℝ (fun a => PiTensorProduct.map P (x a)) := by
  classical
  obtain ⟨n, hn, hdim⟩ := exists_tensor_exponent (Module.finrank ℝ V - 2 + 2) (r - 1 + 1)
  rw [Nat.sub_add_cancel hV, Nat.sub_add_cancel hr] at hdim
  obtain ⟨c, hc⟩ := exists_labels_surjective
    (N := Fin n) (M := Fin (Module.finrank ℝ V)) (R := Fin r)
    (by simpa only [Fintype.card_fin] using hdim)
  let e := (Module.finBasis ℝ V).equivFun
  refine ⟨n, hn, (fun a => PiTensorProduct.map
    (fun _ : Fin n => e.symm.toLinearMap) (c a)), ?_⟩
  intro E hAdd hModule P hP
  choose Q hQ using fun j => exists_surjective_postcomposition (P j) (hP j)
  apply LinearIndependent.of_comp (PiTensorProduct.map Q)
  have hsurj : ∀ j, Function.Surjective
      ((Q j).comp ((P j).comp e.symm.toLinearMap)) := by
    intro j
    exact (hQ j).comp e.symm.surjective
  have h := hc (fun j => (Q j).comp ((P j).comp e.symm.toLinearMap)) hsurj
  simpa only [PiTensorProduct.map_comp, LinearMap.coe_comp, Function.comp_def] using h


end KirchbergRordam.GenericRW

universe uQuot
namespace KirchbergRordam.QuotientNormSupport

theorem distance_eq {R : Type uQuot} [NormedRing R] (I : Ideal R) [I.IsTwoSided]
    [IsClosed (I : Set R)] (x y : R ⧸ I) :
    dist x y = ‖-x + y‖ := dist_eq_norm_neg_add x y

theorem multiplication_bound {R : Type uQuot} [NormedRing R] (I : Ideal R) [I.IsTwoSided]
    [IsClosed (I : Set R)] (x y : R ⧸ I) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖ := le_of_forall_pos_le_add fun ε hε =>
  let neighborhood : ∃ radii : ℝ × ℝ, (0 < radii.1 ∧ 0 < radii.2) ∧
    ∀ point : ℝ × ℝ, (dist point.1 ‖x‖ < radii.1 ∧ dist point.2 ‖y‖ < radii.2) →
      dist (point.1 * point.2) (‖x‖ * ‖y‖) < ε :=
    ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
      Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
  neighborhood.elim fun radii radii_spec =>
    (Submodule.Quotient.norm_mk_lt x radii_spec.1.1).elim fun representative_x x_spec =>
      (Submodule.Quotient.norm_mk_lt y radii_spec.1.2).elim fun representative_y y_spec =>
        let lower_x : ‖x‖ ≤ ‖representative_x‖ :=
          Eq.mp (congrArg (fun value : R ⧸ I => ‖value‖ ≤ ‖representative_x‖) x_spec.1)
            (Submodule.Quotient.norm_mk_le I representative_x)
        let lower_y : ‖y‖ ≤ ‖representative_y‖ :=
          Eq.mp (congrArg (fun value : R ⧸ I => ‖value‖ ≤ ‖representative_y‖) y_spec.1)
            (Submodule.Quotient.norm_mk_le I representative_y)
        let distance_x : dist ‖representative_x‖ ‖x‖ < radii.1 :=
          Eq.mpr (congrArg (fun distance : ℝ => distance < radii.1)
            (Real.dist_eq ‖representative_x‖ ‖x‖))
              (abs_sub_lt_iff.mpr ⟨sub_lt_iff_lt_add'.mpr x_spec.2,
                (sub_nonpos.mpr lower_x).trans_lt radii_spec.1.1⟩)
        let distance_y : dist ‖representative_y‖ ‖y‖ < radii.2 :=
          Eq.mpr (congrArg (fun distance : ℝ => distance < radii.2)
            (Real.dist_eq ‖representative_y‖ ‖y‖))
              (abs_sub_lt_iff.mpr ⟨sub_lt_iff_lt_add'.mpr y_spec.2,
                (sub_nonpos.mpr lower_y).trans_lt radii_spec.1.2⟩)
        let product_distance :=
          radii_spec.2 (‖representative_x‖, ‖representative_y‖) ⟨distance_x, distance_y⟩
        let product_bound : ‖x * y‖ ≤ ‖representative_x‖ * ‖representative_y‖ :=
          Eq.mp (congrArg₂ (fun left right : R ⧸ I =>
            ‖left * right‖ ≤ ‖representative_x‖ * ‖representative_y‖) x_spec.1 y_spec.1)
              ((Submodule.Quotient.norm_mk_le I (representative_x * representative_y)).trans
                (norm_mul_le representative_x representative_y))
        product_bound.trans (sub_lt_iff_lt_add'.mp (abs_sub_lt_iff.mp
          (Eq.mp (congrArg (fun distance : ℝ => distance < ε)
            (Real.dist_eq (‖representative_x‖ * ‖representative_y‖) (‖x‖ * ‖y‖)))
              product_distance)).1).le


end KirchbergRordam.QuotientNormSupport


open Topology
namespace KirchbergRordam.GenericRW
namespace DetectingSpace


noncomputable instance quotientNormedRing {R : Type uQuot} [NormedRing R] (I : Ideal R)
    [I.IsTwoSided] [IsClosed (I : Set R)] : NormedRing (R ⧸ I) :=
  KirchbergRordam.QuotientNormSupport.normedRing I

variable {D : Type*} [CStarAlgebra D]


def commutatorIdeal : TwoSidedIdeal D :=
  TwoSidedIdeal.span {z | ∃ a b : selfAdjoint D, z = (a : D) * b - b * a}

def closedCommutatorIdeal : Ideal D :=
  (commutatorIdeal (D := D)).asIdeal.topologicalClosure

instance : (closedCommutatorIdeal (D := D)).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    exact (show Set.MapsTo (fun x : D => x * b)
      (commutatorIdeal (D := D) : Set D) (commutatorIdeal (D := D) : Set D) from
      fun x hx => TwoSidedIdeal.mul_mem_right _ _ _ hx).closure
        (continuous_mul_const b) ha

instance : IsClosed (closedCommutatorIdeal (D := D) : Set D) := isClosed_closure

lemma commutator_mem (a b : selfAdjoint D) :
    (a : D) * b - b * a ∈ closedCommutatorIdeal :=
  subset_closure (TwoSidedIdeal.subset_span ⟨a, b, rfl⟩)

abbrev CommutativeQuotient (D : Type*) [CStarAlgebra D] := D ⧸ closedCommutatorIdeal (D := D)

instance : NormedAlgebra ℂ (CommutativeQuotient D) where
  norm_smul_le := norm_smul_le

lemma quotient_sa_commute (a b : selfAdjoint D) :
    Commute (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)) (a : D))
      (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)) (b : D)) := by
  change Ideal.Quotient.mk _ ((a : D) * b) = Ideal.Quotient.mk _ ((b : D) * a)
  exact Ideal.Quotient.eq.mpr (commutator_mem a b)

lemma quotient_commute (a b : D) :
    Commute (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)) a)
      (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)) b) := by
  rw [← realPart_add_I_smul_imaginaryPart a, ← realPart_add_I_smul_imaginaryPart b]
  simp only [map_add, map_smul]
  exact ((quotient_sa_commute _ _).add_right ((quotient_sa_commute _ _).smul_right _)).add_left
    (((quotient_sa_commute _ _).smul_left _).add_right
      (((quotient_sa_commute _ _).smul_left _).smul_right _))

instance : CommRing (CommutativeQuotient D) :=
  { (inferInstance : Ring (CommutativeQuotient D)) with
    mul_comm := by
      intro a b
      induction a using Quotient.inductionOn with | _ a =>
        induction b using Quotient.inductionOn with | _ b =>
          exact quotient_commute a b }

instance : NormedCommRing (CommutativeQuotient D) where

lemma closedCommutatorIdeal_eq_top (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    closedCommutatorIdeal (D := D) = ⊤ := by
  by_contra h
  have : Nontrivial (CommutativeQuotient D) := Ideal.Quotient.nontrivial_iff.mpr h
  obtain ⟨χ, _⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero
    (not_isUnit_zero : ¬ IsUnit (0 : CommutativeQuotient D))
  let f : D →ₐ[ℂ] ℂ := (WeakDual.CharacterSpace.equivAlgHom χ).comp
    (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)))
  let : StarHomClass (D →ₐ[ℂ] ℂ) D ℂ := AlgHomClass.instStarHomClass
  exact hD.false ({toAlgHom := f, map_star' := map_star f} : D →⋆ₐ[ℂ] ℂ)


lemma commutatorIdeal_eq_top (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    commutatorIdeal (D := D) = ⊤ := by
  have h1 : (1 : D) ∈ closure (commutatorIdeal (D := D) : Set D) := by
    change (1 : D) ∈ closedCommutatorIdeal
    rw [closedCommutatorIdeal_eq_top hD]
    trivial
  obtain ⟨x, hx, hnear⟩ := Metric.mem_closure_iff.mp h1 1 zero_lt_one
  have hu : IsUnit x := by
    have hnorm : ‖1 - x‖ < 1 := by simpa only [dist_eq_norm] using hnear
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnorm
  have ht := (commutatorIdeal (D := D)).asIdeal.eq_top_of_isUnit_mem hx hu
  apply le_antisymm le_top
  intro x _
  change x ∈ (commutatorIdeal (D := D)).asIdeal
  rw [ht]
  trivial


def finiteCommutators (s : Finset (selfAdjoint D)) : Set D :=
  {z | ∃ a ∈ s, ∃ b ∈ s, z = (a : D) * b - b * a}

lemma finiteCommutators_mono {s t : Finset (selfAdjoint D)} (h : s ⊆ t) :
    finiteCommutators s ⊆ finiteCommutators t := by
  rintro z ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, h ha, b, h hb, rfl⟩

lemma mem_commutatorIdeal_finite {x : D} (hx : x ∈ commutatorIdeal) :
    ∃ s : Finset (selfAdjoint D), x ∈ TwoSidedIdeal.span (finiteCommutators s) := by
  classical
  induction hx using TwoSidedIdeal.span_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl⟩ := hz
    exact ⟨{a, b}, TwoSidedIdeal.subset_span ⟨a, by simp, b, by simp, rfl⟩⟩
  | zero => exact ⟨∅, TwoSidedIdeal.zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    refine ⟨s ∪ t, TwoSidedIdeal.add_mem _ ?_ ?_⟩
    · exact TwoSidedIdeal.span_mono (finiteCommutators_mono Finset.subset_union_left) hs
    · exact TwoSidedIdeal.span_mono (finiteCommutators_mono Finset.subset_union_right) ht
  | neg x hx ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s, TwoSidedIdeal.neg_mem _ hs⟩
  | left_absorb a x hx ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s, TwoSidedIdeal.mul_mem_left _ _ _ hs⟩
  | right_absorb b x hx ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s, TwoSidedIdeal.mul_mem_right _ _ _ hs⟩

lemma finite_commutators_span_one (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ s : Finset (selfAdjoint D), (1 : D) ∈ TwoSidedIdeal.span (finiteCommutators s) :=
  mem_commutatorIdeal_finite (by rw [commutatorIdeal_eq_top hD]; trivial)

end DetectingSpace


theorem finite_detecting_space {D : Type*} [CStarAlgebra D] [Nontrivial D]
    (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ V : Submodule ℝ D, Module.Finite ℝ V ∧
      V ≤ selfAdjoint.submodule ℝ D ∧
      ∀ (B : Type*) [CStarAlgebra B] [Nontrivial B] (φ : D →⋆ₐ[ℂ] B),
        ∃ x ∈ V, ∃ y ∈ V, ¬ Commute (φ x) (φ y) := by
  classical
  obtain ⟨s, hs⟩ := DetectingSpace.finite_commutators_span_one hD
  let V : Submodule ℝ D := Submodule.span ℝ (Subtype.val '' (s : Set (selfAdjoint D)))
  have hmem (a : selfAdjoint D) (ha : a ∈ s) : (a : D) ∈ V :=
    Submodule.subset_span ⟨a, ha, rfl⟩
  refine ⟨V, FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image Subtype.val), ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨a, _, rfl⟩
    exact a.property
  · intro B _ _ φ
    by_contra h
    push Not at h
    have hk : TwoSidedIdeal.span (DetectingSpace.finiteCommutators s) ≤
        TwoSidedIdeal.ker φ.toRingHom := by
      apply TwoSidedIdeal.span_le.mpr
      rintro z ⟨a, ha, b, hb, rfl⟩
      apply (TwoSidedIdeal.mem_ker _).mpr
      change φ ((a : D) * b - b * a) = 0
      rw [map_sub, map_mul, map_mul, sub_eq_zero]
      exact h (a : D) (hmem a ha) (b : D) (hmem b hb)
    have h1 := hk hs
    have h1 := (TwoSidedIdeal.mem_ker _).mp h1
    change φ 1 = 0 at h1
    exact one_ne_zero (map_one φ ▸ h1)

end KirchbergRordam.GenericRW
end

end OAI
