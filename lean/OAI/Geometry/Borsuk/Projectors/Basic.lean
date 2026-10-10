import Mathlib
import OAI.Geometry.Borsuk.Model

namespace OAI

namespace BorsukNine

open scoped RealInnerProductSpace ContDiff

@[simp] theorem projector_apply (u : Vector4) (i j : Fin 4) :
    projector u (i, j) = u i * u j := rfl

@[simp] theorem projector_neg (u : Vector4) : projector (-u) = projector u := by
  ext ⟨i, j⟩
  simp [projector]

theorem continuous_projector : Continuous projector := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  exact (PiLp.continuous_apply 2 _ ij.1).mul (PiLp.continuous_apply 2 _ ij.2)

theorem isCompact_projectorSet : IsCompact projectorSet := by
  have h : {u : Vector4 | ‖u‖ = 1} = Metric.sphere 0 1 := by
    ext u
    simp
  rw [projectorSet, h]
  exact (isCompact_sphere (0 : Vector4) 1).image continuous_projector

theorem projector_inner (u v : Vector4) :
    ⟪projector u, projector v⟫ = ⟪u, v⟫ ^ 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, projector]
  change (∑ ij : Fin 4 × Fin 4, (v ij.1 * v ij.2) * (u ij.1 * u ij.2)) =
    (∑ i : Fin 4, v i * u i) ^ 2
  rw [Fintype.sum_prod_type]
  simp only [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem projector_norm_sq (u : Vector4) : ‖projector u‖ ^ 2 = ‖u‖ ^ 4 := by
  rw [← real_inner_self_eq_norm_sq, projector_inner, real_inner_self_eq_norm_sq]
  ring

theorem projectorSet_subset_traceOneSymmetric : projectorSet ⊆ traceOneSymmetric := by
  rintro _ ⟨u, hu, rfl⟩
  constructor
  · intro i j
    simp [mul_comm]
  · have he : (∑ i : Fin 4, u i * u i) = ‖u‖ ^ 2 := by
      exact (EuclideanSpace.inner_eq_star_dotProduct u u).symm.trans
        (real_inner_self_eq_norm_sq u)
    change ‖u‖ = 1 at hu
    simp only [projector_apply, he, hu, one_pow]

theorem projector_dist_sq (u v : Vector4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (projector u) (projector v) ^ 2 = 2 - 2 * ⟪u, v⟫ ^ 2 := by
  rw [dist_eq_norm, norm_sub_sq_real, projector_norm_sq, projector_norm_sq,
    projector_inner, hu, hv]
  ring

theorem projector_dist_le (u v : Vector4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (projector u) (projector v) ≤ Real.sqrt 2 := by
  have hd := projector_dist_sq u v hu hv
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [sq_nonneg ⟪u, v⟫, dist_nonneg (x := projector u) (y := projector v)]

theorem projector_dist_eq_sqrt_two_iff (u v : Vector4)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (projector u) (projector v) = Real.sqrt 2 ↔ ⟪u, v⟫ = 0 := by
  have hd := projector_dist_sq u v hu hv
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  constructor
  · intro h
    rw [h] at hd
    nlinarith [sq_nonneg ⟪u, v⟫]
  · intro h
    rw [h] at hd
    have hn := dist_nonneg (x := projector u) (y := projector v)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith

theorem diam_projectorSet : Metric.diam projectorSet = Real.sqrt 2 := by
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg 2)
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact projector_dist_le u v hu hv
  · let u : Vector4 := EuclideanSpace.single 0 1
    let v : Vector4 := EuclideanSpace.single 1 1
    have hu : ‖u‖ = 1 := by simp [u]
    have hv : ‖v‖ = 1 := by simp [v]
    have huv : ⟪u, v⟫ = 0 := by simp [u, v, EuclideanSpace.inner_single_left]
    have hd := (projector_dist_eq_sqrt_two_iff u v hu hv).mpr huv
    rw [← hd]
    exact Metric.dist_le_diam_of_mem isCompact_projectorSet.isBounded
      ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩

structure Admissible {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] (f : V → ι → ℝ) : Prop where
  smooth : ∀ i, ContDiff ℝ ∞ (fun u => f u i)
  antipodal : ∀ u i, f (-u) i = f u i
  nonneg : ∀ u, ‖u‖ = 1 → ∀ i, 0 ≤ f u i
  sum_one : ∀ u, ‖u‖ = 1 → ∑ i, f u i = 1
  orthogonal : ∀ u v, ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫ = 0 →
    ∀ i, ¬ (0 < f u i ∧ 0 < f v i)

theorem contDiff_projector : ContDiff ℝ ∞ projector := by
  apply (contDiff_piLp 2).mpr
  intro ij
  exact (contDiff_piLp_apply (p := 2) (i := ij.1)).mul (contDiff_piLp_apply (p := 2) (i := ij.2))

theorem dist_lt_of_mem_thickening_small {C : Set Matrix4}
    (hC : C ⊆ projectorSet) (hd : Metric.diam C < Real.sqrt 2)
    {P Q : Matrix4}
    (hP : P ∈ Metric.thickening ((Real.sqrt 2 - Metric.diam C) / 4) C)
    (hQ : Q ∈ Metric.thickening ((Real.sqrt 2 - Metric.diam C) / 4) C) :
    dist P Q < Real.sqrt 2 := by
  rcases Metric.mem_thickening_iff.mp hP with ⟨p, hp, hPp⟩
  rcases Metric.mem_thickening_iff.mp hQ with ⟨q, hq, hQq⟩
  have hb := isCompact_projectorSet.isBounded.subset hC
  have hpq := Metric.dist_le_diam_of_mem hb hp hq
  have ht : dist P Q ≤ dist P p + dist p q + dist Q q := by
    calc
      dist P Q ≤ dist P p + dist p Q := dist_triangle P p Q
      _ ≤ dist P p + (dist p q + dist q Q) :=
        add_le_add le_rfl (dist_triangle p q Q)
      _ = dist P p + dist p q + dist Q q := by rw [dist_comm q Q]; ring
  linarith

open scoped Manifold

theorem cover_to_admissible (h : HasTenSmallCover) :
    ∃ f : Vector4 → Fin 10 → ℝ, Admissible f := by
  classical
  rcases h with ⟨C, hCX, hcov, hdiam⟩
  let U : Fin 10 → Set Matrix4 := fun i =>
    Metric.thickening ((Real.sqrt 2 - Metric.diam (C i)) / 4) (C i)
  have hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_thickening
  have hCU : ∀ i, C i ⊆ U i := by
    intro i
    apply Metric.self_subset_thickening
    linarith [hdiam i]
  have hXU : projectorSet ⊆ ⋃ i, U i := by
    intro P hP
    rcases Set.mem_iUnion.mp (hcov hP) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hCU i hi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, Matrix4)) isCompact_projectorSet.isClosed U hU hXU
  refine ⟨fun u i => ρ i (projector u), ?_⟩
  constructor
  · intro i
    exact (contMDiff_iff_contDiff.mp (ρ i).contMDiff).comp contDiff_projector
  · intro u i
    simp
  · intro u _ i
    exact ρ.nonneg i (projector u)
  · intro u hu
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (show projector u ∈ projectorSet
      from ⟨u, hu, rfl⟩)
  · intro u v hu hv huv i ⟨hui, hvi⟩
    have huU : projector u ∈ U i := hρ i (subset_tsupport _ (ne_of_gt hui))
    have hvU : projector v ∈ U i := hρ i (subset_tsupport _ (ne_of_gt hvi))
    have hd := dist_lt_of_mem_thickening_small (hCX i) (hdiam i) huU hvU
    rw [(projector_dist_eq_sqrt_two_iff u v hu hv).mpr huv] at hd
    exact lt_irrefl _ hd

theorem compact_diam_lt {C : Set Matrix4} (hC : IsCompact C) {d : ℝ}
    (hd : 0 < d) (hpair : ∀ x ∈ C, ∀ y ∈ C, dist x y < d) :
    Metric.diam C < d := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simpa using hd
  · obtain ⟨⟨x, y⟩, hxy, hmax⟩ := (hC.prod hC).exists_isMaxOn (hne.prod hne)
      (continuous_fst.dist continuous_snd).continuousOn
    have hbound : Metric.diam C ≤ dist x y := by
      apply Metric.diam_le_of_forall_dist_le dist_nonneg
      intro a ha b hb
      exact (isMaxOn_iff.mp hmax) (a, b) ⟨ha, hb⟩
    exact hbound.trans_lt (hpair x hxy.1 y hxy.2)

theorem admissible_to_cover {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f) :
    HasTenSmallCover := by
  classical
  let L : Fin 10 → Set Vector4 := fun i =>
    {u | ‖u‖ = 1} ∩ {u | (1 : ℝ) / 10 ≤ f u i}
  let C : Fin 10 → Set Matrix4 := fun i => projector '' L i
  have hLcompact : ∀ i, IsCompact (L i) := by
    intro i
    have hsphere : IsCompact {u : Vector4 | ‖u‖ = 1} := by
      have he : {u : Vector4 | ‖u‖ = 1} = Metric.sphere 0 1 := by
        ext u
        simp
      rw [he]
      exact isCompact_sphere (0 : Vector4) 1
    exact hsphere.inter_right (isClosed_le continuous_const (hf.smooth i).continuous)
  have hCcompact : ∀ i, IsCompact (C i) := fun i =>
    (hLcompact i).image continuous_projector
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i P hP
    rcases hP with ⟨u, hu, rfl⟩
    exact ⟨u, hu.1, rfl⟩
  · rintro P ⟨u, hu, rfl⟩
    have hsum : (∑ _i : Fin 10, (1 : ℝ) / 10) ≤ ∑ i, f u i := by
      rw [hf.sum_one u hu]
      norm_num
    obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    exact Set.mem_iUnion.mpr ⟨i, u, ⟨hu, hi⟩, rfl⟩
  · intro i
    apply compact_diam_lt (hCcompact i) (Real.sqrt_pos.mpr (by norm_num))
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    by_contra h
    have heq : dist (projector u) (projector v) = Real.sqrt 2 :=
      le_antisymm (projector_dist_le u v hu.1 hv.1) (le_of_not_gt h)
    have huv := (projector_dist_eq_sqrt_two_iff u v hu.1 hv.1).mp heq
    exact hf.orthogonal u v hu.1 hv.1 huv i
      ⟨lt_of_lt_of_le (by norm_num) hu.2, lt_of_lt_of_le (by norm_num) hv.2⟩

theorem cover_iff_admissible : HasTenSmallCover ↔
    ∃ f : Vector4 → Fin 10 → ℝ, Admissible f :=
  ⟨cover_to_admissible, fun ⟨_, hf⟩ => admissible_to_cover hf⟩

theorem exists_unit_orthogonal {n : ℕ} (hn : n < 4) (v : Fin n → Vector4) :
    ∃ w : Vector4, ‖w‖ = 1 ∧ ∀ i, ⟪v i, w⟫ = 0 := by
  classical
  let W : Submodule ℝ Vector4 := Submodule.span ℝ (Set.range v)
  have hW : W ≠ ⊤ := by
    intro he
    have hh := finrank_le_of_span_eq_top he
    have hd : Module.finrank ℝ Vector4 = 4 := by simp
    rw [hd, Fintype.card_fin] at hh
    omega
  have hO : Wᗮ ≠ ⊥ := by
    intro he
    exact hW (Submodule.orthogonal_eq_bot_iff.mp he)
  obtain ⟨w, hw, hwne⟩ := (Submodule.ne_bot_iff Wᗮ).mp hO
  refine ⟨(‖w‖⁻¹ : ℝ) • w, norm_smul_inv_norm hwne, ?_⟩
  intro i
  rw [inner_smul_right, Submodule.inner_right_of_mem_orthogonal
    (show v i ∈ W from Submodule.subset_span (Set.mem_range_self i)) hw, mul_zero]

noncomputable def positiveSupport {ι : Type*} [Fintype ι]
    {V : Type*} (f : V → ι → ℝ) (u : V) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 0 < f u i)

@[simp] theorem mem_positiveSupport {ι : Type*} [Fintype ι]
    {V : Type*} (f : V → ι → ℝ) (u : V) (i : ι) :
    i ∈ positiveSupport f u ↔ 0 < f u i := by
  classical
  simp [positiveSupport]

lemma Admissible.support_nonempty {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ι → ℝ} (hf : Admissible f) {u : V} (hu : ‖u‖ = 1) :
    (positiveSupport f u).Nonempty := by
  classical
  have hs : 0 < ∑ i, f u i := by rw [hf.sum_one u hu]; norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hf.nonneg u hu i)).mp hs
  exact ⟨i, (mem_positiveSupport f u i).mpr hi⟩

lemma Admissible.disjoint_supports {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ι → ℝ} (hf : Admissible f) {u v : V}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : ⟪u, v⟫ = 0) :
    Disjoint (positiveSupport f u) (positiveSupport f v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hf.orthogonal u v hu hv horth i
    ⟨(mem_positiveSupport f u i).mp hi, (mem_positiveSupport f v i).mp hj⟩

theorem Admissible.exists_label_absent {ι : Type*} [Fintype ι]
    {f : Vector4 → ι → ℝ} (hf : Admissible f) {n : ℕ} (hn : n < 4)
    (v : Fin n → Vector4) (hv : ∀ j, ‖v j‖ = 1) :
    ∃ i, ∀ j, i ∉ positiveSupport f (v j) := by
  obtain ⟨w, hw, hvw⟩ := exists_unit_orthogonal hn v
  obtain ⟨i, hi⟩ := hf.support_nonempty hw
  refine ⟨i, ?_⟩
  intro j hj
  exact Finset.disjoint_left.mp (hf.disjoint_supports (hv j) hw (hvw j)) hj hi

end BorsukNine

end OAI
