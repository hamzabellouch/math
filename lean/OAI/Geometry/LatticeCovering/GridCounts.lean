import OAI.Geometry.LatticeCovering.GaussianSections

namespace OAI

section
noncomputable section

namespace SingleLatticeCovering.RealLatticeCount
open Module MeasureTheory Measure Filter Set Bornology
open scoped Pointwise Topology
variable {ι : Type*} [Fintype ι]

lemma convex_dilation_mono {ι : Type*} [Fintype ι] {S : Set (ι → ℝ)} (hS : Convex ℝ S) (h0 : 0 ∈ S)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : x • S ⊆ y • S := by
  rintro _ ⟨u,hu,rfl⟩
  have hy : 0 < y := hx.trans_le hxy
  refine ⟨(x/y) • u, ?_, ?_⟩
  · have h := hS h0 hu (sub_nonneg.mpr ((div_le_one hy).mpr hxy))
      (div_nonneg hx.le hy.le) (by ring : 1-x/y+x/y=1)
    simpa using h
  · change y • ((x/y) • u) = x • u
    rw [smul_smul]
    congr 1
    field_simp



theorem tendsto_real_grid_count (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] {S : Set (ι → ℝ)}
    (hSb : IsBounded S) (hSm : MeasurableSet S)
    (hSf : volume (frontier S) = 0)
    (hSd : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • S ⊆ y • S) :
    Tendsto (fun t : ℝ => (Nat.card ↥(S ∩ t⁻¹ • (L : Set (ι → ℝ))) : ℝ) /
      t ^ Fintype.card ι) atTop (𝓝 (volume.real S / ZLattice.covolume L)) := by
  let b := IsZLattice.basis L
  let f := (b.ofZLatticeBasis ℝ).equivFun
  have hbound : IsBounded (f '' S) := by
    rw [←NormedSpace.isVonNBounded_iff ℝ] at hSb ⊢
    exact hSb.image ((b.ofZLatticeBasis ℝ).equivFunL : (ι → ℝ) →L[ℝ] ι → ℝ)
  have hmeas : MeasurableSet (f '' S) :=
    (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hSm
  have hfront : volume (frontier (f '' S)) = 0 := by
    have hf : frontier (f '' S) = f '' frontier S := by
      rw [LinearEquiv.image_eq_preimage_symm, LinearEquiv.image_eq_preimage_symm]
      exact (Homeomorph.preimage_frontier (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.symm S).symm
    rw [hf, ZLattice.volume_image_eq_volume_div_covolume L b, hSf, ENNReal.zero_div]
  have hdilate : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • (f '' S) ⊆ y • (f '' S) := by
    intro x y hx hxy
    simp_rw [←image_smul_set]
    exact Set.image_mono (hSd hx hxy)
  have hlim := tendsto_card_div_pow_atTop_volume' (f '' S) hbound hmeas hfront hdilate
  have hv : volume.real (f '' S) = volume.real S / ZLattice.covolume L := by
    simp only [measureReal_def]
    rw [ZLattice.volume_image_eq_volume_div_covolume L b, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (ZLattice.covolume_pos L volume).le]
  rw [hv] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  congr 1
  congr 1
  refine Nat.card_congr <| (f.toEquiv.subtypeEquiv (fun x => ?_)).symm
  dsimp only [f]
  simp only [Set.mem_inter_iff, ← b.ofZLatticeBasis_span ℝ, LinearEquiv.coe_toEquiv,
    Basis.equivFun_apply, Set.mem_image, DFunLike.coe_fn_eq, EmbeddingLike.apply_eq_iff_eq,
    exists_eq_right, Set.mem_inv_smul_set_iff₀ ht.ne',
    ←Finsupp.coe_smul, ←map_smul, SetLike.mem_coe, Basis.mem_span_iff_repr_mem,
    Pi.basisFun_repr]



theorem tendsto_convex_grid_count (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] {S : Set (ι → ℝ)}
    (hSc : IsCompact S) (hSv : Convex ℝ S) (h0 : 0 ∈ S) :
    Tendsto (fun t : ℝ => (Nat.card ↥(S ∩ t⁻¹ • (L : Set (ι → ℝ))) : ℝ) /
      t ^ Fintype.card ι) atTop (𝓝 (volume.real S / ZLattice.covolume L)) :=
  tendsto_real_grid_count L hSc.isBounded hSc.measurableSet
    (hSv.addHaar_frontier volume) (fun _ _ => convex_dilation_mono hSv h0)


end SingleLatticeCovering.RealLatticeCount


noncomputable section
namespace SingleLatticeCovering.GridGeometry
open MeasureTheory Measure Set Bornology
open scoped BigOperators Pointwise



def weightedGridConfiguration {r d : ℕ} (J : Set (Fin d → ℝ)) (c : Fin r → ℝ) :
    Set (Fin r × Fin d → ℝ) :=
  {x | (∀ i, (fun j => x (i,j)) ∈ J) ∧ (fun j => ∑ i, c i*x (i,j)) ∈ J}

lemma weightedGridConfiguration_convex {r d : ℕ} {J : Set (Fin d → ℝ)}
    (hJ : Convex ℝ J) (c : Fin r → ℝ) : Convex ℝ (weightedGridConfiguration J c) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact hJ (hx.1 i) (hy.1 i) ha hb hab
  · have he : (fun j => ∑ i, c i*(a • x+b • y) (i,j)) =
        a • (fun j => ∑ i, c i*x (i,j)) + b • (fun j => ∑ i, c i*y (i,j)) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact hJ hx.2 hy.2 ha hb hab

lemma weightedGridConfiguration_closed {r d : ℕ} {J : Set (Fin d → ℝ)}
    (hJ : IsClosed J) (c : Fin r → ℝ) : IsClosed (weightedGridConfiguration J c) := by
  have he : weightedGridConfiguration J c =
      (⋂ i, (fun x : Fin r × Fin d → ℝ => fun j => x (i,j)) ⁻¹' J) ∩
      (fun x : Fin r × Fin d → ℝ => fun j => ∑ i, c i*x (i,j)) ⁻¹' J := by
    ext x
    simp [weightedGridConfiguration]
  rw [he]
  exact (isClosed_iInter (fun i => hJ.preimage (by fun_prop))).inter
    (hJ.preimage (by fun_prop))

lemma weightedGridConfiguration_bounded {r d : ℕ} {J : Set (Fin d → ℝ)}
    (hJ : IsBounded J) (c : Fin r → ℝ) : IsBounded (weightedGridConfiguration J c) := by
  obtain ⟨R,hR⟩ := hJ.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max R 0, fun x hx => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (le_max_right R 0)).mpr
  intro ij
  exact (norm_le_pi_norm (fun j => x (ij.1,j)) ij.2).trans
    ((hR _ (hx.1 ij.1)).trans (le_max_left R 0))

lemma weightedGridConfiguration_compact {r d : ℕ} {J : Set (Fin d → ℝ)}
    (hJ : IsCompact J) (c : Fin r → ℝ) : IsCompact (weightedGridConfiguration J c) :=
  Metric.isCompact_of_isClosed_isBounded
    (weightedGridConfiguration_closed hJ.isClosed c)
    (weightedGridConfiguration_bounded hJ.isBounded c)

lemma zero_mem_weightedGridConfiguration {r d : ℕ} {J : Set (Fin d → ℝ)}
    (h0 : 0 ∈ J) (c : Fin r → ℝ) : 0 ∈ weightedGridConfiguration J c := by
  constructor
  · intro i
    exact h0
  · convert h0 using 1
    ext j
    simp



end SingleLatticeCovering.GridGeometry

namespace SingleLatticeCovering.GridLimit
open MeasureTheory Measure Filter Set
open FiniteKernel GridGeometry RealLatticeCount
open scoped Topology Pointwise


theorem primitive_configuration_limit {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha0 : a 0 ≠ 0) (hprim : Finset.univ.gcd a = 1)
    {J : Set (Fin d → ℝ)} (hJc : IsCompact J) (hJv : Convex ℝ J) (h0 : 0 ∈ J) :
    Tendsto (fun t : ℝ =>
      (Nat.card ↥(weightedGridConfiguration J (fun i => -(a i.succ:ℝ)/(a 0:ℝ)) ∩
        t⁻¹ • (kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ)) :
          Set (Fin r × Fin d → ℝ))) : ℝ) / t^(r*d))
      atTop (𝓝 (volume.real (weightedGridConfiguration J (fun i => -(a i.succ:ℝ)/(a 0:ℝ))) /
        |(a 0:ℝ)|^d)) := by
  let : NeZero (a 0).natAbs := ⟨Int.natAbs_ne_zero.mpr ha0⟩
  have h := tendsto_convex_grid_count
    (kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ)))
    (weightedGridConfiguration_compact hJc (fun i => -(a i.succ:ℝ)/(a 0:ℝ)))
    (weightedGridConfiguration_convex hJv _)
    (zero_mem_weightedGridConfiguration h0 _)
  simpa only [Fintype.card_prod, Fintype.card_fin, primitive_grid_covolume a ha0 hprim] using h


end SingleLatticeCovering.GridLimit

namespace SingleLatticeCovering.GridLimit
open MeasureTheory Measure Filter Set
open FiniteKernel GridGeometry RealLatticeCount
open scoped Topology Pointwise BigOperators

lemma finite_scaled_lattice_inter {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    {S : Set (ι → ℝ)} (hS : IsCompact S) {t : ℝ} (ht : t ≠ 0) :
    (S ∩ t⁻¹ • (L : Set (ι → ℝ))).Finite := by
  have hT : ((t • S) ∩ (L : Set (ι → ℝ))).Finite := by
    apply Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (hS.smul t).isBounded
    exact AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup)
  apply Set.Finite.of_injOn (t := (t • S) ∩ (L : Set (ι → ℝ)))
    (f := fun x => t • x) ?_ ?_ hT
  · rintro x ⟨hx, y, hy, rfl⟩
    constructor
    · exact ⟨t⁻¹ • y,hx,rfl⟩
    · simpa only [smul_smul, mul_inv_cancel₀ ht, one_smul] using hy
  · intro x hx y hy hxy
    exact smul_right_injective (ι → ℝ) ht hxy

lemma projected_grid_relation_mem {r d : ℕ} (a : Fin (r+1) → ℤ)
    (x : Fin (r+1) → Fin d → ℤ) (h : ∀ j, ∑ i, a i*x i j = 0) :
    (fun ij : Fin r × Fin d => (x ij.1.succ ij.2 : ℝ)) ∈
      kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ)) := by
  let z : integerLattice (Fin r × Fin d) := integerCoordinates.symm (fun ij => x ij.1.succ ij.2)
  have he : (z : Fin r × Fin d → ℝ) = (fun ij => (x ij.1.succ ij.2 : ℝ)) := by
    ext ij
    rw [←integerCoordinates_cast]
    simp [z]
  rw [←he, mem_kernelLattice_iff]
  ext j
  have hcast := congrArg (fun t : ℤ => (t : ZMod (a 0).natAbs)) (h j)
  have hzero : (a 0 : ZMod (a 0).natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natAbs_dvd.mpr (dvd_refl (a 0))
  simpa [gridRelationForm,z,Fin.sum_univ_succ,Int.cast_add,Int.cast_mul,Int.cast_sum,hzero]
    using hcast

lemma omitted_vertex_identity {r d : ℕ} (a : Fin (r+1) → ℤ) (ha0 : a 0 ≠ 0)
    (x : Fin (r+1) → Fin d → ℤ) (h : ∀ j, ∑ i, a i*x i j = 0) (t : ℝ) :
    (fun j => ∑ i : Fin r, (-(a i.succ:ℝ)/(a 0:ℝ))*(t⁻¹*(x i.succ j:ℝ))) =
      (fun j => t⁻¹*(x 0 j:ℝ)) := by
  ext j
  have hh := congrArg (fun z : ℤ => (z:ℝ)) (h j)
  simp only [Fin.sum_univ_succ,Int.cast_add,Int.cast_sum,Int.cast_mul,Int.cast_zero] at hh
  have haR : (a 0:ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha0
  apply (mul_left_cancel₀ haR)
  rw [Finset.mul_sum]
  have he (i : Fin r) : (a 0:ℝ)*(-(a i.succ:ℝ)/(a 0:ℝ)*(t⁻¹*(x i.succ j:ℝ))) =
      -t⁻¹*((a i.succ:ℝ)*(x i.succ j:ℝ)) := by field_simp
  simp_rw [he]
  rw [←Finset.mul_sum]
  rw [show (∑ i : Fin r, (a i.succ:ℝ)*(x i.succ j:ℝ)) = -(a 0:ℝ)*(x 0 j:ℝ) by linarith]
  ring




theorem circuit_count_le_primitive_grid {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha0 : a 0 ≠ 0) (J : Set (Fin d → ℝ)) (hJ : IsCompact J)
    (X : Finset (Fin (r+1) → Fin d → ℤ)) {t : ℝ} (ht : 0 < t)
    (hX : ∀ x ∈ X, ∀ i, (fun j => t⁻¹*(x i j:ℝ)) ∈ J)
    (hrel : ∀ x ∈ X, ∀ j, ∑ i, a i*x i j = 0) :
    (X.card:ℝ) / t^(r*d) ≤
      (Nat.card ↥(weightedGridConfiguration J (fun i => -(a i.succ:ℝ)/(a 0:ℝ)) ∩
        t⁻¹ • (kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ)) :
          Set (Fin r × Fin d → ℝ))) : ℝ) / t^(r*d) := by
  classical
  let S := weightedGridConfiguration J (fun i => -(a i.succ:ℝ)/(a 0:ℝ))
  let L := kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ))
  have hfin : (S ∩ t⁻¹ • (L : Set (Fin r × Fin d → ℝ))).Finite :=
    finite_scaled_lattice_inter L (weightedGridConfiguration_compact hJ _) ht.ne'
  let := hfin.fintype
  let f : X → ↥(S ∩ t⁻¹ • (L : Set (Fin r × Fin d → ℝ))) := fun x =>
    ⟨fun ij => t⁻¹*(x.val ij.1.succ ij.2:ℝ), by
      constructor
      · refine ⟨fun i => hX x.val x.property i.succ, ?_⟩
        rw [omitted_vertex_identity a ha0 x.val (hrel x.val x.property) t]
        exact hX x.val x.property 0
      · exact ⟨(fun ij => (x.val ij.1.succ ij.2:ℝ)),
          projected_grid_relation_mem a x.val (hrel x.val x.property),rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hs (i : Fin r) (j : Fin d) : x.val i.succ j = y.val i.succ j := by
      have hh := congrFun (congrArg Subtype.val hxy) (i,j)
      change t⁻¹*(x.val i.succ j:ℝ) = t⁻¹*(y.val i.succ j:ℝ) at hh
      exact Int.cast_injective (mul_left_cancel₀ (inv_ne_zero ht.ne') hh)
    apply Subtype.ext
    funext i j
    refine Fin.cases ?_ (fun i => hs i j) i
    have hx := hrel x.val x.property j
    have hy := hrel y.val y.property j
    rw [Fin.sum_univ_succ] at hx hy
    simp_rw [hs] at hx
    apply mul_left_cancel₀ ha0
    linarith
  apply div_le_div_of_nonneg_right _ (pow_nonneg ht.le _)
  change (X.card:ℝ) ≤ (Nat.card ↥(S ∩ t⁻¹ • (L : Set (Fin r × Fin d → ℝ))) : ℝ)
  apply Nat.cast_le.mpr
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective f hf


end SingleLatticeCovering.GridLimit







noncomputable section
namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix Filter Topology
open scoped ENNReal BigOperators

abbrev V (r : ℕ) := Fin r → ℝ

def simplexMean {r : ℕ} (u : V (r+1)) : ℝ := (∑ i, u i) / (r+1:ℕ)

def simplexForm {r : ℕ} (i : Fin (r+1)) : V r →ₗ[ℝ] ℝ :=
  Fin.cases (-(∑ j : Fin r, (LinearMap.proj j : V r →ₗ[ℝ] ℝ)))
    (fun j => LinearMap.proj j) i

lemma simplexForm_zero {r : ℕ} (x : V r) : simplexForm 0 x = -∑ j, x j := by
  simp [simplexForm]
lemma simplexForm_succ {r : ℕ} (j : Fin r) (x : V r) : simplexForm j.succ x = x j := rfl
lemma sum_simplexForm {r : ℕ} (x : V r) : (∑ i, simplexForm i x) = 0 := by
  simp [Fin.sum_univ_succ, simplexForm_zero, simplexForm_succ]

def simplexDual {r : ℕ} : V (r+1) →ₗ[ℝ] V r where
  toFun u j := u j.succ - simplexMean u
  map_add' u v := by
    ext j
    simp [simplexMean, Finset.sum_add_distrib, add_div]; ring
  map_smul' c u := by
    ext j
    simp only [simplexMean, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [←Finset.mul_sum]
    ring

lemma simplexDual_apply {r : ℕ} (u : V (r+1)) (j : Fin r) :
    simplexDual u j = u j.succ - simplexMean u := rfl
lemma simplexDual_form {r : ℕ} (x : V r) :
    simplexDual (fun i => simplexForm i x) = x := by
  ext j
  simp [simplexDual_apply, simplexMean, sum_simplexForm, simplexForm_succ]
lemma simplexForm_dual {r : ℕ} (u : V (r+1)) (i : Fin (r+1)) :
    simplexForm i (simplexDual u) = u i - simplexMean u := by
  refine Fin.cases ?_ (fun j => rfl) i
  rw [simplexForm_zero]
  simp only [simplexDual_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (r+1:ℝ) ≠ 0 := by positivity
  dsimp [simplexMean]
  rw [Fin.sum_univ_succ]
  push_cast
  field_simp [hn]
  ring

lemma simplex_projection_square {r : ℕ} (u : V (r+1)) :
    (∑ i, (simplexForm i (simplexDual u))^2) ≤ ∑ i, (u i)^2 := by
  simp_rw [simplexForm_dual]
  have hex : (∑ i, (u i - simplexMean u)^2) =
      (∑ i, (u i)^2) - (r+1:ℕ) * (simplexMean u)^2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have he : (∑ i, 2 * u i * simplexMean u) = 2 * simplexMean u * (∑ i, u i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [he]
    dsimp [simplexMean]
    field_simp
    ring
  rw [hex]
  exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

lemma det_diagonal_rankOne {r : ℕ} (a u v : V r) (ha : ∀ i, a i ≠ 0) :
    (Matrix.diagonal a + Matrix.replicateCol Unit u * Matrix.replicateRow Unit v).det =
      (∏ i, a i) * (1 + ∑ i, v i * (a i)⁻¹ * u i) := by
  have hai : Ring.inverse a = fun i => (a i)⁻¹ := by
    let au : (V r)ˣ := ⟨a, (fun i => (a i)⁻¹), by ext i; simp [ha i], by ext i; simp [ha i]⟩
    exact Ring.inverse_unit au
  rw [Matrix.det_add_replicateCol_mul_replicateRow
    (isUnit_iff_ne_zero.mpr (by simpa using Finset.prod_ne_zero_iff.mpr (fun i _ => ha i))),
    Matrix.det_diagonal, Matrix.inv_diagonal, hai, Matrix.det_unique]
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

def simplexJacobian {r : ℕ} (s : V (r+1)) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal (fun j : Fin r => s j.succ) +
    Matrix.replicateCol Unit (fun _ : Fin r => (1:ℝ)) *
      Matrix.replicateRow Unit (fun j : Fin r => (s 0-s j.succ)/(r+1:ℕ))

lemma simplexJacobian_apply {r : ℕ} (s : V (r+1)) (j l : Fin r) :
    simplexJacobian s j l = (if j=l then s j.succ else 0) +
      (s 0-s l.succ)/(r+1:ℕ) := by
  simp [simplexJacobian, Matrix.diagonal_apply, Matrix.mul_apply]

lemma simplexJacobian_det {r : ℕ} (s : V (r+1)) (hs : ∀ i, 0 < s i) :
    (simplexJacobian s).det = (∏ i, s i) * ((∑ i, (s i)⁻¹)/(r+1:ℕ)) := by
  rw [simplexJacobian, det_diagonal_rankOne _ _ _ (fun i => (hs i.succ).ne')]
  simp only [mul_one]
  have hsum : (∑ i : Fin r, ((s 0-s i.succ)/(r+1:ℕ)) * (s i.succ)⁻¹) =
      s 0/(r+1:ℕ) * (∑ i : Fin r, (s i.succ)⁻¹) - (r:ℝ)/(r+1:ℕ) := by
    have he (i : Fin r) : ((s 0-s i.succ)/(r+1:ℕ)) * (s i.succ)⁻¹ =
        (s 0/(r+1:ℕ)) * (s i.succ)⁻¹ - 1/(r+1:ℕ) := by
      field_simp [(hs i.succ).ne']
    simp_rw [he]
    rw [Finset.sum_sub_distrib, ←Finset.mul_sum]
    simp [div_eq_mul_inv]
  rw [hsum, Fin.prod_univ_succ, Fin.sum_univ_succ]
  have hn : (r+1:ℕ) ≠ (0:ℝ) := by positivity
  field_simp [(hs 0).ne', hn]
  push_cast
  ring

lemma simplexJacobian_det_ge {r : ℕ} (s : V (r+1)) (hs : ∀ i, 0 < s i) :
    (∏ i, (s i)^((r:ℝ)/(r+1:ℕ))) ≤ (simplexJacobian s).det := by
  have hn : (0:ℝ) < (r+1:ℕ) := by positivity
  have hg := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
    (fun _ : Fin (r+1) => (1:ℝ)/(r+1:ℕ)) (fun i => (s i)⁻¹)
    (fun _ _ => (div_pos zero_lt_one hn).le)
    (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp) (fun i _ => (inv_pos.mpr (hs i)).le)
  have hp : 0 < ∏ i, s i := Finset.prod_pos (fun i _ => hs i)
  have he : (∏ i, (s i)^((r:ℝ)/(r+1:ℕ))) =
      (∏ i, s i) * (∏ i, ((s i)⁻¹)^((1:ℝ)/(r+1:ℕ))) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.inv_rpow (hs i).le, ←div_eq_mul_inv]
    calc
      (s i)^((r:ℝ)/(r+1:ℕ)) = (s i)^((1:ℝ)-1/(r+1:ℕ)) := by
        congr 1; push_cast; field_simp; ring
      _ = (s i)^((1:ℝ)) / (s i)^((1:ℝ)/(r+1:ℕ)) := Real.rpow_sub (hs i) _ _
      _ = _ := by rw [Real.rpow_one]
  rw [he, simplexJacobian_det s hs]
  apply mul_le_mul_of_nonneg_left _ hp.le
  calc
    _ ≤ ∑ i, (1:ℝ)/(r+1:ℕ) * (s i)⁻¹ := hg
    _ = _ := by rw [←Finset.mul_sum]; ring


def simplexTransport {r : ℕ} (T : Fin (r+1) → ℝ → ℝ) (x : V r) : V r :=
  simplexDual (fun i => T i (simplexForm i x))

lemma simplexTransport_injective {r : ℕ} {T : Fin (r+1) → ℝ → ℝ}
    (hT : ∀ i, StrictMono (T i)) : Function.Injective (simplexTransport T) := by
  intro x y hxy
  let u : V (r+1) := fun i => T i (simplexForm i x)-T i (simplexForm i y)
  have hu : simplexDual u = 0 := by
    change simplexDual ((fun i => T i (simplexForm i x)) - (fun i => T i (simplexForm i y))) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  have hue (i : Fin (r+1)) : u i = simplexMean u := by
    have h := simplexForm_dual u i
    rw [hu, map_zero] at h
    exact sub_eq_zero.mp h.symm
  have hsum : (∑ i, u i * (simplexForm i x-simplexForm i y)) = 0 := by
    simp_rw [hue, ← map_sub]
    rw [←Finset.mul_sum, sum_simplexForm, mul_zero]
  have hn (i : Fin (r+1)) : 0 ≤ u i*(simplexForm i x-simplexForm i y) := by
    dsimp [u]
    rcases le_total (simplexForm i x) (simplexForm i y) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ((hT i).monotone h)) (sub_nonpos.mpr h)
    · exact mul_nonneg (sub_nonneg.mpr ((hT i).monotone h)) (sub_nonneg.mpr h)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hsum
  ext j
  have h := hzero j.succ (Finset.mem_univ _)
  change (T j.succ (x j)-T j.succ (y j))*(x j-y j)=0 at h
  rcases mul_eq_zero.mp h with h | h
  · exact (hT j.succ).injective (sub_eq_zero.mp h)
  · exact sub_eq_zero.mp h

def simplexDerivative {r : ℕ} (s : V (r+1)) : V r →L[ℝ] V r :=
  simplexDual.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => s i • (simplexForm i).toContinuousLinearMap))

lemma simplexTransport_hasFDerivAt {r : ℕ} {T T' : Fin (r+1) → ℝ → ℝ}
    (hT : ∀ i t, HasDerivAt (T i) (T' i t) t) (x : V r) :
    HasFDerivAt (simplexTransport T)
      (simplexDerivative (fun i => T' i (simplexForm i x))) x := by
  apply simplexDual.toContinuousLinearMap.hasFDerivAt.comp
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hT i (simplexForm i x)).comp_hasFDerivAt x
    (simplexForm i).toContinuousLinearMap.hasFDerivAt

lemma simplexDerivative_eq {r : ℕ} (s : V (r+1)) :
    (simplexDerivative s).toLinearMap = Matrix.toLin' (simplexJacobian s) := by
  apply LinearMap.ext
  intro x
  ext j
  change s j.succ * simplexForm j.succ x -
    simplexMean (fun i => s i * simplexForm i x) = (simplexJacobian s *ᵥ x) j
  simp only [simplexForm_succ, simplexMean, Fin.sum_univ_succ, simplexForm_zero,
    Matrix.mulVec, dotProduct, simplexJacobian_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [div_mul_eq_mul_div, sub_mul]
  rw [←Finset.sum_div, Finset.sum_sub_distrib, ←Finset.mul_sum]
  ring

lemma simplexDerivative_det {r : ℕ} (s : V (r+1)) :
    (simplexDerivative s).det = (simplexJacobian s).det := by
  change LinearMap.det (simplexDerivative s).toLinearMap = _
  rw [simplexDerivative_eq, LinearMap.det_toLin']

lemma simplex_transport_pointwise {r : ℕ} (u s : V (r+1)) (hs : ∀ i, 0 < s i) :
    (∏ i, (Real.exp (-(u i)^2) * s i) ^ ((r:ℝ)/(r+1:ℕ))) ≤
      |(simplexDerivative s).det| *
        Real.exp (-((r:ℝ)/(r+1:ℕ)) * ∑ i, (simplexForm i (simplexDual u))^2) := by
  have hpow (i : Fin (r+1)) :
      (Real.exp (-(u i)^2) * s i) ^ ((r:ℝ)/(r+1:ℕ)) =
        Real.exp (-((r:ℝ)/(r+1:ℕ))*(u i)^2) * (s i)^((r:ℝ)/(r+1:ℕ)) := by
    rw [Real.mul_rpow (Real.exp_pos _).le (hs i).le, ← Real.exp_mul]
    congr 2; ring
  simp_rw [hpow]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  have hex : Real.exp (∑ i, -((r:ℝ)/(r+1:ℕ))*(u i)^2) ≤
      Real.exp (-((r:ℝ)/(r+1:ℕ)) * ∑ i, (simplexForm i (simplexDual u))^2) := by
    apply Real.exp_le_exp.mpr
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonpos_left (simplex_projection_square u) (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hd := simplexJacobian_det_ge s hs
  have hdn : 0 ≤ (simplexJacobian s).det :=
    (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hs i).le _)).trans hd
  rw [simplexDerivative_det, abs_of_nonneg hdn]
  exact (mul_le_mul hex hd (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hs i).le _))
    (Real.exp_pos _).le).trans_eq (mul_comm _ _)


def simplexRoot {r : ℕ} : Matrix (Fin r) (Fin r) ℝ :=
  1 + Matrix.replicateCol Unit (fun _ : Fin r => (1:ℝ)) *
    Matrix.replicateRow Unit (fun _ : Fin r => (1:ℝ)/(Real.sqrt (r+1:ℕ)+1))

lemma simplexRoot_mulVec {r : ℕ} (x : V r) (j : Fin r) :
    simplexRoot.mulVec x j = x j + (∑ l, x l)/(Real.sqrt (r+1:ℕ)+1) := by
  rw [simplexRoot, Matrix.add_mulVec, Matrix.one_mulVec]
  simp [Matrix.mulVec, Matrix.mul_apply, dotProduct, ←Finset.mul_sum]
  ring

lemma simplexRoot_det {r : ℕ} :
    (simplexRoot (r:=r)).det = Real.sqrt (r+1:ℕ) := by
  rw [simplexRoot, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : 0 ≤ (r+1:ℕ) := Nat.zero_le _
  have hs : (Real.sqrt (r+1:ℕ))^2 = (r+1:ℕ) := Real.sq_sqrt (by positivity)
  have hd : Real.sqrt (r+1:ℕ)+1 ≠ 0 := by positivity
  push_cast at *
  field_simp
  nlinarith

lemma simplexRoot_square {r : ℕ} (x : V r) :
    (∑ j, (simplexRoot.mulVec x j)^2) = ∑ i, (simplexForm i x)^2 := by
  simp_rw [simplexRoot_mulVec]
  rw [Fin.sum_univ_succ]
  simp only [simplexForm_zero, simplexForm_succ, neg_sq]
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hs : (∑ j : Fin r, 2*x j*((∑ l, x l)/(Real.sqrt (r+1:ℕ)+1))) =
      2*((∑ l, x l)/(Real.sqrt (r+1:ℕ)+1)) * ∑ j, x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he : (Real.sqrt (r+1:ℕ))^2 = (r+1:ℕ) := Real.sq_sqrt (by positivity)
  have hd : Real.sqrt (r+1:ℕ)+1 ≠ 0 := by positivity
  push_cast at *
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*(∑ j, x j)^2) he]

lemma simplex_gaussian_integral {r : ℕ} (c : ℝ) (hc : 0 < c) :
    (∫⁻ x : V r, ENNReal.ofReal
      (Real.exp (-c * ∑ i : Fin (r+1), (simplexForm i x)^2))) =
      ENNReal.ofReal ((Real.sqrt (Real.pi/c))^r / Real.sqrt (r+1:ℕ)) := by
  let B : V r →ₗ[ℝ] V r := Matrix.toLin' simplexRoot
  have hdet : B.det = Real.sqrt (r+1:ℕ) := by
    rw [LinearMap.det_toLin', simplexRoot_det]
  have hp : 0 < Real.sqrt (r+1:ℕ) := Real.sqrt_pos.mpr (by positivity)
  let g : V r → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-c * ∑ j, (x j)^2))
  have hg : Measurable g := by
    apply Continuous.measurable
    dsimp [g]
    apply ENNReal.continuous_ofReal.comp
    fun_prop
  have he (x : V r) : g (B x) =
      ENNReal.ofReal (Real.exp (-c * ∑ i : Fin (r+1), (simplexForm i x)^2)) := by
    dsimp [g, B]
    rw [simplexRoot_square]
  have hgi : (∫⁻ x, g x) = ENNReal.ofReal ((Real.sqrt (Real.pi/c))^r) := by
    have hex (x : V r) : Real.exp (-c * ∑ j, (x j)^2) =
        ∏ j, Real.exp (-c*(x j)^2) := by rw [Finset.mul_sum, Real.exp_sum]
    dsimp [g]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (show Integrable (fun x : V r => Real.exp (-c * ∑ j, (x j)^2)) volume from by
        simp_rw [hex]
        exact Integrable.fintype_prod (fun i : Fin r => integrable_exp_neg_mul_sq hc))
      (Filter.Eventually.of_forall (fun x : V r => (Real.exp_pos _).le))]
    congr 1
    simp_rw [hex]
    rw [integral_fintype_prod_volume_eq_prod (fun (_ : Fin r) (t : ℝ) => Real.exp (-c*t^2))]
    simp only [integral_gaussian, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f:=B) (by rw [hdet]; exact hp.ne')
  calc
    _ = ∫⁻ x, g (B x) := by simp_rw [he]
    _ = ∫⁻ y, g y ∂(Measure.map B volume) := (lintegral_map hg B.continuous_of_finiteDimensional.measurable).symm
    _ = _ := by
      rw [hm, lintegral_smul_measure, hgi, hdet, abs_of_pos (inv_pos.mpr hp), smul_eq_mul,
        ←ENNReal.ofReal_mul (inv_pos.mpr hp).le]
      congr 1; ring

lemma simplex_transport_integral {r : ℕ} (hr : 0 < r) {T T' : Fin (r+1) → ℝ → ℝ}
    (hmono : ∀ i, StrictMono (T i))
    (hT : ∀ i t, HasDerivAt (T i) (T' i t) t) (hpos : ∀ i t, 0 < T' i t) :
    (∫⁻ x : V r, ENNReal.ofReal
      (∏ i, (Real.exp (-(T i (simplexForm i x))^2) * T' i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
      ENNReal.ofReal ((Real.sqrt (Real.pi/((r:ℝ)/(r+1:ℕ))))^r / Real.sqrt (r+1:ℕ)) := by
  let g : V r → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Real.exp (-((r:ℝ)/(r+1:ℕ)) * ∑ i, (simplexForm i x)^2))
  calc
    _ ≤ ∫⁻ x : V r, ENNReal.ofReal |(simplexDerivative (fun i => T' i (simplexForm i x))).det| *
        g (simplexTransport T x) := by
      apply lintegral_mono
      intro x
      change _ ≤ ENNReal.ofReal |_| * ENNReal.ofReal _
      rw [←ENNReal.ofReal_mul (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (simplex_transport_pointwise
        (fun i => T i (simplexForm i x)) (fun i => T' i (simplexForm i x)) (fun i => hpos i _))
    _ = ∫⁻ y in simplexTransport T '' Set.univ, g y := by
      symm
      simpa using lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        MeasurableSet.univ (fun x _ => (simplexTransport_hasFDerivAt hT x).hasFDerivWithinAt)
        (simplexTransport_injective hmono).injOn g
    _ ≤ ∫⁻ y, g y := lintegral_mono' Measure.restrict_le_self (le_refl _)
    _ = _ := simplex_gaussian_integral _ (div_pos (Nat.cast_pos.mpr hr) (by positivity))



end SingleLatticeCovering.SimplexYoung





open MeasureTheory Filter Set
open scoped Topology
noncomputable section

end
end
end
end
end

end OAI
