import OAI.Analysis.CharacterCriterion.SpatialTensor

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace


variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

namespace KirchbergRordam.GenericRW
namespace Intertwining
variable {A : Type*} [CStarAlgebra A]


def algebra (v : A) : StarSubalgebra ℂ (A × A) where
  carrier := {p | v * p.1 = p.2 * v ∧ star v * p.2 = p.1 * star v}
  mul_mem' := by
    intro p q hp hq
    constructor
    · change v * (p.1 * q.1) = (p.2 * q.2) * v
      rw [← mul_assoc, hp.1, mul_assoc, hq.1, mul_assoc]
    · change star v * (p.2 * q.2) = (p.1 * q.1) * star v
      rw [← mul_assoc, hp.2, mul_assoc, hq.2, mul_assoc]
  one_mem' := by simp
  add_mem' := by
    intro p q hp hq
    constructor <;> change _ * (_ + _) = (_ + _) * _
    · rw [mul_add, add_mul, hp.1, hq.1]
    · rw [mul_add, add_mul, hp.2, hq.2]
  zero_mem' := by simp
  algebraMap_mem' := by
    intro z
    constructor
    · exact Algebra.commutes z v |>.symm
    · exact Algebra.commutes z (star v) |>.symm
  star_mem' := by
    intro p hp
    constructor
    · simpa only [star_mul, star_star, Prod.fst_star, Prod.snd_star] using (congrArg star hp.2).symm
    · simpa only [star_mul, star_star, Prod.fst_star, Prod.snd_star] using (congrArg star hp.1).symm

instance closed (v : A) : IsClosed ((algebra v : StarSubalgebra ℂ (A × A)) : Set (A × A)) :=
  (isClosed_eq (by fun_prop) (by fun_prop)).inter (isClosed_eq (by fun_prop) (by fun_prop))

omit instSize in
lemma cfc.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {v a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (h : v * a = b * v) (f : ℝ → ℝ) (hf : Continuous f) :
    v * cfc f a = cfc f b * v := by
  let : ContinuousFunctionalCalculus ℝ (A × A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hm : (a, b) ∈ algebra v := by
    refine ⟨h, ?_⟩
    simpa only [star_mul, ha.star_eq, hb.star_eq] using (congrArg star h).symm
  have hh := cfc_mem (p := IsSelfAdjoint) (s := algebra v) f hm
  rw [cfc_map_prod (S := ℂ) (pab := IsSelfAdjoint) f a b (hf.continuousOn)
    (show IsSelfAdjoint (a, b) from Prod.ext ha hb) ha hb] at hh
  exact hh.1

variable [PartialOrder A] [StarOrderedRing A]
lemma sqrt {v a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : v * a = b * v) :
    v * CFC.sqrt a = CFC.sqrt b * v := by
  rw [CFC.sqrt_eq_real_sqrt a ha, CFC.sqrt_eq_real_sqrt b hb,
    cfcₙ_eq_cfc (f := Real.sqrt) (a := a) (hf0 := Real.sqrt_zero),
    cfcₙ_eq_cfc (f := Real.sqrt) (a := b) (hf0 := Real.sqrt_zero)]
  exact cfc (IsSelfAdjoint.of_nonneg ha) (IsSelfAdjoint.of_nonneg hb) h _ Real.continuous_sqrt

lemma mul_sqrt_eq_zero {v a : A} (ha : 0 ≤ a) (h : v * a = 0) :
    v * CFC.sqrt a = 0 := by
  simpa only [CFC.sqrt_zero, zero_mul] using sqrt ha (le_refl (0 : A)) (v := v) (by simpa)

lemma sqrt_mul_eq_zero {v a : A} (ha : 0 ≤ a) (h : a * v = 0) :
    CFC.sqrt a * v = 0 := by
  have hh : star v * a = 0 := by
    simpa only [star_mul, IsSelfAdjoint.of_nonneg ha |>.star_eq, star_zero] using congrArg star h
  have he := congrArg star (mul_sqrt_eq_zero ha hh)
  simpa only [star_mul, IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a) |>.star_eq,
    star_star, star_zero] using he
end Intertwining

namespace SquareZeroCone
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


structure WeightedMatrix (A : Type*) [CStarAlgebra A] [PartialOrder A] where
  h : A
  x : Fin rankNum → Fin rankNum → A
  h_nonneg : 0 ≤ h
  norm_h_le : ‖h‖ ≤ 1
  star_x : ∀ i j, star (x i j) = x j i
  mul_x : ∀ i j k l, x i j * x k l = if j = k then h * x i l else 0
  diagonal : ∑ i, x i i = h

omit instSize in
lemma norm_mul_le_of_pair.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {x y h : A} (he : star x * x + star y * y = star h * h) (z : A) :
    ‖x * z‖ ≤ ‖h * z‖ := by
  have he' : star (x * z) * (x * z) + star (y * z) * (y * z) =
      star (h * z) * (h * z) := by
    simp only [star_mul]
    calc
      star z * star x * (x * z) + star z * star y * (y * z) =
          star z * (star x * x + star y * y) * z := by noncomm_ring
      _ = star z * star h * (h * z) := by rw [he]; noncomm_ring
  have hl : star (x * z) * (x * z) ≤ star (h * z) * (h * z) := by
    rw [← he']
    exact le_add_of_nonneg_right (star_mul_self_nonneg _)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hl (star_mul_self_nonneg _)
  simp only [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (x * z), norm_nonneg (h * z)]

namespace WeightedMatrix
variable (W : WeightedMatrix A)
omit [StarOrderedRing A] in
lemma commute_h (i j : Fin rankNum) : Commute (W.x i j) W.h := by
  change W.x i j * W.h = W.h * W.x i j
  conv_lhs => rw [← W.diagonal, Finset.mul_sum]
  simp only [W.mul_x]
  simp

lemma column_sum (i : Fin rankNum) : ∑ j, star (W.x i j) * W.x i j = star W.h * W.h := by
  simp only [W.star_x, W.mul_x, ite_true, ← Finset.mul_sum, W.diagonal,
    (IsSelfAdjoint.of_nonneg W.h_nonneg).star_eq]

lemma norm_mul_le (i j : Fin rankNum) (z : A) : ‖W.x i j * z‖ ≤ ‖W.h * z‖ := by
  have he : ∑ k, star (W.x i k * z) * (W.x i k * z) = star (W.h * z) * (W.h * z) := by
    simp only [star_mul]
    calc
      _ = star z * (∑ k, star (W.x i k) * W.x i k) * z := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        noncomm_ring
      _ = _ := by rw [W.column_sum]; noncomm_ring
  have hl : star (W.x i j * z) * (W.x i j * z) ≤ star (W.h * z) * (W.h * z) := by
    rw [← he]
    exact Finset.single_le_sum (fun k _ => star_mul_self_nonneg (W.x i k * z)) (Finset.mem_univ j)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hl (star_mul_self_nonneg _)
  simp only [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (W.x i j * z), norm_nonneg (W.h * z)]

end WeightedMatrix

end SquareZeroCone

namespace IntervalCalculus
open scoped ComplexOrder


def coord : C(unitInterval, ℂ) := ⟨fun t => (t : ℝ), by fun_prop⟩
omit instSize in
@[simp] lemma coord_apply
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : coord t = (t : ℝ) := rfl

variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

omit instSize in
lemma spectrum_mem_interval.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [Nontrivial A]
    [PartialOrder A]
    [StarOrderedRing A]
    {h : A} (hh : 0 ≤ h) (hn : ‖h‖ ≤ 1)
    {z : ℂ} (hz : z ∈ spectrum ℂ h) : z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 := by
  obtain ⟨r, hr, rfl⟩ := (IsSelfAdjoint.of_nonneg hh).spectrumRestricts.algebraMap_image ▸ hz
  have hr0 := spectrum_nonneg_of_nonneg hh hr
  have hr1 := spectrum.norm_le_norm_of_mem hr
  change 0 = 0 ∧ 0 ≤ r ∧ r ≤ 1
  exact ⟨rfl, hr0, (le_abs_self r).trans (hr1.trans hn)⟩


def spectralPoint {h : A} (hh : 0 ≤ h) (hn : ‖h‖ ≤ 1) : C(spectrum ℂ h, unitInterval) :=
  ⟨fun z => ⟨z.1.re, (spectrum_mem_interval hh hn z.2).2⟩, by fun_prop⟩

def hom {h : A} (hh : 0 ≤ h) (hn : ‖h‖ ≤ 1) : C(unitInterval, ℂ) →⋆ₐ[ℂ] A :=
  (cfcHom (IsSelfAdjoint.of_nonneg hh).isStarNormal).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ (spectralPoint hh hn))

lemma hom_coord {h : A} (hh : 0 ≤ h) (hn : ‖h‖ ≤ 1) : hom hh hn coord = h := by
  change cfcHom (IsSelfAdjoint.of_nonneg hh).isStarNormal
    (coord.comp (spectralPoint hh hn)) = h
  have he : coord.comp (spectralPoint hh hn) = (ContinuousMap.restrict (spectrum ℂ h) (ContinuousMap.id ℂ)) := by
    ext z
    apply Complex.ext
    · rfl
    · exact (spectrum_mem_interval hh hn z.property).1.symm
  rw [he, cfcHom_id]

lemma norm_hom_le {h : A} (hh : 0 ≤ h) (hn : ‖h‖ ≤ 1) (f : C(unitInterval, ℂ)) :
    ‖hom hh hn f‖ ≤ ‖f‖ := NonUnitalStarAlgHom.norm_apply_le (hom hh hn) f

end IntervalCalculus
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.IntervalCalculus
open scoped ContinuousMapZero
def coordMul : C(unitInterval, ℂ) →ₗ[ℂ] C(unitInterval, ℂ)₀ where
  toFun f := ⟨coord * f, by simp [coord]⟩
  map_add' f g := by ext t; simp [mul_add]
  map_smul' c f := by ext t; simp [mul_comm, mul_left_comm]

omit instSize in
@[simp] lemma coordMul_apply
    [KirchbergRordam.GenericRW.Size]
    (f : C(unitInterval, ℂ)) (t : unitInterval) :
    coordMul f t = coord t * f t := rfl

omit instSize in
lemma coordMul_dense
    [KirchbergRordam.GenericRW.Size]
    : DenseRange coordMul := by
  let I : Ideal C(unitInterval, ℂ) := Ideal.span {coord}
  have hs : ContinuousMap.setOfIdeal I = ({0} : Set unitInterval)ᶜ := by
    ext t
    rw [ContinuousMap.mem_setOfIdeal]
    constructor
    · rintro ⟨f, hf, hne⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro ht
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      apply hne
      simp [ht, coord]
    · intro ht
      refine ⟨coord, Ideal.subset_span (Set.mem_singleton _), ?_⟩
      intro he
      apply ht
      apply Subtype.ext
      change ((t : ℝ) : ℂ) = 0 at he
      exact_mod_cast he
  have hi : (fun f : C(unitInterval, ℂ)₀ => f.toContinuousMap) '' Set.range coordMul = I := by
    ext f
    constructor
    · rintro ⟨g, ⟨v, rfl⟩, rfl⟩
      exact Ideal.mul_mem_right _ I (Ideal.subset_span (Set.mem_singleton _))
    · intro hf
      obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hf
      refine ⟨coordMul g, ⟨g, rfl⟩, ?_⟩
      change coord * g = f
      rw [mul_comm, hg]
  apply (ContinuousMapZero.isometry_toContinuousMap.isEmbedding.isInducing.dense_iff).mpr
  intro f
  rw [hi, ← Ideal.coe_closure, ← ContinuousMap.idealOfSet_ofIdeal_eq_closure, hs]
  intro t ht
  have ht0 : t = 0 := by simpa only [compl_compl, Set.mem_singleton_iff] using ht
  rw [ht0]
  exact map_zero f

end KirchbergRordam.GenericRW.IntervalCalculus

namespace KirchbergRordam.GenericRW
namespace SquareZeroCone
namespace WeightedMatrix
open scoped ContinuousMapZero
open IntervalCalculus
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedMatrix A)

abbrev eval : C(unitInterval, ℂ) →⋆ₐ[ℂ] A := hom W.h_nonneg W.norm_h_le

lemma commute_eval (i j : Fin rankNum) (f : C(unitInterval, ℂ)) : Commute (W.x i j) (W.eval f) := by
  exact ((IsSelfAdjoint.of_nonneg W.h_nonneg).commute_cfcHom
    (IsSelfAdjoint.of_nonneg W.h_nonneg).isStarNormal (W.commute_h i j).symm _).symm

def coeffAux (i j : Fin rankNum) : C(unitInterval, ℂ) →ₗ[ℂ] A where
  toFun f := W.x i j * W.eval f
  map_add' f g := by simp [mul_add]
  map_smul' c f := by simp

lemma coeffAux_bound (i j : Fin rankNum) (f : C(unitInterval, ℂ)) :
    ‖W.coeffAux i j f‖ ≤ ‖coordMul f‖ := by
  change ‖W.x i j * W.eval f‖ ≤ ‖coord * f‖
  calc
    _ ≤ ‖W.h * W.eval f‖ := W.norm_mul_le i j _
    _ = ‖W.eval (coord * f)‖ := by rw [map_mul, hom_coord]
    _ ≤ ‖coord * f‖ := norm_hom_le _ _ _


def coeff (i j : Fin rankNum) : C(unitInterval, ℂ)₀ →L[ℂ] A :=
  (W.coeffAux i j).extendOfNorm coordMul

lemma coeff_coordMul (i j : Fin rankNum) (f : C(unitInterval, ℂ)) :
    W.coeff i j (coordMul f) = W.x i j * W.eval f := by
  exact LinearMap.extendOfNorm_eq coordMul_dense
    ⟨1, fun f => by simpa using W.coeffAux_bound i j f⟩ f

lemma norm_coeff_le (i j : Fin rankNum) (f : C(unitInterval, ℂ)₀) : ‖W.coeff i j f‖ ≤ ‖f‖ := by
  simpa only [coeff, one_mul] using LinearMap.norm_extendOfNorm_apply_le (f := W.coeffAux i j)
    coordMul_dense 1 (fun f => by simpa using W.coeffAux_bound i j f) f

omit instSize in
lemma coordMul_star
    [KirchbergRordam.GenericRW.Size]
    (f : C(unitInterval, ℂ)) : star (coordMul f) = coordMul (star f) := by
  ext t
  simp [coordMul_apply]

omit instSize in
lemma coordMul_mul
    [KirchbergRordam.GenericRW.Size]
    (f g : C(unitInterval, ℂ)) :
    coordMul f * coordMul g = coordMul (coord * f * g) := by
  ext t
  change (coord t * f t) * (coord t * g t) = coord t * (coord t * f t * g t)
  ring

lemma star_coeff (i j : Fin rankNum) (f : C(unitInterval, ℂ)₀) :
    star (W.coeff i j f) = W.coeff j i (star f) := by
  refine coordMul_dense.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [coordMul_star, W.coeff_coordMul, W.coeff_coordMul, star_mul, W.star_x, map_star]
  simpa only [map_star] using (W.commute_eval j i (star g)).symm.eq

lemma mul_coeff (i j k l : Fin rankNum) (f g : C(unitInterval, ℂ)₀) :
    W.coeff i j f * W.coeff k l g = if j = k then W.coeff i l (f * g) else 0 := by
  classical
  refine coordMul_dense.induction_on₂ (p := fun f g =>
    W.coeff i j f * W.coeff k l g = if j = k then W.coeff i l (f * g) else 0)
    (isClosed_eq (by fun_prop) (by by_cases hjk : j = k <;> simp only [hjk, ↓reduceIte] <;> fun_prop)) ?_ f g
  intro f g
  rw [coordMul_mul, W.coeff_coordMul, W.coeff_coordMul, W.coeff_coordMul]
  have he : W.x i j * W.eval f * (W.x k l * W.eval g) =
      (W.x i j * W.x k l) * (W.eval f * W.eval g) := by
    rw [mul_assoc (W.x i j), ← mul_assoc (W.eval f), (W.commute_eval k l f).symm.eq]
    noncomm_ring
  rw [he, W.mul_x]
  split_ifs with hjk
  · rw [map_mul, map_mul, hom_coord]
    have hc := W.commute_h i l
    rw [← hc.eq]
    noncomm_ring
  · simp
end WeightedMatrix
end SquareZeroCone
end KirchbergRordam.GenericRW
namespace KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix
open scoped ContinuousMapZero BigOperators
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedMatrix A)

abbrev ConeMatrix := Matrix (Fin rankNum) (Fin rankNum) C(unitInterval, ℂ)₀

def matrixCoeffs (m : ConeMatrix) : A := ∑ i, ∑ j, W.coeff i j (m i j)

lemma matrixCoeffs_add (m n : ConeMatrix) :
    W.matrixCoeffs (m + n) = W.matrixCoeffs m + W.matrixCoeffs n := by
  simp [matrixCoeffs, map_add, Finset.sum_add_distrib]

lemma matrixCoeffs_smul (c : ℂ) (m : ConeMatrix) :
    W.matrixCoeffs (c • m) = c • W.matrixCoeffs m := by
  simp [matrixCoeffs, map_smul, Finset.smul_sum]

lemma matrixCoeffs_single (i j : Fin rankNum) (f : C(unitInterval, ℂ)₀) :
    W.matrixCoeffs (Matrix.single i j f) = W.coeff i j f := by
  simp [matrixCoeffs, Matrix.single, ite_and, apply_ite]

lemma matrixCoeffs_zero : W.matrixCoeffs 0 = 0 := by simp [matrixCoeffs]

lemma matrixCoeffs_mul (m n : ConeMatrix) :
    W.matrixCoeffs (m * n) = W.matrixCoeffs m * W.matrixCoeffs n := by
  induction m using Matrix.induction_on' with
  | h_zero => simp [W.matrixCoeffs_zero]
  | h_add m m' hm hm' => simp only [add_mul, W.matrixCoeffs_add, hm, hm']
  | h_std_basis i j f =>
    induction n using Matrix.induction_on' with
    | h_zero => simp [W.matrixCoeffs_zero]
    | h_add n n' hn hn' => simp only [mul_add, W.matrixCoeffs_add, hn, hn']
    | h_std_basis k l g =>
      by_cases h : j = k
      · subst k
        rw [Matrix.single_mul_single_same, W.matrixCoeffs_single,
          W.matrixCoeffs_single, W.matrixCoeffs_single, W.mul_coeff, ite_eq_left rfl]
      · rw [Matrix.single_mul_single_of_ne (h := h), W.matrixCoeffs_single,
          W.matrixCoeffs_single, W.mul_coeff, ite_eq_right h, W.matrixCoeffs_zero]

lemma matrixCoeffs_star (m : ConeMatrix) : W.matrixCoeffs (star m) = star (W.matrixCoeffs m) := by
  simp only [matrixCoeffs, star_sum, W.star_coeff]
  exact Finset.sum_comm


def matrixHom : ConeMatrix →⋆ₙₐ[ℂ] A where
  toFun := W.matrixCoeffs
  map_zero' := by simp [matrixCoeffs]
  map_add' := W.matrixCoeffs_add
  map_smul' := W.matrixCoeffs_smul
  map_mul' := W.matrixCoeffs_mul
  map_star' := W.matrixCoeffs_star

end KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix
end

end OAI
