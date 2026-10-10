import OAI.Analysis.CharacterCriterion.OrderZeroPair

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
namespace Domination
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private def invReg (τ : ℝ) (t : ℝ) : ℝ := (max t 0 + τ)⁻¹
private def remReg (τ : ℝ) (t : ℝ) : ℝ := 1 - t * invReg τ t

omit instSize in
private lemma invReg_cont
    [KirchbergRordam.GenericRW.Size]
    {τ : ℝ} (hτ : 0 < τ) : Continuous (invReg τ) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t
  exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right t 0) hτ)

private lemma remReg_cont {τ : ℝ} (hτ : 0 < τ) : Continuous (remReg τ) := by
  exact continuous_const.sub (continuous_id.mul (invReg_cont hτ))

omit instSize in
private lemma remReg_nonneg
    [KirchbergRordam.GenericRW.Size]
    {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    0 ≤ remReg τ t := by
  dsimp only [remReg, invReg]
  rw [max_eq_left ht]
  have hs : 0 < t + τ := add_pos_of_nonneg_of_pos ht hτ
  rw [sub_nonneg, ← div_eq_mul_inv, div_le_one hs]
  linarith

omit instSize in
private lemma remReg_bound
    [KirchbergRordam.GenericRW.Size]
    {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    (remReg τ t) * t * (remReg τ t) ≤ τ := by
  have hs : 0 < t + τ := add_pos_of_nonneg_of_pos ht hτ
  have he : remReg τ t = τ / (t + τ) := by
    dsimp only [remReg, invReg]
    rw [max_eq_left ht]
    field_simp
    ring
  rw [he]
  apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hs))
  field_simp
  nlinarith [sq_nonneg t, mul_nonneg ht hτ.le]

omit instSize in
lemma norm_sandwich_sqrt_sq.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    (h : A) {e : A} (he : 0 ≤ e) (hh : IsSelfAdjoint h) :
    ‖h * CFC.sqrt e‖ ^ 2 = ‖h * e * h‖ := by
  rw [pow_two, ← CStarRing.norm_self_mul_star, star_mul,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg e)).star_eq, hh.star_eq]
  congr 1
  rw [mul_assoc, ← mul_assoc (CFC.sqrt e), CFC.sqrt_mul_sqrt_self e, ← mul_assoc]

lemma norm_sandwich_le {e T : A} (he : 0 ≤ e) {C : ℝ} (hC : 0 ≤ C)
    (hle : e ≤ C • T) (h : A) (hh : IsSelfAdjoint h) :
    ‖h * CFC.sqrt e‖ ^ 2 ≤ C * ‖h * T * h‖ := by
  rw [norm_sandwich_sqrt_sq h he hh]
  have hle' := star_right_conjugate_le_conjugate hle h
  rw [hh.star_eq, mul_smul_comm, smul_mul_assoc] at hle'
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle'
    (by simpa only [hh.star_eq] using star_right_conjugate_nonneg he h)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hn


lemma regularizer_estimate {e T : A} (he : 0 ≤ e) (hT : 0 ≤ T)
    {C τ : ℝ} (hC : 0 ≤ C) (hle : e ≤ C • T) (hτ : 0 < τ) :
    ‖(1 - T * cfc (invReg τ) T) * CFC.sqrt e‖ ^ 2 ≤ C * τ := by
  have hTs := IsSelfAdjoint.of_nonneg hT
  have hid : cfc (fun t : ℝ => t) T = T := cfc_id ℝ T hTs
  let h := cfc (remReg τ) T
  have hh : IsSelfAdjoint h := cfc_predicate (remReg τ) T
  have heq : h = 1 - T * cfc (invReg τ) T := by
    change cfc (fun t : ℝ => 1 - t * invReg τ t) T = _
    rw [cfc_sub (fun _ : ℝ => 1) (fun t : ℝ => t * invReg τ t) T
      continuous_const.continuousOn (continuous_id.mul (invReg_cont hτ)).continuousOn,
      cfc_const _ _ hTs, map_one,
      cfc_mul (fun t : ℝ => t) (invReg τ) T continuous_id.continuousOn (invReg_cont hτ).continuousOn,
      hid]
  rw [← heq]
  apply (norm_sandwich_le he hC hle h hh).trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hc : h * T * h = cfc (fun t : ℝ => remReg τ t * t * remReg τ t) T := by
    rw [cfc_mul (fun t : ℝ => remReg τ t * t) (remReg τ) T
      ((remReg_cont hτ).mul continuous_id).continuousOn (remReg_cont hτ).continuousOn,
      cfc_mul (remReg τ) (fun t : ℝ => t) T (remReg_cont hτ).continuousOn continuous_id.continuousOn, hid]
  rw [hc]
  apply norm_cfc_le hτ.le
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hT ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (remReg_nonneg hτ ht0) ht0)
    (remReg_nonneg hτ ht0))]
  exact remReg_bound hτ ht0

end

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma sqrt_mem_right_range {e T : A} (he : 0 ≤ e) (hT : 0 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) (hle : e ≤ C • T) :
    CFC.sqrt e ∈ ClosedRightRange.space T := by
  change CFC.sqrt e ∈ closure (Set.range (fun x : A => T * x))
  rw [Metric.mem_closure_iff]
  intro ε hε
  let τ := ε ^ 2 / (C + 1)
  have hτ : 0 < τ := div_pos (sq_pos_of_pos hε) (by linarith)
  refine ⟨T * (cfc (invReg τ) T * CFC.sqrt e), ⟨_, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have heq : CFC.sqrt e - T * (cfc (invReg τ) T * CFC.sqrt e) =
      (1 - T * cfc (invReg τ) T) * CFC.sqrt e := by noncomm_ring
  rw [heq]
  have hn := regularizer_estimate he hT hC hle hτ
  have ht : C * τ < ε ^ 2 := by
    dsimp only [τ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < C+1)).mpr
    nlinarith [sq_pos_of_pos hε]
  nlinarith [norm_nonneg ((1 - T * cfc (invReg τ) T) * CFC.sqrt e)]

lemma sqrt_mem_self (e : A) (he : 0 ≤ e) : CFC.sqrt e ∈ ClosedRightRange.space e :=
  sqrt_mem_right_range he he (by norm_num : (0:ℝ) ≤ 1) (by simp)

lemma sqrt_right_range_eq (e : A) (he : 0 ≤ e) :
    ClosedRightRange.space (CFC.sqrt e) = ClosedRightRange.space e := by
  apply le_antisymm
  · exact ClosedRightRange.space_le (sqrt_mem_self e he)
  · have hh := ClosedRightRange.space_mul_le (CFC.sqrt e) (CFC.sqrt e)
    rwa [CFC.sqrt_mul_sqrt_self e he] at hh


lemma exists_factor {e y : A} (he : 0 ≤ e) {C : ℝ} (hC : 0 ≤ C)
    (hle : e ≤ C • (star y * y)) :
    ∃ z : A, star z * z = e ∧ z ∈ ClosedRightRange.space y := by
  let a := CFC.sqrt (star y * y)
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have haa : star a * a = star y * y := by
    rw [ha.star_eq]
    exact CFC.sqrt_mul_sqrt_self _
  have hmem : CFC.sqrt e ∈ ClosedRightRange.space a := by
    rw [sqrt_right_range_eq _ (star_mul_self_nonneg y)]
    exact sqrt_mem_right_range he (star_mul_self_nonneg y) hC hle
  let x : ClosedRightRange.space a := ⟨CFC.sqrt e, hmem⟩
  refine ⟨ClosedRightRange.transport a y x, ?_, ClosedRightRange.transport_mem haa x⟩
  rw [ClosedRightRange.transport_inner haa]
  change star (CFC.sqrt e) * CFC.sqrt e = e
  rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg e)).star_eq, CFC.sqrt_mul_sqrt_self e he]

end Domination


section
variable {A : Type*} [CStarAlgebra A]


def CuntzBelow (a b : A) : Prop :=
  a ∈ closure (Set.range (fun x : A => star x * b * x))

namespace CuntzBelow
omit instSize in
lemma approx.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a b : A} (h : CuntzBelow a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : A, ‖a - star x * b * x‖ < ε := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.mp h ε hε
  exact ⟨x, by simpa only [dist_eq_norm] using hx⟩

omit instSize in
lemma of_approx.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a b : A} (h : ∀ ε > 0, ∃ x : A, ‖a - star x * b * x‖ < ε) :
    CuntzBelow a b := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨x, hx⟩ := h ε hε
  exact ⟨_, ⟨x, rfl⟩, by simpa only [dist_eq_norm] using hx⟩

omit instSize in
lemma of_eq.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a b x : A} (h : star x * b * x = a) : CuntzBelow a b :=
  subset_closure ⟨x, h⟩

@[refl] lemma refl (a : A) : CuntzBelow a a := of_eq (x := 1) (by simp)

lemma trans {a b c : A} (hab : CuntzBelow a b) (hbc : CuntzBelow b c) : CuntzBelow a c := by
  apply of_approx
  intro ε hε
  obtain ⟨x, hx⟩ := hab.approx (half_pos hε)
  obtain ⟨y, hy⟩ := hbc.approx (div_pos (half_pos hε) (by positivity : (0:ℝ) < ‖x‖^2+1))
  refine ⟨y*x, ?_⟩
  have he : a - star (y*x) * c * (y*x) =
      (a - star x*b*x) + star x * (b-star y*c*y) * x := by
    rw [star_mul]
    noncomm_ring
  have hn : ‖star x * (b-star y*c*y) * x‖ ≤ ‖x‖^2 * ‖b-star y*c*y‖ := by
    calc
      _ ≤ (‖star x‖ * ‖b-star y*c*y‖) * ‖x‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = _ := by rw [norm_star]; ring
  have hy' : (‖x‖^2+1)*‖b-star y*c*y‖ < ε/2 := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < ‖x‖^2+1)).mp hy
    nlinarith
  rw [he]
  exact (norm_add_le _ _).trans_lt (by nlinarith [norm_nonneg (b-star y*c*y)])

lemma map {B : Type*} [CStarAlgebra B] {a b : A} (h : CuntzBelow a b) (f : A →⋆ₐ[ℂ] B) :
    CuntzBelow (f a) (f b) := by
  apply of_approx
  intro ε hε
  obtain ⟨x, hx⟩ := h.approx hε
  refine ⟨f x, ?_⟩
  have he : f a - star (f x) * f b * f x = f (a - star x * b * x) := by simp only [map_sub, map_mul, map_star]
  rw [he]
  exact (NonUnitalStarAlgHom.norm_apply_le f _).trans_lt hx
end CuntzBelow
end

namespace ExactCut
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


def cut (a : A) (δ : ℝ) : A := (a - algebraMap ℝ A δ)⁺

omit instSize in
lemma cut_nonneg.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    (a : A) (δ : ℝ) : 0 ≤ cut a δ := CFC.posPart_nonneg _

lemma cut_lower (a : A) (ha : IsSelfAdjoint a) (δ : ℝ) :
    δ • cut a δ ≤ CFC.sqrt (cut a δ) * a * CFC.sqrt (cut a δ) := by
  let d := a - algebraMap ℝ A δ
  let p := cut a δ
  let q := d⁻
  let s := CFC.sqrt p
  have hd : IsSelfAdjoint d := ha.sub (IsSelfAdjoint.algebraMap A (IsSelfAdjoint.all δ))
  have hp : 0 ≤ p := cut_nonneg a δ
  have hs : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)
  have hss : s*s = p := CFC.sqrt_mul_sqrt_self p hp
  have hqs : q*s=0 := Intertwining.mul_sqrt_eq_zero hp (CFC.negPart_mul_posPart d)
  have hdq : d = p-q := (CFC.posPart_sub_negPart d hd).symm
  have hnonneg : 0 ≤ s*d*s := by
    have hh := star_left_conjugate_nonneg hp s
    rw [hs.star_eq] at hh
    rw [hdq, mul_sub, sub_mul, mul_assoc s q s, hqs, mul_zero, sub_zero]
    exact hh
  have heq : s*d*s = s*a*s - δ • p := by
    dsimp only [d]
    rw [mul_sub, sub_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, hss]
  rw [heq, sub_nonneg] at hnonneg
  exact hnonneg

omit instSize in
lemma close_lower.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {η : ℝ} (h : ‖a-b‖ ≤ η) : a ≤ b + algebraMap ℝ A η := by
  have hh := (ha.sub hb).le_algebraMap_norm_self
  have hs : algebraMap ℝ A ‖a-b‖ ≤ algebraMap ℝ A η := by
    simpa only [Algebra.algebraMap_eq_smul_one] using smul_le_smul_of_nonneg_right h (zero_le_one : (0:A) ≤ 1)
  have ht := hh.trans hs
  exact sub_le_iff_le_add.mp ht |>.trans_eq (add_comm _ _)

lemma cut_dominated {a b x : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {δ : ℝ} (hδ : 0 < δ) (hclose : ‖a-star x*b*x‖ < δ/2) :
    cut a δ ≤ (2/δ) • (star (CFC.sqrt b*x*CFC.sqrt (cut a δ)) *
      (CFC.sqrt b*x*CFC.sqrt (cut a δ))) := by
  let e := cut a δ
  let s := CFC.sqrt e
  let y := CFC.sqrt b*x*s
  have hs : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hss : s*s=e := CFC.sqrt_mul_sqrt_self _ (cut_nonneg _ _)
  have hbroot : IsSelfAdjoint (CFC.sqrt b) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have ht : star y*y = s*(star x*b*x)*s := by
    dsimp only [y]
    rw [star_mul, star_mul, hs.star_eq, hbroot.star_eq]
    calc
      _ = s * star x * (CFC.sqrt b * CFC.sqrt b) * x * s := by noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self b hb]; noncomm_ring
  have hc := close_lower (IsSelfAdjoint.of_nonneg ha)
    (IsSelfAdjoint.of_nonneg (star_left_conjugate_nonneg hb x)) hclose.le
  have hc' := star_left_conjugate_le_conjugate hc s
  rw [hs.star_eq, mul_add, add_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, hss, ← ht] at hc'
  have hl := (cut_lower a (IsSelfAdjoint.of_nonneg ha) δ).trans hc'
  have hl' : (δ/2) • e ≤ star y*y := by
    have h : δ • e - (δ/2) • e ≤ star y*y := (sub_le_iff_le_add).mpr hl
    convert h using 1
    rw [← sub_smul]
    congr 1
    ring
  have hC : 0 ≤ 2/δ := le_of_lt (div_pos (by norm_num) hδ)
  have hf := smul_le_smul_of_nonneg_left hl' hC
  rw [smul_smul] at hf
  have hscalar : (2/δ)*(δ/2) = (1:ℝ) := by field_simp
  rw [hscalar, one_smul] at hf
  exact hf


theorem exists_exact_cut {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : CuntzBelow a b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z : A, star z*z = cut a δ ∧ z*star z ∈ ClosedRightRange.hereditary b := by
  obtain ⟨x,hx⟩ := hab.approx (half_pos hδ)
  let y := CFC.sqrt b*x*CFC.sqrt (cut a δ)
  obtain ⟨z,hz,hzm⟩ := Domination.exists_factor (cut_nonneg a δ)
    (le_of_lt (div_pos (by norm_num : (0:ℝ)<2) hδ)) (cut_dominated ha hb hδ hx)
  refine ⟨z,hz,?_⟩
  have hy : y ∈ ClosedRightRange.space b := by
    exact ClosedRightRange.mul_right_mem
      (ClosedRightRange.mul_right_mem (Domination.sqrt_mem_self b hb) x) _
  have hzb : z ∈ ClosedRightRange.space b := ClosedRightRange.space_le hy hzm
  exact ClosedRightRange.self_mul_star_mem_hereditary (IsSelfAdjoint.of_nonneg hb) hzb
end ExactCut
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.RWCut
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

def j (t : ℝ) : ℝ := (max t (1/2))⁻¹
def f (t : ℝ) : ℝ := j t*t
omit instSize in
lemma j_cont
    [KirchbergRordam.GenericRW.Size]
    : Continuous j := Continuous.inv₀ (by fun_prop)
  (fun t => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (le_max_right t _)))
lemma f_cont : Continuous f := j_cont.mul continuous_id
omit instSize in
lemma f_nonneg
    [KirchbergRordam.GenericRW.Size]
    {t : ℝ} (ht : 0≤t) : 0≤f t :=
  mul_nonneg (inv_nonneg.mpr (le_trans (by norm_num) (le_max_right t (1/2)))) ht
omit instSize in
lemma f_le_one
    [KirchbergRordam.GenericRW.Size]
    {t : ℝ} : f t≤1 := by
  unfold f j
  have hp : 0 < max t (1/2:ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  rw [mul_comm,← div_eq_mul_inv,div_le_one hp]
  exact le_max_left _ _
omit instSize in
lemma f_high
    [KirchbergRordam.GenericRW.Size]
    {t : ℝ} (ht : 1/2≤t) : f t=1 := by
  have hp : 0<t := lt_of_lt_of_le (by norm_num) ht
  unfold f j
  rw [max_eq_left ht,inv_mul_cancel₀ (ne_of_gt hp)]
omit instSize in
lemma f_low
    [KirchbergRordam.GenericRW.Size]
    {t : ℝ} (ht : t≤1/2) : f t=2*t := by
  norm_num [f,j,max_eq_right ht]
lemma defect {t : ℝ} : 1-f t=2*max ((1-t)-1/2) 0 := by
  by_cases h : t≤1/2
  · rw [f_low h,max_eq_left (by linarith)]; ring
  · rw [f_high (le_of_lt (lt_of_not_ge h)),max_eq_right (by linarith)]; ring

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
omit instSize in
lemma cut_cfc.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a : A} (ha : IsSelfAdjoint a) (δ : ℝ) :
    ExactCut.cut a δ=cfc (fun t : ℝ => max (t-δ) 0) a := by
  rw [ExactCut.cut,CFC.posPart_def,cfcₙ_eq_cfc]
  have hd : cfc (fun t : ℝ => t-δ) a=a-algebraMap ℝ A δ := by
    rw [cfc_sub ..]
    change cfc id a-cfc (fun _ : ℝ=>δ) a=_
    rw [cfc_id ℝ a ha,cfc_const _ _ ha]
  rw [← hd,← cfc_comp (fun t : ℝ=>t⁺) (fun t : ℝ=>t-δ) a ha]
  rfl

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
lemma function_mul (a : A) (ha : IsSelfAdjoint a) : cfc j a*a=cfc f a := by
  calc
    _=cfc j a*cfc id a := by rw [cfc_id ℝ a ha]
    _=_ := (cfc_mul j id a j_cont.continuousOn continuous_id.continuousOn).symm

omit [Nontrivial A] in
lemma rescaled_nonneg {a : A} (ha : 0≤a) : 0≤cfc f a :=
  cfc_nonneg fun _ ht => f_nonneg (spectrum_nonneg_of_nonneg ha ht)
omit [Nontrivial A] in
lemma rescaled_norm {a : A} (ha : 0≤a) : ‖cfc f a‖≤1 := by
  apply norm_cfc_le (by norm_num)
  intro t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (f_nonneg (spectrum_nonneg_of_nonneg ha ht))]
  exact f_le_one

omit [Nontrivial A] in
lemma rescaled_defect {a : A} (ha : 0≤a) : 1-cfc f a=(2:ℝ) • ExactCut.cut (1-a) (1/2) := by
  have hs := IsSelfAdjoint.of_nonneg ha
  have hd : cfc (fun t : ℝ=>1-t) a=1-a := by
    rw [cfc_sub ..,cfc_const_one ℝ a hs]
    change 1-cfc id a=1-a
    rw [cfc_id ℝ a hs]
  rw [cut_cfc ((IsSelfAdjoint.one A).sub hs),← hd,
    ← cfc_comp (fun t : ℝ=>max (t-1/2) 0) (fun t : ℝ=>1-t) a hs]
  have he : cfc (fun t : ℝ=>1-f t) a=cfc (fun t : ℝ=>2*max ((1-t)-1/2) 0) a :=
    cfc_congr fun _ _ => defect
  rw [cfc_sub _ _ a continuous_const.continuousOn f_cont.continuousOn,cfc_const_one ℝ a hs] at he
  rw [he,cfc_const_mul ..]
  rfl

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
lemma fixes_cut {a : A} (ha : IsSelfAdjoint a) :
    cfc f a*ExactCut.cut a (1/2)=ExactCut.cut a (1/2) := by
  rw [cut_cfc ha,← cfc_mul f _ a f_cont.continuousOn (by fun_prop)]
  apply cfc_congr
  intro t _
  change f t*max (t-1/2) 0=max (t-1/2) 0
  by_cases ht : 1/2≤t
  · simp [f_high ht]
  · rw [max_eq_right (by linarith : t-1/2≤0),mul_zero]

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
omit instSize in
lemma fixes_hereditary.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a c z : A} (hc : c*a=a) (hz : z∈ClosedRightRange.hereditary a) : c*z=z := by
  have hs : IsClosed {z : A | c*z=z} := isClosed_eq (by fun_prop) continuous_id
  apply closure_minimal ?_ hs hz
  rintro _ ⟨x,rfl⟩
  change c*(a*x*a)=a*x*a
  rw [← mul_assoc,← mul_assoc,hc]

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
omit instSize in
lemma fixes_of_mul_star.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a v : A} (h : a*(v*star v)=v*star v) : a*v=v := by
  have he : (a*v-v)*star (a*v-v)=0 := by
    have hh := congrArg star h
    simp only [star_mul,star_star] at hh
    calc
      _=a*(v*star v)*star a-a*(v*star v)-(v*star v)*star a+v*star v := by
        simp only [star_sub,star_mul]; noncomm_ring
      _=0 := by rw [h,show v*star v*star a=v*star v from hh]; noncomm_ring
  exact sub_eq_zero.mp ((CStarRing.mul_star_self_eq_zero_iff _).mp he)
end KirchbergRordam.GenericRW.RWCut

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
section
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)
def cutoffRescale : WeightedUnits (Fin rankNum) A :=
  W.rescale (cfc RWCut.j W.h) (cfc RWCut.f W.h) (cfc_predicate ..)
    (fun i j => (W.commute_h i j).symm.cfc_real _) (RWCut.function_mul _ (IsSelfAdjoint.of_nonneg W.nonneg))
    (RWCut.rescaled_nonneg W.nonneg) (RWCut.rescaled_norm W.nonneg)
omit [Nontrivial A] in
lemma cutoffRescale_corner : W.cutoffRescale.x 0 0=cfc RWCut.f (W.x 0 0) := by
  change cfc RWCut.j W.h*W.x 0 0=_
  rw [((W.commute_h 0 0).symm.cfc_real RWCut.j).eq]
  have hm : W.x 0 0*W.h=W.x 0 0*W.x 0 0 := by
    rw [(W.commute_h 0 0).eq,W.mul_x,ite_eq_left rfl]
  rw [Intertwining.cfc (IsSelfAdjoint.of_nonneg W.nonneg) (W.star_x 0 0) hm RWCut.j RWCut.j_cont]
  exact RWCut.function_mul _ (W.star_x 0 0)

omit [Nontrivial A] in

theorem exists_cutoff_relations
    (hcomp : CuntzBelow (1-W.h) (ExactCut.cut (W.x 0 0) (1/2))) :
    ∃ v : A, star v*v=1-W.cutoffRescale.h ∧ W.cutoffRescale.x 0 0*v=v := by
  have hp : 0≤1-W.h := sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg W.h W.nonneg).mp W.norm_le)
  obtain ⟨z,hz,hzm⟩ := ExactCut.exists_exact_cut hp (ExactCut.cut_nonneg _ _) hcomp (by norm_num : (0:ℝ)<1/2)
  let v : A := (Real.sqrt 2:ℝ) • z
  have hev : star v*v=(2:ℝ) • ExactCut.cut (1-W.h) (1/2) := by
    dsimp only [v]
    rw [star_smul,star_trivial,smul_mul_smul_comm,Real.mul_self_sqrt (by norm_num),hz]
  refine ⟨v,hev.trans (RWCut.rescaled_defect W.nonneg).symm,?_⟩
  have hfix : W.cutoffRescale.x 0 0*(z*star z)=z*star z := by
    rw [W.cutoffRescale_corner]
    exact RWCut.fixes_hereditary (RWCut.fixes_cut (W.star_x 0 0)) hzm
  have hfv := RWCut.fixes_of_mul_star hfix
  dsimp only [v]
  rw [mul_smul_comm,hfv]
end

variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

def cutoffHom (W : WeightedUnits (Fin rankNum) A)
    (hcomp : CuntzBelow (1-W.h) (ExactCut.cut (W.x 0 0) (1/2))) :
    DimensionDrop23 →⋆ₐ[ℂ] A :=
  W.cutoffRescale.rwHom (W.exists_cutoff_relations hcomp).choose_spec.1
    (W.exists_cutoff_relations hcomp).choose_spec.2
end KirchbergRordam.GenericRW.OrderZero.WeightedUnits
end

end OAI
