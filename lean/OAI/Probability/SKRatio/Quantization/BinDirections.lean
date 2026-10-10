import Mathlib
import OAI.Probability.SKRatio.Quantization.BinParameters

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma sum_scale_bin (σ : ι → α) (c : α → ℝ) (u : ι → ℝ) (a : α) :
    sum σ (fun i => c (σ i)*u i) a = c a*sum σ u a := by
  unfold sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only []
  rw [(Finset.mem_filter.mp hi).2]

lemma zeroSum_scale_bin {σ : ι → α} (c : α → ℝ) {u : ι → ℝ} (hu : ZeroSum σ u) :
    ZeroSum σ (fun i => c (σ i)*u i) := by
  intro a
  rw [sum_scale_bin,hu a,mul_zero]

lemma overlap_scale_bin (σ : ι → α) (c : α → ℝ) (u : ι → ℝ) (a : α) :
    overlap σ (fun i => c (σ i)*u i) (fun i => c (σ i)*u i) a =
      c a^2*overlap σ u u a := by
  have he : (fun i => (c (σ i)*u i)*(c (σ i)*u i)) =
      fun i => c (σ i)^2*(u i*u i) := by ext i; ring
  rw [overlap,he,sum_scale_bin σ (fun a => c a^2)]
  rfl

def DirectionSet (σ : ι → α) : Set (EuclideanSpace ℝ ι) :=
  {u | ∀ a, sum σ u a=0 ∧ overlap σ u u a=1}

abbrev Directions (σ : ι → α) := ↥(DirectionSet σ)

lemma directions_zeroSum {σ : ι → α} (u : Directions σ) : ZeroSum σ u.val :=
  fun a => (u.property a).1

lemma directions_overlap {σ : ι → α} (u : Directions σ) (a : α) :
    overlap σ u.val u.val a=1 := (u.property a).2

variable [Fintype α]

lemma directions_norm_sq {σ : ι → α} (u : Directions σ) : ‖u.val‖^2=(Fintype.card α:ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq,←sum_fibers σ]
  have he (a : α) : sum σ (fun i => u.val i^2) a=1 := by
    simpa only [pow_two,overlap] using directions_overlap u a
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

omit [Fintype α] in
lemma directionSet_closed (σ : ι → α) : IsClosed (DirectionSet σ) := by
  simp only [DirectionSet,Set.ofPred_forall,Set.ofPred_and]
  apply isClosed_iInter
  intro a
  apply IsClosed.inter <;> apply isClosed_eq _ continuous_const
  · exact continuous_finsetSum _ (fun i _ => (EuclideanSpace.proj i).continuous)
  · exact continuous_finsetSum _ (fun i _ => (EuclideanSpace.proj i).continuous.mul
      (EuclideanSpace.proj i).continuous)

lemma directionSet_compact (σ : ι → α) : IsCompact (DirectionSet σ) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ ι) (sqrt (Fintype.card α))).of_isClosed_subset
    (directionSet_closed σ)
  intro u hu
  simp only [Metric.mem_closedBall,dist_zero_right]
  have hs := directions_norm_sq (⟨u,hu⟩ : Directions σ)
  exact (le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)).mpr hs.le

instance (σ : ι → α) : CompactSpace (Directions σ) := isCompact_iff_compactSpace.mp (directionSet_compact σ)

omit [Fintype α] in
lemma two_sites_of_count {σ : ι → α} (hcount : ∀ a, 2≤count σ a) (a : α) :
    ∃ i j : ι, σ i=a ∧ σ j=a ∧ i≠j := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (show 1<(Finset.univ.filter (fun i => σ i=a)).card from hcount a)
  exact ⟨i,j,(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hj).2,hij⟩

omit [Fintype α] in
lemma directions_nonempty {σ : ι → α} (hcount : ∀ a, 2≤count σ a) : Nonempty (Directions σ) := by
  choose i j hi hj hij using two_sites_of_count hcount
  let u : ι → ℝ := fun k => (if k=i (σ k) then 1/sqrt 2 else 0)-
    (if k=j (σ k) then 1/sqrt 2 else 0)
  refine ⟨⟨WithLp.toLp 2 u,fun a => ?_⟩⟩
  have himem : i a∈Finset.univ.filter (fun k => σ k=a) := by simp only [Finset.mem_filter,Finset.mem_univ,true_and,hi]
  have hjmem : j a∈Finset.univ.filter (fun k => σ k=a) := by simp only [Finset.mem_filter,Finset.mem_univ,true_and,hj]
  have hue (k : ι) (hk : k∈Finset.univ.filter (fun k => σ k=a)) :
      u k = (if k=i a then 1/sqrt 2 else 0)-(if k=j a then 1/sqrt 2 else 0) := by
    dsimp only [u]
    rw [(Finset.mem_filter.mp hk).2]
  constructor
  · change (∑ k with σ k=a, u k)=0
    rw [Finset.sum_congr rfl hue,Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq',himem,hjmem,ite_true,sub_self]
  · change (∑ k with σ k=a, u k*u k)=1
    have hh (k : ι) (hk : k∈Finset.univ.filter (fun k => σ k=a)) :
        u k*u k=(if k=i a then (1:ℝ)/2 else 0)+(if k=j a then (1:ℝ)/2 else 0) := by
      rw [hue k hk]
      split_ifs with hki hkj
      · exact False.elim (hij a (hki.symm.trans hkj))
      · simp only [sub_zero,←pow_two,div_pow,one_pow,sq_sqrt (show (0:ℝ)≤2 by norm_num),add_zero]
      · simp only [zero_sub,←pow_two,neg_sq,div_pow,one_pow,sq_sqrt (show (0:ℝ)≤2 by norm_num),zero_add]
      · ring
    rw [Finset.sum_congr rfl hh,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',himem,hjmem,ite_true]
    norm_num

def vectorOf {σ : ι → α} (z : Parameters α) (u : Directions σ) (i : ι) : ℝ :=
  paramB z (σ i)/sqrt (count σ (σ i):ℝ)+paramR z (σ i)*u.val i

lemma vectorOf_unit {σ : ι → α} (hcount : ∀ a, 0<count σ a)
    (z : Parameters α) (u : Directions σ) : ∑ i, vectorOf z u i^2=1 := by
  rw [←sum_fibers σ]
  have he (a : α) : sum σ (fun i => vectorOf z u i^2) a =
      (paramB z a)^2+(paramR z a)^2 := by
    simp only [vectorOf]
    rw [bin_orthogonal_decomposition (zeroSum_scale_bin (paramR z) (directions_zeroSum u))
      (fun a => paramB z a/sqrt (count σ a:ℝ)) a,
      overlap_scale_bin,directions_overlap,mul_one,div_pow,sq_sqrt (Nat.cast_nonneg _)]
    congr 1
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (hcount a).ne')
  simp only [he,param_sum_sq]

lemma vectorOf_continuous {σ : ι → α} (z : Parameters α) :
    Continuous (fun u : Directions σ => vectorOf z u) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (((EuclideanSpace.proj i).continuous.comp continuous_subtype_val).const_mul _)

lemma scaled_directions_continuous {σ : ι → α} (z : Parameters α) :
    Continuous (fun u : Directions σ => fun i => paramR z (σ i)*u.val i) := by
  apply continuous_pi
  intro i
  exact ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val).const_mul _

lemma vectorOf_difference {σ : ι → α} (hcount : ∀ a, 0<count σ a)
    (z z' : Parameters α) (u : Directions σ) :
    ‖WithLp.toLp 2 (fun i => vectorOf z u i-vectorOf z' u i)‖=‖z.val-z'.val‖ := by
  have he (i : ι) : vectorOf z u i-vectorOf z' u i=
      (paramB z (σ i)-paramB z' (σ i))/sqrt (count σ (σ i):ℝ)+
      (paramR z (σ i)-paramR z' (σ i))*u.val i := by unfold vectorOf; ring
  have hs : ‖WithLp.toLp 2 (fun i => vectorOf z u i-vectorOf z' u i)‖^2=‖z.val-z'.val‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    simp only [he,←sum_fibers σ]
    have hh (a : α) : sum σ (fun i =>
        ((paramB z (σ i)-paramB z' (σ i))/sqrt (count σ (σ i):ℝ)+
        (paramR z (σ i)-paramR z' (σ i))*u.val i)^2) a=
        (paramB z a-paramB z' a)^2+(paramR z a-paramR z' a)^2 := by
      rw [bin_orthogonal_decomposition (zeroSum_scale_bin (fun a => paramR z a-paramR z' a) (directions_zeroSum u))
        (fun a => (paramB z a-paramB z' a)/sqrt (count σ a:ℝ)) a,
        overlap_scale_bin σ (fun a => paramR z a-paramR z' a),directions_overlap,mul_one,div_pow,sq_sqrt (Nat.cast_nonneg _)]
      congr 1
      exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (hcount a).ne')
    conv_lhs =>
      arg 2
      intro a
      rw [hh a]
    simp only [Finset.sum_add_distrib,Fintype.sum_sum_type,PiLp.sub_apply,paramB,paramR]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

omit [Fintype α] in
lemma fiber_sq_le (σ : ι → α) (u : ι → ℝ) (i : ι) :
    u i^2≤overlap σ u u (σ i) := by
  simpa only [overlap,sum,pow_two] using
    Finset.single_le_sum (s := Finset.univ.filter (fun k => σ k=σ i))
      (f := fun k => u k^2) (fun k _ => sq_nonneg (u k)) (by simp)

omit [Fintype α] in
lemma fiber_zero_of_sqrt_zero {σ : ι → α} {u : ι → ℝ} {i : ι}
    (h : sqrt (overlap σ u u (σ i))=0) : u i=0 := by
  have ht : overlap σ u u (σ i)=0 := by
    simpa only [h,zero_pow (by decide : (2:ℕ)≠0)] using (sq_sqrt (overlap_self_nonneg σ u (σ i))).symm
  have hs := fiber_sq_le σ u i
  rw [ht] at hs
  exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))

theorem vectorOf_surjective {σ : ι → α} (hcount : ∀ a, 2≤count σ a)
    (p : ι → ℝ) (hp : ∑ i, p i^2=1) :
    ∃ u : Directions σ, vectorOf (parametersOf σ p hp) u=p := by
  obtain ⟨u₀⟩ := directions_nonempty hcount
  let q := binCentered σ p
  let r := fun a => sqrt (overlap σ q q a)
  let u : ι → ℝ := fun i => if r (σ i)=0 then u₀.val i else (r (σ i))⁻¹*q i
  have hu : WithLp.toLp 2 u ∈ DirectionSet σ := by
    intro a
    by_cases hr : r a=0
    · have he : ∀ i∈Finset.univ.filter (fun i => σ i=a), u i=u₀.val i := by
        intro i hi
        dsimp only [u]
        rw [(Finset.mem_filter.mp hi).2,ite_eq_left hr]
      constructor
      · exact (Finset.sum_congr rfl he).trans (directions_zeroSum u₀ a)
      · exact (Finset.sum_congr rfl (fun i hi => congrArg (fun t : ℝ => t*t) (he i hi))).trans
          (directions_overlap u₀ a)
    · have he : ∀ i∈Finset.univ.filter (fun i => σ i=a), u i=(r a)⁻¹*q i := by
        intro i hi
        dsimp only [u]
        rw [(Finset.mem_filter.mp hi).2,ite_eq_right hr]
      constructor
      · change (∑ i with σ i=a, u i)=0
        rw [Finset.sum_congr rfl he,←Finset.mul_sum]
        change (r a)⁻¹*sum σ q a=0
        rw [binCentered_zeroSum σ p a,mul_zero]
      · change (∑ i with σ i=a, u i*u i)=1
        have hs (i : ι) (hi : i∈Finset.univ.filter (fun i => σ i=a)) :
            u i*u i=((r a)⁻¹)^2*(q i*q i) := by rw [he i hi]; ring
        rw [Finset.sum_congr rfl hs,←Finset.mul_sum]
        change ((r a)⁻¹)^2*overlap σ q q a=1
        rw [←sq_sqrt (overlap_self_nonneg σ q a)]
        change (r a)⁻¹^2*r a^2=1
        simpa only [inv_pow] using inv_mul_cancel₀ (pow_ne_zero 2 hr)
  refine ⟨⟨WithLp.toLp 2 u,hu⟩,?_⟩
  funext i
  simp only [vectorOf,parametersOf_B,parametersOf_R]
  have hpos : sqrt (count σ (σ i):ℝ)≠0 := (sqrt_pos.mpr (Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) (hcount (σ i))))).ne'
  rw [mul_div_cancel_left₀ _ hpos]
  change binMean σ p (σ i)+r (σ i)*u i=p i
  rw [binCentered_decomp σ p i]
  congr 1
  by_cases hr : r (σ i)=0
  · have hqi : q i=0 := fiber_zero_of_sqrt_zero hr
    rw [hr,zero_mul]
    exact hqi.symm
  · simp only [u,ite_eq_right hr,←mul_assoc,mul_inv_cancel₀ hr,one_mul,q]

end SKRatio.Bins

end

end OAI
