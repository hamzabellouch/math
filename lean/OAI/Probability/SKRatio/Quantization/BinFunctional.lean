import Mathlib
import OAI.Probability.SKRatio.Quantization.BinProjected
import OAI.Probability.SKRatio.Quantization.BinDirections

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def binT (σ : ι → α) (a : α) : ℝ := sqrt (count σ a:ℝ)/sqrt (Fintype.card ι:ℝ)

omit [DecidableEq ι] in
lemma sum_count (σ : ι → α) : (∑ a, (count σ a:ℝ))=(Fintype.card ι:ℝ) := by
  have hh := sum_fibers σ (fun _ => (1:ℝ))
  simpa only [sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,count] using hh

omit [DecidableEq ι] [Fintype α] in
lemma binT_nonneg (σ : ι → α) (a : α) : 0≤binT σ a := by unfold binT; positivity

omit [DecidableEq ι] [Fintype α] in
lemma binT_sq (σ : ι → α) (a : α) : binT σ a^2=(count σ a:ℝ)/(Fintype.card ι:ℝ) := by
  simp only [binT,div_pow,sq_sqrt (Nat.cast_nonneg _)]

omit [DecidableEq ι] in
lemma binT_unit [Nonempty ι] (σ : ι → α) : (∑ a, binT σ a^2)=1 := by
  simp only [binT_sq,←Finset.sum_div,sum_count]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [DecidableEq ι] [Fintype α] in
lemma sqrt_count_mul_div {σ : ι → α} (hcount : ∀ a, 0<count σ a) (B : α → ℝ) (a : α) :
    (count σ a:ℝ)*(B a/sqrt (count σ a:ℝ))=sqrt (count σ a:ℝ)*B a := by
  have hc : sqrt (count σ a:ℝ)≠0 := (sqrt_pos.mpr (Nat.cast_pos.mpr (hcount a))).ne'
  field_simp
  rw [sq_sqrt (Nat.cast_nonneg _)]; ring

omit [DecidableEq ι] in
lemma vectorOf_sum {σ : ι → α} (hcount : ∀ a, 0<count σ a)
    (z : Parameters α) (u : Directions σ) (a : α) :
    sum σ (vectorOf z u) a=sqrt (count σ a:ℝ)*paramB z a := by
  unfold vectorOf
  rw [sum_add_bin,sum_const_bin σ (fun a => paramB z a/sqrt (count σ a:ℝ)),
    zeroSum_scale_bin (paramR z) (directions_zeroSum u) a,add_zero]
  exact sqrt_count_mul_div hcount (paramB z) a

omit [DecidableEq ι] in
lemma vectorOf_sq_sum {σ : ι → α} (hcount : ∀ a, 0<count σ a)
    (z : Parameters α) (u : Directions σ) (a : α) :
    sum σ (fun i => vectorOf z u i^2) a=(paramB z a)^2+(paramR z a)^2 := by
  simp only [vectorOf]
  rw [bin_orthogonal_decomposition (zeroSum_scale_bin (paramR z) (directions_zeroSum u))
      (fun a => paramB z a/sqrt (count σ a:ℝ)) a,
    overlap_scale_bin,directions_overlap,mul_one,div_pow,sq_sqrt (Nat.cast_nonneg _)]
  congr 1
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (hcount a).ne')

def moment (t B f : α → ℝ) : ℝ := ∑ a, t a*B a*f a

omit [DecidableEq ι] in
lemma vectorOf_moment {σ : ι → α} (hcount : ∀ a, 0<count σ a)
    (z : Parameters α) (u : Directions σ) (f : α → ℝ) :
    (∑ i, vectorOf z u i*f (σ i))/sqrt (Fintype.card ι:ℝ)=
      moment (binT σ) (paramB z) f := by
  rw [sum_weighted,Finset.sum_div]
  simp only [vectorOf_sum hcount, moment,binT]
  apply Finset.sum_congr rfl
  intro a _
  ring

def finiteRadicalSq (t v : α → ℝ) (z : Parameters α) (a : α) : ℝ :=
  (∑ d, (v a+v d)^2*((paramB z d)^2+(paramR z d)^2))-
    (moment t (paramB z) (fun d => v a+v d))^2

def finiteGaussian (β : ℝ) (t v : α → ℝ) (z : Parameters α) : ℝ :=
  β*∑ a, t a*paramR z a*sqrt (finiteRadicalSq t v z a)

omit [DecidableEq ι] in
lemma binVariance_normalized [Nonempty ι] {σ : ι → α} (hcount : ∀ a, 0<count σ a)
    (v B : α → ℝ) (a : α) :
    binVariance σ (crossCoeff σ v (fun d => B d/sqrt (count σ d:ℝ))) a=
      (∑ d, (v a+v d)^2*B d^2)-(moment (binT σ) B (fun d => v a+v d))^2 := by
  let f : ι → ℝ := fun i => (v a+v (σ i))*(B (σ i)/sqrt (count σ (σ i):ℝ))
  have he : binVariance σ (crossCoeff σ v (fun d => B d/sqrt (count σ d:ℝ))) a =
      ∑ i, centered f i^2 := rfl
  rw [he,centered_sq]
  have hsum : (∑ i, f i)=sqrt (Fintype.card ι:ℝ)*moment (binT σ) B (fun d => v a+v d) := by
    rw [←sum_fibers σ]
    have hf (d : α) : sum σ f d=sqrt (count σ d:ℝ)*B d*(v a+v d) := by
      change sum σ (fun i => (fun d => (v a+v d)*(B d/sqrt (count σ d:ℝ))) (σ i)) d=_
      rw [sum_const_bin σ (fun d => (v a+v d)*(B d/sqrt (count σ d:ℝ)))]
      rw [show (count σ d:ℝ)*((v a+v d)*(B d/sqrt (count σ d:ℝ)))=
        ((count σ d:ℝ)*(B d/sqrt (count σ d:ℝ)))*(v a+v d) by ring,
        sqrt_count_mul_div hcount]
    simp only [hf,moment,Finset.mul_sum,binT]
    apply Finset.sum_congr rfl
    intro d _
    have hn : sqrt (Fintype.card ι:ℝ)≠0 := (sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne'
    field_simp
  have hsq : (∑ i, f i^2)=∑ d, (v a+v d)^2*B d^2 := by
    rw [←sum_fibers σ]
    apply Finset.sum_congr rfl
    intro d _
    change sum σ (fun i => (fun d => ((v a+v d)*(B d/sqrt (count σ d:ℝ)))^2) (σ i)) d=_
    rw [sum_const_bin σ (fun d => ((v a+v d)*(B d/sqrt (count σ d:ℝ)))^2),mul_pow,div_pow,sq_sqrt (Nat.cast_nonneg _)]
    have hc : (count σ d:ℝ)≠0 := Nat.cast_ne_zero.mpr (hcount d).ne'
    field_simp
  rw [hsq,average,hsum]
  have hn : (Fintype.card ι:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [div_pow,mul_pow,sq_sqrt (Nat.cast_nonneg _)]
  field_simp

omit [DecidableEq ι] in
lemma radicalSq_normalized [Nonempty ι] {σ : ι → α} (hcount : ∀ a, 0<count σ a)
    (v : α → ℝ) (z : Parameters α) (a : α) :
    radicalSq σ (crossCoeff σ v (fun d => paramB z d/sqrt (count σ d:ℝ)))
      (fun a d => v a+v d) (fun d => (paramR z d)^2) a=
      finiteRadicalSq (binT σ) v z a := by
  rw [radicalSq,binVariance_normalized hcount]
  simp only [finiteRadicalSq,mul_add,Finset.sum_add_distrib]
  ring

theorem normalized_projected_tail {n : ℕ} (hn : 0<n) {σ : Fin n → α}
    (hcount : ∀ a, 2≤count σ a) (v : α → ℝ) (hv : ∀ a, |v a|≤1)
    {β : ℝ} (hβ : 0<β) (z : Parameters α) {a : ℝ} (ha : 0≤a) :
    (standardArrayLaw (Fin n × Fin n)).real {g |
      finiteGaussian β (binT σ) v z+a≤
        projectedSup β (fun i => v (σ i)) (vectorOf z : Directions σ → Fin n → ℝ) g}≤
      exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have : Nonempty (Directions σ) := directions_nonempty hcount
  have hc : ∀ a, 0<count σ a := fun a => lt_of_lt_of_le (by norm_num) (hcount a)
  have hh := projectedSup_tail hn σ v (fun a => paramB z a/sqrt (count σ a:ℝ)) hv hβ
    (scaled_directions_continuous z)
    (fun u => zeroSum_scale_bin (paramR z) (directions_zeroSum u))
    (show ∀ u : Directions σ, overlap σ (fun i => paramR z (σ i)*u.val i)
      (fun i => paramR z (σ i)*u.val i)=(fun a => (paramR z a)^2) from by
      intro u
      ext a
      rw [overlap_scale_bin,directions_overlap,mul_one])
    (fun u => vectorOf_unit hc z u) ha
  have he : (∑ d, β/sqrt n*sqrt (radicalSq σ
        (crossCoeff σ v (fun a => paramB z a/sqrt (count σ a:ℝ)))
        (fun a d => v a+v d) (fun a => (paramR z a)^2) d)*
      sqrt ((paramR z d)^2)*sqrt ((Finset.univ.filter (fun i => σ i=d)).card : ℝ))=
      finiteGaussian β (binT σ) v z := by
    simp_rw [radicalSq_normalized hc,sqrt_sq (paramR_nonneg z _)]
    unfold finiteGaussian binT
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [count,Fintype.card_fin]
    ring
  rw [he] at hh
  exact hh

def finiteA (β : ℝ) (t h : α → ℝ) (z : Parameters α) : ℝ :=
  moment t (paramB z) h*moment t (paramB z) (fun a => v (h a))+
  moment t (paramB z) (fun _ => 1)*moment t (paramB z) (fun a => h a*v (h a))-
  β^2*moment t (paramB z) (fun _ => 1)*moment t (paramB z) (fun a => v (h a))+
  2*β^2*moment t (paramB z) (fun _ => 1)*moment t (paramB z) (fun a => m (h a)*v (h a))+
  β^2*(∑ a, ∑ d, t d^2*(v (h d)^2/(w (h a)+w (h d)))*
      ((paramB z a)^2+(paramR z a)^2))+
  β^2*(∑ a, ∑ d, t a*paramB z a*kernel (h a) (h d)*(t d*paramB z d))

def finiteV (β : ℝ) (t h : α → ℝ) (z : Parameters α) : ℝ :=
  finiteA β t h z+finiteGaussian β t (fun a => v (h a)) z

omit [DecidableEq α]

lemma continuous_paramB (a : α) : Continuous (fun z : Parameters α => paramB z a) :=
  (EuclideanSpace.proj (Sum.inl a : α ⊕ α)).continuous.comp continuous_subtype_val
lemma continuous_paramR (a : α) : Continuous (fun z : Parameters α => paramR z a) :=
  (EuclideanSpace.proj (Sum.inr a : α ⊕ α)).continuous.comp continuous_subtype_val

lemma continuous_moment : Continuous (fun q : (α → ℝ) × (α → ℝ) × (α → ℝ) =>
    moment q.1 q.2.1 q.2.2) := by
  unfold moment
  fun_prop

lemma continuous_finiteRadicalSq (v : α → ℝ) (a : α) :
    Continuous (fun q : (α → ℝ) × Parameters α => finiteRadicalSq q.1 v q.2 a) := by
  unfold finiteRadicalSq moment
  have hb (d : α) := (continuous_paramB d).comp (continuous_snd (X := α → ℝ))
  have hr (d : α) := (continuous_paramR d).comp (continuous_snd (X := α → ℝ))
  fun_prop

lemma continuous_finiteGaussian (β : ℝ) (v : α → ℝ) :
    Continuous (fun q : (α → ℝ) × Parameters α => finiteGaussian β q.1 v q.2) := by
  unfold finiteGaussian
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro a _
  exact (((continuous_apply a).comp continuous_fst).mul
    ((continuous_paramR a).comp continuous_snd)).mul
    (continuous_sqrt.comp (continuous_finiteRadicalSq v a))

lemma continuous_finiteA (β : ℝ) (h : α → ℝ) :
    Continuous (fun q : (α → ℝ) × Parameters α => finiteA β q.1 h q.2) := by
  unfold finiteA moment
  have hb (a : α) := (continuous_paramB a).comp (continuous_snd (X := α → ℝ))
  have hr (a : α) := (continuous_paramR a).comp (continuous_snd (X := α → ℝ))
  fun_prop

lemma continuous_finiteV (β : ℝ) (h : α → ℝ) :
    Continuous (fun q : (α → ℝ) × Parameters α => finiteV β q.1 h q.2) :=
  (continuous_finiteA β h).add (continuous_finiteGaussian β (fun a => v (h a)))

end SKRatio.Bins

end

end OAI
