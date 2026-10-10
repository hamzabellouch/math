import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.RestrictionB
import OAI.Combinatorics.Chromatic.GradedAlgebra.Product

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I J : Type*} [Fintype I] [Fintype J]
variable (c η : I → ℝ) (hc : ∀ i,0 < c i)
lemma mass_sum (f : J → I → ℕ) : mass c (∑ j,f j)=∑ j,mass c (f j) := by
  simp only [mass,Finset.sum_apply,Nat.cast_sum,Finset.sum_mul]
  exact Finset.sum_comm
include hc
lemma mass_mono {d e : I → ℕ} (h : d ≤ e) : mass c d ≤ mass c e := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (h i)) (le_of_lt (hc i))
lemma mass_eq_of_le {d e : I → ℕ} (h : d ≤ e) (he : mass c d=mass c e) : d=e := by
  have hh : ∀ i, (d i : ℝ)*c i=(e i : ℝ)*c i := by
    intro i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _=>
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (h i)) (le_of_lt (hc i)))).mp he i (Finset.mem_univ i)
  funext i
  exact Nat.cast_injective (mul_right_cancel₀ (hc i).ne' (hh i))

lemma split_row_slope_le (β : ℝ) (q r : J → I → ℕ) (d : I → ℕ)
    (hd : d≠0) (hq : ∑ j,q j=d)
    (ht : ∀ j,slope c η (r j) ≤ β)
    (hp : ∀ j,mass η (q j) ≤ slope c η (r j)*mass c (q j)) :
    slope c η d ≤ β := by
  apply (div_le_iff₀ (mass_pos c hc d hd)).mpr
  calc
    mass η d = ∑ j,mass η (q j) := hq ▸ mass_sum η q
    _ ≤ ∑ j,β*mass c (q j) := Finset.sum_le_sum (fun j _=>
      (hp j).trans (mul_le_mul_of_nonneg_right (ht j) (mass_nonneg c (fun i=>(hc i).le) (q j))))
    _ = β*mass c d := by rw [←Finset.mul_sum,←mass_sum, hq]

lemma split_row_max_zero (β : ℝ) (q r : J → I → ℕ) (d : I → ℕ)
    (hq : ∑ j,q j=d) (hd : mass η d=β*mass c d)
    (ht : ∀ j,slope c η (r j) ≤ β)
    (hp : ∀ j,mass η (q j) ≤ slope c η (r j)*mass c (q j))
    {j : J} (hj : slope c η (r j) < β) : q j=0 := by
  have hn (k : J) : 0 ≤ β*mass c (q k)-mass η (q k) := by
    exact sub_nonneg.mpr ((hp k).trans (mul_le_mul_of_nonneg_right (ht k)
      (mass_nonneg c (fun i=>(hc i).le) (q k))))
  have hs : ∑ k,(β*mass c (q k)-mass η (q k))=0 := by
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←mass_sum,←mass_sum,hq,hd,sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _=>hn k)).mp hs j (Finset.mem_univ j)
  by_contra hjq
  have hpos := mass_pos c hc (q j) hjq
  have hlt := mul_lt_mul_of_pos_right hj hpos
  linarith [hp j]

lemma split_row_max_single [DecidableEq J] (j₀ : J) (q r : J → I → ℕ) (d : I → ℕ)
    (hq : ∑ j,q j=d) (hd : slope c η d=slope c η (r j₀))
    (ht : ∀ j,j≠j₀ → slope c η (r j) < slope c η (r j₀))
    (hp : ∀ j,mass η (q j) ≤ slope c η (r j)*mass c (q j)) :
    q j₀=d ∧ ∀ j,j≠j₀ → q j=0 := by
  have hmax (j : J) : slope c η (r j) ≤ slope c η (r j₀) := by
    by_cases hj : j=j₀
    · rw [hj]
    · exact (ht j hj).le
  have hzero (j : J) (hj : j≠j₀) : q j=0 :=
    split_row_max_zero c η hc _ q r d hq (by rw [←hd]; exact mass_eq c η hc d) hmax hp (ht j hj)
  refine ⟨?_,hzero⟩
  rw [←hq]
  symm
  exact Finset.sum_eq_single j₀ (fun j _ hj=>hzero j hj) (by simp)

lemma split_row_equal_key [DecidableEq J] (j₀ : J) (q r : J → I → ℕ) (d : I → ℕ)
    (hq : ∑ j,q j=d) (hd : slope c η d=slope c η (r j₀))
    (ht : ∀ j,j≠j₀ → slope c η (r j) < slope c η (r j₀))
    (hp : ∀ j,mass η (q j) ≤ slope c η (r j)*mass c (q j))
    (hle : ∀ j,q j ≤ r j) (hm : mass c d=mass c (r j₀)) :
    d=r j₀ ∧ q j₀=r j₀ ∧ ∀ j,j≠j₀ → q j=0 := by
  obtain ⟨hs,hz⟩:=split_row_max_single c η hc j₀ q r d hq hd ht hp
  have he : d=r j₀ := mass_eq_of_le c hc (hs ▸ hle j₀) hm
  exact ⟨he,hs.trans he,hz⟩
end ElementaryPositivity.SlopeArithmetic

end
section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ)
noncomputable def clippedSlope (θ : ℝ) (d : I → ℕ) : ℝ := max (slope c η d) θ
lemma clippedSlope_of_le {θ : ℝ} {d : I → ℕ} (h : slope c η d ≤ θ) :
    clippedSlope c η θ d=θ := max_eq_right h
lemma clippedSlope_of_ge {θ : ℝ} {d : I → ℕ} (h : θ ≤ slope c η d) :
    clippedSlope c η θ d=slope c η d := max_eq_left h
lemma clippedSlope_le (θ : ℝ) (d : I → ℕ) : slope c η d ≤ clippedSlope c η θ d := le_max_left _ _
lemma clipped_mass_bound (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :
    mass η d ≤ clippedSlope c η θ d*mass c d := by
  rw [mass_eq c η hc d]
  exact mul_le_mul_of_nonneg_right (clippedSlope_le c η θ d) (mass_nonneg c (fun i=>(hc i).le) d)

lemma clipped_high_mass (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ)
    (h : clippedSlope c η θ (d+e)*mass c d < mass η d) :
    d≠0 ∧ e≠0 ∧ clippedSlope c η θ (d+e) < clippedSlope c η θ d := by
  have hm : slope c η (d+e)*mass c d < mass η d :=
    (mul_le_mul_of_nonneg_right (clippedSlope_le c η θ (d+e))
      (mass_nonneg c (fun i=>(hc i).le) d)).trans_lt h
  obtain ⟨hd,he,_⟩:=high_mass_destabilizes c η hc d e hm
  refine ⟨hd,he,lt_of_lt_of_le ?_ (clippedSlope_le c η θ d)⟩
  exact (lt_div_iff₀ (mass_pos c hc d hd)).mpr h

lemma clipped_split_destabilizes (hc : ∀ i,0<c i) (κ θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (h₁ : clippedSlope c η κ (d₁+e₁) ≤ θ) (h₂ : clippedSlope c η κ (d₂+e₂) ≤ θ)
    (hd : d₁+d₂≠0) (hs : θ < slope c η (d₁+d₂)) :
    (d₁≠0 ∧ e₁≠0 ∧ clippedSlope c η κ (d₁+e₁) < clippedSlope c η κ d₁) ∨
    (d₂≠0 ∧ e₂≠0 ∧ clippedSlope c η κ (d₂+e₂) < clippedSlope c η κ d₂) := by
  by_cases hp : clippedSlope c η κ (d₁+e₁)*mass c d₁ < mass η d₁
  · exact Or.inl (clipped_high_mass c η hc κ d₁ e₁ hp)
  by_cases hq : clippedSlope c η κ (d₂+e₂)*mass c d₂ < mass η d₂
  · exact Or.inr (clipped_high_mass c η hc κ d₂ e₂ hq)
  have hpd := (mul_le_mul_of_nonneg_right h₁ (mass_nonneg c (fun i=>(hc i).le) d₁))
  have hqd := (mul_le_mul_of_nonneg_right h₂ (mass_nonneg c (fun i=>(hc i).le) d₂))
  have hh := (lt_div_iff₀ (mass_pos c hc (d₁+d₂) hd)).mp hs
  rw [mass_add,mass_add] at hh
  push Not at hp hq
  nlinarith
end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)
lemma clipped_destabilizingSpace_eq (κ : ℝ) (d : I → ℕ) (h : κ ≤ slope c η d) :
    destabilizingSpace a (clippedSlope c η κ) d=destabilizingSpace a (slope c η) d := by
  unfold destabilizingSpace
  congr 1
  ext f
  constructor <;> rintro ⟨u,v,he,x,y,hu,hv,hs,hf⟩
  · refine ⟨u,v,he,x,y,hu,hv,?_,hf⟩
    rw [clippedSlope_of_ge c η h,clippedSlope] at hs
    exact (lt_max_iff.mp hs).resolve_right (not_lt_of_ge h)
  · refine ⟨u,v,he,x,y,hu,hv,?_,hf⟩
    rw [clippedSlope_of_ge c η h]
    exact hs.trans_le (le_max_left _ _)

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
omit [∀ i, Fintype (A i)] in
lemma clipped_gridShape_zero (hc : ∀ i,0<c i) (κ θ : ℝ)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) (hd : d≠0)
    (hα : clippedSlope c η κ α ≤ θ) (hβ : clippedSlope c η κ β ≤ θ)
    (hμ : θ < slope c η d) :
    quotientTensor a (clippedSlope c η κ) α β (gridShapeTensor a f g p R T u v)=0 := by
  unfold gridShapeTensor
  apply quotientTensor_cast_zero
  by_cases hs : (fun i=>(u i).val)+(fun i=>(v i).val)=d
  · apply quotient_cellTransfer_zero
    apply clipped_split_destabilizes c η hc κ θ
    · rwa [(shape_add_complement u).trans (realization_card R)]
    · rwa [(shape_add_complement v).trans (realization_card T)]
    · rwa [hs]
    · rwa [hs]
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hs,map_zero,map_zero]
omit [∀ i, Fintype (A i)] in
lemma clipped_grid_zero (hc : ∀ i,0<c i) (κ θ : ℝ)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p)) (hd : d≠0)
    (hα : clippedSlope c η κ α ≤ θ) (hβ : clippedSlope c η κ β ≤ θ)
    (hμ : θ < slope c η d) :
    quotientTensor a (clippedSlope c η κ) α β (gridTensor a f g p R T)=0 := by
  simp only [gridTensor,map_sum]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  exact clipped_gridShape_zero a c η hc κ θ f g p R T u v hd hα hβ hμ
omit [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in

theorem clipped_restrict_high (hc : ∀ i,0<c i) (κ θ : ℝ)
    {d e α β : I → ℕ} (h : d+e=α+β) (f : S d) (g : S e) (u : Cut α β) (hd : d≠0)
    (hα : clippedSlope c η κ α ≤ θ) (hβ : clippedSlope c η κ β ≤ θ)
    (hμ : θ < slope c η d) :
    quotientTensor a (clippedSlope c η κ) α β
      (restrictTensor u (dimensionCast h (shufflePolynomial a f g)))=0 := by
  rw [dimensionCast_eq_castS]
  apply quotient_crossTensor_cancel
  let s : Pack (A:=fun i=>Fin ((α+β) i)) := fun _=>Finset.univ
  let R : Realization (α+β) s := defaultRealization (by intro i; simp [s])
  rw [cleared_restrictTensor a h f g R u,map_smul,
    clipped_grid_zero a c η hc κ θ f g _ _ _ hd hα hβ hμ,smul_zero]

lemma clipped_restrict_ideal (hc : ∀ i,0<c i) (κ θ : ℝ)
    (α β : I → ℕ) (hμ : slope c η (α+β) ≤ θ)
    (hα : clippedSlope c η κ α ≤ θ) (hβ : clippedSlope c η κ β ≤ θ)
    (u : Cut α β) (f : S (α+β))
    (hf : f∈destabilizingSpace a (clippedSlope c η θ) (α+β)) :
    quotientTensor a (clippedSlope c η κ) α β (restrictTensor u f)=0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨d,e,h,x,y,hd,he,hs,rfl⟩:=hf
    have hs' : θ < slope c η d := by
      rw [clippedSlope_of_le c η hμ,clippedSlope] at hs
      exact (lt_max_iff.mp hs).resolve_right (lt_irrefl θ)
    exact clipped_restrict_high a c η hc κ θ h x y u hd hα hβ hs'
  | zero => rw [map_zero,map_zero]
  | add f g _ _ hf hg => rw [map_add,map_add,hf,hg,add_zero]
  | smul q f _ hf => rw [map_smul,map_smul,hf,smul_zero]

end ElementaryPositivity.RawShuffle

end

end OAI
