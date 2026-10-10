import Mathlib
import OAI.Analysis.BoundedHochschild.PolarApproximation

namespace OAI

/-! Signed block sums, good patterns and spans of word evaluations. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildBlockAssembly
noncomputable section
open Finset Filter Topology HochschildCollision HochschildBlockError HochschildBlockWords
variable {A : Type*} [CStarAlgebra A]
variable {α : Type*} [Fintype α] [DecidableEq α]

def allSum (u : FreeGroup α →* A) {L : ℕ} (σ : Fin L → Bool) : A :=
  ∑ f : Fin L → α, u (wordOf σ f)

lemma sum_badSum (u : FreeGroup α →* A) {L : ℕ} (σ : Fin L → Bool) :
    (∑ q ∈ range (L+1), badSum u σ q) =
      ∑ f : Fin L → α with ¬ ((FreeGroup.reduce (tupleWord σ f)).map Prod.fst).Nodup,
        u (wordOf σ f) := by
  classical
  let s : Finset (Fin L → α) := univ.filter fun f =>
    ¬ ((FreeGroup.reduce (tupleWord σ f)).map Prod.fst).Nodup
  have hlen (f : Fin L → α) (_hf : f ∈ s) : (wordOf σ f).toWord.length ∈ range (L+1) := by
    have h := @FreeGroup.norm_mk_le α (tupleWord σ f)
    rw [tupleWord_length] at h
    exact mem_range.mpr (by exact Nat.lt_succ_of_le h)
  rw [← sum_fiberwise_of_maps_to hlen (fun f => u (wordOf σ f))]
  apply sum_congr rfl
  intro q _
  unfold badSum
  symm
  apply sum_subtype
  intro f
  constructor
  · intro h
    exact ⟨(Finset.mem_filter.mp h).2, (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2⟩,h.1⟩

lemma map_allSum_eq_badSum (u : FreeGroup α →* A) (T : A →L[ℝ] A)
    {L : ℕ} (σ : Fin L → Bool)
    (hT : ∀ f : Fin L → α,
      ((FreeGroup.reduce (tupleWord σ f)).map Prod.fst).Nodup → T (u (wordOf σ f)) = 0) :
    T (allSum u σ) = T (∑ q ∈ range (L+1), badSum u σ q) := by
  classical
  rw [sum_badSum,allSum,map_sum,map_sum]
  rw [sum_filter]
  apply sum_congr rfl
  intro f _
  split_ifs with h
  · exact hT f h
  · rfl

variable [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder

lemma tendsto_map_allSum (τ : A →ₚ[ℂ] ℂ)
    (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (T : A →L[ℝ] A) {L : ℕ} (hL : 0 < L) (σ : Fin L → Bool)
    (hT : ∀ r (f : Fin L → Fin (r+1)),
      ((FreeGroup.reduce (tupleWord σ f)).map Prod.fst).Nodup → T (u r (wordOf σ f)) = 0) :
    Tendsto (fun r => T (normalizer (r+1) L • allSum (u r) σ)) atTop (nhds 0) := by
  have he (r : ℕ) : T (normalizer (r+1) L • allSum (u r) σ) =
      T (∑ q ∈ range (L+1),normalizer (r+1) L • badSum (u r) σ q) := by
    rw [map_smul,map_allSum_eq_badSum (u r) T σ (hT r),← map_smul,smul_sum]
  simp_rw [he]
  simpa only [map_zero,Function.comp_def] using T.continuous.tendsto 0 |>.comp
    (tendsto_total_badSum τ u h1 hu hfree htr hf hL σ)

end
end HochschildBlockAssembly

namespace HochschildWordEval
noncomputable section
open Finset HochschildCollision HochschildBlockError HochschildBlockAssembly HochschildFreeSums
variable {A : Type*} [CStarAlgebra A]

def letter (s : A) (b : Bool) : A := if b then s else star s

def eval (s : A) (σ : List Bool) : A := (σ.map (letter s)).prod

@[simp] lemma eval_nil (s : A) : eval s [] = 1 := rfl
@[simp] lemma eval_cons (s : A) (b : Bool) (σ : List Bool) :
    eval s (b::σ) = letter s b * eval s σ := rfl
@[simp] lemma eval_append (s : A) (σ ρ : List Bool) :
    eval s (σ++ρ) = eval s σ * eval s ρ := by simp [eval,List.prod_append]

lemma letter_smul (c : ℝ) (s : A) (b : Bool) : letter (c • s) b = c • letter s b := by
  cases b <;> simp [letter,star_smul]

lemma eval_smul (c : ℝ) (s : A) (σ : List Bool) :
    eval (c • s) σ = c^σ.length • eval s σ := by
  induction σ with
  | nil => simp
  | cons b σ ih => simp only [eval_cons,letter_smul,ih,List.length_cons,smul_mul_smul,pow_succ']

variable {α : Type*} [Fintype α]

lemma letter_sum (s : α → A) (b : Bool) : letter (∑ i, s i) b = ∑ i, letter (s i) b := by
  cases b <;> simp [letter,star_sum]

omit [Fintype α] in
lemma wordOf_cons (b : Bool) (σ : List Bool) (f : Fin (σ.length+1) → α) :
    wordOf (fun i => (b::σ)[i]) f = FreeGroup.mk [(f 0,b)] *
      wordOf (fun i => σ[i]) (fun i => f i.succ) := by
  simp only [wordOf,tupleWord,List.ofFn_succ,FreeGroup.mul_mk]
  rfl

omit [Fintype α] in
lemma map_singleton (u : FreeGroup α →* A) (hu : ∀ g, star (u g) = u g⁻¹)
    (i : α) (b : Bool) : u (FreeGroup.mk [(i,b)]) = letter (u (FreeGroup.of i)) b := by
  cases b
  · simpa only [letter,Bool.false_eq_true,↓reduceIte,FreeGroup.of,FreeGroup.inv_mk,FreeGroup.invRev,List.map_cons,List.map_nil,List.reverse_cons,List.reverse_nil,List.nil_append,Bool.not_true] using (hu (FreeGroup.of i)).symm
  · rfl

lemma allSum_cons (u : FreeGroup α →* A) (hu : ∀ g, star (u g) = u g⁻¹)
    (b : Bool) (σ : List Bool) :
    allSum u (fun i => (b::σ)[i]) =
      (∑ i, letter (u (FreeGroup.of i)) b) * allSum u (fun i => σ[i]) := by
  classical
  unfold allSum
  calc
    _ = ∑ p : α × (Fin σ.length → α),
        u (wordOf (fun i => (b::σ)[i]) (Fin.cons p.1 p.2)) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (σ.length+1) => α)) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type,sum_mul]
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro f _
      rw [wordOf_cons,map_mul,map_singleton u hu]
      rfl

lemma eval_sum_eq (u : FreeGroup α →* A) (hu : ∀ g, star (u g) = u g⁻¹)
    (σ : List Bool) : eval (∑ i, u (FreeGroup.of i)) σ = allSum u (fun i => σ[i]) := by
  classical
  induction σ with
  | nil => simp [allSum,wordOf,tupleWord,← FreeGroup.one_eq_mk]
  | cons b σ ih => rw [eval_cons,letter_sum,ih,allSum_cons u hu]

lemma eval_freeSum (u : FreeGroup α →* A) (hu : ∀ g, star (u g) = u g⁻¹)
    (σ : List Bool) :
    eval (freeSum u) σ = normalizer (Fintype.card α) σ.length • allSum u (fun i => σ[i]) := by
  rw [freeSum,eval_smul,eval_sum_eq u hu]
  rfl

end
end HochschildWordEval

namespace HochschildGoodPatterns
noncomputable section
open HochschildCatalanWords HochschildBlockWords HochschildWordEval

 
def Good (b : Bool) (σ : List Bool) : Prop :=
  ∀ (α : Type) [DecidableEq α] (w : List (α × Bool)),
    w.map Prod.snd = σ → Ends b (FreeGroup.reduce w)

def alt (b : Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => b :: alt (!b) n

@[simp] lemma length_alt (b : Bool) (n : ℕ) : (alt b n).length = n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp [alt,ih]

lemma signed_fst {α : Type*} (b : Bool) (l : List α) : (signed b l).map Prod.fst = l := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp [signed,ih]

lemma signed_snd {α : Type*} (b : Bool) (l : List α) :
    (signed b l).map Prod.snd = alt b l.length := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp [signed,alt,ih]

lemma good_alt (b : Bool) (d : ℕ) : Good b (alt b (2*d+1)) := by
  intro α _ w hw
  have hlen : w.length = 2*d+1 := by
    simpa only [List.length_map,length_alt] using congrArg List.length hw
  have he : signed b (w.map Prod.fst) = w := by
    apply (List.zip_of_prod (signed_fst b _) ?_).trans
    · exact (List.zip_of_prod rfl rfl).symm
    · rw [signed_snd,List.length_map,hlen,← hw]
  rw [← he]
  exact reduce_signed_odd_ends _ (by simp only [List.length_map,hlen]; omega) b

lemma good_append {b : Bool} {σ ρ : List Bool} (hσ : Good b σ) (hρ : Good b ρ) :
    Good b (σ++ρ) := by
  intro α _ w hw
  obtain ⟨l,k,rfl,hl,hk⟩ := List.map_eq_append_iff.mp hw
  exact (reduce_append_odd_blocks l k (hσ α l hl) (hρ α k hk)).2

lemma good_length_pos {b : Bool} {σ : List Bool} (hσ : Good b σ) : 0 < σ.length := by
  by_contra h
  have he : σ = [] := List.length_eq_zero_iff.mp (by omega)
  obtain ⟨⟨a,l,ha⟩,_⟩ := hσ Unit [] he.symm
  simp at ha

def invPattern (σ : List Bool) : List Bool := (σ.map Bool.not).reverse

@[simp] lemma invPattern_invPattern (σ : List Bool) : invPattern (invPattern σ) = σ := by
  simp [invPattern,List.map_reverse,List.map_map,Function.comp_def]

lemma invRev_snd {α : Type*} (w : List (α × Bool)) :
    (FreeGroup.invRev w).map Prod.snd = invPattern (w.map Prod.snd) := by
  simp [FreeGroup.invRev,invPattern,List.map_reverse,List.map_map,Function.comp_def]

lemma ends_invRev {α : Type*} {b : Bool} {w : List (α × Bool)} (hw : Ends b w) :
    Ends (!b) (FreeGroup.invRev w) := by
  rcases hw with ⟨⟨a,l,ha⟩,⟨k,c,hc⟩⟩
  constructor
  · refine ⟨c,FreeGroup.invRev k,?_⟩
    rw [hc,FreeGroup.invRev_append]
    simp [FreeGroup.invRev]
  · refine ⟨FreeGroup.invRev l,a,?_⟩
    rw [ha,FreeGroup.invRev_cons]
    rfl

lemma good_inv {b : Bool} {σ : List Bool} (hσ : Good b σ) : Good (!b) (invPattern σ) := by
  intro α _ w hw
  have hg := hσ α (FreeGroup.invRev w) (by rw [invRev_snd,hw,invPattern_invPattern])
  have hh := ends_invRev hg
  simpa only [FreeGroup.reduce_invRev,FreeGroup.invRev_invRev] using hh

variable {A : Type*} [CStarAlgebra A]

lemma letter_not (s : A) (b : Bool) : letter s (!b) = star (letter s b) := by
  cases b <;> simp [letter]

lemma eval_inv (s : A) (σ : List Bool) : eval s (invPattern σ) = star (eval s σ) := by
  induction σ with
  | nil => simp [invPattern]
  | cons b σ ih =>
    simp only [invPattern,List.map_cons,List.reverse_cons]
    rw [eval_append]
    change eval s (invPattern σ) * eval s [!b] = _
    rw [ih,eval_cons,eval_nil,mul_one,letter_not,eval_cons,star_mul]

lemma eval_alt (s : A) (b : Bool) (d : ℕ) :
    eval s (alt b (2*d+1)) = letter s b * (letter s (!b) * letter s b)^d := by
  induction d with
  | zero => simp [alt]
  | succ d ih =>
    have he : 2*(d+1)+1 = (2*d+1)+1+1 := by omega
    rw [he,alt,alt,Bool.not_not,eval_cons,eval_cons,ih,pow_succ']
    simp only [mul_assoc]

end
end HochschildGoodPatterns

namespace HochschildBlockSpan
noncomputable section
open Filter Topology HochschildWordEval HochschildGoodPatterns
open scoped Polynomial
variable {A : Type*} [CStarAlgebra A]

 
def span (s : ℕ → A) (b : Bool) : Submodule ℝ (ℕ → A) :=
  Submodule.span ℝ {f | ∃ σ, Good b σ ∧ f = fun r => eval (s r) σ}

lemma generator_mem (s : ℕ → A) {b : Bool} {σ : List Bool} (hσ : Good b σ) :
    (fun r => eval (s r) σ) ∈ span s b := Submodule.subset_span ⟨σ,hσ,rfl⟩

lemma mul_mem (s : ℕ → A) (b : Bool) {x y : ℕ → A} (hx : x ∈ span s b) (hy : y ∈ span s b) :
    x*y ∈ span s b := by
  refine Submodule.span_induction₂ (p := fun x y _ _ => x*y ∈ span s b) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro x y ⟨σ,hσ,rfl⟩ ⟨ρ,hρ,rfl⟩
    apply Submodule.subset_span
    refine ⟨σ++ρ,good_append hσ hρ,?_⟩
    funext r
    exact (eval_append (s r) σ ρ).symm
  · intro y _
    simpa only [zero_mul] using (span s b).zero_mem
  · intro x _
    simpa only [mul_zero] using (span s b).zero_mem
  · intro x y z _ _ _ ihx ihy
    rw [add_mul]
    exact (span s b).add_mem ihx ihy
  · intro x y z _ _ _ ihy ihz
    rw [mul_add]
    exact (span s b).add_mem ihy ihz
  · intro c x y _ _ ih
    rw [smul_mul_assoc]
    exact (span s b).smul_mem c ih
  · intro c x y _ _ ih
    rw [mul_smul_comm]
    exact (span s b).smul_mem c ih

lemma pow_mem (s : ℕ → A) (b : Bool) {x : ℕ → A} (hx : x ∈ span s b)
    (k : ℕ) (hk : 0 < k) : x^k ∈ span s b := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa only [pow_succ] using mul_mem s b (ih (Nat.succ_pos _)) hx

lemma star_mem (s : ℕ → A) (b : Bool) {x : ℕ → A} (hx : x ∈ span s b) :
    star x ∈ span s (!b) := by
  induction hx using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨σ,hσ,rfl⟩ := hf
    apply Submodule.subset_span
    refine ⟨invPattern σ,good_inv hσ,?_⟩
    funext r
    exact (eval_inv (s r) σ).symm
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [star_add]
    exact (span s (!b)).add_mem ihx ihy
  | smul c x hx ih =>
    rw [star_smul,star_trivial]
    exact (span s (!b)).smul_mem c ih

lemma polynomial_block_mem (s : ℕ → A) (p : ℝ[X]) :
    (fun r => s r * Polynomial.aeval (star (s r)*s r) p) ∈ span s true := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add,mul_add,Pi.add_def] using (span s true).add_mem hp hq
  | monomial n c =>
    have hg := (span s true).smul_mem c (generator_mem s (good_alt true n))
    simpa only [Pi.smul_def,eval_alt,letter,Bool.not_true,↓reduceIte,
      Bool.false_eq_true,Polynomial.aeval_monomial,← Algebra.smul_def,mul_smul_comm] using hg

lemma polarApprox_mem (s : ℕ → A) (n : ℕ) :
    (fun r => HochschildNewtonPolar.polarApprox (s r) n) ∈ span s true :=
  polynomial_block_mem s (HochschildNewtonPolar.polarPoly n)

variable [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder

lemma tendsto_eval_of_good (τ : A →ₚ[ℂ] ℂ)
    (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (T : A →L[ℝ] A) (b : Bool)
    (hT : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends b g.toWord → T (u r g) = 0)
    (σ : List Bool) (hσ : Good b σ) :
    Tendsto (fun r => T (eval (HochschildFreeSums.freeSum (u r)) σ)) atTop (nhds 0) := by
  simp_rw [eval_freeSum _ (hu _), Fintype.card_fin]
  apply HochschildBlockAssembly.tendsto_map_allSum τ u h1 hu hfree htr hf T (good_length_pos hσ)
  intro r f hnodup
  apply hT r _
  · simpa only [HochschildBlockError.wordOf,FreeGroup.toWord_mk] using hnodup
  · rw [HochschildBlockError.wordOf,FreeGroup.toWord_mk]
    apply hσ (Fin (r+1))
    simp only [HochschildCollision.tupleWord,List.map_ofFn,Function.comp_def]
    exact List.ofFn_get σ

lemma tendsto_of_mem (τ : A →ₚ[ℂ] ℂ)
    (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (T : A →L[ℝ] A) (b : Bool)
    (hT : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends b g.toWord → T (u r g) = 0)
    {x : ℕ → A} (hx : x ∈ span (fun r => HochschildFreeSums.freeSum (u r)) b) :
    Tendsto (fun r => T (x r)) atTop (nhds 0) := by
  induction hx using Submodule.span_induction with
  | mem f hf' =>
    obtain ⟨σ,hσ,rfl⟩ := hf'
    exact tendsto_eval_of_good τ u h1 hu hfree htr hf T b hT σ hσ
  | zero => simp only [Pi.zero_apply,map_zero]; exact tendsto_const_nhds
  | add x y hx hy ihx ihy => simpa only [Pi.add_apply,map_add,add_zero] using ihx.add ihy
  | smul c x hx ih => simpa only [Pi.smul_apply,map_smul,smul_zero] using ih.const_smul c

end
end HochschildBlockSpan
end

end OAI
