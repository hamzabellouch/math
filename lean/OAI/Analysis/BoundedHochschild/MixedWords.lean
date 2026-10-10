import Mathlib
import OAI.Analysis.BoundedHochschild.PartialUnitaries
import OAI.Analysis.BoundedHochschild.ProductTaylor

namespace OAI

/-! Mixed-word Taylor expansions, moment corners and patch coefficients. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]

 
def wordProduct {J : Type*} (ρ : J → M) : List (J × M) → M
  | [] => 1
  | (k,a)::l => ρ k*a*wordProduct ρ l
@[simp] lemma wordProduct_nil {J : Type*} (ρ : J → M) : wordProduct ρ []=1 := rfl
@[simp] lemma wordProduct_cons {J : Type*} (ρ : J → M) (k : J) (a : M) (l : List (J × M)) :
    wordProduct ρ ((k,a)::l)=ρ k*a*wordProduct ρ l := rfl
lemma wordProduct_append {J : Type*} (ρ : J → M) (l r : List (J × M)) :
    wordProduct ρ (l++r)=wordProduct ρ l*wordProduct ρ r := by
  induction l with
  | nil => simp
  | cons ka l ih => rcases ka with ⟨k,a⟩; simp only [List.cons_append,wordProduct_cons,ih,mul_assoc]
lemma norm_wordProduct_le_one {J : Type*} (ρ : J → M) (hρ : ∀ k, ‖ρ k‖ ≤ 1)
    (l : List (J × M)) (hl : ∀ ka ∈ l, ‖ka.2‖ ≤ 1) : ‖wordProduct ρ l‖ ≤ 1 := by
  induction l with
  | nil => exact IsStarProjection.norm_le (1 : M) (IsStarProjection.one M)
  | cons ka l ih =>
    rcases ka with ⟨k,a⟩
    have ha := hl (k,a) (List.mem_cons_self ..)
    have ht := ih (fun ka hk => hl ka (List.mem_cons_of_mem _ hk))
    exact (norm_mul_le_of_le (norm_mul_le_of_le (hρ k) ha) ht).trans_eq (by simp)

variable {I : Type*} (F : I → M)
def wordCoeff : Option I → M | none => 1 | some i => F i
@[simp] lemma wordCoeff_none : wordCoeff F none=1 := rfl
@[simp] lemma wordCoeff_some (i : I) : wordCoeff F (some i)=F i := rfl
lemma norm_wordCoeff (hF : ∀ i, ‖F i‖ ≤ 1) (a : Option I) : ‖wordCoeff F a‖ ≤ 1 := by
  cases a with
  | none => exact IsStarProjection.norm_le (1 : M) (IsStarProjection.one M)
  | some i => exact hF i
abbrev WordAtom (I : Type*) (K : ℕ) := (Bool × Fin K) × Option I
abbrev BoundedWord (I : Type*) (K N : ℕ) := Option I × {l : List (WordAtom I K) // l.length ≤ N}
instance [Finite I] (K N : ℕ) : Finite (BoundedWord I K N) := by
  let : Finite {l : List (WordAtom I K) // l.length ≤ N} := (List.finite_length_le (WordAtom I K) N).to_subtype
  infer_instance
instance [Finite I] (K N : ℕ) : Fintype (BoundedWord I K N) := Fintype.ofFinite _

def admissibleTail {K : ℕ} (l : List (WordAtom I K)) : Prop :=
  l ≠ [] ∧ ∀ ka ∈ l.dropLast, ka.2 ≠ none

def evaluatedTail {K : ℕ} (l : List (WordAtom I K)) : List ((Bool × ℕ) × M) :=
  l.map (fun ka => ((ka.1.1,ka.1.2.val),wordCoeff F ka.2))
def mixedEval {K : ℕ} (v : PartialUnitary M) (a : Option I) (l : List (WordAtom I K)) : M :=
  wordCoeff F a*wordProduct v.power (evaluatedTail F l)
lemma norm_mixedEval {K : ℕ} (hF : ∀ i, ‖F i‖ ≤ 1) (v : PartialUnitary M)
    (a : Option I) (l : List (WordAtom I K)) : ‖mixedEval F v a l‖ ≤ 1 := by
  apply (norm_mul_le_of_le (norm_wordCoeff F hF a) (norm_wordProduct_le_one _ v.norm_power_le_one _ ?_)).trans_eq (one_mul 1)
  rintro ka hk
  obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp hk
  exact norm_wordCoeff F hF kb.2

variable [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr in
lemma wordProduct_tendsto {J L : Type*} {f : Filter L} (ρ : L → J → M) (σ : J → M)
    (hρ : ∀ k, GNSTendsto τ (fun i => ρ i k) f (σ k))
    (hbn : ∀ i k, ‖ρ i k‖ ≤ 1) (l : List (J × M)) :
    GNSTendsto τ (fun i => wordProduct (ρ i) l) f (wordProduct σ l) := by
  induction l with
  | nil => exact GNSTendsto.const τ 1 f
  | cons ka l ih =>
    obtain ⟨k,a⟩ := ka
    apply GNSTendsto.mul τ htr ((hρ k).mul τ htr (GNSTendsto.const τ a f) 1 (fun i => hbn i k)) ih ‖a‖
    intro i
    simpa only [one_mul] using norm_mul_le_of_le (hbn i k) (le_refl ‖a‖)
include htr in
lemma mixedEval_tendsto {K : Type*} {r : ℕ} {f : Filter K}
    {v : K → PartialUnitary M} {w : PartialUnitary M}
    (h : GNSTendsto τ (fun i => (v i : M)) f (w : M))
    (a : Option I) (l : List (WordAtom I r)) :
    GNSTendsto τ (fun i => mixedEval F (v i) a l) f (mixedEval F w a l) := by
  apply GNSTendsto.mul τ htr (GNSTendsto.const τ (wordCoeff F a) f) _ ‖wordCoeff F a‖ (fun _ => le_rfl)
  exact wordProduct_tendsto τ htr (fun i => (v i).power) w.power
    (fun k => PartialUnitary.power_tendsto τ htr h k) (fun i k => (v i).norm_power_le_one k) _

lemma trace_tendsto_of_gns (h1 : τ 1=1) {J : Type*} {f : Filter J} {x : J → M} {y : M}
    (h : GNSTendsto τ x f y) : Tendsto (fun i => τ (x i)) f (𝓝 (τ y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ h
  intro i
  rw [← map_sub]
  exact HochschildUltrapower.norm_trace_le τ h1 _

 
def MomentBound {K N : ℕ} (b : ℝ → ℝ) (v : PartialUnitary M) : Prop :=
  ∀ w : BoundedWord I K N, admissibleTail w.2.val →
    ‖τ (mixedEval F v w.1 w.2.val)‖ ≤ b ((τ v.support).re)

include htr in
lemma momentBound_limit {K N : ℕ} {b : ℝ → ℝ} {v : ℕ → PartialUnitary M} {w : PartialUnitary M}
    (h1 : τ 1=1) (h : GNSTendsto τ (fun i => (v i : M)) atTop (w : M))
    (hb : ContinuousAt b ((τ w.support).re))
    (hv : ∀ i, MomentBound F τ (K := K) (N := N) b (v i)) :
    MomentBound F τ (K := K) (N := N) b w := by
  intro a ha
  have he := trace_tendsto_of_gns τ h1 (mixedEval_tendsto F τ htr h a.1 a.2.val)
  have hs := (h.star τ htr).mul τ htr h 1 (fun i => by simpa only [norm_star] using (v i).norm_le_one)
  have hst := (Complex.continuous_re.tendsto _).comp (trace_tendsto_of_gns τ h1 hs)
  exact le_of_tendsto_of_tendsto he.norm (hb.tendsto.comp hst) (Filter.Eventually.of_forall (fun i => hv i a ha))
end HochschildPatching

 

 

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
namespace ProductTaylor
variable {A R : Type*} [Ring R]
lemma mem_linearTerms_map (f : A → R × R) {l : List A} {x : R}
    (hx : x ∈ linearTerms (l.map f)) :
    ∃ pre a post, l=pre++a::post ∧ x=oldProduct (pre.map f)*(f a).2*oldProduct (post.map f) := by
  obtain ⟨p,b,t,he,hx⟩ := mem_linearTerms hx
  obtain ⟨pre,rest,hr,hp,ht⟩ := List.map_eq_append_iff.mp he
  obtain ⟨a,post,hs,ha,hpost⟩ := List.map_eq_cons_iff.mp ht
  exact ⟨pre,a,post,by rw [hr,hs],by rw [hp,ha,hpost]; exact hx⟩
lemma mem_quadraticTerms_map (f : A → R × R) {l : List A} {x : R}
    (hx : x ∈ quadraticTerms (l.map f)) :
    ∃ pre a middle b post, l=pre++a::(middle++b::post) ∧
      x=oldProduct (pre.map f)*(f a).2*oldProduct (middle.map f)*(f b).2*totalProduct (post.map f) := by
  obtain ⟨p,a,m,b,t,he,hx⟩ := mem_quadraticTerms hx
  obtain ⟨pre,rest,hr,hp,ht⟩ := List.map_eq_append_iff.mp he
  obtain ⟨aa,rest2,hs,ha,ht2⟩ := List.map_eq_cons_iff.mp ht
  obtain ⟨mid,rest3,hr2,hm,ht3⟩ := List.map_eq_append_iff.mp ht2
  obtain ⟨bb,post,hs2,hb,hpost⟩ := List.map_eq_cons_iff.mp ht3
  exact ⟨pre,aa,mid,bb,post,by rw [hr,hs,hr2,hs2],by rw [hp,ha,hm,hb,hpost]; exact hx⟩
end ProductTaylor

variable {M : Type*} [CStarAlgebra M]
variable {I : Type*} (F : I → M)
def atomPower {K : ℕ} (v : PartialUnitary M) (a : WordAtom I K) : M := v.power (a.1.1,a.1.2.val)
def splitFactor {K : ℕ} (v w : PartialUnitary M) (a : WordAtom I K) : M × M :=
  (atomPower v a*wordCoeff F a.2,atomPower w a*wordCoeff F a.2)
lemma oldProduct_split {K : ℕ} (v w : PartialUnitary M) (l : List (WordAtom I K)) :
    ProductTaylor.oldProduct (l.map (splitFactor F v w))=wordProduct v.power (evaluatedTail F l) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,ProductTaylor.old_cons,evaluatedTail,wordProduct_cons,splitFactor,atomPower] at *; rw [ih]
lemma totalProduct_split {K : ℕ} (v w : PartialUnitary M) (h : v.support*w.support=0) (l : List (WordAtom I K)) :
    ProductTaylor.totalProduct (l.map (splitFactor F v w))=wordProduct (v.orthogonalSum w h).power (evaluatedTail F l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,ProductTaylor.total_cons,evaluatedTail,wordProduct_cons,splitFactor,atomPower] at *
    rw [ih,PartialUnitary.power_orthogonalSum]
    simp only [add_mul]
lemma mixedEval_split {K : ℕ} (v w : PartialUnitary M) (h : v.support*w.support=0) (a : Option I) (l : List (WordAtom I K)) :
    mixedEval F (v.orthogonalSum w h) a l=mixedEval F v a l+
      wordCoeff F a*(ProductTaylor.linearTerms (l.map (splitFactor F v w))).sum+
      wordCoeff F a*(ProductTaylor.quadraticTerms (l.map (splitFactor F v w))).sum := by
  rw [mixedEval,← totalProduct_split F v w h,ProductTaylor.total_eq_old_add_linear_add_quadratic,
    mul_add,mul_add,oldProduct_split]
  rfl

lemma admissible_middle {K : ℕ} {l pre middle post : List (WordAtom I K)} {a b : WordAtom I K}
    (hl : admissibleTail l) (he : l=pre++a::(middle++b::post)) :
    a.2 ≠ none ∧ ∀ c ∈ middle, c.2 ≠ none := by
  have hsub : ∀ c ∈ pre++a::middle, c.2 ≠ none := by
    intro c hc
    apply hl.2 c
    have he' : l=(pre++a::middle)++b::post := by rw [he]; simp only [List.append_assoc,List.cons_append]
    rw [he',List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
    exact List.mem_append_left _ hc
  exact ⟨hsub a (List.mem_append_right _ (List.mem_cons_self ..)),fun c hc =>
    hsub c (List.mem_append_right _ (List.mem_cons_of_mem _ hc))⟩

variable [PartialOrder M] (τ : M →ₚ[ℂ] ℂ)
lemma trace_list_sum_bound (A : M) (l : List M) (c : ℝ)
    (h : ∀ x ∈ l, ‖τ (A*x)‖ ≤ c) : ‖τ (A*l.sum)‖ ≤ (l.length : ℝ)*c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.sum_cons,mul_add,map_add,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    exact (norm_add_le _ _).trans ((add_le_add (h x (List.mem_cons_self ..))
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))).trans_eq (add_comm _ _))

lemma mixedEval_patch_bound {K N : ℕ} (v w : PartialUnitary M) (h : v.support*w.support=0)
    (a : Option I) (l : List (WordAtom I K)) (hlen : l.length ≤ N) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hlin : ∀ x ∈ ProductTaylor.linearTerms (l.map (splitFactor F v w)), ‖τ (wordCoeff F a*x)‖ ≤ c)
    (hquad : ∀ x ∈ ProductTaylor.quadraticTerms (l.map (splitFactor F v w)), ‖τ (wordCoeff F a*x)‖ ≤ d) :
    ‖τ (mixedEval F (v.orthogonalSum w h) a l)‖ ≤ ‖τ (mixedEval F v a l)‖+(N : ℝ)*c+(N : ℝ)^2*d := by
  rw [mixedEval_split,map_add,map_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add le_rfl
    apply (trace_list_sum_bound τ _ _ _ hlin).trans
    rw [ProductTaylor.linearTerms_length,List.length_map]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hc
  · apply (trace_list_sum_bound τ _ _ _ hquad).trans
    apply mul_le_mul_of_nonneg_right _ hd
    have hn := ProductTaylor.quadraticTerms_length_le (l.map (splitFactor F v w))
    rw [List.length_map] at hn
    exact_mod_cast hn.trans (Nat.pow_le_pow_left hlen 2)
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M]
variable {I : Type*} (F : I → M) (τ : M →ₚ[ℂ] ℂ)

lemma centered_word_bound {K N : ℕ} {b : ℝ → ℝ} {v : PartialUnitary M}
    (hF : ∀ i, τ (F i)=0) (hb : 0 ≤ b ((τ v.support).re))
    (hv : MomentBound F τ (K := K) (N := N) b v)
    (i : I) (l : List (WordAtom I K)) (hl : ∀ a ∈ l, a.2 ≠ none) (hn : l.length ≤ N) :
    ‖τ (mixedEval F v (some i) l)‖ ≤ b ((τ v.support).re) := by
  by_cases he : l=[]
  · subst l
    simpa only [mixedEval,evaluatedTail,List.map_nil,wordProduct_nil,mul_one,wordCoeff_some,hF,norm_zero] using hb
  · exact hv (some i,⟨l,hn⟩) ⟨he,fun a ha => hl a (List.mem_of_mem_dropLast ha)⟩

omit [PartialOrder M] in
lemma support_wrapped_eval {K : ℕ} (hK : 0<K) (v : PartialUnitary M) (i : I) (l : List (WordAtom I K)) :
    mixedEval F v none (((true,⟨0,hK⟩),some i)::(l++[((false,⟨0,hK⟩),none)]))=
      star (v:M)*mixedEval F v (some i) l*(v:M) := by
  simp only [mixedEval,evaluatedTail,List.map_cons,List.map_append,List.map_nil,wordProduct_cons,
    wordProduct_append,wordProduct_nil,wordCoeff_none,wordCoeff_some,one_mul,mul_one,
    PartialUnitary.power,ite_true,Bool.false_eq_true,ite_false,zero_add,pow_one,mul_assoc]

lemma support_wrapped_admissible {K : ℕ} (hK : 0<K) (i : I) (l : List (WordAtom I K))
    (hl : ∀ a ∈ l, a.2 ≠ none) :
    admissibleTail (((true,⟨0,hK⟩),some i)::(l++[((false,⟨0,hK⟩),none)])) := by
  constructor
  · exact List.cons_ne_nil _ _
  · intro a ha
    have he : (((true,⟨0,hK⟩),some i)::(l++[((false,⟨0,hK⟩),none)]) : List (WordAtom I K))=
        (((true,⟨0,hK⟩),some i)::l)++[((false,⟨0,hK⟩),none)] := rfl
    rw [he,List.dropLast_concat] at ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact Option.some_ne_none _
    · exact hl a ha

lemma normalized_corner_trace_eq (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (v : PartialUnitary M) (z : M) :
    τ ((1-v.support)*z*(1-v.support))=τ z-τ (star (v:M)*z*(v:M)) := by
  have hp := v.support_proj.one_sub
  have hcompress : τ ((1-v.support)*z*(1-v.support))=τ ((1-v.support)*z) := by
    rw [htr,← mul_assoc,hp.isIdempotentElem.eq]
  rw [hcompress,sub_mul,one_mul,map_sub]
  congr 1
  rw [htr (star (v:M)*z) (v:M),← mul_assoc,v.mul_star_self_eq_support]

lemma residual_centered_word_bound {K N : ℕ} {b : ℝ → ℝ} {v : PartialUnitary M}
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hF : ∀ i, τ (F i)=0) (hb : 0 ≤ b ((τ v.support).re))
    (hv : MomentBound F τ (K := K) (N := N) b v) (hK : 0<K)
    (i : I) (l : List (WordAtom I K)) (hl : ∀ a ∈ l, a.2 ≠ none) (hn : l.length+2 ≤ N) :
    ‖τ ((1-v.support)*mixedEval F v (some i) l*(1-v.support))‖ ≤ 2*b ((τ v.support).re) := by
  have hz := centered_word_bound F τ hF hb hv i l hl (by omega)
  have hlen : (((true,⟨0,hK⟩),some i)::(l++[((false,⟨0,hK⟩),none)]) : List (WordAtom I K)).length ≤ N := by
    simpa only [List.length_cons,List.length_append,List.length_singleton,List.length_nil,Nat.add_assoc] using hn
  have hw := hv (none,⟨_,hlen⟩) (support_wrapped_admissible hK i l hl)
  rw [support_wrapped_eval] at hw
  rw [normalized_corner_trace_eq τ htr]
  exact (norm_sub_le _ _).trans ((add_le_add hz hw).trans_eq (by ring))

omit [PartialOrder M] in
lemma mixedEval_zero {K : ℕ} (a : Option I) (l : List (WordAtom I K)) (hl : l ≠ []) :
    mixedEval F (0 : PartialUnitary M) a l=0 := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons ka l =>
    rcases ka with ⟨⟨s,k⟩,j⟩
    simp only [mixedEval,evaluatedTail,List.map_cons,wordProduct_cons,PartialUnitary.power,PartialUnitary.coe_zero,star_zero,ite_self,zero_pow (Nat.succ_ne_zero _),zero_mul,mul_zero]
lemma momentBound_zero {K N : ℕ} {b : ℝ → ℝ} (hb : 0 ≤ b 0) :
    MomentBound F τ (K := K) (N := N) b 0 := by
  intro w hw
  rw [mixedEval_zero F _ _ hw.1,map_zero,norm_zero,PartialUnitary.support_zero,map_zero,Complex.zero_re]
  exact hb
end HochschildPatching

 

 

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {I : Type*} (F : I → M)
abbrev ShortTail (I : Type*) (K N : ℕ) := {l : List (WordAtom I K) // l.length ≤ N}
abbrev LinearLabel (I : Type*) (K N : ℕ) := Option I × ShortTail I K N × WordAtom I K × ShortTail I K N
instance [Finite I] (K N : ℕ) : Finite (LinearLabel I K N) := by
  let : Finite (ShortTail I K N) := (List.finite_length_le (WordAtom I K) N).to_subtype
  infer_instance
instance [Finite I] (K N : ℕ) : Fintype (LinearLabel I K N) := Fintype.ofFinite _
def linearCoeff {K N : ℕ} (v : PartialUnitary M) (a : LinearLabel I K N) : M :=
  wordCoeff F a.2.2.1.2 * wordProduct v.power (evaluatedTail F a.2.2.2.val) *
    mixedEval F v a.1 a.2.1.val
def linearPower {K N : ℕ} (a : LinearLabel I K N) : Bool × ℕ := (a.2.2.1.1.1,a.2.2.1.1.2.val)

variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
omit [StarOrderedRing M] in
include htr in
lemma linear_trace_bound {K N : ℕ} (v w : PartialUnitary M) (a : Option I)
    (l : List (WordAtom I K)) (hlen : l.length ≤ N) (c : ℝ)
    (hweak : ∀ j : LinearLabel I K N, ‖τ (linearCoeff F v j*w.power (linearPower j))‖ ≤ c)
    (x : M) (hx : x ∈ ProductTaylor.linearTerms (l.map (splitFactor F v w))) :
    ‖τ (wordCoeff F a*x)‖ ≤ c := by
  obtain ⟨pre,b,post,he,rfl⟩ := ProductTaylor.mem_linearTerms_map _ hx
  have hn := hlen
  rw [he,List.length_append,List.length_cons] at hn
  let j : LinearLabel I K N := (a,⟨pre,by omega⟩,b,⟨post,by omega⟩)
  have hh := hweak j
  have ht : τ (wordCoeff F a*(ProductTaylor.oldProduct (pre.map (splitFactor F v w))*
      (splitFactor F v w b).2*ProductTaylor.oldProduct (post.map (splitFactor F v w))))=
      τ (linearCoeff F v j*w.power (linearPower j)) := by
    simp only [oldProduct_split,splitFactor,linearCoeff,linearPower,mixedEval,atomPower,j]
    rw [show wordCoeff F a*(wordProduct v.power (evaluatedTail F pre)*
        (w.power (b.1.1,b.1.2.val)*wordCoeff F b.2)*wordProduct v.power (evaluatedTail F post))=
      (wordCoeff F a*wordProduct v.power (evaluatedTail F pre)*w.power (b.1.1,b.1.2.val))*
        (wordCoeff F b.2*wordProduct v.power (evaluatedTail F post)) by simp only [mul_assoc],htr]
    simp only [mul_assoc]
  rw [ht]
  exact hh

def residualScalar (v : PartialUnitary M) (z : M) : ℂ :=
  (((τ (1-v.support)).re : ℂ)⁻¹)*τ ((1-v.support)*z*(1-v.support))
omit [StarOrderedRing M] in
include htr in
lemma residualScalar_bound {K N : ℕ} {b : ℝ → ℝ} {v : PartialUnitary M}
    (hF : ∀ i, τ (F i)=0) (hb : 0 ≤ b ((τ v.support).re))
    (hv : MomentBound F τ (K := K) (N := N) b v) (hK : 0<K)
    (hp : 0<(τ (1-v.support)).re)
    (i : I) (l : List (WordAtom I K)) (hl : ∀ a ∈ l, a.2 ≠ none) (hn : l.length+2 ≤ N) :
    ‖residualScalar τ v (mixedEval F v (some i) l)‖ ≤ 2*b ((τ v.support).re)/(τ (1-v.support)).re := by
  rw [residualScalar,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (residual_centered_word_bound F τ htr hF hb hv hK i l hl hn) (inv_nonneg.mpr hp.le)

include htr in
lemma quadratic_trace_bound {K N : ℕ} {b : ℝ → ℝ} (v w : PartialUnitary M)
    (horth : v.support*w.support=0) (hK : 0<K)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, τ (F i)=0)
    (hb : 0 ≤ b ((τ v.support).re)) (hv : MomentBound F τ (K := K) (N := N) b v)
    (hp : 0<(τ (1-v.support)).re) (ε : ℝ)
    (hsmall : ∀ z : BoundedWord I K N,
      ‖τ.toPreGNS (w.support*mixedEval F v z.1 z.2.val*w.support-
        residualScalar τ v (mixedEval F v z.1 z.2.val) • w.support)‖ ≤ ε*‖τ.toPreGNS w.support‖)
    (a : Option I) (l : List (WordAtom I K)) (hlen : l.length ≤ N) (hl : admissibleTail l)
    (x : M) (hx : x ∈ ProductTaylor.quadraticTerms (l.map (splitFactor F v w))) :
    ‖τ (wordCoeff F a*x)‖ ≤ (ε+2*b ((τ v.support).re)/(τ (1-v.support)).re)*(τ w.support).re := by
  obtain ⟨pre,aa,middle,bb,post,he,rfl⟩ := ProductTaylor.mem_quadraticTerms_map _ hx
  obtain ⟨haa,hmid⟩ := admissible_middle hl he
  obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp haa
  have hn := hlen
  rw [he,List.length_append,List.length_cons,List.length_append,List.length_cons] at hn
  let z : BoundedWord I K N := (some i,⟨middle,by omega⟩)
  have hs := hsmall z
  have hc := residualScalar_bound F τ htr hFτ hb hv hK hp i middle hmid (by omega)
  have ht := small_compression_trace_bound τ htr w.support_proj
    (mixedEval F v a pre) (atomPower w aa) (mixedEval F v (some i) middle)
    (atomPower w bb) (mixedEval F (v.orthogonalSum w horth) bb.2 post)
    (residualScalar τ v (mixedEval F v (some i) middle)) ε
    (norm_mixedEval F hF v a pre) (w.norm_power_le_one _) (w.norm_power_le_one _)
    (norm_mixedEval F hF _ _ _) (w.power_support _) (w.support_power _) hs
  have heq : wordCoeff F a*(ProductTaylor.oldProduct (pre.map (splitFactor F v w))*(splitFactor F v w aa).2*
      ProductTaylor.oldProduct (middle.map (splitFactor F v w))*(splitFactor F v w bb).2*
      ProductTaylor.totalProduct (post.map (splitFactor F v w)))=
        mixedEval F v a pre*atomPower w aa*mixedEval F v (some i) middle*
          atomPower w bb*mixedEval F (v.orthogonalSum w horth) bb.2 post := by
    simp only [splitFactor,oldProduct_split,totalProduct_split F v w horth,mixedEval,hi,mul_assoc]
  rw [heq]
  exact ht.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl hc) (τ.map_nonneg w.support_proj.nonneg).1)
end HochschildPatching
end

end OAI
