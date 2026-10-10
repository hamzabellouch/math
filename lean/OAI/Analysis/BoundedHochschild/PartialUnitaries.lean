import Mathlib
import OAI.Analysis.BoundedHochschild.PartialIsometries

namespace OAI

/-! Partial unitaries, ordered limits and trace estimates. -/

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
namespace HochschildComparison
open BoundedHochschild
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

abbrev PartialUnitary (M : Type*) [CStarAlgebra M] :=
  {v : PartialIso M // v.final = v.initial}
namespace PartialUnitary
instance : Coe (PartialUnitary M) M := ⟨fun v => v.val.val⟩
instance : PartialOrder (PartialUnitary M) := inferInstanceAs (PartialOrder {v : PartialIso M // v.final=v.initial})
section
omit [PartialOrder M] [StarOrderedRing M]

@[ext] lemma ext {v w : PartialUnitary M} (h : (v : M)=w) : v=w :=
  Subtype.ext (PartialIso.ext h)
abbrev support (v : PartialUnitary M) : M := v.val.initial
lemma support_proj (v : PartialUnitary M) : IsStarProjection v.support := v.val.initial_proj
lemma norm_le_one (v : PartialUnitary M) : ‖(v : M)‖≤1 := v.val.norm_le_one
lemma star_mul_self_eq_support (v : PartialUnitary M) : star (v : M)*v=v.support := rfl
lemma mul_star_self_eq_support (v : PartialUnitary M) : (v : M)*star (v : M)=v.support := v.property
lemma mul_support (v : PartialUnitary M) : (v : M)*v.support=v := v.val.mul_initial
lemma support_mul (v : PartialUnitary M) : v.support*(v : M)=v := by
  change v.val.initial*(v : M)=v
  rw [← v.property]; exact v.val.final_mul
lemma star_support (v : PartialUnitary M) : star (v : M)*v.support=star (v : M) := by
  simpa only [star_mul,star_star,v.support_proj.isSelfAdjoint.star_eq] using congrArg star v.support_mul
lemma support_star (v : PartialUnitary M) : v.support*star (v : M)=star (v : M) := by
  simpa only [star_mul,star_star,v.support_proj.isSelfAdjoint.star_eq] using congrArg star v.mul_support
instance : Zero (PartialUnitary M) := ⟨⟨0,by simp [PartialIso.final,PartialIso.initial]⟩⟩
@[simp] lemma coe_zero : ((0 : PartialUnitary M) : M)=0 := rfl
@[simp] lemma support_zero : (0 : PartialUnitary M).support=0 := by simp [support,PartialIso.initial]
end

lemma zero_le (v : PartialUnitary M) : 0≤v := by
  constructor
  · change star (0 : M)*0≤v.support
    simpa only [star_zero,zero_mul] using v.support_proj.nonneg
  · simp [PartialIso.initial]
section
omit [PartialOrder M] [StarOrderedRing M]

lemma orthogonal_symm {v w : PartialUnitary M} (h : v.support*w.support=0) : w.support*v.support=0 :=
  PartialIso.orthogonal_initial_symm h
lemma mul_eq_zero {v w : PartialUnitary M} (h : v.support*w.support=0) : (v : M)*w=0 := by
  calc
    _ = ((v : M)*v.support)*(w.support*(w : M)) := by rw [mul_support,support_mul]
    _ = (v : M)*(v.support*w.support)*w := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

def orthogonalSum (v w : PartialUnitary M) (h : v.support*w.support=0) : PartialUnitary M :=
  ⟨PartialIso.orthogonalSum v.val w.val h (by simpa only [v.property,w.property] using h), by
    rw [PartialIso.orthogonalSum_final,PartialIso.orthogonalSum_initial,v.property,w.property]⟩
@[simp] lemma coe_orthogonalSum (v w : PartialUnitary M) (h : v.support*w.support=0) :
    ((v.orthogonalSum w h : PartialUnitary M) : M)=(v : M)+w := rfl
lemma support_orthogonalSum (v w : PartialUnitary M) (h : v.support*w.support=0) :
    (v.orthogonalSum w h).support=v.support+w.support :=
  PartialIso.orthogonalSum_initial v.val w.val h (by simpa only [v.property,w.property] using h)
end

lemma le_orthogonalSum (v w : PartialUnitary M) (h : v.support*w.support=0) : v≤v.orthogonalSum w h :=
  PartialIso.le_orthogonalSum v.val w.val h (by simpa only [v.property,w.property] using h)

 

section
omit [PartialOrder M] [StarOrderedRing M]

def power (v : PartialUnitary M) (k : Bool × ℕ) : M :=
  (if k.1 then star (v : M) else (v : M))^(k.2+1)
lemma norm_power_le_one (v : PartialUnitary M) (k : Bool × ℕ) : ‖v.power k‖≤1 := by
  apply (norm_pow_le' _ (Nat.succ_pos _)).trans
  apply pow_le_one₀ (norm_nonneg _)
  split <;> simpa only [norm_star] using v.norm_le_one
lemma support_power (v : PartialUnitary M) (k : Bool × ℕ) : v.support*v.power k=v.power k := by
  have h : v.support*(if k.1 then star (v : M) else (v : M)) =
      (if k.1 then star (v : M) else (v : M)) := by split <;> first | exact v.support_star | exact v.support_mul
  dsimp only [power]
  rw [pow_succ',← mul_assoc,h]
lemma power_support (v : PartialUnitary M) (k : Bool × ℕ) : v.power k*v.support=v.power k := by
  have h : (if k.1 then star (v : M) else (v : M))*v.support =
      (if k.1 then star (v : M) else (v : M)) := by split <;> first | exact v.star_support | exact v.mul_support
  dsimp only [power]
  rw [pow_succ,mul_assoc,h]

lemma add_pow_succ_of_orthogonal {a b : M} (hab : a*b=0) (hba : b*a=0) (n : ℕ) :
    (a+b)^(n+1)=a^(n+1)+b^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih,add_mul,mul_add,mul_add,← pow_succ,← pow_succ]
    have h₁ : a^(n+1)*b=0 := by rw [pow_succ,mul_assoc,hab,mul_zero]
    have h₂ : b^(n+1)*a=0 := by rw [pow_succ,mul_assoc,hba,mul_zero]
    rw [h₁,h₂,add_zero,zero_add]
lemma power_orthogonalSum (v w : PartialUnitary M) (h : v.support*w.support=0) (k : Bool × ℕ) :
    (v.orthogonalSum w h).power k=v.power k+w.power k := by
  have hab := mul_eq_zero h
  have hba := mul_eq_zero (orthogonal_symm h)
  dsimp only [power]
  rw [coe_orthogonalSum]
  split
  · rw [star_add]
    exact add_pow_succ_of_orthogonal (by simpa only [star_mul,star_zero] using congrArg star hba)
      (by simpa only [star_mul,star_zero] using congrArg star hab) _
  · exact add_pow_succ_of_orthogonal hab hba _
end

variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr in
lemma power_tendsto {I : Type*} {l : Filter I} {v : I → PartialUnitary M} {w : PartialUnitary M}
    (h : GNSTendsto τ (fun i => (v i : M)) l (w : M)) (k : Bool × ℕ) :
    GNSTendsto τ (fun i => (v i).power k) l (w.power k) := by
  have hbase : GNSTendsto τ (fun i => if k.1 then star (v i : M) else (v i : M)) l
      (if k.1 then star (w : M) else (w : M)) := by split <;> first | exact h.star τ htr | exact h
  have hn : ∀ i, ‖if k.1 then star (v i : M) else (v i : M)‖≤1 := by
    intro i; split <;> simpa only [norm_star] using (v i).norm_le_one
  have hp (n : ℕ) : GNSTendsto τ (fun i => (if k.1 then star (v i : M) else (v i : M))^n) l
      ((if k.1 then star (w : M) else (w : M))^n) := by
    induction n with
    | zero => simpa only [pow_zero] using GNSTendsto.const τ (1 : M) l
    | succ n ih =>
      simpa only [pow_succ'] using hbase.mul τ htr ih 1 hn
  exact hp _
end PartialUnitary
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
namespace PartialUnitary
include e hL hτ htr hfaith in
lemma exists_monotone_limit (v : ℕ → PartialUnitary M) (hv : Monotone v) :
    ∃ w : PartialUnitary M, GNSTendsto τ (fun n => (v n : M)) atTop (w : M) ∧
      (∀ n, v n ≤ w) ∧ ∀ z : PartialUnitary M, (∀ n, v n ≤ z) → w ≤ z := by
  obtain ⟨w,ht,hvw,hwleast⟩ := PartialIso.exists_monotone_limit e τ hL hτ htr hfaith
    (fun n => (v n).val) hv
  have hf := ht.mul τ htr (ht.star τ htr) 1 (fun n => (v n).norm_le_one)
  have hi := (ht.star τ htr).mul τ htr ht 1 (fun n => by simpa only [norm_star] using (v n).norm_le_one)
  have he : w.final=w.initial := by
    apply GNSTendsto.unique τ hfaith hf
    change GNSTendsto τ (fun n => (v n).val.final) atTop w.initial
    simpa only [(v _).property,PartialIso.initial] using hi
  exact ⟨⟨w,he⟩,ht,hvw,fun z hz => hwleast z.val hz⟩

 

include e hL hτ htr hfaith in
lemma chain_limit (c : Set (PartialUnitary M)) (hc : IsChain (·  ≤  ·) c) (hne : c.Nonempty) :
    ∃ a : ℕ → PartialUnitary M, (∀ n, a n ∈ c) ∧ Monotone a ∧
      ∃ s : PartialUnitary M, GNSTendsto τ (fun n => (a n : M)) atTop (s : M) ∧
        (∀ v  ∈  c, v ≤ s) ∧ ∀ z : PartialUnitary M, (∀ v  ∈  c, v ≤ z) → s ≤ z := by
  classical
  let T : Set ℝ := (fun v : PartialUnitary M => (τ v.support).re) '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := ⟨(τ 1).re,by
    rintro _ ⟨v,hv,rfl⟩
    exact Complex.re_le_re (τ.monotone v.support_proj.le_one)⟩
  obtain ⟨b,hbm,_hbub,hbt,hb⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hab using hb
  change ∀ n, (τ (a n).support).re=b n at hab
  have ham : Monotone a := by
    intro m n hmn
    apply PartialIso.le_of_comparable_trace_le τ hfaith (hc.total (ha m) (ha n))
    rw [hab,hab]
    exact hbm hmn
  obtain ⟨s,ht,has,hsleast⟩ := exists_monotone_limit e τ hL hτ htr hfaith a ham
  have hi := (ht.star τ htr).mul τ htr ht 1
    (fun n => by simpa only [norm_star] using (a n).norm_le_one)
  change GNSTendsto τ (fun n => (a n).support) atTop s.support at hi
  have htrace : (τ s.support).re=sSup T := by
    have hz := trace_predual_tendsto e τ hτ
      (predual_tendsto_of_preGNS e τ hL hτ hfaith 1
        (fun n => (a n).support_proj.norm_le _) hi)
    apply tendsto_nhds_unique (Complex.continuous_re.tendsto _ |>.comp hz)
    simpa only [Function.comp_def,hab] using hbt
  refine ⟨a,ha,ham,s,ht,?_,fun z hz => hsleast z (fun n => hz _ (ha n))⟩
  intro z hz
  by_cases hex : ∃ n, z ≤ a n
  · obtain ⟨n,hn⟩ := hex
    exact hn.trans (has n)
  · have haz : ∀ n, a n ≤ z := fun n =>
      (hc.total (ha n) hz).resolve_right (fun h => hex ⟨n,h⟩)
    apply PartialIso.le_of_comparable_trace_le τ hfaith (Or.inr (hsleast z haz))
    rw [htrace]
    exact le_csSup hTbd ⟨z,hz,rfl⟩

include e hL hτ htr hfaith in
lemma maximal_of_sequentially_closed (P : PartialUnitary M → Prop) (h0 : P 0)
    (hclosed : ∀ (a : ℕ → PartialUnitary M) (s : PartialUnitary M),
      Monotone a → (∀ n, P (a n)) →
      GNSTendsto τ (fun n => (a n : M)) atTop (s : M) → P s) :
    ∃ v : PartialUnitary M, Maximal P v := by
  apply zorn_le₀
  intro c hc hchain
  by_cases hne : c.Nonempty
  · obtain ⟨a,ha,ham,s,ht,hs,_⟩ := chain_limit e τ hL hτ htr hfaith c hchain hne
    exact ⟨s,hclosed a s ham (fun n => hc (ha n)) ht,hs⟩
  · exact ⟨0,h0,fun v hv => (hne ⟨v,hv⟩).elim⟩
end PartialUnitary
end HochschildComparison

 

 

 

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include htr in
lemma norm_trace_mul_le_gns (a b : M) :
    ‖τ (a*b)‖ ≤ ‖τ.toPreGNS a‖*‖τ.toPreGNS b‖ := by
  have hi : inner ℂ (τ.toPreGNS (star a)) (τ.toPreGNS b)=τ (a*b) := by
    simp only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,star_star]
  rw [← hi]
  simpa only [preGNS_norm_star τ htr] using norm_inner_le_norm (𝕜 := ℂ) (τ.toPreGNS (star a)) (τ.toPreGNS b)

lemma projection_gns_sq {q : M} (hq : IsStarProjection q) : ‖τ.toPreGNS q‖^2=(τ q).re := by
  have ht := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS q))
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re,PositiveLinearMap.ofPreGNS_toPreGNS,
    hq.isSelfAdjoint.star_eq,hq.isIdempotentElem.eq] using ht

include htr in
lemma small_compression_trace_bound {q : M} (hq : IsStarProjection q)
    (A x z y B : M) (c : ℂ) (ε : ℝ)
    (hA : ‖A‖ ≤ 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hxq : x*q=x) (hqy : q*y=y)
    (hsmall : ‖τ.toPreGNS (q*z*q-c • q)‖ ≤ ε*‖τ.toPreGNS q‖) :
    ‖τ (A*x*z*y*B)‖ ≤ (ε+‖c‖)*(τ q).re := by
  let D : M := q*z*q-c • q
  let G : M := y*B*A*x
  have hG : ‖G‖ ≤ 1 := by
    dsimp [G]
    simpa only [one_mul] using norm_mul_le_of_le (norm_mul_le_of_le (norm_mul_le_of_le hy hB) hA) hx
  have hGq : G*q=G := by dsimp [G]; simp only [mul_assoc,hxq]
  have hqG : q*G=G := by dsimp [G]; rw [← mul_assoc,← mul_assoc,← mul_assoc,hqy]
  have hGgns : ‖τ.toPreGNS G‖ ≤ ‖τ.toPreGNS q‖ := by
    calc
      _ = ‖τ.toPreGNS (G*q)‖ := congrArg (fun t => ‖τ.toPreGNS t‖) hGq.symm
      _ ≤ ‖G‖*‖τ.toPreGNS q‖ := preGNS_norm_mul_le τ G q
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hG (norm_nonneg _)
  have hrotate : τ (A*x*z*y*B)=τ (z*G) := by
    calc
      _ = τ ((A*x)*(z*y*B)) := by congr 1; simp only [mul_assoc]
      _ = τ ((z*y*B)*(A*x)) := htr _ _
      _ = _ := by congr 1; simp only [G,mul_assoc]
  have hinsert : τ (q*z*q*G)=τ (z*G) := by
    calc
      _ = τ (q*(z*G)) := by congr 1; simp only [mul_assoc,hqG]
      _ = τ ((z*G)*q) := htr _ _
      _ = _ := by rw [mul_assoc,hGq]
  have htrace : τ (A*x*z*y*B)=τ (D*G)+c*τ (q*G) := by
    calc
      _ = τ (q*z*q*G) := hrotate.trans hinsert.symm
      _ = τ (D*G+c • (q*G)) := by
        congr 1
        simp only [D,sub_mul,smul_mul_assoc,sub_add_cancel]
      _ = _ := by rw [map_add,map_smul,smul_eq_mul]
  have hscalar : ‖τ (q*G)‖ ≤ (τ q).re := by
    exact (HochschildTraceNorm.positive_weight_trace_bound τ htr q G hq.nonneg).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hG (τ.map_nonneg hq.nonneg).1)
  have herror : ‖τ (D*G)‖ ≤ ε*(τ q).re := by
    apply (norm_trace_mul_le_gns τ htr D G).trans
    calc
      _ ≤ (ε*‖τ.toPreGNS q‖)*‖τ.toPreGNS q‖ := mul_le_mul hsmall hGgns (norm_nonneg _) (hsmall.trans' (norm_nonneg _))
      _ = _ := by rw [← projection_gns_sq τ hq]; ring
  rw [htrace]
  apply (norm_add_le _ _).trans
  rw [norm_mul,add_mul]
  exact add_le_add herror (mul_le_mul_of_nonneg_left hscalar (norm_nonneg c))
end HochschildPatching
end

end OAI
