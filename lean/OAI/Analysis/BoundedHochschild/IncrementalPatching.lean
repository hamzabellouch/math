import Mathlib
import OAI.Analysis.BoundedHochschild.MixedWords
import OAI.Analysis.BoundedHochschild.RelativeQuantization

namespace OAI

/-! Corner partial unitaries, incremental moment estimates and unitary completion. -/

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
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildSakai HochschildCorners HochschildComparison
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (q : M) (hq : IsStarProjection q)

def ofCornerUnitary (u : unitary (Corner q hq)) : PartialUnitary M :=
  ⟨⟨((u : Corner q hq):M),by
    have hh := congrArg (fun a : Corner q hq => (a : M)) (Unitary.coe_mul_star_self u)
    change ((u : Corner q hq):M)*star ((u : Corner q hq):M)=q at hh
    rw [hh]
    exact (u : Corner q hq).property.1⟩,by
      have hl := congrArg (fun a : Corner q hq => (a : M)) (Unitary.coe_mul_star_self u)
      have hr := congrArg (fun a : Corner q hq => (a : M)) (Unitary.coe_star_mul_self u)
      exact hl.trans hr.symm⟩
@[simp] lemma ofCornerUnitary_coe (u : unitary (Corner q hq)) :
    ((ofCornerUnitary q hq u : PartialUnitary M):M)=((u : Corner q hq):M) := rfl
@[simp] lemma ofCornerUnitary_support (u : unitary (Corner q hq)) :
    (ofCornerUnitary q hq u).support=q := by
  exact congrArg (fun a : Corner q hq => (a : M)) (Unitary.coe_star_mul_self u)

lemma corner_coe_pow_succ (a : Corner q hq) (n : ℕ) : ((a^(n+1) : Corner q hq):M)=(a:M)^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (a := a),corner_coe_mul,ih]
    exact (pow_succ (a : M) (n+1)).symm

def signedExponent (k : Bool × ℕ) : ℤ := if k.1 then -((k.2 : ℤ)+1) else (k.2 : ℤ)+1
lemma signedExponent_ne_zero (k : Bool × ℕ) : signedExponent k ≠ 0 := by
  dsimp [signedExponent]; split <;> omega
lemma ofCornerUnitary_power (u : unitary (Corner q hq)) (k : Bool × ℕ) :
    (ofCornerUnitary q hq u).power k=(((u^signedExponent k : unitary (Corner q hq)) : Corner q hq):M) := by
  dsimp only [PartialUnitary.power,signedExponent]
  split
  · rw [zpow_neg,show (k.2 : ℤ)+1=((k.2+1 : ℕ):ℤ) by simp,zpow_natCast,← Unitary.star_eq_inv,
      Unitary.coe_star,SubmonoidClass.coe_pow,corner_coe_star,corner_coe_pow_succ,star_pow]
    rfl
  · rw [show (k.2 : ℤ)+1=((k.2+1 : ℕ):ℤ) by simp,zpow_natCast,SubmonoidClass.coe_pow,corner_coe_pow_succ]
    rfl

variable [PartialOrder M] [StarOrderedRing M]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]
include e hq in
theorem exists_partial_unitary_weak_powers
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M) (hq0 : q ≠ 0)
    (a : I → M) (k : I → Bool × ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ w : PartialUnitary M, w.support=q ∧ ∀ i, ‖τ (a i*w.power (k i))‖<ε*(τ q).re := by
  let eC := cornerPredualEquiv q hq e
  let ρ := cornerTrace q hq τ
  let b : I → Corner q hq := fun i => ⟨q*a i*q,compress_mem_corner hq (a i)⟩
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  obtain ⟨u,hu⟩ := HochschildMatrixSystems.exists_unitary_weak_powers eC ρ
    (cornerTrace_normal q hq e τ hτ) (cornerTrace_one q hq τ hfaith hq0)
    (cornerTrace_tracial q hq τ htr) (cornerTrace_faithful q hq τ hfaith hq0)
    (corner_factor q hq e τ hτ h1 htr hfaith hfactor hdiff hq0)
    (corner_no_minimal q hq hdiff) b (fun i => signedExponent (k i)) (fun i => signedExponent_ne_zero _) hε
  refine ⟨ofCornerUnitary q hq u,ofCornerUnitary_support q hq u,fun i => ?_⟩
  let v : Corner q hq := (u^signedExponent (k i) : unitary (Corner q hq))
  have hvq : (v:M)*q=(v:M) := v.property.2
  have hqv : q*(v:M)=(v:M) := v.property.1
  have he : τ ((b i*v : Corner q hq):M)=τ (a i*(v:M)) := by
    change τ (q*a i*q*(v:M))=_
    calc
      _ = τ (q*(a i*(v:M))) := by rw [mul_assoc,mul_assoc,hqv]
      _ = τ ((a i*(v:M))*q) := htr _ _
      _ = _ := by rw [mul_assoc,hvq]
  have hh := hu i
  change ‖cornerTrace q hq τ (b i*v)‖<ε at hh
  rw [cornerTrace_apply,he,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht] at hh
  rw [ofCornerUnitary_power]
  have hh' := (mul_lt_mul_of_pos_left hh ht)
  simpa only [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul,mul_comm (τ q).re ε] using hh'
end HochschildPatching

 

 

 

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {I : Type v} [Fintype I] (F : I → M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
lemma exists_incremental_patch
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, τ (F i)=0)
    {K N : ℕ} (hK : 0<K) {b : ℝ → ℝ} (v : PartialUnitary M)
    (hb : 0 ≤ b ((τ v.support).re)) (hv : MomentBound F τ (K := K) (N := N) b v)
    (hs : (τ v.support).re<1) {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ w : PartialUnitary M, ∃ h : v.support*w.support=0,
      0<(τ w.support).re ∧ (τ w.support).re<η ∧
      ∀ a : BoundedWord I K N, admissibleTail a.2.val →
        ‖τ (mixedEval F (v.orthogonalSum w h) a.1 a.2.val)‖ ≤ b ((τ v.support).re)+
          ((N : ℝ)*ε+(N : ℝ)^2*(ε+2*b ((τ v.support).re)/(1-(τ v.support).re)))*(τ w.support).re := by
  have hpt : (τ (1-v.support)).re=1-(τ v.support).re := by rw [map_sub,h1,Complex.sub_re,Complex.one_re]
  have hp : 0<(τ (1-v.support)).re := by rw [hpt]; linarith
  have hp0 : 1-v.support ≠ 0 := by intro he; rw [he,map_zero,Complex.zero_re] at hp; exact lt_irrefl _ hp
  obtain ⟨q,hq,hqv,hq0,hqt,hqsmall⟩ := HochschildQuantization.exists_relative_small_corner
    (1-v.support) v.support_proj.one_sub e τ hτ h1 htr hfaith hfactor hdiff hp0
    (fun a : BoundedWord I K N => mixedEval F v a.1 a.2.val) (sq_pos_of_pos hε) hη
  obtain ⟨w,hw,hweak⟩ := exists_partial_unitary_weak_powers q hq e τ hτ h1 htr hfaith hfactor hdiff hq0
    (linearCoeff F v (K := K) (N := N)) linearPower hε
  have horth : v.support*w.support=0 := by
    rw [hw]
    have hh := (hq.le_iff_mul_eq_right v.support_proj.one_sub).mp hqv
    rw [sub_mul,one_mul,sub_eq_self] at hh
    exact hh
  have hwpos : 0<(τ w.support).re := by rw [hw]; exact HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  refine ⟨w,horth,hwpos,by rwa [hw],fun a ha => ?_⟩
  have hsmall : ∀ z : BoundedWord I K N,
      ‖τ.toPreGNS (w.support*mixedEval F v z.1 z.2.val*w.support-
        residualScalar τ v (mixedEval F v z.1 z.2.val) • w.support)‖ ≤ ε*‖τ.toPreGNS w.support‖ := by
    intro z
    rw [hw]
    apply le_of_sq_le_sq _ (mul_nonneg hε.le (norm_nonneg _))
    rw [mul_pow,projection_gns_sq τ hq]
    exact (hqsmall z).le
  have hlin := linear_trace_bound F τ htr v w a.1 a.2.val a.2.property
    (ε*(τ w.support).re) (fun j => by rw [hw]; exact (hweak j).le)
  have hquad := quadratic_trace_bound F τ htr v w horth hK hF hFτ hb hv hp ε hsmall
    a.1 a.2.val a.2.property ha
  have hh := mixedEval_patch_bound F τ v w horth a.1 a.2.val a.2.property
    (mul_nonneg hε.le hwpos.le)
    (mul_nonneg (add_nonneg hε.le (div_nonneg (mul_nonneg (by norm_num) hb) hp.le)) hwpos.le) hlin hquad
  rw [hpt] at hh
  calc
    _ ≤ ‖τ (mixedEval F v a.1 a.2.val)‖+(N : ℝ)*(ε*(τ w.support).re)+
        (N : ℝ)^2*((ε+2*b ((τ v.support).re)/(1-(τ v.support).re))*(τ w.support).re) := hh
    _ ≤ b ((τ v.support).re)+(N : ℝ)*(ε*(τ w.support).re)+
        (N : ℝ)^2*((ε+2*b ((τ v.support).re)/(1-(τ v.support).re))*(τ w.support).re) :=
          add_le_add (add_le_add (hv a ha) le_rfl) le_rfl
    _ = _ := by ring

end HochschildPatching

 

 

 

namespace HochschildPatching

def expBudget (δ C s : ℝ) : ℝ := δ*(Real.exp (C*s)-1)
lemma expBudget_zero (δ C : ℝ) : expBudget δ C 0=0 := by simp [expBudget]
lemma expBudget_continuous (δ C : ℝ) : Continuous (expBudget δ C) := by unfold expBudget; fun_prop
lemma expBudget_nonneg {δ C s : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hs : 0 ≤ s) : 0 ≤ expBudget δ C s := by
  exact mul_nonneg hδ (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hC hs)))
lemma expBudget_increment {δ C s t : ℝ} (hδ : 0 ≤ δ) :
    expBudget δ C s+C*(δ+expBudget δ C s)*t ≤ expBudget δ C (s+t) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (C*t)) (mul_nonneg hδ (Real.exp_pos (C*s)).le)
  have he : Real.exp (C*(s+t))=Real.exp (C*s)*Real.exp (C*t) := by rw [mul_add,Real.exp_add]
  unfold expBudget
  rw [he]
  nlinarith

def patchRate (n T : ℝ) : ℝ := 1+2*n^2/(1-T)
def patchTolerance (δ n : ℝ) : ℝ := δ/(n+n^2+1)
lemma patchRate_ge_one {n T : ℝ} (hT : T<1) : 1 ≤ patchRate n T := by
  unfold patchRate
  have : 0 ≤ 2*n^2/(1-T) := div_nonneg (mul_nonneg (by norm_num) (sq_nonneg n)) (by linarith)
  linarith
lemma patchTolerance_pos {δ n : ℝ} (hδ : 0<δ) (hn : 0 ≤ n) : 0<patchTolerance δ n := by
  unfold patchTolerance
  apply div_pos hδ
  nlinarith [sq_nonneg n]
lemma patch_slope_bound {δ n T s B : ℝ} (hδ : 0 ≤ δ) (hn : 0 ≤ n) (hT : T<1) (hs : s ≤ T) (hB : 0 ≤ B) :
    n*patchTolerance δ n+n^2*(patchTolerance δ n+2*B/(1-s)) ≤ patchRate n T*(δ+B) := by
  have hden : 0<n+n^2+1 := by nlinarith [sq_nonneg n]
  have heps : patchTolerance δ n*(n+n^2) ≤ δ := by
    unfold patchTolerance
    calc
      δ/(n+n^2+1)*(n+n^2) ≤ δ/(n+n^2+1)*(n+n^2+1) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hδ hden.le)
      _ = δ := div_mul_cancel₀ _ hden.ne'
  have hds : 0<1-s := by linarith
  have hdt : 0<1-T := by linarith
  have hr : 2*n^2/(1-s) ≤ 2*n^2/(1-T) :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg n)) hdt (by linarith)
  have hrB := mul_le_mul_of_nonneg_right hr hB
  have hC := patchRate_ge_one (n := n) hT
  have hCd : δ ≤ patchRate n T*δ := by nlinarith
  have he : n*patchTolerance δ n+n^2*(patchTolerance δ n+2*B/(1-s))=
      patchTolerance δ n*(n+n^2)+(2*n^2/(1-s))*B := by ring
  rw [he]
  calc
    _ ≤ δ+(2*n^2/(1-T))*B := add_le_add heps hrB
    _ ≤ patchRate n T*(δ+B) := by unfold patchRate at *; nlinarith

lemma expBudget_patch_bound {δ n T s t : ℝ} (hδ : 0 ≤ δ) (hn : 0 ≤ n)
    (hT : T<1) (hs : 0 ≤ s) (hsT : s ≤ T) (ht : 0 ≤ t) :
    expBudget δ (patchRate n T) s+
      (n*patchTolerance δ n+n^2*(patchTolerance δ n+2*expBudget δ (patchRate n T) s/(1-s)))*t ≤
        expBudget δ (patchRate n T) (s+t) := by
  have hb := expBudget_nonneg hδ ((by norm_num : (0 : ℝ) ≤ 1).trans (patchRate_ge_one (n := n) hT)) hs
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right (patch_slope_bound hδ hn hT hsT hb) ht)).trans (expBudget_increment hδ)
end HochschildPatching

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {I : Type v} [Fintype I] (F : I → M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
theorem exists_partial_unitary_moments
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, τ (F i)=0)
    {K N : ℕ} (hK : 0<K) {δ T : ℝ} (hδ : 0<δ) (hT0 : 0 ≤ T) (hT : T<1) :
    ∃ v : PartialUnitary M, (τ v.support).re=T ∧
      MomentBound F τ (K := K) (N := N) (expBudget δ (patchRate N T)) v := by
  let b := expBudget δ (patchRate N T)
  let P : PartialUnitary M → Prop := fun v => (τ v.support).re ≤ T ∧ MomentBound F τ (K := K) (N := N) b v
  have h0 : P 0 := by
    constructor
    · simpa only [PartialUnitary.support_zero,map_zero,Complex.zero_re] using hT0
    · exact momentBound_zero F τ (by dsimp only [b]; rw [expBudget_zero])
  have hclosed : ∀ (a : ℕ → PartialUnitary M) (s : PartialUnitary M), Monotone a →
      (∀ n, P (a n)) → GNSTendsto τ (fun n => (a n : M)) atTop (s : M) → P s := by
    intro a s _ha hPa ht
    constructor
    · have hs := (ht.star τ htr).mul τ htr ht 1 (fun n => by simpa only [norm_star] using (a n).norm_le_one)
      have htrace := (Complex.continuous_re.tendsto _).comp (trace_tendsto_of_gns τ h1 hs)
      exact le_of_tendsto htrace (Filter.Eventually.of_forall (fun n => (hPa n).1))
    · exact momentBound_limit F τ htr h1 ht (expBudget_continuous δ _).continuousAt (fun n => (hPa n).2)
  obtain ⟨v,hv⟩ := PartialUnitary.maximal_of_sequentially_closed e τ (HochschildSakai.mul_hasPreadjoint e)
    hτ htr hfaith P h0 hclosed
  have hs0 : 0 ≤ (τ v.support).re := (τ.map_nonneg v.support_proj.nonneg).1
  have hb : 0 ≤ b ((τ v.support).re) := expBudget_nonneg hδ.le
    ((by norm_num : (0 : ℝ) ≤ 1).trans (patchRate_ge_one hT)) hs0
  refine ⟨v,?_,hv.1.2⟩
  by_contra hne
  have hsT : (τ v.support).re<T := lt_of_le_of_ne hv.1.1 hne
  obtain ⟨w,horth,hwpos,hwt,hwm⟩ := exists_incremental_patch F e τ hτ h1 htr hfaith hfactor hdiff
    hF hFτ hK v hb hv.1.2 (hsT.trans hT) (patchTolerance_pos hδ (Nat.cast_nonneg N)) (sub_pos.mpr hsT)
  let z := v.orthogonalSum w horth
  have hzs : (τ z.support).re=(τ v.support).re+(τ w.support).re := by
    rw [PartialUnitary.support_orthogonalSum,map_add,Complex.add_re]
  have hz : P z := by
    constructor
    · rw [hzs]; linarith
    · intro a ha
      have hh := hwm a ha
      have hr := expBudget_patch_bound hδ.le (Nat.cast_nonneg N) hT hs0 hv.1.1 hwpos.le
      rw [hzs]
      exact hh.trans hr
  have hvz : v ≤ z := v.le_orthogonalSum w horth
  have hzv : z ≤ v := hv.2 hz hvz
  have he : z=v := le_antisymm hzv hvz
  rw [he] at hzs
  linarith

end HochschildPatching

 

 

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr in
lemma trace_supported_insertion {q : M} (hq : IsStarProjection q) (A x B : M)
    (hA : ‖A‖ ≤ 1) (hx : ‖x‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hqx : q*x=x) :
    ‖τ (A*x*B)‖ ≤ (τ q).re := by
  have he : τ (A*x*B)=τ (q*(x*B*A)) := by
    rw [mul_assoc,htr A (x*B),← mul_assoc,← mul_assoc,hqx]
  rw [he]
  apply (HochschildTraceNorm.positive_weight_trace_bound τ htr q (x*B*A) hq.nonneg).trans
  have hn : ‖x*B*A‖ ≤ 1 := by simpa only [one_mul] using norm_mul_le_of_le (norm_mul_le_of_le hx hB) hA
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (τ.map_nonneg hq.nonneg).1
include htr in
lemma trace_wordProduct_patch (v w : PartialUnitary M) (horth : v.support*w.support=0)
    (l : List ((Bool × ℕ) × M)) (hl : ∀ a ∈ l, ‖a.2‖ ≤ 1)
    (A : M) (hA : ‖A‖ ≤ 1) :
    ‖τ (A*wordProduct (v.orthogonalSum w horth).power l)-τ (A*wordProduct v.power l)‖ ≤
      (l.length : ℝ)*(τ w.support).re := by
  induction l generalizing A with
  | nil => simp
  | cons a l ih =>
    obtain ⟨k,c⟩ := a
    have hc := hl (k,c) (List.mem_cons_self ..)
    have htail := fun a ha => hl a (List.mem_cons_of_mem _ ha)
    have hA' : ‖A*v.power k*c‖ ≤ 1 := by
      simpa only [one_mul] using norm_mul_le_of_le (norm_mul_le_of_le hA (v.norm_power_le_one k)) hc
    have hin := ih htail (A*v.power k*c) hA'
    have hnew := trace_supported_insertion τ htr w.support_proj A (w.power k)
      (c*wordProduct (v.orthogonalSum w horth).power l) hA (w.norm_power_le_one k)
      (by simpa only [one_mul] using norm_mul_le_of_le hc (norm_wordProduct_le_one _ (fun k => (v.orthogonalSum w horth).norm_power_le_one k) l htail))
      (w.support_power k)
    have he : A*wordProduct (v.orthogonalSum w horth).power ((k,c)::l)-A*wordProduct v.power ((k,c)::l)=
        (A*v.power k*c*wordProduct (v.orthogonalSum w horth).power l-A*v.power k*c*wordProduct v.power l)+
          A*w.power k*(c*wordProduct (v.orthogonalSum w horth).power l) := by
      rw [wordProduct_cons,wordProduct_cons,PartialUnitary.power_orthogonalSum]
      noncomm_ring
    rw [← map_sub,he,map_add,map_sub]
    apply (norm_add_le _ _).trans
    have hh := add_le_add hin hnew
    simpa only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh

variable {I : Type*} (F : I → M)
include htr in
lemma trace_mixedEval_patch {K : ℕ} (v w : PartialUnitary M) (horth : v.support*w.support=0)
    (hF : ∀ i, ‖F i‖ ≤ 1) (a : Option I) (l : List (WordAtom I K)) :
    ‖τ (mixedEval F (v.orthogonalSum w horth) a l)-τ (mixedEval F v a l)‖ ≤
      (l.length : ℝ)*(τ w.support).re := by
  have hh := trace_wordProduct_patch τ htr v w horth (evaluatedTail F l)
    (fun a ha => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact norm_wordCoeff F hF b.2)
    (wordCoeff F a) (norm_wordCoeff F hF a)
  simpa only [mixedEval,evaluatedTail,List.length_map] using hh

 
def unitaryCompletion (v : PartialUnitary M) : unitary M :=
  ⟨(v:M)+(1-v.support),by
    apply Unitary.mem_iff.mpr
    have hp := v.support_proj
    have horth : v.support*(1-v.support)=0 := by rw [mul_sub,mul_one,hp.isIdempotentElem.eq,sub_self]
    let w := ofCornerUnitary (1-v.support) hp.one_sub 1
    have hw : w.support=1-v.support := ofCornerUnitary_support ..
    have hwv : (w:M)=1-v.support := rfl
    let he := v.orthogonalSum w (by rwa [hw])
    have hs : he.support=1 := by dsimp only [he]; rw [PartialUnitary.support_orthogonalSum,hw,add_sub_cancel]
    constructor
    · have hh := he.star_mul_self_eq_support.trans hs
      change star ((v:M)+(w:M))*((v:M)+(w:M))=1 at hh
      simpa only [hwv] using hh
    · have hh := he.mul_star_self_eq_support.trans hs
      change ((v:M)+(w:M))*star ((v:M)+(w:M))=1 at hh
      simpa only [hwv] using hh⟩

end HochschildPatching
end

end OAI
