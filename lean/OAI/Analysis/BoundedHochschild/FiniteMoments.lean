import Mathlib
import OAI.Analysis.BoundedHochschild.IncrementalPatching

namespace OAI

/-! Small unitary moments, reindexing and simultaneous moment sequences. -/

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
open BoundedHochschild HochschildRigidity HochschildComparison
universe u v
variable {M : Type u} [CStarAlgebra M]

def asPartialUnitary (u : unitary M) : PartialUnitary M :=
  ⟨⟨(u:M),by rw [u.property.2,one_mul]⟩,by
    change (u:M)*star (u:M)=star (u:M)*(u:M)
    exact u.property.2.trans u.property.1.symm⟩
@[simp] lemma asPartialUnitary_coe (u : unitary M) : ((asPartialUnitary u : PartialUnitary M):M)=(u:M) := rfl
lemma asPartialUnitary_power (u : unitary M) (k : Bool × ℕ) :
    (asPartialUnitary u).power k=((u^signedExponent k : unitary M):M) := by
  dsimp only [PartialUnitary.power,signedExponent]
  split
  · rw [zpow_neg,show (k.2 : ℤ)+1=((k.2+1 : ℕ):ℤ) by simp,zpow_natCast,← Unitary.star_eq_inv,
      Unitary.coe_star,SubmonoidClass.coe_pow,star_pow]
    rfl
  · rw [show (k.2 : ℤ)+1=((k.2+1 : ℕ):ℤ) by simp,zpow_natCast,SubmonoidClass.coe_pow]
    rfl

variable [PartialOrder M] [StarOrderedRing M]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {I : Type v} [Fintype I] (F : I → M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
theorem exists_unitary_small_moments
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, τ (F i)=0)
    {K N : ℕ} (hK : 0<K) {ε : ℝ} (hε : 0<ε) :
    ∃ u : unitary M, ∀ a : BoundedWord I K N, admissibleTail a.2.val →
      ‖τ (mixedEval F (asPartialUnitary u) a.1 a.2.val)‖<ε := by
  let t : ℝ := min (1/2) (ε/(4*((N : ℝ)+1)))
  have ht0 : 0<t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht1 : t ≤ 1/2 := min_le_left _ _
  have htε : t ≤ ε/(4*((N : ℝ)+1)) := min_le_right _ _
  let T : ℝ := 1-t
  have hT0 : 0 ≤ T := by dsimp only [T]; linarith
  have hT : T<1 := by dsimp only [T]; linarith
  let C := patchRate (N : ℝ) T
  let δ := ε/(4*Real.exp (C*T))
  have hδ : 0<δ := div_pos hε (mul_pos (by norm_num) (Real.exp_pos _))
  obtain ⟨v,hvs,hvm⟩ := exists_partial_unitary_moments F e τ hτ h1 htr hfaith hfactor hdiff
    hF hFτ hK (N := N) hδ hT0 hT
  let w := ofCornerUnitary (1-v.support) v.support_proj.one_sub 1
  have hw : w.support=1-v.support := ofCornerUnitary_support ..
  have hwv : (w:M)=1-v.support := rfl
  have horth : v.support*w.support=0 := by
    rw [hw,mul_sub,mul_one,v.support_proj.isIdempotentElem.eq,sub_self]
  have hwt : (τ w.support).re=t := by rw [hw,map_sub,h1,Complex.sub_re,Complex.one_re,hvs]; dsimp only [T]; ring
  have he : asPartialUnitary (unitaryCompletion v)=v.orthogonalSum w horth := by
    apply PartialUnitary.ext
    rfl
  refine ⟨unitaryCompletion v,fun a ha => ?_⟩
  rw [he]
  have herr := trace_mixedEval_patch τ htr F v w horth hF a.1 a.2.val
  rw [hwt] at herr
  have hvb := hvm a ha
  rw [hvs] at hvb
  have hb : expBudget δ (patchRate N T) T ≤ ε/4 := by
    change δ*(Real.exp (C*T)-1) ≤ ε/4
    have heq : δ*Real.exp (C*T)=ε/4 := by dsimp only [δ]; field_simp
    nlinarith
  have hn : (a.2.val.length : ℝ)*t ≤ ε/4 := by
    have hnN : (a.2.val.length : ℝ) ≤ (N : ℝ)+1 := by exact_mod_cast (a.2.property.trans (Nat.le_succ N))
    have hnt := mul_le_mul_of_nonneg_right hnN ht0.le
    have hpos : 0<(4*((N : ℝ)+1)) := by positivity
    have htbound := (le_div_iff₀ hpos).mp htε
    nlinarith
  have htotal : ‖τ (mixedEval F (v.orthogonalSum w horth) a.1 a.2.val)‖ ≤ ε/2 := by
    calc
      _ ≤ ‖τ (mixedEval F (v.orthogonalSum w horth) a.1 a.2.val)-τ (mixedEval F v a.1 a.2.val)‖+
          ‖τ (mixedEval F v a.1 a.2.val)‖ := by
            simpa only [sub_add_cancel] using norm_add_le
              (τ (mixedEval F (v.orthogonalSum w horth) a.1 a.2.val)-τ (mixedEval F v a.1 a.2.val))
              (τ (mixedEval F v a.1 a.2.val))
      _ ≤ ε/4+ε/4 := add_le_add (herr.trans hn) (hvb.trans hb)
      _ = _ := by ring
  exact htotal.trans_lt (by linarith)

end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]
variable {I J : Type*} {K L : ℕ}

def mapAtom (f : I → J) (g : Fin K → Fin L) (a : WordAtom I K) : WordAtom J L :=
  ((a.1.1,g a.1.2),a.2.map f)
lemma wordCoeff_map (F : J → M) (f : I → J) (a : Option I) :
    wordCoeff F (a.map f)=wordCoeff (F ∘ f) a := by cases a <;> rfl
lemma mixedEval_map (F : J → M) (f : I → J) (g : Fin K → Fin L)
    (hg : ∀ k, (g k).val=k.val) (v : PartialUnitary M) (a : Option I) (l : List (WordAtom I K)) :
    mixedEval F v (a.map f) (l.map (mapAtom f g))=mixedEval (F ∘ f) v a l := by
  unfold mixedEval
  rw [wordCoeff_map]
  congr 1
  unfold evaluatedTail
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp_apply,mapAtom,wordCoeff_map,hg]

lemma admissibleTail_map (f : I → J) (g : Fin K → Fin L) (l : List (WordAtom I K))
    (hl : admissibleTail l) : admissibleTail (l.map (mapAtom f g)) := by
  constructor
  · intro h; exact hl.1 (List.map_eq_nil_iff.mp h)
  · intro b hb
    rw [← List.map_dropLast] at hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    intro h
    exact hl.2 a ha (Option.map_eq_none_iff.mp h)

def coeffNumber (a : Option I) : ℕ := if a.isSome then 1 else 0
def wordCoeffNumber (a : Option I) (l : List (WordAtom I K)) : ℕ :=
  coeffNumber a + (l.map (fun b => coeffNumber b.2)).sum
lemma wordCoeff_smul (F : I → M) (c : ℂ) (a : Option I) :
    wordCoeff (fun i => c • F i) a=c^coeffNumber a • wordCoeff F a := by
  cases a <;> simp [wordCoeff,coeffNumber]
lemma mixedEval_smul (F : I → M) (c : ℂ) (v : PartialUnitary M)
    (a : Option I) (l : List (WordAtom I K)) :
    mixedEval (fun i => c • F i) v a l=c^wordCoeffNumber a l • mixedEval F v a l := by
  have ht (l : List (WordAtom I K)) :
      wordProduct v.power (evaluatedTail (fun i => c • F i) l)=
        c^(l.map (fun b => coeffNumber b.2)).sum • wordProduct v.power (evaluatedTail F l) := by
    induction l with
    | nil => simp [evaluatedTail]
    | cons b l ih =>
      change v.power (b.1.1,b.1.2.val)*wordCoeff (fun i => c • F i) b.2*
        wordProduct v.power (evaluatedTail (fun i => c • F i) l) =
        c^(coeffNumber b.2+(l.map (fun b => coeffNumber b.2)).sum) •
          (v.power (b.1.1,b.1.2.val)*wordCoeff F b.2*wordProduct v.power (evaluatedTail F l))
      rw [wordCoeff_smul,ih]
      simp only [pow_add,mul_smul_comm,smul_mul_assoc,smul_smul,mul_comm]
  unfold mixedEval wordCoeffNumber
  rw [wordCoeff_smul,ht,pow_add]
  simp only [mul_smul_comm,smul_mul_assoc,smul_smul,mul_comm]
end HochschildPatching

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
theorem exists_small_moment_sequence
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (F : ℕ → ℕ → M) (hF : ∀ n i, ‖F n i‖ ≤ 1) (hFτ : ∀ n i, τ (F n i)=0) :
    ∃ u : ℕ → unitary M, ∀ m K N : ℕ, ∀ a : BoundedWord (Fin m) K N,
      admissibleTail a.2.val →
      Tendsto (fun n => τ (mixedEval (fun i : Fin m => F n i.val) (asPartialUnitary (u n)) a.1 a.2.val)) atTop (nhds 0) := by
  classical
  have hex (n : ℕ) := exists_unitary_small_moments (fun i : Fin n => F n i.val) e τ
    hτ h1 htr hfaith hfactor hdiff (fun i => hF n i.val) (fun i => hFτ n i.val)
    (Nat.zero_lt_succ n) (N := n) (ε := 1/((n:ℝ)+1)) (by positivity)
  choose u hu using hex
  refine ⟨u,fun m K N a ha => ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨b,hb⟩ := exists_nat_gt (1/ε)
  filter_upwards [eventually_ge_atTop (max b (max m (max K N)))] with n hn
  have hbn : b ≤ n := (le_max_left _ _).trans hn
  have hmn : m ≤ n := (le_max_left m (max K N)).trans ((le_max_right b _).trans hn)
  have hKn : K ≤ n := (le_max_left K N).trans ((le_max_right m _).trans ((le_max_right b _).trans hn))
  have hNn : N ≤ n := (le_max_right K N).trans ((le_max_right m _).trans ((le_max_right b _).trans hn))
  let f : Fin m → Fin n := fun i => ⟨i.val,i.isLt.trans_le hmn⟩
  let g : Fin K → Fin (n+1) := fun i => ⟨i.val,i.isLt.trans_le (hKn.trans (Nat.le_succ n))⟩
  let a' : BoundedWord (Fin n) (n+1) n :=
    (a.1.map f,⟨a.2.val.map (mapAtom f g),by simpa using a.2.property.trans hNn⟩)
  have htest := hu n a' (admissibleTail_map f g a.2.val ha)
  change ‖τ (mixedEval (fun i : Fin n => F n i.val) (asPartialUnitary (u n))
    (a.1.map f) (a.2.val.map (mapAtom f g)))‖ < _ at htest
  rw [mixedEval_map _ f g (fun _ => rfl)] at htest
  have hFcomp : (fun i : Fin n => F n i.val) ∘ f = (fun i : Fin m => F n i.val) := rfl
  rw [hFcomp] at htest
  have hne : 1/((n:ℝ)+1)<ε := by
    have hbR : (b:ℝ) ≤ n := by exact_mod_cast hbn
    have hpos : (0:ℝ)<(n:ℝ)+1 := by positivity
    apply (div_lt_iff₀ hpos).mpr
    have hh := (div_lt_iff₀ hε).mp hb
    nlinarith
  simpa only [dist_zero_right] using htest.trans hne

end HochschildPatching
end

end OAI
