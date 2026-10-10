import OAI.Dynamics.StandardMap.CriticalSequence

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy

def dyadicTimes : AddSubgroup ℝ where
  carrier := {x | ∃ n : ℕ, ∃ a : ℤ, x=(a:ℝ)/(2:ℝ)^n}
  zero_mem' := ⟨0,0,by norm_num⟩
  add_mem' := by
    rintro x y ⟨n,a,rfl⟩ ⟨m,b,rfl⟩
    refine ⟨n+m,a*2^m+b*2^n,?_⟩
    rw [pow_add]
    push_cast
    field_simp
  neg_mem' := by
    rintro x ⟨n,a,rfl⟩
    exact ⟨n,-a,by push_cast; ring⟩
abbrev DyadicTime := dyadicTimes
lemma dyadicTime_mem (x : DyadicTime) : ∃ n : ℕ, ∃ a : ℤ, (x:ℝ)=(a:ℝ)/(2:ℝ)^n := x.property
noncomputable instance : Countable DyadicTime := by
  apply Set.Countable.to_subtype
  have hh : (dyadicTimes : Set ℝ)⊆Set.range (fun p : ℕ × ℤ => (p.2:ℝ)/(2:ℝ)^p.1) := by
    rintro x ⟨n,a,h⟩
    exact ⟨(n,a),h.symm⟩
  exact (Set.countable_range _).mono hh
noncomputable def dyadicInt (a : ℤ) : DyadicTime := ⟨a,0,a,by norm_num⟩
@[simp] lemma dyadicInt_val (a : ℤ) : (dyadicInt a:ℝ)=(a:ℝ) := rfl
noncomputable def dyadicHalf (x : DyadicTime) : DyadicTime :=
  ⟨(x:ℝ)/2,by
    obtain ⟨n,a,ha⟩ := dyadicTime_mem x
    refine ⟨n+1,a,?_⟩
    rw [ha,pow_succ]; ring⟩
@[simp] lemma dyadicHalf_val (x : DyadicTime) : (dyadicHalf x:ℝ)=(x:ℝ)/2 := rfl
@[simp] lemma dyadicHalf_add_self (x : DyadicTime) : dyadicHalf x+dyadicHalf x=x := by
  apply Subtype.ext
  change (x:ℝ)/2+(x:ℝ)/2=(x:ℝ); ring
@[simp] lemma dyadicHalf_double (x : DyadicTime) : dyadicHalf (x+x)=x := by
  apply Subtype.ext
  change ((x:ℝ)+(x:ℝ))/2=(x:ℝ); ring
noncomputable def dyadicMid (s t : DyadicTime) : DyadicTime := dyadicHalf (s+t)
@[simp] lemma dyadicMid_val (s t : DyadicTime) : (dyadicMid s t:ℝ)=((s:ℝ)+(t:ℝ))/2 := rfl
lemma dyadicTime_dense : Dense (Set.range ((↑) : DyadicTime → ℝ)) := by
  rw [dense_iff_inter_open]
  intro U hU hUn
  obtain ⟨x,hx⟩ := hUn
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
  let m := n
  have hp (n : ℕ) : (n:ℝ)+1≤2^n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; push_cast; nlinarith
  let a : ℤ := ⌊x*2^m⌋
  let y : DyadicTime := ⟨(a:ℝ)/2^m,m,a,rfl⟩
  have hpow : (0:ℝ)<2^m := by positivity
  have hfl : (a:ℝ)≤x*2^m ∧ x*2^m<(a:ℝ)+1 := ⟨Int.floor_le _,Int.lt_floor_add_one _⟩
  have hd : dist (y:ℝ) x<ε := by
    rw [Real.dist_eq]
    change |(a:ℝ)/2^m-x|<ε
    rw [abs_lt]
    constructor
    · have hεp : (1:ℝ)<ε*2^m := by
        have he := (div_lt_iff₀ (show (0:ℝ)<(n:ℝ)+1 by positivity)).mp hn
        have hp' := hp m
        change (n:ℝ)+1≤2^m at hp'
        nlinarith
      have hlow : x-ε<(a:ℝ)/2^m := (lt_div_iff₀ hpow).mpr (by nlinarith [hfl.2])
      linarith
    · have hle : (a:ℝ)/2^m≤x := (div_le_iff₀ hpow).mpr hfl.1
      linarith
  exact ⟨y,hball hd,⟨y,rfl⟩⟩

def AmbientArray (d : DyadicTime → DyadicTime → ℝ) : Prop :=
  (∀ s t, 0≤d s t) ∧ (∀ s, d s s=0) ∧ (∀ s t, d s t=d t s) ∧
  (∀ s t u, d s u≤d s t+d t u) ∧ (∀ s t, d s t≤|(t:ℝ)-(s:ℝ)|+2)
abbrev DistanceArray := {d : DyadicTime → DyadicTime → ℝ // AmbientArray d}
lemma isClosed_ambientArray : IsClosed {d | AmbientArray d} := by
  unfold AmbientArray
  simp only [Set.ofPred_and,Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_le continuous_const (continuous_apply t |>.comp (continuous_apply s))
  apply IsClosed.inter
  · exact isClosed_iInter fun s => isClosed_eq (continuous_apply s |>.comp (continuous_apply s)) continuous_const
  apply IsClosed.inter
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_eq
      (continuous_apply t |>.comp (continuous_apply s)) (continuous_apply s |>.comp (continuous_apply t))
  apply IsClosed.inter
  · refine isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun u => ?_
    have h1 : Continuous (fun d : DyadicTime → DyadicTime → ℝ => d s t) := (continuous_apply t).comp (continuous_apply s)
    have h2 : Continuous (fun d : DyadicTime → DyadicTime → ℝ => d t u) := (continuous_apply u).comp (continuous_apply t)
    exact isClosed_le ((continuous_apply u).comp (continuous_apply s)) (h1.add h2)
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_le
      (continuous_apply t |>.comp (continuous_apply s)) continuous_const
lemma isCompact_ambientArray : IsCompact {d | AmbientArray d} := by
  have hc : IsCompact {d : DyadicTime → DyadicTime → ℝ | ∀ s t : DyadicTime, d s t∈Icc (0:ℝ) (|(t:ℝ)-(s:ℝ)|+2)} :=
    isCompact_pi_infinite fun s => isCompact_pi_infinite fun t => isCompact_Icc
  apply hc.of_isClosed_subset isClosed_ambientArray
  intro d hd s t
  exact ⟨hd.1 s t,hd.2.2.2.2 s t⟩
noncomputable instance : CompactSpace DistanceArray := isCompact_iff_compactSpace.mp isCompact_ambientArray
noncomputable def arrayEval (s t : DyadicTime) (d : DistanceArray) : ℝ := d.val s t
lemma continuous_arrayEval (s t : DyadicTime) : Continuous (arrayEval s t) :=
  (continuous_apply t).comp ((continuous_apply s).comp continuous_subtype_val)
noncomputable def affineArray (w : Set.Icc (0:ℝ) 1) : DistanceArray := ⟨fun s t => w.val*|(t:ℝ)-(s:ℝ)|,by
  refine ⟨fun s t => mul_nonneg w.property.1 (abs_nonneg _),?_,?_,?_,?_⟩
  · intro s; simp
  · intro s t; dsimp only; rw [abs_sub_comm]
  · intro s t u
    calc
      _ ≤ w.val*(|(t:ℝ)-(s:ℝ)|+|(u:ℝ)-(t:ℝ)|) := mul_le_mul_of_nonneg_left (by
        simpa only [add_comm] using abs_sub_le (u:ℝ) (t:ℝ) (s:ℝ)) w.property.1
      _ = _ := by ring
  · intro s t
    have hh := mul_le_mul_of_nonneg_right w.property.2 (abs_nonneg ((t:ℝ)-(s:ℝ)))
    linarith⟩
lemma continuous_affineArray : Continuous affineArray := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact continuous_subtype_val.mul continuous_const
noncomputable def affineLocus : Set DistanceArray := Set.range affineArray
lemma isCompact_affineLocus : IsCompact affineLocus := isCompact_range continuous_affineArray
lemma isClosed_affineLocus : IsClosed affineLocus := isCompact_affineLocus.isClosed
abbrev NonAffineArray := {d : DistanceArray // d∉affineLocus}
end StandardMapEntropy

end OAI
