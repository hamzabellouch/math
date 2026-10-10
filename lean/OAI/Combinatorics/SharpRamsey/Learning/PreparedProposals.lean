import Mathlib

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.PublicTables

structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

universe u

def Table (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => Ω × Table Ω n

instance instFintypeTable (Ω : Type*) [Fintype Ω] (n : ℕ) : Fintype (Table Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (Ω × Table Ω n))

variable {Ω : Type*} [Fintype Ω]

noncomputable def tableWeight (p : Law Ω) : (n : ℕ) → Table Ω n → ℝ
  | 0, _ => 1
  | n+1, z => p.mass z.1 * tableWeight p n z.2

noncomputable def first (A : Ω → Prop) [DecidablePred A] : (n : ℕ) → Table Ω n → Option Ω
  | 0, _ => none
  | n+1, z => if A z.1 then some z.1 else first A n z.2

noncomputable def outcome (A : Ω → Prop) [DecidablePred A] (f : Ω → ℝ)
    (n : ℕ) (z : Table Ω n) : ℝ :=
  (first A n z).elim 0 f

noncomputable def integral (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (n : ℕ) : ℝ := ∑ z, tableWeight p n z * outcome A f n z

noncomputable def accepted (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) : ℝ := ∑ x, if A x then p.mass x*f x else 0

noncomputable def acceptProb (p : Law Ω) (A : Ω → Prop) [DecidablePred A] : ℝ :=
  accepted p A (fun _ => 1)

theorem tableWeight_nonneg (p : Law Ω) (n : ℕ) (z : Table Ω n) :
    0 ≤ tableWeight p n z := by
  induction n with
  | zero => simp [tableWeight]
  | succ n ih => exact mul_nonneg (p.nonneg z.1) (ih z.2)

theorem tableWeight_total (p : Law Ω) (n : ℕ) : ∑ z, tableWeight p n z = 1 := by
  induction n with
  | zero =>
    change (∑ z : PUnit, (1 : ℝ)) = 1
    simp
  | succ n ih =>
    change (∑ z : Ω × Table Ω n, p.mass z.1 * tableWeight p n z.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum,ih,mul_one]
    exact p.total

theorem acceptProb_nonneg (p : Law Ω) (A : Ω → Prop) [DecidablePred A] :
    0 ≤ acceptProb p A := by
  apply sum_nonneg
  intro x hx
  split <;> simp_all [p.nonneg x]

theorem acceptProb_le_one (p : Law Ω) (A : Ω → Prop) [DecidablePred A] :
    acceptProb p A ≤ 1 := by
  rw [← p.total]
  apply sum_le_sum
  intro x hx
  split <;> simp_all [p.nonneg x]

theorem rejectProb (p : Law Ω) (A : Ω → Prop) [DecidablePred A] :
    (∑ x, if A x then 0 else p.mass x) = 1-acceptProb p A := by
  have he (x : Ω) : (if A x then 0 else p.mass x) =
      p.mass x-(if A x then p.mass x*1 else 0) := by split_ifs <;> ring
  simp_rw [he]
  rw [sum_sub_distrib,p.total]
  rfl

theorem integral_succ (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (n : ℕ) :
    integral p A f (n+1) = accepted p A f + (1-acceptProb p A)*integral p A f n := by
  have ho (z : Table Ω (n+1)) : outcome A f (n+1) z =
      if A z.1 then f z.1 else outcome A f n z.2 := by
    change (if A z.1 then some z.1 else first A n z.2).elim 0 f = _
    split_ifs <;> rfl
  simp only [integral, tableWeight, ho]
  change (∑ z : Ω × Table Ω n, p.mass z.1 * tableWeight p n z.2 *
    (if A z.1 then f z.1 else outcome A f n z.2)) = _
  rw [Fintype.sum_prod_type]
  have he (x : Ω) : (∑ z : Table Ω n, p.mass x*tableWeight p n z*
      (if A x then f x else outcome A f n z)) =
      (if A x then p.mass x*f x else 0) +
      (if A x then 0 else p.mass x)*integral p A f n := by
    by_cases hx : A x
    · simp only [hx,ite_true,zero_mul,add_zero]
      calc
        _ = (p.mass x*f x)*∑ z : Table Ω n, tableWeight p n z := by
          rw [mul_sum]; apply sum_congr rfl; intro z hz; ring
        _ = _ := by rw [tableWeight_total,mul_one]
    · simp only [hx,ite_false,zero_add]
      unfold integral
      rw [mul_sum]
      apply sum_congr rfl
      intro z hz
      ring
  simp_rw [he]
  rw [sum_add_distrib,← sum_mul,rejectProb]
  rfl

theorem integral_formula (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (n : ℕ) :
    integral p A f n = (∑ i ∈ range n, (1-acceptProb p A)^i)*accepted p A f := by
  induction n with
  | zero => simp [integral,outcome,first,Table]
  | succ n ih =>
    rw [integral_succ,ih]
    have he : (∑ i ∈ range (n+1), (1-acceptProb p A)^i) =
        1+(1-acceptProb p A)*(∑ i ∈ range n, (1-acceptProb p A)^i) := by
      rw [sum_range_succ']
      simp_rw [pow_succ']
      rw [← mul_sum]
      simp [add_comm]
    rw [he]
    ring

theorem geometric_normalization (a : ℝ) (n : ℕ) :
    a*(∑ i ∈ range n, (1-a)^i) = 1-(1-a)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih,pow_succ]
    ring

theorem first_accepted_law (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (n : ℕ) (ha : 0 < acceptProb p A) :
    integral p A f n = (1-(1-acceptProb p A)^n)*
      (accepted p A f / acceptProb p A) := by
  rw [integral_formula,← geometric_normalization]
  field_simp

theorem produced_domination (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) (ha : 0 < acceptProb p A) :
    integral p A f n ≤ accepted p A f / acceptProb p A := by
  rw [first_accepted_law p A f n ha]
  have hn : 0 ≤ accepted p A f := by
    apply sum_nonneg
    intro x hx
    split <;> simp_all [mul_nonneg (p.nonneg x) (hf x)]
  have hc : 1-(1-acceptProb p A)^n ≤ 1 := by
    have h := pow_nonneg (sub_nonneg.mpr (acceptProb_le_one p A)) n
    linarith
  simpa using mul_le_mul_of_nonneg_right hc (div_nonneg hn ha.le)

theorem production_probability (p : Law Ω) (A : Ω → Prop) [DecidablePred A] (n : ℕ) :
    integral p A (fun _ => 1) n = 1-(1-acceptProb p A)^n := by
  rw [integral_formula]
  simpa only [acceptProb,mul_comm] using geometric_normalization (acceptProb p A) n

end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.PublicTables
open MeasureTheory Finset
open scoped Classical BigOperators
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [Fintype Y]

def Law.fromMeasure (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y)
    (hf : ∀ y,MeasurableSet (f ⁻¹' {y})) : Law Y where
  mass y := μ.real (f ⁻¹' {y})
  nonneg _ := measureReal_nonneg
  total := by
    have h := sum_measureReal_preimage_singleton (μ:=μ) univ (fun y _ => hf y)
    simpa using h

lemma acceptProb_fromMeasure (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y)
    (hf : ∀ y,MeasurableSet (f ⁻¹' {y})) (A : Y → Prop) :
    acceptProb (Law.fromMeasure μ f hf) A=μ.real {x | A (f x)} := by
  unfold acceptProb accepted Law.fromMeasure
  simp only [mul_one]
  rw [←sum_filter]
  have h := sum_measureReal_preimage_singleton (μ:=μ) (univ.filter A) (fun y _ => hf y)
  simpa using h

end
end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.FiniteSchedules
open Finset MeasureTheory
open scoped Classical BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι]

def clip (M : ℕ) (ω : ι → ℕ) : ι → Fin (M+2) := fun i =>
  ⟨min (ω i) (M+1),by omega⟩

def total (ω : ι → ℕ) : ℕ := ∑ i,ω i

lemma coordinate_le_total (ω : ι → ℕ) (i : ι) : ω i ≤ total ω :=
  single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)

lemma clip_eq_iff (M : ℕ) (ω : ι → ℕ) (z : ι → Fin (M+2))
    (hz : total (fun i => (z i:ℕ))≤M) :
    clip M ω=z ↔ ω=(fun i => (z i:ℕ)) := by
  constructor
  · intro h
    funext i
    have he : min (ω i) (M+1)=(z i:ℕ) := congrArg Fin.val (congrFun h i)
    have hi := (coordinate_le_total (fun i => (z i:ℕ)) i).trans hz
    omega
  · rintro rfl
    funext i
    apply Fin.ext
    have hi := (coordinate_le_total (fun i => (z i:ℕ)) i).trans hz
    change min (z i:ℕ) (M+1)=(z i:ℕ)
    omega

lemma clip_preimage (M : ℕ) (z : ι → Fin (M+2))
    (hz : total (fun i => (z i:ℕ))≤M) :
    clip M ⁻¹' {z}={fun i => (z i:ℕ)} := by
  ext ω
  exact clip_eq_iff M ω z hz

lemma clip_total_iff (M : ℕ) (ω : ι → ℕ) :
    total (fun i => (clip M ω i:ℕ))≤M ↔ total ω≤M := by
  constructor
  · intro h
    have he := (clip_eq_iff M ω (clip M ω) h).mp rfl
    exact (congrArg total he).le.trans h
  · intro h
    unfold total clip
    have hi : ∀ i,min (ω i) (M+1)=ω i := fun i => by
      have hh := (coordinate_le_total ω i).trans h
      omega
    simp_rw [hi]
    exact h

lemma acceptance_preimage (M : ℕ) (P : (ι → ℕ) → Prop) :
    {ω | total (fun i => (clip M ω i:ℕ))≤M ∧ P (fun i => (clip M ω i:ℕ))}=
      {ω | total ω≤M ∧ P ω} := by
  ext ω
  constructor
  · rintro ⟨h,hp⟩
    have he := (clip_eq_iff M ω (clip M ω) h).mp rfl
    exact ⟨(clip_total_iff M ω).mp h,he ▸ hp⟩
  · rintro ⟨h,hp⟩
    have hc := (clip_total_iff M ω).mpr h
    have he := (clip_eq_iff M ω (clip M ω) hc).mp rfl
    exact ⟨hc,he ▸ hp⟩

end
end SharpLogRamsey.FiniteSchedules

namespace SharpLogRamsey.PoissonLikelihood
open MeasureTheory ProbabilityTheory Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

def law (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rate i))

instance probability (rate : ι → ℝ≥0) : IsProbabilityMeasure (law rate) := by
  unfold law
  infer_instance

theorem singleton_formula (rate : ι → ℝ≥0) (ω : ι → ℕ) :
    (law rate).real {ω} = Real.exp (-(∑ i,(rate i:ℝ))) *
      (∏ i,(rate i:ℝ)^(ω i))/(∏ i,((ω i).factorial:ℝ)) := by
  simp only [law,Measure.real,Measure.pi_singleton,ENNReal.toReal_prod,
    poissonMeasure_singleton,ENNReal.toReal_ofReal (show 0 ≤ Real.exp (-(rate _ : ℝ)) *
      (rate _ : ℝ)^ω _ /((ω _).factorial:ℝ) from by positivity)]
  rw [prod_div_distrib,prod_mul_distrib,←Real.exp_sum,sum_neg_distrib]

theorem singleton_ratio (proposal hidden : ι → ℝ≥0) (c : ℝ) (ω : ι → ℕ)
    (htotal : (∑ i,(proposal i:ℝ))=∑ i,(hidden i:ℝ))
    (hp : ∀ i,(proposal i:ℝ)^ω i=c^ω i*(hidden i:ℝ)^ω i) :
    (law proposal).real {ω}=c^(∑ i,ω i)*(law hidden).real {ω} := by
  rw [singleton_formula,singleton_formula,htotal]
  simp_rw [hp]
  rw [prod_mul_distrib,prod_pow_eq_pow_sum]
  ring

def uniformRate (S : Finset ι) (a : ℝ≥0) (i : ι) : ℝ≥0 :=
  if i∈S then a/(S.card:ℝ≥0) else 0

lemma sum_uniformRate (S : Finset ι) (a : ℝ≥0) (hS : S.Nonempty) :
    (∑ i,(uniformRate S a i:ℝ))=a := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast ne_of_gt (card_pos.mpr hS)
  simp only [uniformRate,apply_ite,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_zero]
  rw [←sum_filter]
  simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul]
  field_simp

theorem uniform_singleton_ratio (S U : Finset ι) (a : ℝ≥0) (hS : S.Nonempty)
    (hU : U.Nonempty) (hSU : S ⊆ U) (ω : ι → ℕ) (hω : ∀ i,i∉S → ω i=0) :
    (law (uniformRate U a)).real {ω}=
      ((S.card:ℝ)/(U.card:ℝ))^(∑ i,ω i)*(law (uniformRate S a)).real {ω} := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast ne_of_gt (card_pos.mpr hS)
  have hu : (U.card:ℝ)≠0 := by exact_mod_cast ne_of_gt (card_pos.mpr hU)
  apply singleton_ratio
  · rw [sum_uniformRate U a hU,sum_uniformRate S a hS]
  · intro i
    by_cases hi : i∈S
    · simp only [uniformRate,ite_eq_left hi,ite_eq_left (hSU hi),NNReal.coe_div,NNReal.coe_natCast]
      rw [←mul_pow]
      congr 1
      field_simp
    · rw [hω i hi]
      simp

end
end SharpLogRamsey.PoissonLikelihood

namespace SharpLogRamsey.PreparedProposals
open MeasureTheory ProbabilityTheory Finset
open SharpLogRamsey.PoissonLikelihood SharpLogRamsey.FiniteSchedules SharpLogRamsey.PublicTables
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

def accepts (S : Finset ι) (M : ℕ) (P : (ι → ℕ) → Prop)
    (z : ι → Fin (M+2)) : Prop :=
  total (fun i => (z i:ℕ))≤M ∧ (∀ i,i∉S → (z i:ℕ)=0) ∧ P (fun i => (z i:ℕ))

def proposal (U : Finset ι) (a : ℝ≥0) (M : ℕ) : Law (ι → Fin (M+2)) :=
  Law.fromMeasure (law (uniformRate U a)) (clip M)
    (fun _ => (Set.to_countable _).measurableSet)

lemma proposal_mass (U : Finset ι) (a : ℝ≥0) (M : ℕ) (z : ι → Fin (M+2))
    (hz : total (fun i => (z i:ℕ))≤M) :
    (proposal U a M).mass z=(law (uniformRate U a)).real {fun i => (z i:ℕ)} := by
  change (law _).real (clip M ⁻¹' {z})=_
  rw [clip_preimage M z hz]

theorem atom_domination (S U : Finset ι) (a : ℝ≥0) (M : ℕ)
    (hS : S.Nonempty) (hU : U.Nonempty) (hSU : S⊆U) (P : (ι → ℕ) → Prop)
    (z : ι → Fin (M+2)) (hz : accepts S M P z) :
    ((S.card:ℝ)/(U.card:ℝ))^M*(proposal S a M).mass z ≤ (proposal U a M).mass z := by
  rw [proposal_mass S a M z hz.1,proposal_mass U a M z hz.1,
    uniform_singleton_ratio S U a hS hU hSU _ hz.2.1]
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  apply pow_le_pow_of_le_one (by positivity) _ hz.1
  apply (div_le_one (by exact_mod_cast card_pos.mpr hU)).mpr
  exact_mod_cast card_le_card hSU

lemma accepts_probability (S : Finset ι) (a : ℝ≥0) (M : ℕ) (P : (ι → ℕ) → Prop) :
    acceptProb (proposal S a M) (accepts S M P)=
      (law (uniformRate S a)).real {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω} := by
  rw [proposal,acceptProb_fromMeasure]
  rw [show {x | accepts S M P (clip M x)}=
    {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω} by
      exact acceptance_preimage M (fun ω => (∀ i,i∉S → ω i=0) ∧ P ω)]

theorem proposal_success (S U : Finset ι) (a : ℝ≥0) (M : ℕ)
    (hS : S.Nonempty) (hU : U.Nonempty) (hSU : S⊆U) (P : (ι → ℕ) → Prop) :
    ((S.card:ℝ)/(U.card:ℝ))^M *
      (law (uniformRate S a)).real {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω} ≤
      acceptProb (proposal U a M) (accepts S M P) := by
  rw [←accepts_probability]
  unfold acceptProb accepted
  simp only [mul_one]
  rw [mul_sum]
  apply sum_le_sum
  intro z _
  by_cases hz : accepts S M P z
  · simp only [ite_eq_left hz]
    exact atom_domination S U a M hS hU hSU P z hz
  · simp [hz]

lemma hidden_support_ae (S : Finset ι) (a : ℝ≥0) :
    ∀ᵐ ω ∂law (uniformRate S a),∀ i,i∉S → ω i=0 := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : i∈S
  · filter_upwards [] with ω using (fun h => False.elim (h hi))
  · have hp := measurePreserving_eval (fun j => poissonMeasure (uniformRate S a j)) i
    have hx : ∀ᵐ n ∂poissonMeasure (uniformRate S a i),n=0 := by
      rw [uniformRate,ite_eq_right hi]
      apply (ae_iff_prob_eq_one (measurable_of_countable (fun n : ℕ => n=0))).mpr
      change (poissonMeasure 0) {0}=1
      rw [poissonMeasure_singleton]
      norm_num
    exact (hp.quasiMeasurePreserving.ae hx).mono (fun ω h _ => h)

lemma true_success_probability (S : Finset ι) (a : ℝ≥0) (M : ℕ) (P : (ι → ℕ) → Prop) :
    (law (uniformRate S a)).real {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω}=
      (law (uniformRate S a)).real {ω | total ω≤M ∧ P ω} := by
  apply measureReal_congr
  filter_upwards [hidden_support_ae S a] with ω hω
  apply propext
  tauto

end
end SharpLogRamsey.PreparedProposals

end

end OAI
