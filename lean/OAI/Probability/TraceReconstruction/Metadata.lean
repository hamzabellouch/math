import OAI.Probability.TraceReconstruction.Layout

namespace OAI

/-!
# Metadata

Hidden metadata, fair jitter, heterogeneous emissions, independent window trials, concentration, and fit.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem pairedReportMass_none (P Q H : FiniteLaw α) (ω : ℝ) (z : α × α) :
    pairedReportMass P Q H ω (none,z)=pairedHiddenMass H ω z := by
  simp only [pairedReportMass,Fintype.sum_bool,pairedFlagMass]
  ring

theorem pairedReport_hidden_expect (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0≤ω)
    (hP : ∀a,ω*H.mass a≤P.mass a) (hQ : ∀a,ω*H.mass a≤Q.mass a) (F : ℕ → ℝ) :
    (pairedReport P Q H hω hP hQ).expect (fun z => F (hiddenTrial z.1))=
      ω^2*F 1+(1-ω^2)*F 0 := by
  let R := pairedReport P Q H hω hP hQ
  have hp : R.expect (fun z => if z.1=none then (1:ℝ) else 0)=ω^2 := by
    simp only [expect,R,pairedReport,Fintype.sum_prod_type,Fintype.sum_option]
    simp only [reduceCtorEq,ite_false,mul_zero,Finset.sum_const_zero,add_zero]
    simpa only [pairedReportMass_none,Fintype.sum_prod_type,ite_true,mul_one] using sum_pairedHiddenMass H ω
  have he (z : Option Bool × (α × α)) : F (hiddenTrial z.1)=
      F 0+(F 1-F 0)*(if z.1=none then 1 else 0) := by
    rcases z with ⟨d,z⟩; cases d <;> simp [hiddenTrial]
  simp_rw [he]
  have hadd : R.expect (fun z => F 0+(F 1-F 0)*(if z.1=none then 1 else 0))=
      R.expect (fun _ => F 0)+R.expect (fun z => (F 1-F 0)*(if z.1=none then 1 else 0)) := by
    simp only [expect,mul_add,Finset.sum_add_distrib]
  rw [hadd,expect_const,expect_const_mul,hp]
  ring

/-- Centered hidden-flag MGF, derived from the literal paired experiment. -/
theorem pairedReport_hidden_mgf (P Q H : FiniteLaw α) {ω t : ℝ} (hω : 0≤ω)
    (hP : ∀a,ω*H.mass a≤P.mass a) (hQ : ∀a,ω*H.mass a≤Q.mass a)
    (hp : ω^2∈Set.Icc 0 1) (ht : |t|≤1) :
    (pairedReport P Q H hω hP hQ).expect (fun z =>
      Real.exp (t*((hiddenTrial z.1:ℕ)-ω^2)))≤Real.exp (t^2) := by
  rw [pairedReport_hidden_expect P Q H hω hP hQ (fun k => Real.exp (t*((k:ℝ)-ω^2)))]
  have H := binomialMass_centered_mgf 1 hp ht
  norm_num [Finset.sum_range_succ,binomialMass] at H ⊢
  convert H using 1 ; ring

end FiniteLaw

namespace PairedMechanisms
variable {Side : Type*} [Fintype Side] {m : ℕ} (M : PairedMechanisms Side m)

def hiddenCount (z : Reports Side m) : ℕ := ∑i,hiddenTrial (z i).1

/-- No independence of displacements is presumed: only the flags of the
 distinct literal paired mechanisms are independent. -/
theorem hiddenCount_mgf {ω t : ℝ} (hw : ∀i,M.hiddenWeight i=ω)
    (hp : ω^2∈Set.Icc 0 1) (ht : |t|≤1) :
    M.reports.expect (fun z => Real.exp (t*((hiddenCount z:ℕ)-(m:ℝ)*ω^2)))≤
      Real.exp ((m:ℝ)*t^2) := by
  have he (z : Reports Side m) :
      Real.exp (t*((hiddenCount z:ℕ)-(m:ℝ)*ω^2))=
        ∏i : Fin m,Real.exp (t*((hiddenTrial (z i).1:ℕ)-ω^2)) := by
    rw [←Real.exp_sum]
    congr 1
    simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,hiddenCount,Nat.cast_sum]
    ring
  simp_rw [he]
  rw [reports,FiniteLaw.coordinateProduct_expect_product _
    (fun (_ : Fin m) (z : Option Bool × (Side × Side)) => Real.exp (t*((hiddenTrial z.1:ℕ)-ω^2))) ]
  calc
    _ ≤ ∏i : Fin m,Real.exp (t^2) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun z _ => mul_nonneg
          ((FiniteLaw.pairedReport (M.first i) (M.second i) (M.common i) (M.weight_nonneg i)
            (M.common_first i) (M.common_second i)).nonneg z) (Real.exp_nonneg _))
      · intro i _
        have h := FiniteLaw.pairedReport_hidden_mgf (M.first i) (M.second i) (M.common i)
          (M.weight_nonneg i) (M.common_first i) (M.common_second i) (by simpa [hw i] using hp) ht
        simpa only [hw i] using h
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Real.exp_nat_mul]

/-- A quantitative unconditional bound for failure of a source hidden-count
 condition. The exponent ω⁴m is sufficient for the uniform scale margins. -/
theorem hiddenCount_small {ω : ℝ} (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1) :
    M.reports.expect (fun z => if (hiddenCount z:ℝ)<(m:ℝ)*ω^2/2 then 1 else 0)≤
      Real.exp (-(m:ℝ)*ω^4/16) := by
  have ht : 0≤ω^2/4 := by positivity
  have ht' : |-(ω^2/4)|≤1 := by rw [abs_neg,abs_of_nonneg ht]; linarith [hp.2]
  have H := finite_exp_markov Finset.univ M.reports.mass
    (fun z => -((hiddenCount z:ℕ)-(m:ℝ)*ω^2)) (fun z _ => M.reports.nonneg z)
    ((m:ℝ)*ω^2/2) (ω^2/4) ht
  have hm := M.hiddenCount_mgf hw hp ht'
  have hsub : M.reports.expect (fun z => if (hiddenCount z:ℝ)<(m:ℝ)*ω^2/2 then 1 else 0)≤
      ∑z∈Finset.univ.filter (fun z => (m:ℝ)*ω^2/2≤-((hiddenCount z:ℕ)-(m:ℝ)*ω^2)),M.reports.mass z := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z _
    dsimp only
    by_cases hz : (hiddenCount z:ℝ)<(m:ℝ)*ω^2/2
    · rw [ite_eq_left hz,ite_eq_left (by linarith : (m:ℝ)*ω^2/2≤-((hiddenCount z:ℕ)-(m:ℝ)*ω^2)),mul_one]
    · rw [ite_eq_right hz,mul_zero]; split_ifs <;> positivity [M.reports.nonneg z]
  calc
    _ ≤ _ := hsub.trans H
    _ ≤ Real.exp (-(ω^2/4)*((m:ℝ)*ω^2/2))*Real.exp ((m:ℝ)*(-(ω^2/4))^2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      simpa only [FiniteLaw.expect,neg_mul,mul_neg,neg_neg] using hm
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

/-- Exact Bayes averaging under all metadata, including impossible reports. -/
theorem posterior_average (F : (Fin m → Bool) → ℝ) :
    M.reports.expect (fun z => (orientationsGiven z).expect F)=
      (fairOrientations m).expect F := by
  unfold FiniteLaw.expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hb (z : Reports Side m) : M.reports.mass z*(orientationsGiven z).mass b=
      (fairOrientations m).mass b*(M.reportsGiven b).mass z := by
    change (∏i,FiniteLaw.pairedReportMass (M.first i) (M.second i) (M.common i) (M.hiddenWeight i) (z i))*
      (∏i,(FiniteLaw.flagPosterior (z i).1).mass (b i))=_
    rw [←FiniteLaw.pairedFlags_product_bayes]
    rw [Finset.prod_mul_distrib]
    rfl
  simp_rw [←mul_assoc,hb,mul_assoc]
  rw [←Finset.mul_sum,←Finset.sum_mul,(M.reportsGiven b).total,one_mul]

/-- Markov's inequality for the actual conditional failure probability.
 This does not condition any orientation averages on fitting paths. -/
theorem posterior_bad_mass {a : ℝ} (_ha : 0<a) (bad : (Fin m → Bool) → Prop)
    [DecidablePred bad] :
    a*M.reports.expect (fun z => if a≤(orientationsGiven z).expect (fun b => if bad b then 1 else 0)
      then 1 else 0) ≤ (fairOrientations m).expect (fun b => if bad b then 1 else 0) := by
  rw [←M.posterior_average,←FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_mono
  intro z
  split_ifs with hz
  · simpa using hz
  · simp only [mul_zero]
    exact Finset.sum_nonneg (fun b _ => mul_nonneg ((orientationsGiven z).nonneg b)
      (by dsimp only; split_ifs <;> norm_num))

end PairedMechanisms
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem indexedProduct_expect_product (P : ι → FiniteLaw α) (F : ι → α → ℝ) :
    (indexedProduct P).expect (fun x => ∏i,F i (x i))=∏i,(P i).expect (F i) := by
  simp only [expect,indexedProduct,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).mass a*F i a)).symm

end FiniteLaw

/-- The unconditional orientation distribution on any actual finite trial ID set. -/
def fairField (ι : Type*) [Fintype ι] : FiniteLaw (ι → Bool) :=
  FiniteLaw.indexedProduct (fun _ => FiniteLaw.flagPosterior none)

def fairLinearSum {ι : Type*} [Fintype ι] (c : ι → ℝ) (bits : ι → Bool) : ℝ :=
  ∑i,c i*((bitIndex (bits i):ℝ)-1/2)

/-- Exact MGF calculation for each paired orientation bit. -/
theorem fairBit_mgf (t : ℝ) :
    (FiniteLaw.flagPosterior none).expect (fun b => Real.exp (t*((bitIndex b:ℝ)-1/2)))=
      Real.cosh (t/2) := by
  simp only [FiniteLaw.expect,Fintype.sum_bool,FiniteLaw.flagPosterior,bitIndex]
  norm_num only [Bool.false_eq_true,↓reduceIte,Nat.cast_zero,Nat.cast_one,decide_true,decide_false]
  rw [Real.cosh_eq]
  ring_nf

/-- Hoeffding's exponential estimate for the actual independently fair bits,
 allowing deterministic zero coefficients for completed/nonactive global pairs. -/
theorem fairLinearSum_mgf {ι : Type*} [Fintype ι] (c : ι → ℝ) (t : ℝ) :
    (fairField ι).expect (fun bits => Real.exp (t*fairLinearSum c bits))≤
      Real.exp ((∑i,(c i)^2)*t^2/8) := by
  have he (bits : ι → Bool) : Real.exp (t*fairLinearSum c bits)=
      ∏i,Real.exp ((t*c i)*((bitIndex (bits i):ℝ)-1/2)) := by
    rw [←Real.exp_sum]
    congr 1
    simp only [fairLinearSum,Finset.mul_sum,mul_assoc]
  simp_rw [he]
  rw [fairField,FiniteLaw.indexedProduct_expect_product _
    (fun i b => Real.exp ((t*c i)*((bitIndex b:ℝ)-1/2)))]
  simp_rw [fairBit_mgf]
  calc
    _ ≤ ∏i,Real.exp ((t*c i)^2/8) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact (Real.cosh_pos _).le
      · intro i _
        convert Real.cosh_le_exp_half_sq (t*c i/2) using 1
        congr 1
        ring
    _ = _ := by
      rw [←Real.exp_sum]
      congr 1
      simp only [Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem fairLinearSum_mgf_card {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc : ∀i,|c i|≤1) (t : ℝ) :
    (fairField ι).expect (fun bits => Real.exp (t*fairLinearSum c bits))≤
      Real.exp ((Fintype.card ι:ℝ)*t^2/8) := by
  apply (fairLinearSum_mgf c t).trans
  apply Real.exp_le_exp.mpr
  have hs : (∑i,(c i)^2)≤(Fintype.card ι:ℝ) := by
    calc
      _ ≤ ∑_i : ι,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h:=abs_le.mp (hc i)
        nlinarith [sq_nonneg (c i)]
      _ = _ := by simp
  gcongr

/-- Two-sided finite Hoeffding bound with the source's sharp quadratic scale. -/
theorem fairLinearSum_tail_variance {ι : Type*} [Fintype ι] (c : ι → ℝ)
    {V : ℝ} (hV : 0<V) (hc : (∑i,(c i)^2)≤V) {a : ℝ} (ha : 0≤a) :
    (fairField ι).expect (fun bits => if a≤|fairLinearSum c bits| then 1 else 0)≤
      2*Real.exp (-2*a^2/V) := by
  have oneSide (d : ι → ℝ) (hd : (∑i,(d i)^2)≤V) :
      (fairField ι).expect (fun bits => if a≤fairLinearSum d bits then 1 else 0)≤
        Real.exp (-2*a^2/V) := by
    have H := finite_exp_markov Finset.univ (fairField ι).mass (fairLinearSum d)
      (fun bits _ => (fairField ι).nonneg bits) a (4*a/V) (by positivity)
    have hm : (fairField ι).expect (fun bits => Real.exp ((4*a/V)*fairLinearSum d bits))≤
        Real.exp (V*(4*a/V)^2/8) := by
      apply (fairLinearSum_mgf d (4*a/V)).trans
      apply Real.exp_le_exp.mpr
      gcongr
    have he : (fairField ι).expect (fun bits => if a≤fairLinearSum d bits then 1 else 0)=
        ∑bits∈Finset.univ.filter (fun bits => a≤fairLinearSum d bits),(fairField ι).mass bits := by
      simp only [FiniteLaw.expect,Finset.sum_filter,mul_ite,mul_one,mul_zero]
    rw [he]
    calc
      _ ≤ _ := H
      _ ≤ Real.exp (-(4*a/V)*a)*
          Real.exp (V*(4*a/V)^2/8) := by
        exact mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)
      _ = _ := by
        rw [←Real.exp_add]
        congr 1
        field_simp [ne_of_gt hV]
        ring
  have hneg (bits : ι → Bool) : fairLinearSum (fun i => -c i) bits= -fairLinearSum c bits := by
    simp only [fairLinearSum,neg_mul,Finset.sum_neg_distrib]
  have hnegc : (∑i,(-c i)^2)≤V := by simpa only [neg_sq] using hc
  have Hpos := oneSide c hc
  have Hneg := oneSide (fun i => -c i) hnegc
  have hb : (fairField ι).expect (fun bits => if a≤|fairLinearSum c bits| then 1 else 0)≤
      (fairField ι).expect (fun bits => if a≤fairLinearSum c bits then 1 else 0)+
      (fairField ι).expect (fun bits => if a≤fairLinearSum (fun i => -c i) bits then 1 else 0) := by
    have hpoint (bits : ι → Bool) :
        (if a≤|fairLinearSum c bits| then (1:ℝ) else 0)≤
        (if a≤fairLinearSum c bits then 1 else 0)+(if a≤fairLinearSum (fun i => -c i) bits then 1 else 0) := by
      rw [hneg]
      by_cases h : 0≤fairLinearSum c bits
      · rw [abs_of_nonneg h]; split_ifs <;> norm_num
      · rw [abs_of_neg (lt_of_not_ge h)]; split_ifs <;> norm_num
    unfold FiniteLaw.expect
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro bits _
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (hpoint bits) ((fairField ι).nonneg bits)
  linarith

/-- Cardinal specialization, without imposing any extra computation limits. -/
theorem fairLinearSum_tail {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc : ∀i,|c i|≤1) (hn : 0<Fintype.card ι) {a : ℝ} (ha : 0≤a) :
    (fairField ι).expect (fun bits => if a≤|fairLinearSum c bits| then 1 else 0)≤
      2*Real.exp (-2*a^2/(Fintype.card ι:ℝ)) := by
  apply fairLinearSum_tail_variance c (by exact_mod_cast hn) _ ha
  calc
    _ ≤ ∑_i : ι,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h:=abs_le.mp (hc i)
      nlinarith [sq_nonneg (c i)]
    _ = _ := by simp

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀i,Fintype (A i)]

/-- Independent observations at literal slot IDs, allowing different outcome
 types (side traces and old leaf oracles carry genuinely different data). -/
def dependentProduct (P : ∀i,FiniteLaw (A i)) : FiniteLaw (∀i,A i) where
  mass x := ∏i,(P i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (P i).nonneg _)
  total := by rw [←Fintype.prod_sum]; simp only [(P _).total,Finset.prod_const_one]

theorem dependentProduct_expect_product (P : ∀i,FiniteLaw (A i)) (F : ∀i,A i → ℝ) :
    (dependentProduct P).expect (fun x => ∏i,F i (x i))=∏i,(P i).expect (F i) := by
  simp only [expect,dependentProduct,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).mass a*F i a)).symm

theorem expect_dependentProduct_succ {n : ℕ} {A : Fin (n+1) → Type*}
    [∀i,Fintype (A i)] (P : ∀i,FiniteLaw (A i)) (F : (∀i,A i) → ℝ) :
    (dependentProduct P).expect F=(P 0).expect (fun a =>
      (dependentProduct (fun i : Fin n => P i.succ)).expect (fun x => F (Fin.cons a x))) := by
  change (∑x : ∀i,A i,(∏i,(P i).mass (x i))*F x)=_
  rw [←(Fin.consEquiv A).sum_comp]
  simp only [Fintype.sum_prod_type,Fin.consEquiv,Equiv.coe_fn_mk,
    Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,expect,dependentProduct,Finset.mul_sum,mul_assoc]

/-- A genuine dependent Pi-law is invariant under a fixed bijective relabeling
 of slots. No observation is duplicated and no random order is transmitted. -/
theorem dependentProduct_expect_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] (P : ∀i,FiniteLaw (A i))
    (e : κ ≃ ι) (F : (∀i,A i) → ℝ) :
    (dependentProduct P).expect F=(dependentProduct (fun j => P (e j))).expect
      (fun x => F (fun i => cast (congrArg A (e.apply_symm_apply i)) (x (e.symm i)))) := by
  let E : (∀j,A (e j)) ≃ (∀i,A i) := Equiv.piCongrLeft A e
  have he (x : ∀j,A (e j)) (i : ι) : E x i=
      cast (congrArg A (e.apply_symm_apply i)) (x (e.symm i)) := by
    exact Equiv.piCongrLeft_apply_eq_cast x i
  unfold expect dependentProduct
  rw [←E.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change (∏i,(P i).mass (E x i))*F (E x)=
    (∏j,(P (e j)).mass (x j))*F (fun i => cast (congrArg A (e.apply_symm_apply i)) (x (e.symm i)))
  apply congrArg₂ (· * ·)
  · rw [←e.prod_comp]
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    exact Equiv.piCongrLeft_apply_apply A e x j
  · congr 1
    funext i
    exact he x i

end FiniteLaw

/-- Independent heterogeneous emissions in a literal finite chronological
 order accumulate precisely the sum of their trace approximation costs. -/
theorem dependentCoordinate_approximates {n : ℕ} {A : Fin n → Type*}
    [∀i,Fintype (A i)] {q : ℝ} (hq : q∈Set.Icc 0 1)
    (P : ∀i,FiniteLaw (A i)) (f : ∀i,A i → List Bool)
    (w : Fin n → List Bool) (E : Fin n → ℝ)
    (h : ∀i,ApproximatesTrace q (P i) (f i) (w i) (E i)) :
    ApproximatesTrace q (FiniteLaw.dependentProduct P)
      (fun x => coordinateWord (fun i => f i (x i))) (coordinateWord w) (∑i,E i) := by
  induction n with
  | zero =>
    intro F hF
    change |(FiniteLaw.dependentProduct P).expect (fun _ => F [])-F []|≤∑i : Fin 0,E i
    simp only [FiniteLaw.expect_const,sub_self,abs_zero,Finset.univ_eq_empty,Finset.sum_empty,le_refl]
  | succ n ih =>
    intro F hF
    have ht := ih (fun i => P i.succ) (fun i => f i.succ)
      (fun i => w i.succ) (fun i => E i.succ) (fun i => h i.succ)
    have hh := ApproximatesTrace.append hq (h 0) ht F hF
    rw [FiniteLaw.expect_prod] at hh
    rw [FiniteLaw.expect_dependentProduct_succ,coordinateWord_succ,Fin.sum_univ_succ]
    have he (a : A 0) (x : ∀i : Fin n,A i.succ) :
        coordinateWord (fun i => f i ((Fin.cons a x : ∀i,A i) i))=
          f 0 a++coordinateWord (fun i => f i.succ (x i)) := by
      rw [coordinateWord_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
    simp_rw [he]
    exact hh

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Actual IDs of every local or global paired trial on the whole window tree. -/
def WindowTrial (T n g : ℕ → ℕ) : ℕ → Type
  | 0 => PEmpty
  | b+1 => Fin (n b) ⊕ (Fin (g b) ⊕ (Fin (T b) × WindowTrial T n g b))

noncomputable instance windowTrialFintype (T n g : ℕ → ℕ) :
    (b : ℕ) → Fintype (WindowTrial T n g b)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | b+1 => by
    letI := windowTrialFintype T n g b
    exact inferInstanceAs (Fintype (Fin (n b) ⊕ (Fin (g b) ⊕ (Fin (T b) × WindowTrial T n g b))))

/-- A fixed bijection, independent of every bit, reveal and hypothesis. -/
def windowAssignmentEquiv (T n g : ℕ → ℕ) (A : Type) :
    (b : ℕ) → WindowAssignments T n g A b ≃ (WindowTrial T n g b → A)
  | 0 =>
    { toFun := fun _ i => PEmpty.elim i
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by funext i; exact PEmpty.elim i }
  | b+1 =>
    { toFun := fun x i => match i with
        | .inl k => x.1 k
        | .inr (.inl k) => x.2.1 k
        | .inr (.inr (u,k)) => windowAssignmentEquiv T n g A b (x.2.2 u) k
      invFun := fun x => (fun k => x (.inl k),fun k => x (.inr (.inl k)),
        fun u => (windowAssignmentEquiv T n g A b).symm (fun k => x (.inr (.inr (u,k)))))
      left_inv := fun x => by
        rcases x with ⟨loc,glob,kids⟩
        change (loc,glob,fun u => (windowAssignmentEquiv T n g A b).symm
          (windowAssignmentEquiv T n g A b (kids u)))=(loc,glob,kids)
        simp only [Equiv.symm_apply_apply]

      right_inv := fun x => by
        funext i
        rcases i with k | k
        · rfl
        · rcases k with k | ⟨u,k⟩
          · rfl
          · exact congrFun ((windowAssignmentEquiv T n g A b).apply_symm_apply
              (fun k => x (.inr (.inr (u,k))))) k }

theorem windowPosterior_mass_flat (T n g : ℕ → ℕ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b) (bits : WindowAssignments T n g Bool b) :
    (windowPosteriorLaw T n g b d).mass bits=
      ∏i : WindowTrial T n g b,(FiniteLaw.flagPosterior
        (windowAssignmentEquiv T n g (Option Bool) b d i)).mass
          (windowAssignmentEquiv T n g Bool b bits i) := by
  induction b with
  | zero =>
    change (1:ℝ)=∏i : PEmpty,_
    simp
  | succ b ih =>
    change (∏i,(FiniteLaw.flagPosterior (d.1 i)).mass (bits.1 i))*
      ((∏i,(FiniteLaw.flagPosterior (d.2.1 i)).mass (bits.2.1 i))*
        ∏u,(windowPosteriorLaw T n g b (d.2.2 u)).mass (bits.2.2 u))=_
    simp_rw [ih]
    change _=∏i : Fin (n b) ⊕ (Fin (g b) ⊕ (Fin (T b) × WindowTrial T n g b)),
      (FiniteLaw.flagPosterior (match i with
        | .inl k => d.1 k
        | .inr (.inl k) => d.2.1 k
        | .inr (.inr (u,k)) => windowAssignmentEquiv T n g (Option Bool) b (d.2.2 u) k)).mass
      (match i with
        | .inl k => bits.1 k
        | .inr (.inl k) => bits.2.1 k
        | .inr (.inr (u,k)) => windowAssignmentEquiv T n g Bool b (bits.2.2 u) k)
    simp only [Fintype.prod_sum_type,Fintype.prod_prod_type]

/-- Exact flat posterior distribution, including all paths and zero-mass
 metadata. This is the same independent bit law, not a new assumption. -/
theorem windowPosterior_expect_flat (T n g : ℕ → ℕ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b)
    (F : WindowAssignments T n g Bool b → ℝ) :
    (windowPosteriorLaw T n g b d).expect F=
      (FiniteLaw.indexedProduct (fun i : WindowTrial T n g b => FiniteLaw.flagPosterior
        (windowAssignmentEquiv T n g (Option Bool) b d i))).expect
          (fun bits => F ((windowAssignmentEquiv T n g Bool b).symm bits)) := by
  unfold FiniteLaw.expect FiniteLaw.indexedProduct
  rw [←(windowAssignmentEquiv T n g Bool b).sum_comp]
  apply Finset.sum_congr rfl
  intro bits _
  dsimp only
  rw [Equiv.symm_apply_apply,windowPosterior_mass_flat]

def noReveals (T n g : ℕ → ℕ) (b : ℕ) : WindowAssignments T n g (Option Bool) b :=
  (windowAssignmentEquiv T n g (Option Bool) b).symm (fun _ => none)

theorem windowPosterior_fair_flat (T n g : ℕ → ℕ) (b : ℕ)
    (F : WindowAssignments T n g Bool b → ℝ) :
    (windowPosteriorLaw T n g b (noReveals T n g b)).expect F=
      (FiniteLaw.indexedProduct (fun _ : WindowTrial T n g b => FiniteLaw.flagPosterior none)).expect
        (fun bits => F ((windowAssignmentEquiv T n g Bool b).symm bits)) := by
  rw [windowPosterior_expect_flat]
  simp only [noReveals,Equiv.apply_symm_apply]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The literal global schedule is indexed by a fixed pair/block bijection. -/
def globalTrialEquiv (N t : ℕ) : (Fin (N/4) × Fin t) ≃ Fin ((N/4)*t) :=
  Equiv.ofBijective _ (globalTrialIndex_bijective N t)

def sourceGlobalCoefficient (N t : ℕ) (u : Fin N) (k : Fin ((N/4)*t)) : ℝ :=
  let v := ((globalTrialEquiv N t).symm k).1
  if v.val≤u.val ∧ u.val+v.val<N then 1 else 0

def sourceGroupCoefficient (T n : ℕ → ℕ) (b : ℕ) (u : Fin (T (b+1))) :
    WindowTrial T n (sourceScheduledTrials T n) (b+2) → ℝ
  | .inl _ => 0
  | .inr (.inl k) => sourceGlobalCoefficient (T (b+1)) (n b) u k
  | .inr (.inr (v,.inl _)) => if v=u then 1 else 0
  | .inr (.inr (_,.inr _)) => 0

theorem even_half_cast (t : ℕ) (ht : Even t) : ((t/2:ℕ):ℝ)=(t:ℝ)/2 := by
  have h : 2*(t/2)=t := Nat.mul_div_cancel' ((even_iff_two_dvd).mp ht)
  have hr : (2:ℝ)*(t/2:ℕ)=t := by exact_mod_cast h
  linarith

theorem scheduledGlobalShift_linear (N t : ℕ) (ht : Even t)
    (bits : Fin ((N/4)*t) → Bool) (u : Fin N) :
    (scheduledGlobalShift N t bits u:ℝ)=
      ∑k,sourceGlobalCoefficient N t u k*((bitIndex (bits k):ℝ)-1/2) := by
  rw [←(globalTrialEquiv N t).sum_comp]
  simp only [Fintype.sum_prod_type,sourceGlobalCoefficient,Equiv.symm_apply_apply]
  unfold scheduledGlobalShift
  simp only [Int.cast_sum,Int.cast_ite,Int.cast_sub,Int.cast_natCast,Int.cast_zero]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs with hv
  · simp only [one_mul,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    rw [even_half_cast t ht]
    simp only [globalTrialEquiv,Equiv.ofBijective_apply]
    ring
  · simp only [zero_mul,Finset.sum_const_zero]

theorem sourceDisplacement_linear (T n : ℕ → ℕ) (b : ℕ) (ht : Even (n b))
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+2)) (u : Fin (T (b+1))) :
    (sourceDisplacement (T (b+1)) (n b) (fun v => (bits.2.2 v).1) bits.2.1 u:ℝ)=
      fairLinearSum (sourceGroupCoefficient T n b u)
        (windowAssignmentEquiv T n (sourceScheduledTrials T n) Bool (b+2) bits) := by
  rcases bits with ⟨root,global,children⟩
  change Fin ((T (b+1)/4)*n b) → Bool at global
  change Fin (T (b+1)) → ((Fin (n b) → Bool) ×
    (Fin (sourceScheduledTrials T n b) → Bool) ×
    (Fin (T b) → WindowAssignments T n (sourceScheduledTrials T n) Bool b)) at children
  unfold fairLinearSum
  change _=∑i : Fin (n (b+1)) ⊕ (Fin ((T (b+1)/4)*n b) ⊕
      (Fin (T (b+1)) × (Fin (n b) ⊕ (Fin (sourceScheduledTrials T n b) ⊕
        (Fin (T b) × WindowTrial T n (sourceScheduledTrials T n) b))))),_
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,sourceGroupCoefficient,
    zero_mul,Finset.sum_const_zero,zero_add,add_zero]
  change _=(∑k,sourceGlobalCoefficient (T (b+1)) (n b) u k*
    ((bitIndex (global k):ℝ)-1/2))+
    (∑v : Fin (T (b+1)),∑a : Fin (n b),
      (if v=u then (1:ℝ) else 0)*((bitIndex ((children v).1 a):ℝ)-1/2))
  have hl : (∑v : Fin (T (b+1)),∑a : Fin (n b),
      (if v=u then (1:ℝ) else 0)*((bitIndex ((children v).1 a):ℝ)-1/2))=
        (∑a : Fin (n b),(bitIndex ((children u).1 a):ℝ))-(n b:ℝ)/2 := by
    simp only [ite_mul,one_mul,zero_mul]
    rw [show (∑v : Fin (T (b+1)),∑a : Fin (n b),
      if v=u then ((bitIndex ((children v).1 a):ℝ)-1/2) else 0)=
        ∑v : Fin (T (b+1)),if v=u then
          (∑a : Fin (n b),((bitIndex ((children v).1 a):ℝ)-1/2)) else 0 from by
            apply Finset.sum_congr rfl
            intro v _
            split_ifs <;> simp]
    rw [Finset.sum_ite_eq',ite_eq_left (Finset.mem_univ u)]
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  rw [hl,←scheduledGlobalShift_linear (T (b+1)) (n b) ht global u]
  simp only [sourceDisplacement,Int.cast_add,Int.cast_sub,Int.cast_sum,Int.cast_natCast,
    even_half_cast _ ht]
  ring

theorem sourceGroupCoefficient_variance (T n : ℕ → ℕ) (b : ℕ) (u : Fin (T (b+1))) :
    (∑i,(sourceGroupCoefficient T n b u i)^2)≤((T (b+1):ℝ)+1)*(n b:ℝ) := by
  change (∑i : Fin (n (b+1)) ⊕ (Fin ((T (b+1)/4)*n b) ⊕
      (Fin (T (b+1)) × (Fin (n b) ⊕ (Fin (sourceScheduledTrials T n b) ⊕
        (Fin (T b) × WindowTrial T n (sourceScheduledTrials T n) b))))),_)≤_
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,sourceGroupCoefficient,
    zero_pow (by omega : 2≠0),Finset.sum_const_zero,zero_add,add_zero]
  have hg : (∑k : Fin ((T (b+1)/4)*n b),(sourceGlobalCoefficient (T (b+1)) (n b) u k)^2)≤
      ((T (b+1)/4)*n b:ℕ) := by
    calc
      _ ≤ ∑_k : Fin ((T (b+1)/4)*n b),(1:ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        dsimp only [sourceGlobalCoefficient]
        split_ifs <;> norm_num
      _ = _ := by simp
  have hl : (∑v : Fin (T (b+1)),∑_a : Fin (n b),(if v=u then (1:ℝ) else 0)^2)=(n b:ℝ) := by
    simp only [ite_pow,one_pow,zero_pow (by omega : 2≠0)]
    simp
  rw [hl]
  have hdiv : ((T (b+1)/4:ℕ):ℝ)≤T (b+1) := by exact_mod_cast Nat.div_le_self (T (b+1)) 4
  push_cast at hg
  have hm := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg (n b): (0:ℝ)≤n b)
  nlinarith only [hg,hm]

/-- Actual per-window unconditional fit tail under the full tree's fair law.
 No independence between different window displacements is asserted. -/
theorem sourceDisplacement_tail (T n : ℕ → ℕ) (b : ℕ) (ht : Even (n b))
    (hn : 0<n b) (u : Fin (T (b+1))) {a : ℝ} (ha : 0≤a) :
    (windowPosteriorLaw T n (sourceScheduledTrials T n) (b+2)
      (noReveals T n (sourceScheduledTrials T n) (b+2))).expect
      (fun bits => if a≤|(sourceDisplacement (T (b+1)) (n b)
        (fun v => (bits.2.2 v).1) bits.2.1 u:ℝ)| then 1 else 0)≤
      2*Real.exp (-2*a^2/(((T (b+1):ℝ)+1)*(n b:ℝ))) := by
  rw [windowPosterior_fair_flat]
  simp_rw [sourceDisplacement_linear T n b ht,Equiv.apply_symm_apply]
  exact fairLinearSum_tail_variance (sourceGroupCoefficient T n b u)
    (by positivity) (sourceGroupCoefficient_variance T n b u) ha

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem expect_fintype_sum (P : FiniteLaw α) (f : ι → α → ℝ) :
    P.expect (fun a => ∑i,f i a)=∑i,P.expect (f i) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_add (P : FiniteLaw α) (f g : α → ℝ) :
    P.expect (fun a => f a+g a)=P.expect f+P.expect g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

theorem coordinateProduct_expect_eval {n : ℕ} (P : Fin n → FiniteLaw α)
    (u : Fin n) (f : α → ℝ) :
    (coordinateProduct P).expect (fun x => f (x u))=(P u).expect f := by
  let F : Fin n → α → ℝ := fun j a => if j=u then f a else 1
  have hp (x : Fin n → α) : (∏j,F j (x j))=f (x u) := by simp [F]
  rw [show (fun x : Fin n → α => f (x u))=(fun x => ∏j,F j (x j)) by
    funext x; exact (hp x).symm,coordinateProduct_expect_product]
  have hj (j : Fin n) : (P j).expect (F j)=if j=u then (P j).expect f else 1 := by
    by_cases h : j=u <;> simp [F,h,expect_const]
  simp_rw [hj]
  simp

end FiniteLaw

theorem noReveals_succ (T n g : ℕ → ℕ) (b : ℕ) :
    noReveals T n g (b+1)=(fun _ => none,fun _ => none,fun _ => noReveals T n g b) := rfl

theorem windowPosterior_child (T n g : ℕ → ℕ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (u : Fin (T b))
    (F : WindowAssignments T n g Bool b → ℝ) :
    (windowPosteriorLaw T n g (b+1) d).expect (fun bits => F (bits.2.2 u))=
      (windowPosteriorLaw T n g b (d.2.2 u)).expect F := by
  rcases d with ⟨loc,glob,kids⟩
  change ((posteriorArray loc).prod ((posteriorArray glob).prod
    (FiniteLaw.coordinateProduct (fun i => windowPosteriorLaw T n g b (kids i))))).expect
      (fun bits => F (bits.2.2 u))=_
  rw [FiniteLaw.expect_prod]
  simp_rw [FiniteLaw.expect_prod,FiniteLaw.coordinateProduct_expect_eval,FiniteLaw.expect_const]

theorem failure_forall_le_sum {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] [Decidable (∀i,p i)] :
    (if ∀i,p i then (0:ℝ) else 1)≤∑i,if p i then 0 else 1 := by
  by_cases hp : ∀i,p i
  · simp only [ite_eq_left hp]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  · simp only [ite_eq_right hp]
    push Not at hp
    obtain ⟨i,hi⟩ := hp
    calc
      (1:ℝ) = if p i then 0 else 1 := by simp [hi]
      _ ≤ ∑j,if p j then 0 else 1 := by
        apply Finset.single_le_sum (f:=fun j => if p j then (0:ℝ) else 1)
        · intro j _; split_ifs <;> norm_num
        · exact Finset.mem_univ i

/-- Explicit finite tree union bound. The source's scale estimates will make
 this number exponentially small; no independence of sibling shifts is used. -/
def sourceFitTail (T n : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | b+2 => (T (b+1):ℝ)*(2*Real.exp (-2*((T b:ℝ)/8)^2/(((T (b+1):ℝ)+1)*(n b:ℝ)))+
      sourceFitTail T n (b+1))

theorem sourceTreeFit_tail (T n : ℕ → ℕ) (b : ℕ)
    (hn : ∀j<b,0<n j) (he : ∀j<b,Even (n j)) :
    (windowPosteriorLaw T n (sourceScheduledTrials T n) b
      (noReveals T n (sourceScheduledTrials T n) b)).expect
        (fun bits => if SourceTreeFit T n b bits then 0 else 1) ≤ sourceFitTail T n b := by
  induction b using Nat.twoStepInduction with
  | zero =>
    have hh (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool 0) : SourceTreeFit T n 0 bits := trivial
    simp only [ite_eq_left (hh _),FiniteLaw.expect_const,sourceFitTail,le_refl]
  | one =>
    have hh (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool 1) : SourceTreeFit T n 1 bits := trivial
    simp only [ite_eq_left (hh _),FiniteLaw.expect_const,sourceFitTail,le_refl]
  | more b ih0 ih =>
    let P := windowPosteriorLaw T n (sourceScheduledTrials T n) (b+2)
      (noReveals T n (sourceScheduledTrials T n) (b+2))
    let badShift : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+2) → Fin (T (b+1)) → Prop :=
      fun bits u => (T b:ℝ)/8≤|(sourceDisplacement (T (b+1)) (n b)
        (fun v => (bits.2.2 v).1) bits.2.1 u:ℝ)|
    have hp (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+2)) :
        (if SourceTreeFit T n (b+2) bits then (0:ℝ) else 1)≤
          (∑u : Fin (T (b+1)),if badShift bits u then 1 else 0)+
          (∑u : Fin (T (b+1)),if SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1) := by
      let p := fun u : Fin (T (b+1)) => |8*sourceDisplacement (T (b+1)) (n b)
        (fun v => (bits.2.2 v).1) bits.2.1 u|≤(T b:ℤ)
      have hh : (if SourceTreeFit T n (b+2) bits then (0:ℝ) else 1)≤
          (if ∀u,p u then 0 else 1)+(if ∀u,SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1) := by
        by_cases H : SourceTreeFit T n (b+2) bits
        · rw [ite_eq_left H]
          split_ifs <;> norm_num
        · rw [ite_eq_right H]
          by_cases h1 : ∀u,p u
          · have h2 : ¬∀u,SourceTreeFit T n (b+1) (bits.2.2 u) := fun h2 => H ⟨h1,h2⟩
            rw [ite_eq_left h1,ite_eq_right h2]
            norm_num
          · rw [ite_eq_right h1]
            split_ifs <;> norm_num
      apply hh.trans
      apply add_le_add
      · apply (failure_forall_le_sum p).trans
        apply Finset.sum_le_sum
        intro u _
        by_cases hu : p u
        · simp only [ite_eq_left hu]
          split_ifs <;> norm_num
        · have hr : (T b:ℝ)<8*|(sourceDisplacement (T (b+1)) (n b)
              (fun v => (bits.2.2 v).1) bits.2.1 u:ℝ)| := by
            have hi : (T b:ℤ) < |8*sourceDisplacement (T (b+1)) (n b)
              (fun v => (bits.2.2 v).1) bits.2.1 u| := lt_of_not_ge hu
            have hi' : (T b:ℝ) < |(8*sourceDisplacement (T (b+1)) (n b)
              (fun v => (bits.2.2 v).1) bits.2.1 u:ℤ)| := by exact_mod_cast hi
            norm_num only [Int.cast_abs,Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<8)] at hi'
            exact hi'
          have hb : badShift bits u := by dsimp [badShift]; linarith
          simp [hu,hb]
      · exact failure_forall_le_sum _
    calc
      _ ≤ P.expect (fun bits => (∑u : Fin (T (b+1)),if badShift bits u then 1 else 0)+
          (∑u : Fin (T (b+1)),if SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1)) :=
            P.expect_mono hp
      _ = (∑u : Fin (T (b+1)),P.expect (fun bits => if badShift bits u then 1 else 0))+
          (∑u : Fin (T (b+1)),P.expect (fun bits => if SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1)) := by
            rw [FiniteLaw.expect_add,FiniteLaw.expect_fintype_sum,FiniteLaw.expect_fintype_sum]
      _ ≤ (∑_u : Fin (T (b+1)),2*Real.exp (-2*((T b:ℝ)/8)^2/(((T (b+1):ℝ)+1)*(n b:ℝ))))+
          ∑_u : Fin (T (b+1)),sourceFitTail T n (b+1) := by
            apply add_le_add
            · apply Finset.sum_le_sum
              intro u _
              exact sourceDisplacement_tail T n b (he b (by omega)) (hn b (by omega)) u (by positivity)
            · apply Finset.sum_le_sum
              intro u _
              dsimp only [P]
              rw [windowPosterior_child T n (sourceScheduledTrials T n) (b+1)
                (noReveals T n (sourceScheduledTrials T n) (b+2)) u
                (fun x => if SourceTreeFit T n (b+1) x then 0 else 1)]
              rw [noReveals_succ]
              exact ih (fun j hj => hn j (by omega)) (fun j hj => he j (by omega))
      _ = sourceFitTail T n (b+2) := by simp [sourceFitTail,mul_add]

end TraceReconstruction

end
end
end
end
end
end
end

end OAI
