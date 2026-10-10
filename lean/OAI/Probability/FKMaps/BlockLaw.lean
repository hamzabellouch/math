import OAI.Probability.FKMaps.BlockCritical
import OAI.Probability.FKMaps.ExcursionLaw

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma rawWord_signSum (x : ℕ → Letter) (n : ℕ) :
    ((rawWord x n).map Letter.increment).sum=signSum x n := by
  simp only [rawWord,List.map_ofFn,List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun i => (x i).increment) n
lemma rawWord_take {n j : ℕ} (h : j≤n) (x : ℕ → Letter) : (rawWord x n).take j=rawWord x j := by
  unfold rawWord
  rw [← Fin.ofFn_take_eq_take_ofFn h]
  rfl
lemma emptyProb_le_killed (P : Parameters) (n : ℕ) : emptyProb P n≤SimpleWalk.killed n 0 0 := by
  rw [← rawKilled_measure P 0 0 n]
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  obtain ⟨hz,hn⟩ := emptyReducing_dyck _ hx
  constructor
  · intro j hj
    have hh := hn j
    rw [rawWord_take hj,rawWord_signSum] at hh
    simpa only [Nat.cast_zero,zero_add] using hh
  · simpa only [rawWord_signSum,Nat.cast_zero,zero_add] using hz

/-- Finiteness of the endpoint inventory generating function follows from the
actual killed walk Green sum; no coefficient asymptotic is assumed. -/
theorem emptyProb_summable (P : Parameters) : Summable (emptyProb P) :=
  Summable.of_nonneg_of_le (emptyProb_nonneg P) (emptyProb_le_killed P) (SimpleWalk.killed_summable 0 0)
theorem emptyProb_even_summable (P : Parameters) : Summable (fun n => emptyProb P (2*n)) :=
  (emptyProb_summable P).comp_injective (by intro i j h; omega)
lemma emptyProb_zero (P : Parameters) : emptyProb P 0=1 := by
  have h : EmptyReducing ([] : List Letter) := rfl
  simp [emptyProb,rawWord,h]

def emptyTotal (P : Parameters) : ℝ := ∑' n,emptyProb P (2*n)
lemma emptyTotal_ge_one (P : Parameters) : 1≤emptyTotal P := by
  have h := (emptyProb_even_summable P).le_tsum 0 (fun n _ => emptyProb_nonneg P (2*n))
  change 1≤∑' n,emptyProb P (2*n)
  simpa only [mul_zero,emptyProb_zero] using h
lemma emptyTotal_pos (P : Parameters) : 0<emptyTotal P := lt_of_lt_of_le zero_lt_one (emptyTotal_ge_one P)

def emptyWeights (P : Parameters) : BlockCritical.Weights where
  mass n := emptyProb P (2*n)/emptyTotal P
  nonneg n := div_nonneg (emptyProb_nonneg P (2*n)) (emptyTotal_pos P).le
  total := by
    have hh := (emptyProb_even_summable P).hasSum.div_const (emptyTotal P)
    change HasSum (fun n => emptyProb P (2*n)/emptyTotal P) (emptyTotal P/emptyTotal P) at hh
    simpa only [div_self (emptyTotal_pos P).ne'] using hh

/-- The normalized exact word coefficient law has the required near-endpoint
Abel lower bound. The remaining bridge to map coefficients is combinatorial. -/
theorem emptyWeights_abel_lower (P : Parameters) : ∃ c : ℝ,0<c ∧ ∀ x : ℝ,(3:ℝ)/4≤x → x<1 →
    c≤Real.sqrt (1-x)*(emptyWeights P).abelMean x := by
  obtain ⟨c,hc,h⟩ := empty_abel_lower P
  refine ⟨c/emptyTotal P,div_pos hc (emptyTotal_pos P),?_⟩
  intro x hx hx'
  have hs : 0<Real.sqrt (1-x) := Real.sqrt_pos.mpr (by linarith)
  have he : (emptyWeights P).abelMean x=(∑' n : ℕ,(n:ℝ)*emptyProb P (2*n)*x^n)/emptyTotal P := by
    rw [BlockCritical.Weights.abelMean,← tsum_div_const]
    apply tsum_congr
    intro n
    change (n:ℝ)*(emptyProb P (2*n)/emptyTotal P)*x^n=((n:ℝ)*emptyProb P (2*n)*x^n)/emptyTotal P
    ring
  rw [he]
  have hl := (div_le_iff₀ hs).mp (h x hx hx')
  have := div_le_div_of_nonneg_right hl (emptyTotal_pos P).le
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using this

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

def flexParameter (P : Parameters) : ℝ := 1+2*P.p/(1-P.p)
def radiusParameter (P : Parameters) : ℝ := (1-P.p)/16

lemma flexParameter_pos (P : Parameters) : 0<flexParameter P := by
  have hp := P.lower
  have hu := P.upper
  dsimp [flexParameter]
  have h : 0<2*P.p/(1-P.p) := div_pos (by linarith) (by linarith)
  linarith

lemma radiusParameter_pos (P : Parameters) : 0<radiusParameter P :=
  div_pos (sub_pos.mpr P.upper) (by norm_num)

lemma typedCoefficient_inventory (P : Parameters) (m : ℕ) :
    typedCoefficient (ENNReal.ofReal (flexParameter P)) m*
      (ENNReal.ofReal (radiusParameter P))^m=ENNReal.ofReal (emptyProb P (2*m)) := by
  have h : emptyProb P (2*m)=radiusParameter P^m*
      ∑ v∈typedEmptyWords (2*m),flexParameter P^flexibleCount v [] := by
    rw [emptyProb,rawEmpty_real,empty_wordMass_sum]
    rfl
  rw [h,typedCoefficient,ENNReal.ofReal_mul (pow_nonneg (radiusParameter_pos P).le _),
    ENNReal.ofReal_pow (radiusParameter_pos P).le,ENNReal.ofReal_sum_of_nonneg]
  · rw [mul_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    exact (ENNReal.ofReal_pow (flexParameter_pos P).le _).symm
  · intro w _
    exact pow_nonneg (flexParameter_pos P).le _

def inventorySeries (P : Parameters) (x : ℝ) : ℝ := ∑' m,emptyProb P (2*m)*x^m

lemma inventorySeries_summable (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    Summable (fun m => emptyProb P (2*m)*x^m) := by
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (emptyProb_nonneg P _) (pow_nonneg hx _))
    (fun m => mul_le_of_le_one_right (emptyProb_nonneg P _) (pow_le_one₀ hx hx'))
    (emptyProb_even_summable P)

lemma inventorySeries_nonneg (P : Parameters) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ inventorySeries P x := tsum_nonneg (fun _ => mul_nonneg (emptyProb_nonneg P _) (pow_nonneg hx _))

lemma inventorySeries_ge_one (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    1 ≤ inventorySeries P x := by
  have h := (inventorySeries_summable P hx hx').le_tsum 0
    (fun m _ => mul_nonneg (emptyProb_nonneg P _) (pow_nonneg hx _))
  simpa only [Nat.mul_zero,emptyProb_zero,pow_zero,mul_one,inventorySeries] using h

lemma wordSeries_inventory (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    wordSeries (ENNReal.ofReal (flexParameter P))
      (ENNReal.ofReal (Real.sqrt (radiusParameter P*x)))=ENNReal.ofReal (inventorySeries P x) := by
  have hu : 0 ≤ radiusParameter P*x := mul_nonneg (radiusParameter_pos P).le hx
  rw [wordSeries_coefficients,← ENNReal.ofReal_pow (Real.sqrt_nonneg _),Real.sq_sqrt hu,
    ENNReal.ofReal_mul (radiusParameter_pos P).le]
  simp_rw [mul_pow,← mul_assoc,typedCoefficient_inventory]
  unfold inventorySeries
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg (emptyProb_nonneg P _) (pow_nonneg hx _))
    (inventorySeries_summable P hx hx')]
  apply tsum_congr
  intro m
  rw [ENNReal.ofReal_mul (emptyProb_nonneg P _),ENNReal.ofReal_pow hx]

def coreCoefficientReal (t : ℝ) (m : ℕ) : ℝ :=
  ∑ w∈(typedEmptyWords (2*m)).filter CoreWord,t^flexibleCount w []

lemma coreCoefficientReal_nonneg {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : 0 ≤ coreCoefficientReal t m :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg ht _)

lemma coreCoefficient_ofReal {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    coreCoefficient (ENNReal.ofReal t) m=ENNReal.ofReal (coreCoefficientReal t m) := by
  rw [coreCoefficientReal,ENNReal.ofReal_sum_of_nonneg (fun _ _ => pow_nonneg ht _)]
  unfold coreCoefficient
  apply Finset.sum_congr rfl
  intro w _
  exact (ENNReal.ofReal_pow ht _).symm

lemma coreCoefficientReal_zero (t : ℝ) : coreCoefficientReal t 0=0 := by
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨hw,hcore⟩ := Finset.mem_filter.mp hw
  have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp hw).1
  have hp := coreWord_pos w hcore
  omega

/-- A real HasSum form of the exact root-corner substitution, derived from
finite endpoint summability rather than assumed analytic convergence. -/
theorem actual_core_series (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    HasSum (fun m => coreCoefficientReal (flexParameter P) m*
      (radiusParameter P*x*(inventorySeries P x)^2)^m) (inventorySeries P x-1) := by
  let t := flexParameter P
  let u := radiusParameter P*x*(inventorySeries P x)^2
  have hu : 0 ≤ u := mul_nonneg (mul_nonneg (radiusParameter_pos P).le hx) (sq_nonneg _)
  have he : ENNReal.ofReal (inventorySeries P x)=1+
      ∑' m : ℕ,ENNReal.ofReal (coreCoefficientReal t m*u^m) := by
    have h := wordSeries_core_coefficients (ENNReal.ofReal t)
      (ENNReal.ofReal (Real.sqrt (radiusParameter P*x)))
    rw [wordSeries_inventory P hx hx'] at h
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),Real.sq_sqrt (mul_nonneg (radiusParameter_pos P).le hx)] at h
    rw [← ENNReal.ofReal_pow (inventorySeries_nonneg P hx),
      ← ENNReal.ofReal_mul (mul_nonneg (radiusParameter_pos P).le hx)] at h
    simpa only [coreCoefficient_ofReal (flexParameter_pos P).le,
      ENNReal.ofReal_mul (coreCoefficientReal_nonneg (flexParameter_pos P).le _),
      ENNReal.ofReal_pow hu,t,u] using h
  have hf : (∑' m : ℕ,ENNReal.ofReal (coreCoefficientReal t m*u^m))≠∞ := by
    intro hh
    rw [hh,add_top] at he
    exact ENNReal.ofReal_ne_top he
  have hs := ENNReal.hasSum_toReal hf
  have hv : (∑' m : ℕ,ENNReal.ofReal (coreCoefficientReal t m*u^m)).toReal=
      inventorySeries P x-1 := by
    have h := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_add ENNReal.one_ne_top hf,ENNReal.toReal_one,
      ENNReal.toReal_ofReal (inventorySeries_nonneg P hx)] at h
    linarith
  rw [← ENNReal.tsum_toReal_eq (fun m => ENNReal.ofReal_ne_top),hv] at hs
  simpa only [ENNReal.toReal_ofReal (mul_nonneg
    (coreCoefficientReal_nonneg (flexParameter_pos P).le _) (pow_nonneg hu _)),t,u] using hs

end FKCRT.Inventory
end


noncomputable section
open Filter
open scoped BigOperators Topology
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

def blockCoefficientReal (t : ℝ) (m : ℕ) : ℝ :=
  (if m=0 then 1 else 0)+coreCoefficientReal t m

def actualBlockMass (P : Parameters) (m : ℕ) : ℝ :=
  blockCoefficientReal (flexParameter P) m*
    (radiusParameter P*(emptyTotal P)^2)^m/emptyTotal P

lemma blockCoefficientReal_nonneg {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    0 ≤ blockCoefficientReal t m := by
  apply add_nonneg _ (coreCoefficientReal_nonneg ht m)
  split_ifs <;> norm_num

lemma actualBlockMass_nonneg (P : Parameters) (m : ℕ) : 0 ≤ actualBlockMass P m :=
  div_nonneg (mul_nonneg (blockCoefficientReal_nonneg (flexParameter_pos P).le _)
    (pow_nonneg (mul_nonneg (radiusParameter_pos P).le (sq_nonneg _)) _))
    (emptyTotal_pos P).le

lemma actualBlockMass_zero (P : Parameters) : actualBlockMass P 0=1/emptyTotal P := by
  simp [actualBlockMass,blockCoefficientReal,coreCoefficientReal_zero]

lemma actualBlockMass_zero_pos (P : Parameters) : 0<actualBlockMass P 0 := by
  rw [actualBlockMass_zero]
  exact div_pos zero_lt_one (emptyTotal_pos P)

lemma inventorySeries_pgf (P : Parameters) (x : ℝ) :
    (emptyWeights P).pgf x=inventorySeries P x/emptyTotal P := by
  rw [BlockCritical.Weights.pgf,inventorySeries,← tsum_div_const]
  apply tsum_congr
  intro m
  change (emptyProb P (2*m)/emptyTotal P)*x^m=(emptyProb P (2*m)*x^m)/emptyTotal P
  ring

lemma actual_block_series (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    HasSum (fun m => blockCoefficientReal (flexParameter P) m*
      (radiusParameter P*x*(inventorySeries P x)^2)^m) (inventorySeries P x) := by
  have hs := (hasSum_ite_eq (0:ℕ) (1:ℝ)).add (actual_core_series P hx hx')
  have he : 1+(inventorySeries P x-1)=inventorySeries P x := by ring
  rw [he] at hs
  apply hs.congr_fun
  intro m
  by_cases hm : m=0
  · simp [hm,blockCoefficientReal]
  · simp [hm,blockCoefficientReal]

/-- The actual connected-core coefficients satisfy precisely the normalized
inverse equation required by the analytic criticality proof. -/
lemma actual_inverse_equation (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    HasSum (fun m => actualBlockMass P m*(x*((emptyWeights P).pgf x)^2)^m)
      ((emptyWeights P).pgf x) := by
  have hs := (actual_block_series P hx hx').div_const (emptyTotal P)
  rw [← inventorySeries_pgf] at hs
  apply hs.congr_fun
  intro m
  have hτ := (emptyTotal_pos P).ne'
  have hid : radiusParameter P*(emptyTotal P)^2*(x*((emptyWeights P).pgf x)^2)=
      radiusParameter P*x*(inventorySeries P x)^2 := by
    rw [inventorySeries_pgf]
    field_simp
  dsimp [actualBlockMass]
  rw [← hid,mul_pow]
  ring

def criticalApproach (n : ℕ) : ℝ := 1-(1/2:ℝ)^(n+2)

lemma criticalApproach_bounds (n : ℕ) : (3:ℝ)/4 ≤ criticalApproach n ∧ criticalApproach n<1 := by
  have hpos : 0<(1/2:ℝ)^(n+2) := pow_pos (by norm_num) _
  have hle : (1/2:ℝ)^(n+2) ≤ (1/2:ℝ)^2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  dsimp [criticalApproach]
  norm_num at hle
  constructor <;> linarith

lemma criticalApproach_tendsto : Tendsto criticalApproach atTop (𝓝 1) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)<1)).comp (tendsto_add_atTop_nat 2)
  change Tendsto (fun n : ℕ => 1-(1/2:ℝ)^(n+2)) atTop (𝓝 1)
  simpa only [Function.comp_def,sub_zero] using tendsto_const_nhds.sub h

/-- Criticality and the finite second moment for the genuine block series.
The only assumptions are the original p∈(1/2,1); no block-law or moment
conclusion is postulated. -/
theorem actual_block_moments (P : Parameters) :
    HasSum (actualBlockMass P) 1 ∧
      HasSum (fun m : ℕ => (m:ℝ)*actualBlockMass P m) (1/2) ∧
      Summable (fun m : ℕ => (m:ℝ)^2*actualBlockMass P m) := by
  obtain ⟨c,hc,hc'⟩ := emptyWeights_abel_lower P
  exact BlockCritical.normalized_inverse_critical (emptyWeights P) (actualBlockMass_nonneg P)
    (fun n => ⟨by linarith [(criticalApproach_bounds n).1],(criticalApproach_bounds n).2⟩)
    criticalApproach_tendsto
    (fun n => actual_inverse_equation P (by linarith [(criticalApproach_bounds n).1])
      (criticalApproach_bounds n).2.le)
    hc (fun n => hc' _ (criticalApproach_bounds n).1 (criticalApproach_bounds n).2)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.BlockCritical

def doubleMass (b : ℕ → ℝ) (k : ℕ) : ℝ := if Even k then b (k/2) else 0

lemma doubleMass_even (b : ℕ → ℝ) (k : ℕ) : doubleMass b (2*k)=b k := by
  simp [doubleMass,even_two]

lemma doubleMass_outside (b : ℕ → ℝ) (k : ℕ) (hk : k ∉ Set.range (fun n : ℕ => 2*n)) :
    doubleMass b k=0 := by
  rw [doubleMass,ite_eq_right]
  rintro ⟨j,hj⟩
  exact hk ⟨j,by dsimp only; omega⟩

lemma doubleMass_nonneg {b : ℕ → ℝ} (hb : ∀ k,0≤b k) (k : ℕ) : 0≤doubleMass b k := by
  unfold doubleMass
  split_ifs
  · exact hb _
  · exact le_rfl

lemma hasSum_doubleMass {b : ℕ → ℝ} {a : ℝ} (h : HasSum b a) : HasSum (doubleMass b) a := by
  apply (Function.Injective.hasSum_iff (by intro i j hij; dsimp only at hij; omega : Function.Injective (fun k : ℕ => 2*k))
    (doubleMass_outside b)).1
  simpa only [Function.comp_def,doubleMass_even] using h

lemma hasSum_doubleMean {b : ℕ → ℝ} {a : ℝ} (h : HasSum (fun k : ℕ => (k:ℝ)*b k) a) :
    HasSum (fun k : ℕ => (k:ℝ)*doubleMass b k) (2*a) := by
  apply (Function.Injective.hasSum_iff (f := fun k : ℕ => (k:ℝ)*doubleMass b k)
    (by intro i j hij; dsimp only at hij; omega : Function.Injective (fun k : ℕ => 2*k))
    (fun k hk => by rw [doubleMass_outside b k hk,mul_zero])).1
  simpa only [Function.comp_def,doubleMass_even,Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using h.mul_left 2

lemma summable_doubleSecond {b : ℕ → ℝ} (h : Summable (fun k : ℕ => (k:ℝ)^2*b k)) :
    Summable (fun k : ℕ => (k:ℝ)^2*doubleMass b k) := by
  apply (Function.Injective.summable_iff (f := fun k : ℕ => (k:ℝ)^2*doubleMass b k)
    (by intro i j hij; dsimp only at hij; omega : Function.Injective (fun k : ℕ => 2*k))
    (fun k hk => by rw [doubleMass_outside b k hk,mul_zero])).1
  refine (h.mul_left 4).congr (fun k => ?_)
  simp only [Function.comp_def,doubleMass_even,Nat.cast_mul,Nat.cast_ofNat]
  ring

/-- Doubling block edge counts gives exactly the corner offspring law.
The support span is two, and sizes in the tree theorem are all 2n+1. -/
def evenOffspring (b : Weights) (h₀ : 0<b.mass 0) (h₁ : 0<b.mass 1)
    (hm : HasSum (fun k : ℕ => (k:ℝ)*b.mass k) (1/2))
    (hs : Summable (fun k : ℕ => (k:ℝ)^2*b.mass k)) : TreeCoding.CriticalEvenOffspring where
  mass := doubleMass b.mass
  nonneg := doubleMass_nonneg b.nonneg
  total := hasSum_doubleMass b.total
  even_support k hk := by
    rw [doubleMass,ite_eq_right]
    exact Nat.not_even_iff_odd.mpr hk
  zero_pos := by simpa [doubleMass] using h₀
  two_pos := by simpa [doubleMass] using h₁
  mean := by simpa using hasSum_doubleMean hm
  second := summable_doubleSecond hs

/-- The exact normalized analytic criterion feeds the proved source joint
excursion invariance theorem, with neither criticality nor finite variance
postulated separately. This is a dependency lemma, not the FK main. -/
theorem block_joint_coding (p : Weights) {b : ℕ → ℝ}
    (hb : ∀ k,0≤b k) (hb₀ : 0<b 0) (hb₁ : 0<b 1)
    {x : ℕ → ℝ} (hx : ∀ n,0≤x n ∧ x n<1) (ht : Tendsto x atTop (𝓝 1))
    (heq : ∀ n,HasSum (fun k => b k*(x n*(p.pgf (x n))^2)^k) (p.pgf (x n)))
    {c : ℝ} (hc : 0<c) (hlower : ∀ n,c≤Real.sqrt (1-x n)*p.abelMean (x n)) :
    ∃ offspring : TreeCoding.CriticalEvenOffspring,
      offspring.mass=doubleMass b ∧ TreeCoding.JointCodingStatement offspring := by
  obtain ⟨htotal,hmean,hsecond⟩ := normalized_inverse_critical p hb hx ht heq hc hlower
  let offspring := evenOffspring ⟨b,hb,htotal⟩ hb₀ hb₁ hmean hsecond
  exact ⟨offspring,rfl,offspring.jointCodingStatement⟩

end FKCRT.BlockCritical
end


noncomputable section
open List Filter
open scoped BigOperators Topology
namespace FKCRT.Inventory
open MapCycles Chords
attribute [local instance] Classical.propDecidable

/-- The true one-link word is a connected core, including its root seam. -/
lemma oneLink_core : CoreWord [TypedLetter.burger true,TypedLetter.order true] := by
  let v : Fin 2 → TypedLetter := ![.burger true,.order true]
  have he : stackTypedRun ((List.finRange 2).map v) []=some [] := by decide
  let M := StackMatching.ofEmpty he
  let i : Fin 2 := 0
  have hnf := M.no_fixed (List.nodup_finRange _) i (List.mem_finRange i)
  have hlt : i<M.mate i := by
    have hh := Fin.val_ne_of_ne hnf
    change (M.mate i).val≠0 at hh
    change 0<(M.mate i).val
    omega
  let r : Opener M.mate := ⟨i,hlt⟩
  refine ⟨2,v,M,by decide,r,rfl,?_⟩
  intro x
  have hx : x=r := by
    apply Subtype.ext
    apply Fin.ext
    have hh := x.property
    have hm := (M.mate x.val).isLt
    change x.val.val< (M.mate x.val).val at hh
    change x.val.val=0
    omega
  subst x
  exact SimpleGraph.Reachable.refl r

lemma coreCoefficientReal_one_pos {t : ℝ} (ht : 0<t) : 0<coreCoefficientReal t 1 := by
  let w := [TypedLetter.burger true,TypedLetter.order true]
  have hw : w∈(typedEmptyWords (2*1)).filter CoreWord :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_wordsOfLength.mpr rfl,
      coreWord_empty _ oneLink_core⟩,oneLink_core⟩
  have h := Finset.single_le_sum (s := (typedEmptyWords (2*1)).filter CoreWord)
    (f := fun w => t^flexibleCount w []) (fun _ _ => pow_nonneg ht.le _) hw
  exact (pow_pos ht _).trans_le h

lemma actualBlockMass_one_pos (P : Parameters) : 0<actualBlockMass P 1 := by
  apply div_pos _ (emptyTotal_pos P)
  apply mul_pos
  · change 0<(if (1:ℕ)=0 then 1 else 0)+coreCoefficientReal (flexParameter P) 1
    simpa using coreCoefficientReal_one_pos (flexParameter_pos P)
  · exact pow_pos (mul_pos (radiusParameter_pos P) (sq_pos_of_pos (emptyTotal_pos P))) _

/-- The actual corner offspring distribution, not an abstract replacement. -/
def actualOffspring (P : Parameters) : FKCRT.TreeCoding.CriticalEvenOffspring :=
  FKCRT.BlockCritical.evenOffspring
    ⟨actualBlockMass P,actualBlockMass_nonneg P,(actual_block_moments P).1⟩
    (actualBlockMass_zero_pos P) (actualBlockMass_one_pos P)
    (actual_block_moments P).2.1 (actual_block_moments P).2.2

/-- The proved invariance theorem is instantiated by the genuine core
coefficients, under precisely the original phase parameter range. Finite FK
map metric transport is a separate remaining obligation. -/
theorem actual_offspring_joint_coding (P : Parameters) :
    FKCRT.TreeCoding.JointCodingStatement (actualOffspring P) :=
  (actualOffspring P).jointCodingStatement

end FKCRT.Inventory
end


noncomputable section
open List Equiv MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreTree
/-- Product of genuine root-core probabilities at every vertex. -/
def productMass (t r τ : ℝ) : CoreTree→ℝ
  | leaf => 1/τ
  | branch c ts => (wordMonomial t (r*τ) c.val/τ)*∏ i,productMass t r τ (ts i)

lemma productMass_nonneg {t r τ : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (hτ : 0 ≤ τ) (T : CoreTree) :
    0 ≤ T.productMass t r τ := by
  induction T with
  | leaf => exact div_nonneg zero_le_one hτ
  | branch c ts ih =>
    exact mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg ht _)
      (pow_nonneg (mul_nonneg hr hτ) _)) hτ) (Finset.prod_nonneg (fun i _ => ih i))

/-- Exact cancellation of the τ powers, including every leaf. This is the
pointwise branching density, not merely a generating-function identity. -/
theorem productMass_eq (t r τ : ℝ) (hτ : τ≠0) (T : CoreTree) :
    T.productMass t r τ=wordMonomial t r T.word/τ := by
  induction T with
  | leaf => simp [productMass,word,wordMonomial_nil]
  | branch c ts ih =>
    change (wordMonomial t (r*τ) c.val/τ)*(∏ i,(ts i).productMass t r τ)=_
    have hw := wordMonomial_corners t r c (fun i => (ts i).toWord)
    change wordMonomial t r (branch c ts).word=
      wordMonomial t r c.val*∏ i,wordMonomial t r (ts i).word at hw
    rw [hw]
    simp_rw [ih]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    simp only [wordMonomial,mul_pow]
    field_simp

end CoreTree

lemma wordMonomial_ofReal {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (w : List TypedLetter) :
    wordMonomial (ENNReal.ofReal t) (ENNReal.ofReal r) w=ENNReal.ofReal (wordMonomial t r w) := by
  simp only [wordMonomial,ENNReal.ofReal_mul (pow_nonneg ht _),ENNReal.ofReal_pow ht,
    ENNReal.ofReal_pow hr]

lemma inventorySeries_one (P : Parameters) : inventorySeries P 1=emptyTotal P := by
  simp [inventorySeries,emptyTotal]

lemma wordMonomial_hasSum (P : Parameters) :
    HasSum (fun w : EmptyTypedWord => wordMonomial (flexParameter P)
      (Real.sqrt (radiusParameter P)) w.val) (emptyTotal P) := by
  have he : (∑' w : EmptyTypedWord,ENNReal.ofReal
      (wordMonomial (flexParameter P) (Real.sqrt (radiusParameter P)) w.val))=
      ENNReal.ofReal (emptyTotal P) := by
    have h := wordSeries_inventory P (x := 1) (by norm_num) (by norm_num)
    simpa only [mul_one,wordSeries,wordMonomial_ofReal (flexParameter_pos P).le
      (Real.sqrt_nonneg _),inventorySeries_one] using h
  have hf : (∑' w : EmptyTypedWord,ENNReal.ofReal
      (wordMonomial (flexParameter P) (Real.sqrt (radiusParameter P)) w.val))≠∞ := by
    rw [he];exact ENNReal.ofReal_ne_top
  have hs := ENNReal.hasSum_toReal hf
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),he,
    ENNReal.toReal_ofReal (emptyTotal_pos P).le] at hs
  simpa only [wordMonomial,ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (flexParameter_pos P).le _)
    (pow_nonneg (Real.sqrt_nonneg _) _))] using hs

/-- The genuine finite core trees carry total branching mass one. This also
establishes extinction of this actual branching construction without adding
an extinction or GW identification as a premise. -/
theorem coreTree_productMass_hasSum (P : Parameters) :
    HasSum (CoreTree.productMass (flexParameter P) (Real.sqrt (radiusParameter P)) (emptyTotal P)) 1 := by
  have hs := (wordMonomial_hasSum P).div_const (emptyTotal P)
  rw [div_self (emptyTotal_pos P).ne'] at hs
  have h := (CoreTree.wordEquiv.hasSum_iff).mpr hs
  apply h.congr_fun
  intro T
  exact T.productMass_eq _ _ _ (emptyTotal_pos P).ne'

end FKCRT.Inventory
end


noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreTree

def shape : CoreTree → FKCRT.TreeCoding.PlaneTree
  | leaf => .node []
  | branch _c ts => .node (List.ofFn (fun i => shape (ts i)))

lemma shape_degrees (T : CoreTree) : T.shape.degrees=T.degrees := by
  induction T with
  | leaf => simp [shape,FKCRT.TreeCoding.PlaneTree.degrees,degrees,labels,CoreLabel.arity]
  | branch c ts ih =>
    rw [shape,FKCRT.TreeCoding.PlaneTree.degrees,degrees,labels_branch]
    simp only [List.length_ofFn,List.map_cons,CoreLabel.arity,List.flatMap_def,
      List.map_flatten,List.map_ofFn,Function.comp_def]
    congr 2
    exact congrArg List.ofFn (funext ih)

lemma degrees_excursion (T : CoreTree) : FKCRT.TreeCoding.IsExcursionList
    (FKCRT.TreeCoding.PlaneTree.incrementWord T.degrees) := by
  rw [← shape_degrees]
  exact T.shape.degrees_excursion

abbrev LabelExcursion := {l : List CoreLabel // FKCRT.TreeCoding.IsExcursionList
  (FKCRT.TreeCoding.PlaneTree.incrementWord (l.map CoreLabel.arity))}

def labelEquiv : CoreTree ≃ LabelExcursion :=
  Equiv.ofBijective (fun T => ⟨T.labels,T.degrees_excursion⟩) ⟨by
    intro T U h
    exact labels_injective (congrArg Subtype.val h),by
    intro l
    obtain ⟨T,hT⟩ := exists_of_excursion l.property
    exact ⟨T,Subtype.ext hT⟩⟩

end CoreTree
namespace CoreLabel

def mass (t r τ : ℝ) : CoreLabel → ℝ
  | none => 1/τ
  | some c => wordMonomial t (r*τ) c.val/τ

lemma mass_nonneg {t r τ : ℝ} (ht : 0≤t) (hr : 0≤r) (hτ : 0≤τ) (c : CoreLabel) :
    0 ≤ mass t r τ c := by
  cases c with
  | none => exact div_nonneg zero_le_one hτ
  | some c =>
    exact div_nonneg (mul_nonneg (pow_nonneg ht _) (pow_nonneg (mul_nonneg hr hτ) _)) hτ

end CoreLabel
namespace CoreTree

lemma productMass_labels (t r τ : ℝ) (T : CoreTree) :
    T.productMass t r τ=(T.labels.map (CoreLabel.mass t r τ)).prod := by
  induction T with
  | leaf => simp [productMass,labels,CoreLabel.mass]
  | branch c ts ih =>
    rw [productMass,labels_branch,List.map_cons,List.prod_cons]
    congr 1
    simp only [List.flatMap_def,List.map_flatten,List.prod_flatten,List.map_ofFn,List.prod_ofFn,Function.comp_def]
    exact Finset.prod_congr rfl (fun i _ => ih i)

/-- Exact pointwise GW branching weight in the faithful preorder coding. -/
theorem labels_product_eq_word (t r τ : ℝ) (hτ : τ≠0) (l : LabelExcursion) :
    (l.val.map (CoreLabel.mass t r τ)).prod=
      wordMonomial t r (labelEquiv.symm l).word/τ := by
  have hl : (labelEquiv.symm l).labels=l.val := congrArg Subtype.val (labelEquiv.apply_symm_apply l)
  rw [← hl,← productMass_labels]
  exact productMass_eq t r τ hτ _

end CoreTree
end FKCRT.Inventory
end


noncomputable section
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

/-- The actual connected-core contribution in each fixed edge-size fiber. -/
lemma coreMass_finite_sum (P : Parameters) (m : ℕ) :
    (∑ w∈(typedEmptyWords (2*m)).filter CoreWord,
      ENNReal.ofReal (wordMonomial (flexParameter P)
        (Real.sqrt (radiusParameter P)*emptyTotal P) w/emptyTotal P))=
    ENNReal.ofReal (coreCoefficientReal (flexParameter P) m*
      (radiusParameter P*(emptyTotal P)^2)^m/emptyTotal P) := by
  have hn : ∀ w∈(typedEmptyWords (2*m)).filter CoreWord,
      0≤wordMonomial (flexParameter P)
        (Real.sqrt (radiusParameter P)*emptyTotal P) w/emptyTotal P := by
    intro w _
    exact div_nonneg
      (mul_nonneg (pow_nonneg (flexParameter_pos P).le _) (pow_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (emptyTotal_pos P).le) _)) (emptyTotal_pos P).le
  rw [← ENNReal.ofReal_sum_of_nonneg hn]
  congr 1
  rw [← Finset.sum_div]
  congr 1
  rw [coreCoefficientReal,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  have hs : (Real.sqrt (radiusParameter P)*emptyTotal P)^(2*m)=
      (radiusParameter P*(emptyTotal P)^2)^m := by
    rw [pow_mul,mul_pow,Real.sq_sqrt (radiusParameter_pos P).le]
  rw [wordMonomial,hl,hs]

/-- Grouping is over genuine normalized connected cores, with no abstract
counting coefficients left in the summands. -/
lemma coreMass_by_size (P : Parameters) (F : ℕ→ℝ≥0∞) :
    (∑' c : Core,ENNReal.ofReal (wordMonomial (flexParameter P)
      (Real.sqrt (radiusParameter P)*emptyTotal P) c.val/emptyTotal P)*F c.val.length)=
    ∑' m : ℕ,ENNReal.ofReal (coreCoefficientReal (flexParameter P) m*
      (radiusParameter P*(emptyTotal P)^2)^m/emptyTotal P)*F (2*m) := by
  rw [core_tsum_by_size (fun w => ENNReal.ofReal (wordMonomial (flexParameter P)
    (Real.sqrt (radiusParameter P)*emptyTotal P) w/emptyTotal P)*F w.length)]
  apply tsum_congr
  intro m
  rw [← coreMass_finite_sum P m,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  rw [hl]

end FKCRT.Inventory
end


noncomputable section
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreLabel

def rootMass (P : Parameters) (c : CoreLabel) : ℝ :=
  mass (flexParameter P) (Real.sqrt (radiusParameter P)) (emptyTotal P) c

lemma rootMass_nonneg (P : Parameters) (c : CoreLabel) : 0≤rootMass P c :=
  mass_nonneg (flexParameter_pos P).le (Real.sqrt_nonneg _) (emptyTotal_pos P).le c

lemma rootMass_by_size (P : Parameters) (F : ℕ→ℝ≥0∞) :
    (∑' c : CoreLabel,ENNReal.ofReal (rootMass P c)*F c.arity)=
      ∑' m : ℕ,ENNReal.ofReal (actualBlockMass P m)*F (2*m) := by
  have hs := (Equiv.optionEquivSumPUnit.{0} Core).symm.tsum_eq
    (fun c : CoreLabel => ENNReal.ofReal (rootMass P c)*F c.arity)
  rw [← hs,Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp only [Equiv.optionEquivSumPUnit_symm_inl,Equiv.optionEquivSumPUnit_symm_inr,
    rootMass,mass,arity,tsum_fintype,Fintype.univ_punit,Finset.sum_singleton]
  rw [coreMass_by_size]
  have hi (m : ℕ) : ENNReal.ofReal (actualBlockMass P m)=
      ENNReal.ofReal (coreCoefficientReal (flexParameter P) m*
        (radiusParameter P*(emptyTotal P)^2)^m/emptyTotal P)+
      (if m=0 then ENNReal.ofReal (1/emptyTotal P) else 0) := by
    by_cases hm : m=0
    · simp [hm,actualBlockMass_zero,coreCoefficientReal_zero]
    · simp [hm,actualBlockMass,blockCoefficientReal]
  simp_rw [hi,add_mul]
  rw [ENNReal.tsum_add]
  congr 1
  simp

lemma rootMass_total (P : Parameters) :
    (∑' c : CoreLabel,ENNReal.ofReal (rootMass P c))=1 := by
  have h := rootMass_by_size P (fun _ => 1)
  simp only [mul_one] at h
  rw [h,← ENNReal.ofReal_tsum_of_nonneg (actualBlockMass_nonneg P)
    (actual_block_moments P).1.summable,(actual_block_moments P).1.tsum_eq]
  simp

def rootLaw (P : Parameters) : PMF CoreLabel :=
  ⟨fun c => ENNReal.ofReal (rootMass P c),(rootMass_total P) ▸ ENNReal.summable.hasSum⟩

lemma rootLaw_by_size (P : Parameters) (F : ℕ→ℝ≥0∞) :
    (∑' c : CoreLabel,rootLaw P c*F c.arity)=
      ∑' k : ℕ,(actualOffspring P).law k*F k := by
  change (∑' c : CoreLabel,ENNReal.ofReal (rootMass P c)*F c.arity)=_
  rw [rootMass_by_size]
  have he := Function.Injective.tsum_eq (f := fun k : ℕ => (actualOffspring P).law k*F k)
    (by intro i j hij; dsimp only at hij; omega : Function.Injective (fun k : ℕ => 2*k)) (by
      intro k hk
      by_contra h
      apply hk
      change (actualOffspring P).law k*F k=0
      rw [FKCRT.TreeCoding.CriticalEvenOffspring.law_apply]
      change ENNReal.ofReal (FKCRT.BlockCritical.doubleMass (actualBlockMass P) k)*F k=0
      rw [FKCRT.BlockCritical.doubleMass_outside _ _ h]
      simp)
  rw [← he]
  apply tsum_congr
  intro k
  rw [FKCRT.TreeCoding.CriticalEvenOffspring.law_apply]
  congr 2
  exact (FKCRT.BlockCritical.doubleMass_even (actualBlockMass P) k).symm

/-- The true root core has the already proved critical offspring marginal. -/
theorem rootLaw_arity (P : Parameters) : (rootLaw P).map arity=(actualOffspring P).law := by
  ext k
  rw [PMF.map_apply]
  have h := rootLaw_by_size P (fun j => if j=k then 1 else 0)
  simp_rw [eq_comm (a := k)]
  simpa only [mul_ite,mul_one,mul_zero,tsum_ite_eq] using h

end CoreLabel
end FKCRT.Inventory
end

end OAI
