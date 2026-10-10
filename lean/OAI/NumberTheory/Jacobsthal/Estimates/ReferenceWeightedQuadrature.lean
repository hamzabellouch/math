import OAI.NumberTheory.Jacobsthal.Primes.ActualPrimeQuadrature
import OAI.NumberTheory.Jacobsthal.Primes.PrimeRatioBins

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ReferenceBenchmarkDecay

open FinitePathGeometry LinearSieveFunctions BuchstabBridge NormalizedDeficits
open Dickman DickmanFiniteDecay

noncomputable def benchmark : Side → ℝ → ℝ
  | .even => f sieveA
  | .odd => F sieveA

@[simp] theorem benchmark_even_below_two {s : ℝ} (hs : s ≤ 2) : benchmark .even s=0 :=
  f_initial sieveA hs

theorem benchmark_deviation_le_gap (i : Side) {s : ℝ} (hs : 1 ≤ s) :
    |benchmark i s-1| ≤ gap s := by
  obtain ⟨hl,hu⟩ := deficits_pos hs
  have hsum := deficit_sum s
  cases i with
  | even =>
    have he : benchmark .even s-1 = -lowerDeficit s := by unfold benchmark lowerDeficit; ring
    rw [he,abs_neg,abs_of_pos hl]
    linarith
  | odd =>
    change |upperDeficit s| ≤ gap s
    rw [abs_of_pos hu]
    linarith

theorem gap_le_rho {s : ℝ} (hs : 1 ≤ s) : gap s ≤ sieveA*rho (s-1) := by
  rw [gap_eq_rho hs]
  exact div_le_self (mul_nonneg sieveA_pos.le (rho_nonneg _)) hs

theorem gap_le_constant {s : ℝ} (hs : 1 ≤ s) : gap s ≤ sieveA := by
  calc
    _ ≤ sieveA*rho (s-1) := gap_le_rho hs
    _ ≤ sieveA*1 := mul_le_mul_of_nonneg_left (rho_le_one _) sieveA_pos.le
    _ = _ := mul_one _

theorem boundary_rho_decay {r : ℝ} (hr : 18 ≤ r) :
    rho (r/2-1) ≤ Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) := by
  have hu : 8 ≤ r/2-1 := by linarith
  have hr0 : 0 < r := by linarith
  have hul : r/4 ≤ r/2-1 := by linarith
  have hlog : Real.log (r+2) ≤ 2*Real.log (r/2-1+2) := by
    have hp : 0 < r+2 := by linarith
    have hsq : r+2 ≤ (r/2-1+2)^2 := by nlinarith
    have hm := Real.log_le_log hp hsq
    simpa only [Real.log_pow,Nat.cast_ofNat] using hm
  have hl0 : 0 ≤ Real.log (r+2)/2 := div_nonneg (Real.log_nonneg (by linarith)) (by norm_num)
  have hmul := mul_le_mul hul (show Real.log (r+2)/2 ≤ Real.log (r/2-1+2) by linarith)
    hl0 (by linarith : 0 ≤ r/2-1)
  calc
    _ ≤ Real.exp (-(1/16:ℝ)*(r/2-1)*Real.log (r/2-1+2)) := rho_log_decay hu
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem boundary_benchmark_decay : ∃ C : ℝ,0 < C ∧
    ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |benchmark i (r/2)-1| ≤ C*Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) := by
  let C : ℝ := sieveA*Real.exp ((1/128:ℝ)*18*Real.log 20)
  have hC : 0 < C := mul_pos sieveA_pos (Real.exp_pos _)
  have hCA : sieveA ≤ C := by
    apply le_mul_of_one_le_right sieveA_pos.le
    apply Real.one_le_exp_iff.mpr
    positivity
  refine ⟨C,hC,?_⟩
  intro r hr i
  have hs : 1 ≤ r/2 := by linarith
  have hb := benchmark_deviation_le_gap i hs
  by_cases hlarge : 18 ≤ r
  · calc
      _ ≤ gap (r/2) := hb
      _ ≤ sieveA*rho (r/2-1) := gap_le_rho hs
      _ ≤ sieveA*Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) :=
        mul_le_mul_of_nonneg_left (boundary_rho_decay hlarge) sieveA_pos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hCA (Real.exp_nonneg _)
  · have hr18 : r ≤ 18 := le_of_lt (lt_of_not_ge hlarge)
    have hl : Real.log (r+2) ≤ Real.log 20 := Real.log_le_log (by linarith) (by linarith)
    have hm : r*Real.log (r+2) ≤ 18*Real.log 20 :=
      mul_le_mul hr18 hl (Real.log_nonneg (by linarith)) (by norm_num)
    have he : 1 ≤ Real.exp ((1/128:ℝ)*18*Real.log 20+(-(1/128:ℝ)*r*Real.log (r+2))) :=
      Real.one_le_exp_iff.mpr (by nlinarith)
    calc
      _ ≤ sieveA := hb.trans (gap_le_constant hs)
      _ ≤ sieveA*Real.exp ((1/128:ℝ)*18*Real.log 20+(-(1/128:ℝ)*r*Real.log (r+2))) :=
        le_mul_of_one_le_right sieveA_pos.le he
      _ = _ := by dsimp only [C]; rw [Real.exp_add]; ring

end NumberTheoryLean.ReferenceBenchmarkDecay



namespace NumberTheoryLean.ReferenceDifferentiation

open _root_.Filter _root_.Set
open scoped Topology
open FinitePathGeometry LinearSieveFunctions BuchstabBridge ReferenceBenchmarkDecay

noncomputable def parentBenchmark : Side → ℝ → ℝ
  | .even, s => if s ≤ 2 then startingExtension sieveA s else f sieveA s
  | .odd, s => F sieveA s

def ParentDomain : Side → ℝ → Prop
  | .even, s => 1 < s
  | .odd, s => 0 < s

theorem parent_even_eq_starting {s : ℝ} (hs : s ≤ 4) :
    parentBenchmark .even s = startingExtension sieveA s := by
  simp only [parentBenchmark]
  split_ifs with h
  · rfl
  · exact (startingExtension_eq_f sieveA (le_of_lt (lt_of_not_ge h)) hs).symm

theorem parent_even_eq_ordinary {s : ℝ} (hs : 2 ≤ s) :
    parentBenchmark .even s = benchmark .even s := by
  simp only [parentBenchmark,benchmark]
  split_ifs with h
  · exact startingExtension_eq_f sieveA hs (by linarith)
  · rfl

theorem parent_mass_derivative (i : Side) {s : ℝ} (hs : ParentDomain i s) :
    HasDerivAt (fun t => t*parentBenchmark i t) (benchmark i.flip (s-1)) s := by
  cases i with
  | even =>
    change 1 < s at hs
    by_cases hs2 : 2 < s
    · have heq : (fun t => t*parentBenchmark .even t) =ᶠ[𝓝 s] (fun t => t*f sieveA t) := by
        filter_upwards [Ioi_mem_nhds hs2] with t ht
        rw [parent_even_eq_ordinary ht.le]
        rfl
      exact (mass_f_hasDerivAt sieveA hs2).congr_of_eventuallyEq heq
    · have hsle : s ≤ 2 := le_of_not_gt hs2
      have heq : (fun t => t*parentBenchmark .even t) =ᶠ[𝓝 s] (fun t => sieveA*Real.log (t-1)) := by
        filter_upwards [Ioo_mem_nhds hs (show s < 3 by linarith)] with t ht
        rw [parent_even_eq_starting (by linarith [ht.2] : t ≤ 4)]
        unfold startingExtension
        field_simp [show t ≠ 0 by linarith [ht.1]]
      have hd := ((((hasDerivAt_id s).sub_const 1).log (by linarith : s-1 ≠ 0)).const_mul sieveA)
      have h := hd.congr_of_eventuallyEq heq
      convert! h using 1
      change F sieveA (s-1) = _
      rw [F_initial sieveA (by linarith) (by linarith)]
      simp only [id_eq]
      ring
  | odd =>
    change 0 < s at hs
    by_cases hs2 : 2 < s
    · exact mass_F_hasDerivAt sieveA hs2
    · have hsle : s ≤ 2 := le_of_not_gt hs2
      have heq : (fun t => t*parentBenchmark .odd t) =ᶠ[𝓝 s] (fun _ => sieveA) := by
        filter_upwards [Ioo_mem_nhds hs (show s < 3 by linarith)] with t ht
        change t*F sieveA t=sieveA
        rw [F_initial sieveA ht.1 ht.2.le]
        field_simp [ne_of_gt ht.1]
      have hd := (hasDerivAt_const s sieveA).congr_of_eventuallyEq heq
      convert! hd using 1
      change f sieveA (s-1)=0
      exact f_initial sieveA (by linarith)

theorem reference_derivative (i : Side) {r b : ℝ} (hb : 0 < b)
    (hdomain : ParentDomain i (r/b)) :
    HasDerivAt (fun x => (parentBenchmark i (r/x)-1)/x)
      (-(benchmark i.flip (r/b-1)-1)/b^2) b := by
  have hrb : 0 < r/b := by cases i <;> simp only [ParentDomain] at hdomain <;> linarith
  have hr : 0 < r := (div_pos_iff.mp hrb).resolve_right (by intro h; linarith [h.2]) |>.1
  have hmass := (parent_mass_derivative i hdomain).sub (hasDerivAt_id (r/b))
  have hcomp := hmass.comp b ((hasDerivAt_const b r).div (hasDerivAt_id b) (ne_of_gt hb))
  have h := hcomp.div_const r
  have heq : (fun x => (parentBenchmark i (r/x)-1)/x) =ᶠ[𝓝 b]
      (fun x => ((r/x)*parentBenchmark i (r/x)-r/x)/r) := by
    filter_upwards [Ioi_mem_nhds hb] with x hx
    change 0 < x at hx
    field_simp [ne_of_gt hr,ne_of_gt hx]
  have hh := h.congr_of_eventuallyEq heq
  convert! hh using 1
  simp only [zero_mul,mul_one,zero_sub]
  field_simp

theorem omitted_lower_deviation {r x : ℝ} (hx : 0 < x) (homit : r-x < 2*x) :
    benchmark .even (r/x-1)-1 = -1 := by
  have hs : r/x-1 ≤ 2 := by
    have hd : r/x < 3 := (div_lt_iff₀ hx).mpr (by linarith)
    linarith
  rw [benchmark_even_below_two hs]
  ring

end NumberTheoryLean.ReferenceDifferentiation



namespace NumberTheoryLean.ReferenceAdmission

open _root_.Finset
open FinitePathGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass

def childAdmitted : Side → ℝ → ℝ → Prop
  | .even,_,_ => True
  | .odd,r,x => max (2*x) (x+2) ≤ r-x

noncomputable def admitted (w : ℝ) : Side → ℝ → List ℕ → Prop
  | _,_,[] => True
  | i,r,p::ps => childAdmitted i r (primeExponent w p) ∧ admitted w i.flip (r-primeExponent w p) ps

def endSide : Side → List ℕ → Side
  | i,[] => i
  | i,_::ps => endSide i.flip ps

theorem gap_append (w r : ℝ) (ps qs : List ℕ) :
    primeFinalGap w r (ps++qs)=primeFinalGap w (primeFinalGap w r ps) qs := by
  induction ps generalizing r with
  | nil => rfl
  | cons p ps ih => exact ih (r-primeExponent w p)

theorem endSide_append (i : Side) (ps qs : List ℕ) : endSide i (ps++qs)=endSide (endSide i ps) qs := by
  induction ps generalizing i with
  | nil => rfl
  | cons p ps ih => exact ih i.flip

theorem admitted_append (w r : ℝ) (i : Side) (ps qs : List ℕ) :
    admitted w i r (ps++qs) ↔ admitted w i r ps ∧ admitted w (endSide i ps) (primeFinalGap w r ps) qs := by
  induction ps generalizing i r with
  | nil => simp only [List.nil_append,admitted,primeFinalGap,endSide,true_and]
  | cons p ps ih =>
    simp only [List.cons_append,admitted,endSide,primeFinalGap,ih,and_assoc]

noncomputable def FirstOmitted (w : ℝ) (i : Side) (r : ℝ) (ps : List ℕ) : Prop :=
  ∃ pre : List ℕ,∃ p : ℕ,ps=pre++[p] ∧ admitted w i r pre ∧
    ¬childAdmitted (endSide i pre) (primeFinalGap w r pre) (primeExponent w p)

theorem firstOmitted_not_admitted {w r : ℝ} {i : Side} {ps : List ℕ}
    (hp : FirstOmitted w i r ps) : ¬admitted w i r ps := by
  rcases hp with ⟨pre,p,rfl,hpre,hfail⟩
  rw [admitted_append]
  intro h
  exact hfail h.2.1

theorem exists_first_omitted_prefix {w r : ℝ} {i : Side} {ps : List ℕ}
    (hp : ¬admitted w i r ps) :
    ∃ pre suf : List ℕ,ps=pre++suf ∧ FirstOmitted w i r pre := by
  induction ps generalizing i r with
  | nil => exact False.elim (hp trivial)
  | cons p ps ih =>
    by_cases hchild : childAdmitted i r (primeExponent w p)
    · have ht : ¬admitted w i.flip (r-primeExponent w p) ps := fun h => hp ⟨hchild,h⟩
      obtain ⟨pre,suf,he,hfirst⟩ := ih ht
      rcases hfirst with ⟨pre',q,hpre',ha,hbad⟩
      refine ⟨p::pre,suf,by rw [List.cons_append,he],?_⟩
      refine ⟨p::pre',q,by rw [List.cons_append,hpre'],⟨hchild,ha⟩,?_⟩
      exact hbad
    · exact ⟨[p],ps,rfl,[],p,rfl,trivial,hchild⟩

theorem firstOmitted_boundary_gap {w r : ℝ} {i : Side} {ps : List ℕ}
    (hp : FirstOmitted w i r ps) (hupper : ∀ p ∈ ps,primeExponent w p ≤ 2) :
    primeFinalGap w r ps < 4 := by
  rcases hp with ⟨pre,p,rfl,_hpre,hfail⟩
  have hp2 : primeExponent w p ≤ 2 := hupper p (by simp)
  rw [gap_append]
  change primeFinalGap w r pre-primeExponent w p < 4
  cases he : endSide i pre with
  | even =>
    simp only [he,childAdmitted] at hfail
    exact False.elim (hfail trivial)
  | odd =>
    rw [he] at hfail
    change ¬max (2*primeExponent w p) (primeExponent w p+2) ≤ primeFinalGap w r pre-primeExponent w p at hfail
    have hmax : max (2*primeExponent w p) (primeExponent w p+2)=primeExponent w p+2 :=
      max_eq_right (by linarith)
    rw [hmax] at hfail
    linarith

theorem gap_lower_by_length {w r : ℝ} {ps : List ℕ}
    (hupper : ∀ p ∈ ps,primeExponent w p ≤ 2) :
    r-2*(ps.length:ℝ) ≤ primeFinalGap w r ps := by
  induction ps generalizing r with
  | nil => simp [primeFinalGap]
  | cons p ps ih =>
    have hp := hupper p (by simp)
    have ht := ih (r:=r-primeExponent w p) (fun q hq => hupper q (by simp [hq]))
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,primeFinalGap]
    linarith

theorem firstOmitted_boundary_length {w r : ℝ} {i : Side} {ps : List ℕ}
    (hp : FirstOmitted w i r ps) (hupper : ∀ p ∈ ps,primeExponent w p ≤ 2) :
    (r-4)/2 < (ps.length:ℝ) := by
  have hg := firstOmitted_boundary_gap hp hupper
  have hl := gap_lower_by_length (r:=r) hupper
  linarith

noncomputable def referencePrefixes (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : Finset (List ℕ) := by
  classical
  exact (decreasingPrefixes P).filter (admitted w i r)

noncomputable def firstOmissions (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : Finset (List ℕ) := by
  classical
  exact (decreasingPrefixes P).filter (FirstOmitted w i r)

noncomputable def referencePolynomial (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : ℝ :=
  ∑ ps ∈ referencePrefixes w P i r,(-1:ℝ)^ps.length*prefixWeight ps

noncomputable def boundaryPrimes (w : ℝ) : Finset ℕ := primesBetween w (w^(2:ℝ))

theorem boundary_prime_exponent_upper {w : ℝ} (hw : 1 < w) {p : ℕ} (hp : p ∈ boundaryPrimes w) :
    primeExponent w p ≤ 2 := by
  obtain ⟨hpp,_⟩ := Finset.mem_filter.mp hp
  obtain ⟨hfloor,hprime⟩ := Nat.mem_primesLE.mp hpp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  apply (exponent_le_iff hw hp0).mpr
  exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) 2).le).mp hfloor

theorem actual_first_omission_length {w r : ℝ} (hw : 1 < w) (i : Side) {ps : List ℕ}
    (hp : ps ∈ firstOmissions w (boundaryPrimes w) i r) : (r-4)/2 < (ps.length:ℝ) := by
  classical
  obtain ⟨hfamily,hfirst⟩ := Finset.mem_filter.mp hp
  have hmem := (mem_decreasingPrefixes.mp hfamily).2
  exact firstOmitted_boundary_length hfirst (fun p hp => boundary_prime_exponent_upper hw (hmem p hp))

end NumberTheoryLean.ReferenceAdmission


section

open _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission

noncomputable def upperCutoff : Side → ℝ → ℝ → ℝ
  | .even,_,b => max 1 (min 2 b)
  | .odd,r,b => max 1 (min (min 2 b) ((r-2)/2))

theorem upperCutoff_bounds (i : Side) (r b : ℝ) : 1 ≤ upperCutoff i r b ∧ upperCutoff i r b ≤ 2 := by
  cases i
  · exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  · exact ⟨le_max_left _ _,max_le (by norm_num) ((min_le_left _ _).trans (min_le_left _ _))⟩

theorem upperCutoff_continuous (i : Side) :
    Continuous (fun p : ℝ×ℝ => upperCutoff i p.1 p.2) := by
  cases i <;> unfold upperCutoff <;> fun_prop

theorem upperCutoff_odd_small {r b : ℝ} (hr : r ≤ 4) : upperCutoff .odd r b=1 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem upperCutoff_low {i : Side} {r b : ℝ} (hb : b ≤ 1) : upperCutoff i r b=1 := by
  cases i
  · exact max_eq_left ((min_le_right _ _).trans hb)
  · exact max_eq_left ((min_le_left _ _).trans ((min_le_right _ _).trans hb))

theorem strong_gate_below_two {r x : ℝ} (hx : x ≤ 2) :
    childAdmitted .odd r x ↔ x ≤ (r-2)/2 := by
  change max (2*x) (x+2) ≤ r-x ↔ x ≤ (r-2)/2
  rw [max_eq_right (by linarith : 2*x ≤ x+2)]
  constructor <;> intro h <;> linarith

theorem le_clipped_upper {x t : ℝ} (hx : 1 < x) : x ≤ max 1 t ↔ x ≤ t := by
  rw [le_max_iff]
  exact or_iff_right (not_le_of_gt hx)

theorem mem_upperCutoff (i : Side) (r b x : ℝ) :
    x ∈ Ioc 1 (upperCutoff i r b) ↔
      1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ childAdmitted i r x := by
  constructor
  · intro hx
    cases i with
    | even =>
      have h : x ≤ min 2 b := (le_clipped_upper hx.1).mp hx.2
      exact ⟨hx.1,(le_min_iff.mp h).1,(le_min_iff.mp h).2,trivial⟩
    | odd =>
      have h : x ≤ min (min 2 b) ((r-2)/2) := (le_clipped_upper hx.1).mp hx.2
      obtain ⟨hb,hgate⟩ := le_min_iff.mp h
      obtain ⟨hx2,hxb⟩ := le_min_iff.mp hb
      exact ⟨hx.1,hx2,hxb,(strong_gate_below_two hx2).mpr hgate⟩
  · rintro ⟨hx,hx2,hxb,hgate⟩
    refine ⟨hx,?_⟩
    cases i with
    | even => exact (le_clipped_upper hx).mpr (le_min hx2 hxb)
    | odd => exact (le_clipped_upper hx).mpr (le_min (le_min hx2 hxb) ((strong_gate_below_two hx2).mp hgate))

end ErdosContinuousBoundary

end


namespace NumberTheoryLean.ReferenceCancellation

open _root_.MeasureTheory _root_.Set
open FinitePathGeometry LinearSieveFunctions BuchstabBridge ReferenceBenchmarkDecay
open ReferenceDifferentiation ReferenceAdmission

theorem parent_domain_mono (i : Side) {s t : ℝ} (hs : ParentDomain i s) (hst : s ≤ t) :
    ParentDomain i t := by cases i <;> simp only [ParentDomain] at hs ⊢ <;> linarith

theorem positive_gap_of_parent_domain (i : Side) {r b : ℝ} (hb : 0 < b)
    (hs : ParentDomain i (r/b)) : 0 < r := by
  have hrb : 0 < r/b := by cases i <;> simp only [ParentDomain] at hs <;> linarith
  exact ((div_pos_iff.mp hrb).resolve_right (by intro h; linarith [h.2])).1

theorem parent_domain_interval (i : Side) {r b x : ℝ} (hb : 2 ≤ b)
    (hs : ParentDomain i (r/b)) (hx : x ∈ Icc 2 b) : ParentDomain i (r/x) := by
  have hr := positive_gap_of_parent_domain i (by linarith : 0 < b) hs
  exact parent_domain_mono i hs (div_le_div_of_nonneg_left hr.le (by linarith [hx.1]) hx.2)

theorem prospective_integrand_continuousAt (i : Side) {r x : ℝ} (hx : 0 < x)
    (hs : ParentDomain i (r/x)) :
    ContinuousAt (fun t => (benchmark i.flip (r/t-1)-1)/t^2) x := by
  have hmap : ContinuousAt (fun t : ℝ => r/t-1) x :=
    (continuousAt_const.div continuousAt_id (ne_of_gt hx)).sub continuousAt_const
  have hchild : ContinuousAt (fun t => benchmark i.flip (r/t-1)) x := by
    cases i with
    | even =>
      have hF : ContinuousAt (F sieveA) (r/x-1) :=
        F_continuousAt sieveA (by change 1 < r/x at hs; linarith)
      exact hF.comp (f := fun t => r/t-1) hmap
    | odd => exact (f_continuous sieveA).continuousAt.comp hmap
  exact (hchild.sub continuousAt_const).div (continuousAt_id.pow 2) (pow_ne_zero 2 (ne_of_gt hx))

theorem prospective_interval_integrable (i : Side) {r b : ℝ} (hb : 2 ≤ b)
    (hs : ParentDomain i (r/b)) :
    IntervalIntegrable (fun x => (benchmark i.flip (r/x-1)-1)/x^2) volume 2 b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hb
  intro x hx
  exact (prospective_integrand_continuousAt i (by linarith [hx.1])
    (parent_domain_interval i hb hs hx)).continuousWithinAt

theorem continuous_reference_cancellation (i : Side) {r b : ℝ} (hb : 2 ≤ b)
    (hs : ParentDomain i (r/b)) :
    (parentBenchmark i (r/2)-1)/2-(parentBenchmark i (r/b)-1)/b-
      (∫ x in (2:ℝ)..b,(benchmark i.flip (r/x-1)-1)/x^2)=0 := by
  have hderiv : ∀ x ∈ uIcc 2 b,
      HasDerivAt (fun t => (parentBenchmark i (r/t)-1)/t)
        (-(benchmark i.flip (r/x-1)-1)/x^2) x := by
    intro x hx
    rw [uIcc_of_le hb] at hx
    exact reference_derivative i (by linarith [hx.1]) (parent_domain_interval i hb hs hx)
  have hint : IntervalIntegrable (fun x => -(benchmark i.flip (r/x-1)-1)/x^2) volume 2 b := by
    convert! (prospective_interval_integrable i hb hs).neg using 1
    funext x
    exact neg_div _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp_rw [neg_div] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem upper_admission_above_two {r x : ℝ} (hx : 2 ≤ x) :
    childAdmitted .odd r x ↔ 2*x ≤ r-x := by
  change max (2*x) (x+2) ≤ r-x ↔ 2*x ≤ r-x
  rw [max_eq_left (by linarith)]

theorem actual_omitted_deviation_above_two {r x : ℝ} (hx : 2 ≤ x)
    (homit : ¬childAdmitted .odd r x) :
    benchmark .even (r/x-1)-1 = -1 := by
  rw [upper_admission_above_two hx] at homit
  exact omitted_lower_deviation (by linarith) (lt_of_not_ge homit)

end NumberTheoryLean.ReferenceCancellation



namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem upperCutoff_b_lipschitz (i : Side) (r : ℝ) :
    LipschitzWith 1 (fun b => upperCutoff i r b) := by
  cases i with
  | even => exact (LipschitzWith.id.const_min (2:ℝ)).const_max 1
  | odd => exact ((LipschitzWith.id.const_min (2:ℝ)).min_const ((r-2)/2)).const_max 1

theorem upperCutoff_r_lipschitz (i : Side) (b : ℝ) :
    LipschitzWith 1 (fun r => upperCutoff i r b) := by
  cases i with
  | even =>
    apply LipschitzWith.of_dist_le_mul
    intro r s
    simp [upperCutoff]
  | odd =>
    have h : LipschitzWith 1 (fun r : ℝ => (r-2)/2) := by
      apply LipschitzWith.of_dist_le_mul
      intro r s
      simp only [Real.dist_eq,NNReal.coe_one,one_mul]
      have he : (r-2)/2-(s-2)/2=(r-s)/2 := by ring
      rw [he,abs_div]
      norm_num
    exact (h.const_min (min 2 b)).const_max 1

theorem upperCutoff_b_difference (i : Side) (r b c : ℝ) :
    |upperCutoff i r b-upperCutoff i r c| ≤ |b-c| := by
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using (upperCutoff_b_lipschitz i r).dist_le_mul b c

theorem upperCutoff_r_difference (i : Side) (b r s : ℝ) :
    |upperCutoff i r b-upperCutoff i s b| ≤ |r-s| := by
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using (upperCutoff_r_lipschitz i b).dist_le_mul r s

end ErdosContinuousBoundary



namespace NumberTheoryLean.ReferenceDeviationMonotonicity

open _root_.Filter _root_.Set
open scoped Topology
open FinitePathGeometry LinearSieveFunctions BuchstabBridge NormalizedDeficits
open DeficitFutureIntegrals DerivativeWeights ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation

theorem lower_deficit_antitone : Antitone lowerDeficit := by
  have htail : AntitoneOn lowerDeficit (Ici 2) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 2) lowerDeficit_continuous.continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      exact (lowerDeficit_hasDerivAt hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      change 2 < s at hs
      rw [(lowerDeficit_hasDerivAt hs).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (phiEven_pos (by linarith)).le) (sq_nonneg _)
  intro x y hxy
  by_cases hy : y ≤ 2
  · simp only [lowerDeficit,f_initial sieveA hy,f_initial sieveA (hxy.trans hy),sub_zero,le_refl]
  · by_cases hx : x ≤ 2
    · have hh := htail (show (2:ℝ) ∈ Ici 2 by norm_num) (le_of_not_ge hy) (le_of_not_ge hy)
      simpa only [lowerDeficit,f_initial sieveA hx,f_initial sieveA (le_refl (2:ℝ)),sub_zero] using hh
    · exact htail (le_of_not_ge hx) (le_of_not_ge hy) hxy

theorem upper_deficit_pos_positive {s : ℝ} (hs : 0 < s) : 0 < upperDeficit s := by
  by_cases hs1 : 1 ≤ s
  · exact (deficits_pos hs1).2
  · change 0 < F sieveA s-1
    rw [F_initial sieveA hs (by linarith)]
    have h : 1 < sieveA/s := (one_lt_div hs).mpr (by linarith [sieveA_gt_two])
    linarith

theorem upper_deficit_antitone : AntitoneOn upperDeficit (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro s hs
    exact ((F_continuousAt sieveA (ne_of_gt hs)).sub continuousAt_const).continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    exact ((F_hasDerivAt hs).sub_const 1).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    change deriv (fun t => F sieveA t-1) s ≤ 0
    rw [((F_hasDerivAt hs).sub_const 1).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (phiOdd_pos s).le) (sq_nonneg _)

theorem even_abs_deviation (s : ℝ) : |benchmark .even s-1| = lowerDeficit s := by
  have he : benchmark .even s-1 = -lowerDeficit s := by unfold benchmark lowerDeficit; ring
  rw [he,abs_neg,abs_of_nonneg (lowerDeficit_nonneg s)]

theorem odd_abs_deviation {s : ℝ} (hs : 0 < s) : |benchmark .odd s-1| = upperDeficit s :=
  abs_of_pos (upper_deficit_pos_positive hs)

theorem prospective_absolute_monotone (i : Side) {r u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v)
    (hs : ParentDomain i (r/v)) :
    MonotoneOn (fun x => |benchmark i.flip (r/x-1)-1|) (Icc u v) := by
  have hv : 2 ≤ v := hu.trans huv
  have hr := positive_gap_of_parent_domain i (by linarith : 0 < v) hs
  intro x hx y hy hxy
  have harg : r/y-1 ≤ r/x-1 := sub_le_sub_right
    (div_le_div_of_nonneg_left hr.le (by linarith [hx.1]) hxy) 1
  cases i with
  | even =>
    have hdx := parent_domain_interval .even hv hs ⟨hu.trans hx.1,hx.2⟩
    have hdy := parent_domain_interval .even hv hs ⟨hu.trans hy.1,hy.2⟩
    change 1 < r/x at hdx
    change 1 < r/y at hdy
    change |benchmark .odd (r/x-1)-1| ≤ |benchmark .odd (r/y-1)-1|
    rw [odd_abs_deviation (by linarith),odd_abs_deviation (by linarith)]
    exact upper_deficit_antitone (by change 0 < r/y-1; linarith) (by change 0 < r/x-1; linarith) harg
  | odd =>
    change |benchmark .even (r/x-1)-1| ≤ |benchmark .even (r/y-1)-1|
    rw [even_abs_deviation,even_abs_deviation]
    exact lower_deficit_antitone harg

theorem prospective_signed_monotone (i : Side) {r u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v)
    (hs : ParentDomain i (r/v)) :
    (i=.even → MonotoneOn (fun x => benchmark i.flip (r/x-1)-1) (Icc u v)) ∧
    (i=.odd → AntitoneOn (fun x => benchmark i.flip (r/x-1)-1) (Icc u v)) := by
  have hm := prospective_absolute_monotone i hu huv hs
  cases i with
  | even =>
    refine ⟨?_,by intro h; cases h⟩
    intro _ x hx y hy hxy
    have hp := hm hx hy hxy
    have hxD := parent_domain_interval .even (hu.trans huv) hs ⟨hu.trans hx.1,hx.2⟩
    have hyD := parent_domain_interval .even (hu.trans huv) hs ⟨hu.trans hy.1,hy.2⟩
    change 1 < r/x at hxD
    change 1 < r/y at hyD
    change benchmark .odd (r/x-1)-1 ≤ benchmark .odd (r/y-1)-1
    change |benchmark .odd (r/x-1)-1| ≤ |benchmark .odd (r/y-1)-1| at hp
    rw [odd_abs_deviation (by linarith),odd_abs_deviation (by linarith)] at hp
    exact hp
  | odd =>
    constructor
    · intro h
      cases h
    intro _ x hx y hy hxy
    have hp := hm hx hy hxy
    change |benchmark .even (r/x-1)-1| ≤ |benchmark .even (r/y-1)-1| at hp
    rw [even_abs_deviation,even_abs_deviation] at hp
    change f sieveA (r/y-1)-1 ≤ f sieveA (r/x-1)-1
    unfold lowerDeficit at hp
    linarith

end NumberTheoryLean.ReferenceDeviationMonotonicity



namespace NumberTheoryLean.ReferenceWeightDomination

open FinitePathGeometry LinearSieveFunctions BuchstabBridge NormalizedDeficits
open DeficitFutureIntegrals DerivativeWeights ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation
open ReferenceDeviationMonotonicity

theorem starting_parent_nonpos {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) :
    parentBenchmark .even s ≤ 0 := by
  rw [parent_even_eq_starting (by linarith)]
  unfold startingExtension
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos sieveA_pos.le (Real.log_nonpos (by linarith) (by linarith))) (by linarith)

theorem even_parent_le_one {s : ℝ} (hs : 1 < s) : parentBenchmark .even s ≤ 1 := by
  by_cases hs2 : 2 ≤ s
  · rw [parent_even_eq_ordinary hs2]
    have h := lowerDeficit_nonneg s
    change 0 ≤ 1-f sieveA s at h
    change f sieveA s ≤ 1
    linarith
  · exact (starting_parent_nonpos hs (le_of_lt (lt_of_not_ge hs2))).trans (by norm_num)

theorem even_parent_abs {s : ℝ} (hs : 1 < s) :
    |parentBenchmark .even s-1| = 1-parentBenchmark .even s := by
  rw [abs_of_nonpos (sub_nonpos.mpr (even_parent_le_one hs))]
  ring

theorem weight_deviation_identity (i : Side) {s : ℝ} (hs : ParentDomain i s) :
    weight i s = s*(|parentBenchmark i s-1|+|benchmark i.flip (s-1)-1|) := by
  cases i with
  | even =>
    change 1 < s at hs
    change phiEven s = s*(|parentBenchmark .even s-1|+|benchmark .odd (s-1)-1|)
    rw [even_parent_abs hs,odd_abs_deviation (by linarith)]
    by_cases hs2 : 2 ≤ s
    · rw [phiEven_eq_deficits hs2,parent_even_eq_ordinary hs2]
      rfl
    · have hsle : s ≤ 2 := le_of_lt (lt_of_not_ge hs2)
      rw [phiEven_initial hsle,parent_even_eq_starting (by linarith)]
      unfold evenInitial startingExtension upperDeficit
      rw [F_initial sieveA (by linarith) (by linarith)]
      field_simp
      ring
  | odd =>
    change 0 < s at hs
    change phiOdd s = s*(|benchmark .odd s-1|+|benchmark .even (s-1)-1|)
    rw [odd_abs_deviation hs,even_abs_deviation]
    by_cases hs1 : 1 ≤ s
    · exact phiOdd_eq_deficits hs1
    · rw [phiOdd_initial (by linarith)]
      unfold upperDeficit lowerDeficit
      rw [F_initial sieveA hs (by linarith),f_initial sieveA (by linarith)]
      field_simp
      ring

theorem valid_parent_domain {i : Side} {s : ℝ} (hs : Valid i s) : ParentDomain i s := by
  cases i <;> simp only [Valid,ParentDomain] at hs ⊢ <;> linarith

theorem source_deviation_sum {i : Side} {s : ℝ} (hs : Valid i s) :
    |parentBenchmark i s-1|+|benchmark i.flip (s-1)-1| ≤ 2*weight i s := by
  have hd := valid_parent_domain hs
  have hpos := valid_pos hs
  have he := weight_deviation_identity i hd
  have hs2 : (1/2:ℝ) ≤ s := by cases i <;> simp only [Valid] at hs <;> linarith
  have hsum : 0 ≤ |parentBenchmark i s-1|+|benchmark i.flip (s-1)-1| := by positivity
  nlinarith

theorem ordinary_deviation_le_parent (i : Side) {s : ℝ} (hs : ParentDomain i s) :
    |benchmark i s-1| ≤ |parentBenchmark i s-1| := by
  cases i with
  | odd => exact le_rfl
  | even =>
    change 1 < s at hs
    rw [even_abs_deviation,even_parent_abs hs]
    by_cases hs2 : 2 ≤ s
    · rw [parent_even_eq_ordinary hs2]
      exact le_rfl
    · have hsle := le_of_lt (lt_of_not_ge hs2)
      have h := starting_parent_nonpos hs hsle
      simp only [lowerDeficit,f_initial sieveA hsle,sub_zero]
      linarith

theorem benchmark_absolute_antitone (i : Side) {s t : ℝ} (hs : ParentDomain i s) (hst : s ≤ t) :
    |benchmark i t-1| ≤ |benchmark i s-1| := by
  cases i with
  | even => rw [even_abs_deviation,even_abs_deviation]; exact lower_deficit_antitone hst
  | odd =>
    change 0 < s at hs
    rw [odd_abs_deviation (hs.trans_le hst),odd_abs_deviation hs]
    exact upper_deficit_antitone hs (hs.trans_le hst) hst

theorem residual_deviations_bound (i : Side) {r b x : ℝ} (hb : 2 ≤ b)
    (hs : Valid i (r/b)) (hx : x ∈ Set.Icc 2 b) :
    |parentBenchmark i (r/b)-1|+|benchmark i (r/2)-1|+
      |benchmark i.flip (r/x-1)-1| ≤ 4*weight i (r/b) := by
  have hd := valid_parent_domain hs
  have hr := positive_gap_of_parent_domain i (by linarith : 0 < b) hd
  have hratio : r/b ≤ r/2 := div_le_div_of_nonneg_left hr.le (by norm_num) hb
  have hboundary := (benchmark_absolute_antitone i hd hratio).trans (ordinary_deviation_le_parent i hd)
  have hmono := prospective_absolute_monotone i (u := 2) le_rfl hb hd
  have hnext := hmono hx (show b ∈ Set.Icc 2 b from ⟨hb,le_rfl⟩) hx.2
  have hsum := source_deviation_sum hs
  have hn := abs_nonneg (benchmark i.flip (r/b-1)-1)
  linarith

end NumberTheoryLean.ReferenceWeightDomination



namespace NumberTheoryLean.ReferenceParentMonotonicity

open _root_.Set
open FinitePathGeometry LinearSieveFunctions BuchstabBridge NormalizedDeficits DerivativeWeights
open ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation ReferenceWeightDomination ReferenceDeviationMonotonicity

theorem even_parent_deficit_antitone : AntitoneOn (fun s => 1-parentBenchmark .even s) (Ioi 1) := by
  have hd : ∀ s : ℝ,1 < s → HasDerivAt (parentBenchmark .even)
      ((benchmark .odd (s-1)-parentBenchmark .even s)/s) s := by
    intro s hs
    exact hasDerivAt_of_mass (by linarith) (parent_mass_derivative .even hs)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 1)
  · intro s hs
    exact ((hd s hs).const_sub 1).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    exact ((hd s hs).const_sub 1).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    change 1 < s at hs
    rw [((hd s hs).const_sub 1).deriv]
    have hu := upper_deficit_pos_positive (s:=s-1) (by linarith)
    have he := even_parent_le_one hs
    have hnum : 0 ≤ benchmark .odd (s-1)-parentBenchmark .even s := by
      change 0 < F sieveA (s-1)-1 at hu
      change 0 ≤ F sieveA (s-1)-parentBenchmark .even s
      linarith
    exact neg_nonpos.mpr (div_nonneg hnum (by linarith))

theorem parent_absolute_antitone (i : Side) {s t : ℝ} (hs : ParentDomain i s) (hst : s ≤ t) :
    |parentBenchmark i t-1| ≤ |parentBenchmark i s-1| := by
  cases i with
  | even =>
    change 1 < s at hs
    rw [even_parent_abs (hs.trans_le hst),even_parent_abs hs]
    exact even_parent_deficit_antitone hs (hs.trans_le hst) hst
  | odd => exact benchmark_absolute_antitone .odd hs hst

theorem interval_deviations_bound (i : Side) {r a b x : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hs : Valid i (r/b)) (hx : x ∈ Icc a b) :
    |parentBenchmark i (r/a)-1|+|parentBenchmark i (r/b)-1|+
      |benchmark i.flip (r/x-1)-1| ≤ 4*weight i (r/b) := by
  have hb : 2 ≤ b := ha.trans hab
  have hd := valid_parent_domain hs
  have hr := positive_gap_of_parent_domain i (by linarith : 0 < b) hd
  have hrat : r/b ≤ r/a := div_le_div_of_nonneg_left hr.le (by linarith) hab
  have hleft := parent_absolute_antitone i hd hrat
  have hmono := prospective_absolute_monotone i (u:=2) le_rfl hb hd
  have hnext := hmono ⟨ha.trans hx.1,hx.2⟩ ⟨hb,le_rfl⟩ hx.2
  have hsum := source_deviation_sum hs
  linarith [abs_nonneg (benchmark i.flip (r/b-1)-1)]

end NumberTheoryLean.ReferenceParentMonotonicity



namespace NumberTheoryLean.ReferenceWeightedQuadrature

attribute [local instance] Classical.propDecidable
open _root_.MeasureTheory _root_.Set _root_.Finset
open FinitePathGeometry ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation
open ReferenceDeviationMonotonicity ReferenceWeightDomination ActualPrimeQuadrature
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem source_weighted_quadrature : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ u v b r : ℝ,2 ≤ u → u ≤ v → v ≤ b → ∀ i : Side,
      Valid i (r/b) → ∀ J : Set ℝ,J.OrdConnected → J ⊆ Icc u v →
        |(∑ p ∈ Nat.primesLE ⌊w^v⌋₊,if primeExponent w p ∈ J then
          (p:ℝ)⁻¹*(benchmark i.flip (r/primeExponent w p-1)-1)/primeExponent w p else 0)-
          ∫ x in J,(benchmark i.flip (r/x-1)-1)/x^2| ≤
          (C*weight i (r/b)/u)*Real.exp (-c*Real.sqrt (u*Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := actual_weighted_prime_quadrature
  refine ⟨c,4*C,w₀,hc,by positivity,hw₀,?_⟩
  intro w hw u v b r hu huv hvb i hs J hJ hsub
  have hb : 2 ≤ b := hu.trans (huv.trans hvb)
  have hparent := valid_parent_domain hs
  have hvdom : ParentDomain i (r/v) := parent_domain_interval i hb hparent ⟨hu.trans huv,hvb⟩
  let g : ℝ → ℝ := fun x => benchmark i.flip (r/x-1)-1
  have hmono : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v) := by
    have hm := prospective_signed_monotone i hu huv hvdom
    cases i with
    | even => exact Or.inl (hm.1 rfl)
    | odd => exact Or.inr (hm.2 rfl)
  have hbound : ∀ x ∈ Icc u v,|g x| ≤ 4*weight i (r/b) := by
    intro x hx
    have hh := residual_deviations_bound i hb hs ⟨hu.trans hx.1,hx.2.trans hvb⟩
    have hp := abs_nonneg (parentBenchmark i (r/b)-1)
    have hbnd := abs_nonneg (benchmark i (r/2)-1)
    dsimp only [g]
    linarith
  have hq := h w hw u v hu huv (4*weight i (r/b)) (by have hp := weight_pos hs; positivity)
    g hmono hbound J hJ hsub
  calc
    _ ≤ (C*(4*weight i (r/b))/u)*Real.exp (-c*Real.sqrt (u*Real.log w)) := hq
    _ = _ := by ring

end NumberTheoryLean.ReferenceWeightedQuadrature


end Erdos970

end OAI
