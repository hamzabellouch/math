import OAI.Probability.TraceReconstruction.Oracles

namespace OAI

/-!
# InitialOverlap

Literal periods, count overlap, initial low/high energies, genuine densities, and centered moment bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem primitive_one_add_score_nonneg {q : ℝ} (hq : q ∈ Set.Ioo 0 1)
    (a : PrimitiveMark) : 0 ≤ 1 + primitiveScore q a := by
  have hq1 : 1 ≤ 1/q := (le_div_iff₀ hq.1).mpr (by simpa using hq.2.le)
  have hq0 := hq.1
  fin_cases a <;> norm_num [primitiveScore] <;> linarith [show 2/q=2*(1/q) by ring]

/-- Exact conditional law of the genuine periodic primitive observation. -/
theorem conditionalPeriodLaw_density {u m l : ℕ} (hl : l ≤ u*m)
    {q : ℝ} (hq : q ∈ Set.Ioo 0 1) (off : Fin u → Fin m) (x : Fin l → PrimitiveMark) :
    (conditionalPrimitiveLaw hl q hq (defectTypes (periodSlot off))).mass x =
      ((primitiveMarkLaw q hq false).product l).mass x *
        averagedDensity (uniformSubsetLaw l (by simpa using hl))
          (defectAtRank (Finset.univ.image (periodSlot off))) (primitiveScore q) x := by
  rw [conditionalPrimitiveLaw_density]
  congr 2
  funext S
  exact defectTypes_atRank (periodSlot off) S

/-- Absolute constant in the conditional second-moment exponent. -/
def primitivePeriodConstant : ℝ := 36*rankSchurConstant^2

theorem primitivePeriodConstant_nonneg : 0 ≤ primitivePeriodConstant := by
  unfold primitivePeriodConstant
  positivity

theorem conditionalPeriod_second_moment {u m l : ℕ} (hl : l ≤ u*m)
    (hm : 32 ≤ m) (hum : u ≤ m) {q θ : ℝ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    ((primitiveMarkLaw q ⟨hq.1, by linarith [hq.2]⟩ false).product l).expect (fun x =>
      averagedDensity (uniformSubsetLaw l (by simpa using hl))
        (defectAtRank (Finset.univ.image (periodSlot off))) (primitiveScore q) x ^ 2) ≤
      2*Real.exp (primitivePeriodConstant/q^4 * ((u:ℝ)/m)) := by
  have hqi : q ∈ Set.Ioo 0 1 := ⟨hq.1, by linarith [hq.2]⟩
  let P := primitiveMarkLaw q hqi false
  have hZ : P.expect (primitiveScore q) = 0 := primitive_score_centered hqi
  have h := period_density_second_moment P (primitiveScore q) hZ hl hm hum hq hθ hmean hv off hoff hdiff
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  have hv0 : 0 ≤ P.expect (fun a => primitiveScore q a ^ 2) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  have hv1 : P.expect (fun a => primitiveScore q a ^ 2) ≤ 2/q :=
    primitive_score_variance_le hqi
  have hsq : (P.expect (fun a => primitiveScore q a ^ 2))^2 ≤ (2/q)^2 :=
    pow_le_pow_left₀ hv0 hv1 2
  calc
    _ ≤ (2/q)^2*(3*rankSchurConstant/q)^2*((u:ℝ)/m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) (by positivity)
    _ = _ := by unfold primitivePeriodConstant; field_simp; ring

/-- Association converts the two actual conditional period-laws into common
mass. The two original block totals may differ; only the retained count agrees. -/
theorem conditionalPeriod_overlap {u v m l : ℕ}
    (hl : l ≤ u*m) (hl' : l ≤ v*m) (hm : 32 ≤ m) (hum : u ≤ m) (hvm : v ≤ m)
    {q θ θ' : ℝ} (hq : q ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-q^2) (1-q^2/4))
    (hθ' : θ' ∈ Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hmean' : ((v*m:ℕ):ℝ)*θ'=l)
    (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (hv' : 1 ≤ ((v*m:ℕ):ℝ)*θ'*(1-θ'))
    (off : Fin u → Fin m) (off' : Fin v → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hoff' : ∀ j, |((off' j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (hdiff' : ∀ j k, |((off' j).val:ℝ)-(off' k).val| ≤ 2) :
    Real.exp (-(primitivePeriodConstant/q^4*((u:ℝ)/m+(v:ℝ)/m)))/128 ≤
      FiniteLaw.overlap
        (conditionalPrimitiveLaw hl q ⟨hq.1, by linarith [hq.2]⟩ (defectTypes (periodSlot off)))
        (conditionalPrimitiveLaw hl' q ⟨hq.1, by linarith [hq.2]⟩ (defectTypes (periodSlot off'))) := by
  have hqi : q ∈ Set.Ioo 0 1 := ⟨hq.1, by linarith [hq.2]⟩
  let P := primitiveMarkLaw q hqi false
  let R := uniformSubsetLaw l (show l≤Fintype.card (Fin (u*m)) by simpa using hl)
  let S := uniformSubsetLaw l (show l≤Fintype.card (Fin (v*m)) by simpa using hl')
  let f := defectAtRank (l:=l) (Finset.univ.image (periodSlot off))
  let g := defectAtRank (l:=l) (Finset.univ.image (periodSlot off'))
  let G := averagedDensity R f (primitiveScore q)
  let H := averagedDensity S g (primitiveScore q)
  let A := primitivePeriodConstant/q^4*((u:ℝ)/m)
  let B := primitivePeriodConstant/q^4*((v:ℝ)/m)
  have h1 := conditionalPeriod_second_moment hl hm hum hq hθ hmean hv off hoff hdiff
  have h2 := conditionalPeriod_second_moment hl' hm hvm hq hθ' hmean' hv' off' hoff' hdiff'
  change (P.product l).expect (fun x => G x^2) ≤ 2*Real.exp A at h1
  change (P.product l).expect (fun x => H x^2) ≤ 2*Real.exp B at h2
  have ha := averagedDensity_overlap P R S (primitiveScore q)
    (primitive_score_centered hqi) (primitive_one_add_score_nonneg hqi) f g
  change 1/32 ≤ (P.product l).expect (fun x => min (G x) (H x)) *
    (P.product l).expect (fun x => G x^2) * (P.product l).expect (fun x => H x^2) at ha
  have hG : ∀x, 0 ≤ G x := averagedDensity_nonneg R f _ (primitive_one_add_score_nonneg hqi)
  have hH : ∀x, 0 ≤ H x := averagedDensity_nonneg S g _ (primitive_one_add_score_nonneg hqi)
  have ho : 0 ≤ (P.product l).expect (fun x => min (G x) (H x)) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg ((P.product l).nonneg _) (le_min (hG x) (hH x)))
  have hm2 : 0 ≤ (P.product l).expect (fun x => H x^2) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg ((P.product l).nonneg _) (sq_nonneg _))
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 ho) hm2
  have hc := mul_le_mul_of_nonneg_left h2 (mul_nonneg ho (by positivity : 0≤2*Real.exp A))
  have he : (P.product l).expect (fun x => min (G x) (H x)) =
      FiniteLaw.overlap
        (conditionalPrimitiveLaw hl q hqi (defectTypes (periodSlot off)))
        (conditionalPrimitiveLaw hl' q hqi (defectTypes (periodSlot off'))) := by
    unfold FiniteLaw.expect FiniteLaw.overlap
    apply Finset.sum_congr rfl
    intro x _
    rw [conditionalPeriodLaw_density,conditionalPeriodLaw_density]
    exact mul_min_of_nonneg _ _ ((P.product l).nonneg x)
  rw [← he]
  have hd : Real.exp (-(A+B))/128 ≤ (P.product l).expect (fun x => min (G x) (H x)) := by
    have hx : (1:ℝ)/32 ≤ (P.product l).expect (fun x => min (G x) (H x)) * (4*Real.exp (A+B)) := by
      calc
        _ ≤ _ := ha.trans (hb.trans hc)
        _ = _ := by rw [Real.exp_add]; ring
    have hp : 0 < 4*Real.exp (A+B) := by positivity
    calc
      _ = ((1:ℝ)/32)/(4*Real.exp (A+B)) := by rw [Real.exp_neg]; ring
      _ ≤ _ := (div_le_iff₀ hp).2 hx
  convert hd using 1
  congr 2
  dsimp [A,B]
  ring

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The common count window is admissible for every genuine period count in
the base case. All hypotheses are elementary size/location inequalities. -/
theorem primitive_count_window {q θ : ℝ} {m n l : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ))
    (hnlo : q*(m:ℝ)^2/2 ≤ (n:ℝ)) (hnhi : (n:ℝ) ≤ (m:ℝ)^2)
    (hmean : (n:ℝ)*θ=l)
    (hdev : |(l:ℝ)-(n:ℝ)*(1-q^2/2)| ≤ 2*(m:ℝ)) :
    θ ∈ Set.Icc (1-q^2) (1-q^2/4) ∧
    1 ≤ (n:ℝ)*θ*(1-θ) ∧
    Real.sqrt ((n:ℝ)*θ*(1-θ)) ≤ (m:ℝ) ∧
    ((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 / ((n:ℝ)*(1-q^2/2)*(q^2/2)) ≤ 32/q^3 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hq0 := hq.1
  have hq2 : q^2 ≤ 1/4 := by nlinarith [hq.2]
  have hq2p : 0 < q^2 := sq_pos_of_pos hq0
  have hq3 : 0 < q^3 := pow_pos hq0 3
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (by have hq0 := hq.1; positivity) hnlo
  have hsize : 8*(m:ℝ) ≤ (n:ℝ)*q^2 := by
    have ha := mul_le_mul_of_nonneg_right hnlo hq2p.le
    have hb := mul_le_mul_of_nonneg_right hscale hm0.le
    nlinarith
  have hθ : θ ∈ Set.Icc (1-q^2) (1-q^2/4) := by
    have hl := (abs_le.mp hdev).1
    have hr := (abs_le.mp hdev).2
    rw [←hmean] at hl hr
    constructor
    · nlinarith
    · nlinarith
  have ht0 : 0 < θ := by nlinarith [hθ.1]
  have ht1 : θ < 1 := by nlinarith [hθ.2]
  have hvlo : (n:ℝ)*q^2/8 ≤ (n:ℝ)*θ*(1-θ) := by
    have hlow : (1:ℝ)/2 ≤ θ := by linarith [hθ.1]
    have hhigh : q^2/4 ≤ 1-θ := by linarith [hθ.2]
    have hp := mul_le_mul hlow hhigh (by positivity : (0:ℝ)≤q^2/4) ht0.le
    have hp' := mul_le_mul_of_nonneg_left hp hn0.le
    nlinarith
  have hv : 1 ≤ (n:ℝ)*θ*(1-θ) := by
    have hm32 : (32:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hvhi : (n:ℝ)*θ*(1-θ) ≤ (m:ℝ)^2 := by
    have hprod : θ*(1-θ) ≤ 1 := by nlinarith [sq_nonneg θ]
    have hh := mul_le_mul_of_nonneg_left hprod hn0.le
    nlinarith
  have hsqrt : Real.sqrt ((n:ℝ)*θ*(1-θ)) ≤ (m:ℝ) := by
    exact (Real.sqrt_le_iff).mpr ⟨hm0.le,hvhi⟩
  have hp0 : 0 < 1-q^2/2 := by linarith
  have hden0 : 0 < (n:ℝ)*(1-q^2/2)*(q^2/2) := by positivity
  have hden : q^3*(m:ℝ)^2/8 ≤ (n:ℝ)*(1-q^2/2)*(q^2/2) := by
    have ha := mul_le_mul_of_nonneg_right hnlo hq2p.le
    have hb := mul_le_mul_of_nonneg_right (show (1:ℝ)/2≤1-q^2/2 by linarith)
      (mul_nonneg hn0.le (by positivity : (0:ℝ)≤q^2/2))
    nlinarith
  have hdev2 : ((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 ≤ 4*(m:ℝ)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hdev 2
    rw [sq_abs] at h
    nlinarith
  have hquot : ((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 /
      ((n:ℝ)*(1-q^2/2)*(q^2/2)) ≤ 32/q^3 := by
    apply (div_le_div_iff₀ hden0 hq3).mpr
    have hh := mul_le_mul_of_nonneg_right hdev2 hq3.le
    nlinarith
  exact ⟨hθ,hv,hsqrt,hquot⟩

/-- Genuine binomial count mass in the window, uniformly in the vanishing
working deletion rate, with an absolute explicit exponential cost. -/
theorem primitive_count_mass_lower {q : ℝ} {m n l : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ))
    (hnlo : q*(m:ℝ)^2/2 ≤ (n:ℝ)) (hnhi : (n:ℝ) ≤ (m:ℝ)^2)
    (hdev : |(l:ℝ)-(n:ℝ)*(1-q^2/2)| ≤ 2*(m:ℝ)) :
    Real.exp (-32/q^3)/(12*(m:ℝ)) ≤ binomialMass n (1-primitiveErasure q) l := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (by have hq0 := hq.1; positivity) hnlo
  let θ : ℝ := (l:ℝ)/n
  have hmean : (n:ℝ)*θ=l := by dsimp [θ]; field_simp
  obtain ⟨ht,hv,hsqrt,hquot⟩ := primitive_count_window hq hm hscale hnlo hnhi hmean hdev
  have hq2 : q^2 ≤ 1/4 := by nlinarith [hq.1,hq.2]
  have hq2p : 0 < q^2 := sq_pos_of_pos hq.1
  have ht' : θ ∈ Set.Ioo 0 1 := ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hp : 1-q^2/2 ∈ Set.Ioo 0 1 := ⟨by linarith, by linarith⟩
  have hl : l ≤ n := by
    have h := mul_le_mul_of_nonneg_left ht'.2.le hn0.le
    rw [hmean,mul_one] at h
    exact_mod_cast h
  have hmass := binomialMass_near_mean_lower n l ht' hp hl hmean hv
  have hden : 0 < 12*Real.sqrt ((n:ℝ)*θ*(1-θ)) := by positivity
  have hexp : Real.exp (-32/q^3) ≤ Real.exp (-((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 /
      ((n:ℝ)*(1-q^2/2)*(1-(1-q^2/2)))) := by
    apply Real.exp_le_exp.mpr
    have he : 1-(1-q^2/2)=q^2/2 := by ring
    rw [he]
    simpa only [neg_div] using neg_le_neg hquot
  calc
    _ ≤ Real.exp (-((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 /
        ((n:ℝ)*(1-q^2/2)*(1-(1-q^2/2)))) / (12*Real.sqrt ((n:ℝ)*θ*(1-θ))) := by
      exact div_le_div₀ (Real.exp_nonneg _) hexp hden (by nlinarith)
    _ ≤ _ := by simpa only [primitiveErasure] using hmass


/-- The actual base count, with no redefinition of the working channel. -/
def initialSideCount (q : ℝ) (m : ℕ) : ℕ := ⌊q*(m:ℝ)⌋₊

theorem initialSideCount_bounds {q : ℝ} {m : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ)) :
    q*(m:ℝ)/2 ≤ (initialSideCount q m:ℝ) ∧
    (initialSideCount q m:ℝ) ≤ q*(m:ℝ) ∧ initialSideCount q m+1 ≤ m := by
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hm32 : (32:ℝ) ≤ m := by exact_mod_cast hm
  have hq0 := hq.1
  have hq2 : q^2 ≤ 1 := by nlinarith [hq.2]
  have hqm : 2 ≤ q*(m:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hq2 (mul_nonneg hq0.le hm0)
    nlinarith
  have hlow := Nat.lt_floor_add_one (q*(m:ℝ))
  have hhigh := Nat.floor_le (mul_nonneg hq0.le hm0)
  change q*(m:ℝ) < (initialSideCount q m:ℝ)+1 at hlow
  change (initialSideCount q m:ℝ) ≤ q*(m:ℝ) at hhigh
  refine ⟨by linarith,hhigh,?_⟩
  have hh := mul_le_mul_of_nonneg_right hq.2 hm0
  have : (initialSideCount q m:ℝ)+1 ≤ (m:ℝ) := by linarith
  exact_mod_cast this

/-- An injective enumeration of m common integer counts; no asymptotic
cardinality argument is left implicit. -/
def commonCountIndex {m : ℕ} (k : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) (j : Fin m) :
    Fin ((k+1)*m+1) :=
  ⟨⌊p*((k*m:ℕ):ℝ)⌋₊+j.val,by
    have ha : (⌊p*((k*m:ℕ):ℝ)⌋₊:ℝ) ≤ ((k*m:ℕ):ℝ) := by
      exact (Nat.floor_le (mul_nonneg hp.1 (Nat.cast_nonneg _))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg _) hp.2)
    have ha' : ⌊p*((k*m:ℕ):ℝ)⌋₊ ≤ k*m := by exact_mod_cast ha
    have hj := j.isLt
    rw [Nat.add_mul,one_mul]
    omega⟩

theorem commonCountIndex_injective {m : ℕ} (k : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    Function.Injective (commonCountIndex (m:=m) k p hp) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [commonCountIndex,Nat.add_left_cancel_iff] at hv
  exact Fin.ext hv

theorem commonCountIndex_deviation {m : ℕ} (k : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (j : Fin m) :
    |((commonCountIndex k p hp j).val:ℝ)-((k*m:ℕ):ℝ)*p| ≤ 2*(m:ℝ) ∧
    |((commonCountIndex k p hp j).val:ℝ)-(((k+1)*m:ℕ):ℝ)*p| ≤ 2*(m:ℝ) := by
  have hm : (1:ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_of_lt (Nat.zero_lt_of_lt j.isLt))
  have hj : (j.val:ℝ) < m := by exact_mod_cast j.isLt
  have hj0 : (0:ℝ) ≤ j.val := Nat.cast_nonneg _
  have ha := Nat.floor_le (mul_nonneg hp.1 (Nat.cast_nonneg (k*m)))
  have hb := Nat.lt_floor_add_one (p*((k*m:ℕ):ℝ))
  have hp0 := hp.1
  have hp1 := hp.2
  have hmp : 0 ≤ (m:ℝ)*p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hmp' : (m:ℝ)*p ≤ m := mul_le_of_le_one_right (Nat.cast_nonneg _) hp1
  change |((⌊p*((k*m:ℕ):ℝ)⌋₊+j.val:ℕ):ℝ)-((k*m:ℕ):ℝ)*p| ≤ _ ∧
    |((⌊p*((k*m:ℕ):ℝ)⌋₊+j.val:ℕ):ℝ)-(((k+1)*m:ℕ):ℝ)*p| ≤ _
  have hn : (((k+1)*m:ℕ):ℝ)=((k*m:ℕ):ℝ)+(m:ℝ) := by push_cast; ring
  rw [hn]
  push_cast
  constructor <;> apply abs_le.mpr <;> constructor <;> push_cast at ha hb <;> nlinarith

end TraceReconstruction



namespace TraceReconstruction
open scoped Classical

theorem ordinaryRun_replicate (n : ℕ) :
    (List.replicate n [false,true]).flatten = ordinaryRun n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ordinaryRun,ih]

/-- Unique primitive parsing identifies the rank model with the literal
period words in the manuscript, not just a law on unlabeled locations. -/
theorem primitive_period_word {m : ℕ} (off : Fin m) :
    (List.ofFn (fun j : Fin m => primitiveBlock (decide (j=off)))).flatten =
      initialPeriod m off.val := by
  induction m with
  | zero => exact Fin.elim0 off
  | succ m ih =>
    refine Fin.cases ?_ (fun d => ?_) off
    · simp [List.ofFn_succ,primitiveBlock,initialPeriod,ordinaryRun,ordinaryRun_replicate]
    · rw [List.ofFn_succ,List.flatten_cons]
      have hf : primitiveBlock (decide ((0:Fin (m+1))=d.succ))=[false,true] := by
        simp [primitiveBlock,Ne.symm (Fin.succ_ne_zero d)]
      rw [hf]
      simp only [Fin.succ_inj]
      rw [ih d]
      simp [initialPeriod,ordinaryRun,Nat.sub_sub,Nat.add_comm]

/-- Membership in the true periodic defect set is exactly the within-period
slot test, uniformly for all deterministic period types. -/
theorem periodSlot_range_iff {u m : ℕ} (off : Fin u → Fin m) (i : Fin u) (j : Fin m) :
    (⟨i.val*m+j.val,by
      have hi := Nat.mul_le_mul_right m (Nat.succ_le_of_lt i.isLt)
      have hj := j.isLt
      nlinarith⟩ : Fin (u*m)) ∈ Set.range (periodSlot off) ↔ j=off i := by
  constructor
  · rintro ⟨a,ha⟩
    have hval := congrArg Fin.val ha
    change a.val*m+(off a).val=i.val*m+j.val at hval
    have hm : 0 < m := Nat.zero_lt_of_lt j.isLt
    have hdiv := congrArg (fun k : ℕ => k/m) hval
    simp only [Nat.mul_comm _ m, Nat.mul_add_div hm, Nat.div_eq_of_lt (off a).isLt,
      Nat.div_eq_of_lt j.isLt,add_zero] at hdiv
    have hai : a=i := Fin.ext hdiv
    subst a
    apply Fin.ext
    omega
  · intro h
    refine ⟨i,?_⟩
    apply Fin.ext
    simp only [periodSlot]
    exact congrArg (fun k:Fin m => i.val*m+k.val) h.symm

/-- The simulator's actual primitive list is the unpadded source gadget. -/
theorem periodic_primitive_word {u m : ℕ} (off : Fin u → Fin m) :
    (((List.ofFn (defectTypes (periodSlot off))).map primitiveBlock).flatten) =
      periodString m u off := by
  rw [List.map_ofFn,List.ofFn_mul]
  rw [List.flatten_flatten,List.map_ofFn]
  unfold periodString
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  have he : (fun j:Fin m => primitiveBlock (defectTypes (periodSlot off)
      ⟨i.val*m+j.val,by
        have hi := Nat.mul_le_mul_right m (Nat.succ_le_of_lt i.isLt)
        have hj := j.isLt
        nlinarith⟩)) = fun j:Fin m => primitiveBlock (decide (j=off i)) := by
    funext j
    simp only [defectTypes,periodSlot_range_iff]
  rw [he]
  exact primitive_period_word (off i)

theorem periodString_constant {u m : ℕ} (off : Fin m) :
    periodString m u (fun _ => off) = pureAtomRun (initialPeriod m off.val) u := by
  simp only [periodString,List.ofFn_const,pureAtomRun]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem primitive_count_admissible {q : ℝ} {m n l : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ))
    (hnlo : q*(m:ℝ)^2/2 ≤ (n:ℝ)) (hnhi : (n:ℝ) ≤ (m:ℝ)^2)
    (hdev : |(l:ℝ)-(n:ℝ)*(1-q^2/2)| ≤ 2*(m:ℝ)) :
    ∃ θ : ℝ, l ≤ n ∧ θ ∈ Set.Icc (1-q^2) (1-q^2/4) ∧
      (n:ℝ)*θ=l ∧ 1 ≤ (n:ℝ)*θ*(1-θ) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hq0 := hq.1
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (by positivity) hnlo
  let θ : ℝ := (l:ℝ)/n
  have hmean : (n:ℝ)*θ=l := by dsimp [θ]; field_simp
  obtain ⟨ht,hv,_,_⟩ := primitive_count_window hq hm hscale hnlo hnhi hmean hdev
  have hl : l ≤ n := by
    have ht1 : θ ≤ 1 := by nlinarith [ht.2,sq_nonneg q]
    have hh := mul_le_mul_of_nonneg_left ht1 hn0.le
    rw [hmean,mul_one] at hh
    exact_mod_cast hh
  exact ⟨θ,hl,ht,hmean,hv⟩

/-- The common-mass constant depends only on the working deletion rate. -/
def initialOverlapLower (q : ℝ) : ℝ :=
  Real.exp (-(32+3*primitivePeriodConstant)/q^3)/1536

theorem initialOverlapLower_pos (q : ℝ) : 0 < initialOverlapLower q := by
  unfold initialOverlapLower
  positivity

theorem initialOverlapLower_lt_eighth {q : ℝ} (hq : 0 < q) :
    initialOverlapLower q < 1/8 := by
  have hx : -(32+3*primitivePeriodConstant)/q^3 ≤ 0 := by
    have hc := primitivePeriodConstant_nonneg
    apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith [pow_pos hq 3]
  have he : Real.exp (-(32+3*primitivePeriodConstant)/q^3) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr hx
  unfold initialOverlapLower
  linarith

/-- Unconditioned common mass of the two genuine count-and-mark simulators.
This includes all retained counts, not a conditioned or changed channel. -/
theorem initial_counted_overlap {q : ℝ} {m : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ)) (off : Fin m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3) :
    let k := initialSideCount q m
    initialOverlapLower q ≤ FiniteLaw.overlap
      (countedPrimitiveLaw (N:=(k+1)*m) (Nat.mul_le_mul_right m (Nat.le_succ k))
        ⟨hq.1,by linarith [hq.2]⟩ (defectTypes (periodSlot (u:=k) (fun _ => off))))
      (countedPrimitiveLaw (N:=(k+1)*m) le_rfl
        ⟨hq.1,by linarith [hq.2]⟩ (defectTypes (periodSlot (u:=k+1) (fun _ => off)))) := by
  let k := initialSideCount q m
  let N := (k+1)*m
  have hq0 := hq.1
  have hqi : q ∈ Set.Ioo 0 1 := ⟨hq.1,by linarith [hq.2]⟩
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hq2 : q^2 ≤ 1/4 := by nlinarith [hq.2]
  let p := 1-primitiveErasure q
  have hp : p ∈ Set.Icc 0 1 := primitiveRetention_mem hqi
  have hp' : p=1-q^2/2 := rfl
  obtain ⟨hklo,hkhi,hk1⟩ := initialSideCount_bounds hq hm hscale
  change q*(m:ℝ)/2 ≤ (k:ℝ) at hklo
  change (k:ℝ) ≤ q*(m:ℝ) at hkhi
  change k+1 ≤ m at hk1
  have hk : k ≤ m := by omega
  have hnlo : q*(m:ℝ)^2/2 ≤ ((k*m:ℕ):ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hklo hm0.le
    push_cast
    nlinarith
  have hnhi : ((k*m:ℕ):ℝ) ≤ (m:ℝ)^2 := by
    exact_mod_cast (show k*m ≤ m^2 by simpa [pow_two] using Nat.mul_le_mul_right m hk)
  have hNlo : q*(m:ℝ)^2/2 ≤ (N:ℝ) := by
    exact hnlo.trans (by exact_mod_cast Nat.mul_le_mul_right m (Nat.le_succ k))
  have hNhi : (N:ℝ) ≤ (m:ℝ)^2 := by
    exact_mod_cast (show N ≤ m^2 by simpa [N,pow_two] using Nat.mul_le_mul_right m hk1)
  have hqm : 1 ≤ q*(m:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (show q^2≤1 by linarith) (mul_nonneg hq0.le hm0.le)
    nlinarith
  have hrate : (k:ℝ)/(m:ℝ)+((k+1:ℕ):ℝ)/(m:ℝ) ≤ 3*q := by
    rw [←add_div]
    apply (div_le_iff₀ hm0).mpr
    push_cast
    nlinarith
  have harg : primitivePeriodConstant/q^4*((k:ℝ)/m+((k+1:ℕ):ℝ)/m) ≤
      3*primitivePeriodConstant/q^3 := by
    calc
      _ ≤ primitivePeriodConstant/q^4*(3*q) :=
        mul_le_mul_of_nonneg_left hrate (div_nonneg primitivePeriodConstant_nonneg (by positivity))
      _ = _ := by field_simp
  let C₁ := boundedCountLaw (N:=N) (Nat.mul_le_mul_right m (Nat.le_succ k)) p hp
  let C₂ := boundedCountLaw (N:=N) le_rfl p hp
  let K := boundedConditionalPrimitiveLaw hqi (defectTypes (periodSlot (u:=k) (fun _ => off))) (N:=N)
  let L := boundedConditionalPrimitiveLaw hqi (defectTypes (periodSlot (u:=k+1) (fun _ => off))) (N:=N)
  let f : Fin (N+1) → ℝ := fun l => min (C₁.mass l) (C₂.mass l) * FiniteLaw.overlap (K l) (L l)
  let a : ℝ := Real.exp (-32/q^3)/(12*(m:ℝ))
  let b : ℝ := Real.exp (-(3*primitivePeriodConstant)/q^3)/128
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hf0 : ∀l, 0 ≤ f l := fun l =>
    mul_nonneg (le_min (C₁.nonneg l) (C₂.nonneg l)) (FiniteLaw.overlap_nonneg _ _)
  let ix : Fin m → Fin (N+1) := commonCountIndex k p hp
  have hterm : ∀j : Fin m, a*b ≤ f (ix j) := by
    intro j
    let l := (ix j).val
    have hd := commonCountIndex_deviation k p hp j
    change |(l:ℝ)-((k*m:ℕ):ℝ)*p| ≤ 2*(m:ℝ) ∧ |(l:ℝ)-(N:ℝ)*p| ≤ 2*(m:ℝ) at hd
    rw [hp'] at hd
    obtain ⟨θ,hl,hθ,hmean,hv⟩ := primitive_count_admissible hq hm hscale hnlo hnhi hd.1
    obtain ⟨θ',hl',hθ',hmean',hv'⟩ := primitive_count_admissible hq hm hscale hNlo hNhi hd.2
    have hm1 := primitive_count_mass_lower hq hm hscale hnlo hnhi hd.1
    have hm2 := primitive_count_mass_lower hq hm hscale hNlo hNhi hd.2
    have hmin : a ≤ min (C₁.mass (ix j)) (C₂.mass (ix j)) := le_min hm1 hm2
    have hc := conditionalPeriod_overlap hl hl' hm hk hk1 hq hθ hθ' hmean hmean' hv hv'
      (fun _ => off) (fun _ => off) (fun _ => hoff) (fun _ => hoff)
      (fun _ _ => by simp) (fun _ _ => by simp)
    have hb : b ≤ FiniteLaw.overlap (K (ix j)) (L (ix j)) := by
      dsimp only [K,L,boundedConditionalPrimitiveLaw]
      rw [dite_eq_left hl,dite_eq_left hl']
      refine le_trans ?_ hc
      apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ)≤128)
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg harg
    exact mul_le_mul hmin hb hb0 (le_min (C₁.nonneg _) (C₂.nonneg _))
  have hsub : (∑j : Fin m, f (ix j)) ≤ ∑l : Fin (N+1), f l := by
    have hi := commonCountIndex_injective (m:=m) k p hp
    calc
      _ = ∑l ∈ Finset.univ.image ix, f l := by
        rw [Finset.sum_image]
        exact fun a _ b _ hab => hi hab
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun l _ _ => hf0 l)
  have hsum : (m:ℝ)*(a*b) ≤ ∑l : Fin (N+1), f l := by
    calc
      _ = ∑_j : Fin m, a*b := by simp
      _ ≤ ∑j : Fin m, f (ix j) := Finset.sum_le_sum (fun j _ => hterm j)
      _ ≤ _ := hsub
  have he : (m:ℝ)*(a*b)=initialOverlapLower q := by
    dsimp [a,b,initialOverlapLower]
    rw [div_mul_div_comm,←Real.exp_add]
    have hx : -32/q^3 + -(3*primitivePeriodConstant)/q^3 = -(32+3*primitivePeriodConstant)/q^3 := by ring
    rw [hx]
    field_simp
    ring
  rw [he] at hsum
  exact hsum.trans (FiniteLaw.overlap_sigma_lower C₁ C₂ K L)

/-- Data processing for common exact simulators, stated as a common-mass
inequality and allowing unequal original lengths. -/
theorem simulations_overlap_le {α : Type*} [Fintype α] {q : ℝ}
    (hq : q ∈ Set.Icc 0 1) (P Q : FiniteLaw α) (decode : α → List Bool)
    (x y : List Bool) (hP : SimulatesTrace q P decode x)
    (hQ : SimulatesTrace q Q decode y) :
    P.overlap Q ≤ listTraceOverlap q hq x y := by
  have h := approximations_trace_tv hq P Q decode x y 0 0
    (max x.length y.length) (le_max_left _ _) (le_max_right _ _)
    hP.approximate hQ.approximate
  simp only [add_zero] at h
  unfold listTraceOverlap
  rw [FiniteLaw.overlap_eq_one_sub_tv, FiniteLaw.overlap_eq_one_sub_tv]
  linarith

/-- The initial hidden-bit overlap for ordinary complete deletion traces of
consecutive pure runs. This is the unconditioned original channel. -/
theorem initial_pure_trace_overlap {q : ℝ} {m : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (hm : 32 ≤ m)
    (hscale : 16 ≤ q^3*(m:ℝ)) (off : Fin m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3) :
    let k := initialSideCount q m
    initialOverlapLower q ≤ listTraceOverlap q ⟨hq.1.le, by linarith [hq.2]⟩
      (pureAtomRun (initialPeriod m off.val) k)
      (pureAtomRun (initialPeriod m off.val) (k+1)) := by
  let k := initialSideCount q m
  have hqi : q ∈ Set.Ioo 0 1 := ⟨hq.1,by linarith [hq.2]⟩
  have hca := countedPrimitiveLaw_simulates (N:=(k+1)*m)
    (Nat.mul_le_mul_right m (Nat.le_succ k)) hqi
    (defectTypes (periodSlot (u:=k) (fun _ => off)))
  have hcb := countedPrimitiveLaw_simulates (N:=(k+1)*m) le_rfl hqi
    (defectTypes (periodSlot (u:=k+1) (fun _ => off)))
  rw [periodic_primitive_word,periodString_constant] at hca hcb
  exact (initial_counted_overlap hq hm hscale off hoff).trans
    (simulations_overlap_le ⟨hq.1.le,by linarith [hq.2]⟩ _ _ _ _ _ hca hcb)

end TraceReconstruction



/-! From the actual displaced period words to their conditional oracle
moments.  The coefficient bounds are the rank kernels,
not assumptions on an abstract pair. -/
noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- An interior period slot admits the three literal shifts. -/
def oneStepOffset {m : ℕ} (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m) (a : Fin 3) : Fin m :=
  ⟨off.val+a.val-1,by have ha := a.isLt; omega⟩

theorem oneStepOffset_add_one {m : ℕ} (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m) (a : Fin 3) :
    (oneStepOffset off hi a).val+1=off.val+a.val := by
  dsimp [oneStepOffset]
  omega

theorem oneStepOffset_distance {m : ℕ} (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m) (a : Fin 3) :
    |((oneStepOffset off hi a).val:ℝ)-(off.val:ℝ)|  ≤  1 := by
  have he := oneStepOffset_add_one off hi a
  have ha : (a.val:ℝ)  ≤  2 := by exact_mod_cast (show a.val ≤ 2 by omega)
  have ha0 : (0:ℝ)  ≤  a.val := Nat.cast_nonneg _
  have he' : ((oneStepOffset off hi a).val:ℝ)+1=(off.val:ℝ)+a.val := by exact_mod_cast he
  rw [abs_le]
  constructor <;> linarith

theorem constantPeriod_safe {u m : ℕ} (hm : 3  ≤  m) (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m) :
    SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)) := by
  constructor
  · intro i
    change 1  ≤  i.val*m+off.val ∧ i.val*m+off.val+1<u*m
    have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt i.isLt)
    constructor <;> nlinarith [hi.1,hi.2]
  · intro i j hij
    change i.val*m+off.val+3 ≤ j.val*m+off.val
    have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hij)
    nlinarith

theorem shifted_constantPeriod {u m : ℕ} (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (a : Fin u → Fin 3) :
    shiftedTag (periodSlot (fun _ => off)) hsafe a =
      periodSlot (fun i => oneStepOffset off hi (a i)) := by
  funext i
  apply Fin.ext
  change i.val*m+off.val+(a i).val-1=i.val*m+(off.val+(a i).val-1)
  omega

/-- Arbitrary deterministic motif orientations remain genuine one-defect
periods with the exact geometry used in the high-degree rank bound. -/
theorem signedPeriod_geometry {u m : ℕ} (off : Fin m)
    (hi : 1  ≤  off.val ∧ off.val + 1 < m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (s : ℕ) (X : ℤ) (τ : ℝ) :
    ∃ off' : Fin u → Fin m,
      signedPeriodDefects off hsafe s X τ = periodSlot off' ∧
      (∀j, |((off' j).val:ℝ)-(m:ℝ)/2| ≤ 3) ∧
      (∀j k, |((off' j).val:ℝ)-(off' k).val| ≤ 2) := by
  let a : Fin u → Fin 3 := fun j =>
    motifShift (motifIndicator s ((j.val:ℤ)-X)) ((prouhetSeries s).coeff ((j.val:ℤ)-X)) τ
  refine ⟨fun j => oneStepOffset off hi (a j),shifted_constantPeriod off hi hsafe a,?_,?_⟩
  · intro j
    have h := oneStepOffset_distance off hi (a j)
    have ht := abs_add_le (((oneStepOffset off hi (a j)).val:ℝ)-(off.val:ℝ))
      ((off.val:ℝ)-(m:ℝ)/2)
    rw [sub_add_sub_cancel] at ht
    linarith
  · intro j k
    have hj := oneStepOffset_distance off hi (a j)
    have hk := oneStepOffset_distance off hi (a k)
    rw [abs_le] at hj hk ⊢
    constructor <;> linarith


/-- Every moment of the actual primitive score has the source uniform
bound. -/
theorem primitive_score_evenMoment {q : ℝ} (hq : q∈Set.Ioo 0 1) (k : ℕ) :
    (primitiveMarkLaw q hq false).expect (fun z => |primitiveScore q z|^(2*k))  ≤ 
      (2/q)^(2*k) := by
  calc
    _  ≤  (primitiveMarkLaw q hq false).expect (fun _ => (2/q)^(2*k)) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (primitive_score_bound hq z) _) ((primitiveMarkLaw q hq false).nonneg z)
    _ = _ := (primitiveMarkLaw q hq false).expect_const _

/-- Hypercontractivity now applies directly to the actual signed initial
density difference under its ordinary-mark reference law. -/
theorem initial_moment_of_energy {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (s k : ℕ) (hk : 1 ≤ k) {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    ((primitiveMarkLaw q hq false).product l).evenMomentSq
      (multilinear (fun σ => mixedMotifCoefficient hl off hsafe π s 1 σ-
        mixedMotifCoefficient hl off hsafe π s (-1) σ) (primitiveScore q)) k  ≤ 
      multilinearEnergy (fun σ => mixedMotifCoefficient hl off hsafe π s 1 σ-
        mixedMotifCoefficient hl off hsafe π s (-1) σ) ((6*(2*k:ℕ):ℝ)*(2/q)) := by
  apply multilinear_moment_sq_scaled _ _ k hk
  · exact primitive_score_centered hq
  · exact div_pos (by norm_num) hq.1
  · exact primitive_score_evenMoment hq k


/-- Jensen's inequality on each homogeneous degree. -/
theorem degree_square_mixture_le {Ω : Type*} [Fintype Ω] {n : ℕ}
    (P : FiniteLaw Ω) (A : Ω → (Fin n → Bool) → ℝ) (r : ℕ) :
    (∑σ : Fin n → Bool, if monomialDegree σ=r then
      (P.expect (fun ω => A ω σ))^2 else 0)  ≤ 
    P.expect (fun ω => ∑σ : Fin n → Bool,
      if monomialDegree σ=r then (A ω σ)^2 else 0) := by
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro σ _
  by_cases h : monomialDegree σ=r
  · simp only [ite_eq_left h]
    have H := weighted_sum_sq_le Finset.univ P.mass (fun ω => A ω σ) (fun ω => P.nonneg ω)
    simpa only [P.total,one_mul] using H
  · simp only [ite_eq_right h,mul_zero,Finset.sum_const_zero,le_refl]

theorem degree_square_sub_le {n : ℕ} (A B : (Fin n → Bool) → ℝ) (r : ℕ) :
    (∑σ : Fin n → Bool, if monomialDegree σ=r then (A σ-B σ)^2 else 0)  ≤ 
    2*(∑σ : Fin n → Bool, if monomialDegree σ=r then A σ^2 else 0)+
    2*(∑σ : Fin n → Bool, if monomialDegree σ=r then B σ^2 else 0) := by
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ _
  split_ifs <;> nlinarith [sq_nonneg (A σ+B σ)]

theorem mixedMotifCoefficient_expect {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) (σ : Fin l → Bool) :
    mixedMotifCoefficient hl off hsafe π s τ σ =
      (seriesProbabilityLaw π hπ hπsum).expect (fun X =>
        averagedCoefficient (uniformSubsetLaw l (by simpa using hl))
          (defectAtRank (Finset.univ.image (signedPeriodDefects off hsafe s X.val τ))) σ) := by
  unfold mixedMotifCoefficient FiniteLaw.expect seriesProbabilityLaw
  exact (Finset.sum_coe_sort _ _).symm

theorem mixedMotifCoefficient_empty {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπsum : ∑X∈π.coeff.support,π.coeff X=1) (s : ℕ) (τ : ℝ) :
    mixedMotifCoefficient hl off hsafe π s τ (fun _ => false)=1 := by
  simp only [mixedMotifCoefficient,averagedCoefficient_empty,mul_one,hπsum]

/-- Uniform high-degree estimate after the real hidden-anchor mixture. -/
theorem mixedMotif_degree_le {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hru : r ≤ u) (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q θ : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) :
    (∑σ : Fin l → Bool, if monomialDegree σ=r then
      (mixedMotifCoefficient hl off hsafe π s τ σ)^2 else 0)  ≤ 
      ((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r := by
  simp_rw [mixedMotifCoefficient_expect hl off hsafe π hπ hπsum]
  refine (degree_square_mixture_le _ _ r).trans ?_
  calc
    _  ≤  (seriesProbabilityLaw π hπ hπsum).expect (fun _ =>
        ((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r) := by
      apply FiniteLaw.expect_mono
      intro X
      obtain ⟨d,hd,hnear,hclose⟩ := signedPeriod_geometry off hi hoff hsafe s X.val τ
      rw [hd]
      exact period_degree_square_sum hl hr hru hm hum hq hθ hmean hv d hnear hclose
    _ = _ := FiniteLaw.expect_const _ _

/-- There are never more selected ranks than actual defect periods, even
in the hidden-anchor mixture. -/
theorem mixedMotif_degree_vanish {u m l r : ℕ} (hl : l ≤ u*m) (hru : u < r) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) :
    (∑σ : Fin l → Bool, if monomialDegree σ=r then
      (mixedMotifCoefficient hl off hsafe π s τ σ)^2 else 0)=0 := by
  apply le_antisymm
  · simp_rw [mixedMotifCoefficient_expect hl off hsafe π hπ hπsum]
    refine (degree_square_mixture_le _ _ r).trans ?_
    simp_rw [defect_degree_bound hl _ (signedPeriodDefects_strictMono off hsafe s _ τ) hru]
    rw [FiniteLaw.expect_const]
  · exact Finset.sum_nonneg (fun σ _ => by split_ifs <;> positivity)

/-- The signed difference has no constant term. -/
theorem signedMotif_degree_zero {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπsum : ∑X∈π.coeff.support,π.coeff X=1) (s : ℕ) :
    (∑σ : Fin l → Bool, if monomialDegree σ=0 then
      (mixedMotifCoefficient hl off hsafe π s 1 σ-
        mixedMotifCoefficient hl off hsafe π s (-1) σ)^2 else 0)=0 := by
  simp_rw [monomialDegree_eq_zero_iff]
  simp [mixedMotifCoefficient_empty hl off hsafe π hπsum]

/-- Low-degree cancellation is for exactly the coefficients of the
conditional motif densities, without a rank surrogate at the boundary. -/
theorem signedMotif_degree_cancellation {u m l r : ℕ}
    (hu : 0 < u) (hm : 128 ≤ m) (hr : 0 < r) (hl : l ≤ u*m)
    (off : Fin m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {θ : ℝ} (hθ : θ∈Set.Ioo 0 1) (hhalf : 1/2 ≤ θ)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ)<(u:ℝ)/(3*(r+1:ℝ))) :
    (∑σ : Fin l → Bool, if monomialDegree σ=r then
      (mixedMotifCoefficient hl off hsafe π s 1 σ-
        mixedMotifCoefficient hl off hsafe π s (-1) σ)^2 else 0)  ≤ 
      8*(Fintype.card (Fin r → GapDifference):ℝ)*
        (∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
          signedPatternBound u m r s π θ k else 0) +
      2*((Fintype.card (IncreasingTuple u r):ℝ)*
        (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u))))))^2 := by
  refine (sum_degree_coeff_sq_le _).trans ?_
  simp_rw [mixedMotifCoefficient_rank_difference]
  exact initial_signed_energy hu hm hr hl off hoff hsafe π hπ hπsum s hcentral
    hθ hhalf hmean hv hM

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- A finite tail is no larger than the full geometric tail. -/
theorem finite_geometric_tail_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (N R : ℕ) :
    (∑r ∈ Finset.range N, if R ≤ r then a^r else 0) ≤ a^R/(1-a) := by
  have ht : HasSum (fun n : ℕ => a^(n+R)) (a^R/(1-a)) := by
    simpa only [pow_add, mul_comm, div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one ha ha1).mul_left (a^R)
  have hsum : (∑r ∈ Finset.range N, if R ≤ r then a^r else 0) =
      ∑r ∈ (Finset.range N).filter (R ≤ ·), a^r := by
    rw [Finset.sum_filter]
  rw [hsum]
  calc
    _ = ∑r ∈ ((Finset.range N).filter (R ≤ ·)).image (fun r => r-R), a^(r+R) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro r hr
        rw [Nat.sub_add_cancel (Finset.mem_filter.mp hr).2]
      · intro r hr s hs h
        dsimp only at h
        have hrR := (Finset.mem_filter.mp hr).2
        have hsR := (Finset.mem_filter.mp hs).2
        omega
    _ ≤ _ := by
      rw [←ht.tsum_eq]
      exact ht.summable.sum_le_tsum _ (fun _ _ => by positivity)

/-- Splitting the exact homogeneous expansion, not a surrogate polynomial. -/
theorem multilinearEnergy_low_high {n R : ℕ} (A : (Fin n → Bool) → ℝ)
    (w a K : ℝ) (hw : 0 ≤ w) (ha : 0 ≤ a) (ha1 : a < 1) (hK : 0 ≤ K)
    (L : ℕ → ℝ)
    (hlow : ∀r < R, (∑σ : Fin n → Bool, if monomialDegree σ=r then A σ^2 else 0) ≤ L r)
    (hhigh : ∀r, R ≤ r → w^(2*r)*(∑σ : Fin n → Bool,
      if monomialDegree σ=r then A σ^2 else 0) ≤ K*a^r)
    (hL : ∀r, 0 ≤ L r) :
    multilinearEnergy A w ≤ (∑r ∈ Finset.range R, w^(2*r)*L r)+K*a^R/(1-a) := by
  rw [multilinearEnergy_degrees]
  calc
    _ ≤ ∑r ∈ Finset.range (n+1),
        ((if r < R then w^(2*r)*L r else 0)+(if R ≤ r then K*a^r else 0)) := by
      apply Finset.sum_le_sum
      intro r _
      by_cases h : r < R
      · simp only [ite_eq_left h,ite_eq_right (show ¬R ≤ r by omega),add_zero]
        exact mul_le_mul_of_nonneg_left (hlow r h) (by positivity)
      · simp only [ite_eq_right h,ite_eq_left (show R ≤ r by omega),zero_add]
        exact hhigh r (by omega)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      apply add_le_add
      · rw [←Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro r hr; exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2)
          (fun r _ _ => mul_nonneg (by positivity) (hL r))
      · have he : (∑r ∈ Finset.range (n+1), if R ≤ r then K*a^r else 0)=
            K*∑r ∈ Finset.range (n+1), if R ≤ r then a^r else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          split_ifs <;> ring
        rw [he,mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (finite_geometric_tail_le ha ha1 _ _) hK

/-- The signed high-degree bound includes the true anchor mixture. -/
theorem signedMotif_degree_geometric {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) {q θ : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (w : ℝ) :
    w^(2*r)*(∑σ : Fin l → Bool, if monomialDegree σ=r then
      (mixedMotifCoefficient hl off hsafe π s 1 σ-
        mixedMotifCoefficient hl off hsafe π s (-1) σ)^2 else 0) ≤
      4*(w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^r := by
  have hw0 : 0 ≤ w^(2*r) := by rw [pow_mul]; positivity
  have hp : 0 ≤ 3*rankSchurConstant/q := by positivity [rankSchurConstant_pos,hq.1]
  have hb := degree_square_sub_le (mixedMotifCoefficient hl off hsafe π s 1)
    (mixedMotifCoefficient hl off hsafe π s (-1)) r
  by_cases hru : r ≤ u
  · have hplus := mixedMotif_degree_le hl hr hru hm hum off hi hoff hsafe π hπ hπsum
      s 1 hq hθ hmean hv
    have hminus := mixedMotif_degree_le hl hr hru hm hum off hi hoff hsafe π hπ hπsum
      s (-1) hq hθ hmean hv
    have hsqrt : Real.sqrt ((u:ℝ)/((m:ℝ)*r)) ≤ Real.sqrt ((u:ℝ)/m) := by
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < m by omega))
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    calc
      _ ≤ w^(2*r)*(4*((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r) :=
        mul_le_mul_of_nonneg_left (by linarith) (by rw [pow_mul]; positivity)
      _ ≤ w^(2*r)*(4*((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^r) := by
        gcongr
      _ = _ := by rw [pow_mul, mul_pow, mul_pow]; ring
  · rw [mixedMotif_degree_vanish hl (by omega) off hsafe π hπ hπsum s 1,
      mixedMotif_degree_vanish hl (by omega) off hsafe π hπ hπsum s (-1)] at hb
    have hz : (∑σ : Fin l → Bool, if monomialDegree σ=r then
        (mixedMotifCoefficient hl off hsafe π s 1 σ-
          mixedMotifCoefficient hl off hsafe π s (-1) σ)^2 else 0)=0 := by
      apply le_antisymm (by linarith)
      exact Finset.sum_nonneg (fun σ _ => by split_ifs <;> positivity)
    rw [hz,mul_zero]
    positivity

/-- Explicit low-degree majorant from the signed finite-difference estimate. -/
def signedInitialDegreeBound (u m r s : ℕ) (π : IntSeries) (θ : ℝ) (l : ℕ) : ℝ :=
  if r=0 then 0 else
    8*(Fintype.card (Fin r → GapDifference):ℝ)*
      (∑k : Fin r → GapDifference, if Odd (firstDifferenceCount k) then
        signedPatternBound u m r s π θ k else 0) +
    2*((Fintype.card (IncreasingTuple u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/binomialMass (u*m) θ l * (2*Real.exp (-(m:ℝ)/(1024*u))))))^2

theorem signedInitialDegreeBound_nonneg (u m r s : ℕ) (π : IntSeries) (θ : ℝ) (l : ℕ) :
    0 ≤ signedInitialDegreeBound u m r s π θ l := by
  unfold signedInitialDegreeBound
  split_ifs
  · exact le_rfl
  · apply add_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro k _
    split_ifs
    · unfold signedPatternBound
      split_ifs <;> apply mul_nonneg _ (seriesL2Sq_nonneg _)
      all_goals dsimp only [periodDifferencePrefactor, lengthDifferenceConstant, periodCentralSumConstant, periodBoundedSumConstant]
      all_goals positivity
    · exact le_rfl

/-- A fully finite norm estimate for the actual low and high degree pieces.
Only numerical admissible-count and geometric conditions remain to be chosen. -/
theorem signed_initial_full_energy {u m l R : ℕ} (hu : 0 < u) (hm : 128 ≤ m)
    (hum : u ≤ m) (hR : 0 < R) (hl : l ≤ u*m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (hcentral : CentralMotifSupport u s π)
    {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(R+1:ℝ)))
    (hw : 0 ≤ w) (ha : w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m) < 1) :
    multilinearEnergy (fun σ => mixedMotifCoefficient hl off hsafe π s 1 σ-
        mixedMotifCoefficient hl off hsafe π s (-1) σ) w ≤
      (∑r ∈ Finset.range R, w^(2*r)*signedInitialDegreeBound u m r s π θ l)+
        4*(w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^R /
          (1-w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)) := by
  have hq2 : q^2 ≤ (1/4:ℝ) := by
    calc q^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ hq.1.le hq.2 2
         _ = _ := by norm_num
  have hθ0 : θ∈Set.Ioo 0 1 := by constructor <;> nlinarith [hq.1,hθ.1,hθ.2]
  have hhalf : 1/2 ≤ θ := by nlinarith [hθ.1]
  apply multilinearEnergy_low_high _ w _ 4 hw (by positivity [rankSchurConstant_pos,hq.1]) ha
    (by norm_num) (signedInitialDegreeBound u m · s π θ l) _ _
    (fun r => signedInitialDegreeBound_nonneg _ _ _ _ _ _ _)
  · intro r hr
    by_cases hr0 : r=0
    · subst r
      rw [signedMotif_degree_zero hl off hsafe π hπsum s]
      exact signedInitialDegreeBound_nonneg _ _ _ _ _ _ _
    · have hMr : ((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ)) := by
        apply hM.trans_le
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show r+1 ≤ R+1 by omega)) (by norm_num)
      simpa only [signedInitialDegreeBound,ite_eq_right hr0] using
        signedMotif_degree_cancellation hu hm (Nat.pos_of_ne_zero hr0) hl off
          (hoff.trans (by norm_num)) hsafe π hπ hπsum s hcentral hθ0 hhalf hmean hv hMr
  · intro r hr
    exact signedMotif_degree_geometric hl (by omega) (by omega) hum off hi hoff hsafe π hπ
      hπsum s hq hθ hmean hv w

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem primitive_reference_mass_pos {q : ℝ} (hq : q∈Set.Ioo 0 1) (z : PrimitiveMark) :
    0 < (primitiveMarkLaw q hq false).mass z := by
  change 0 < primitiveMarkMass q false z
  apply div_pos _ (primitive_retain_pos hq)
  fin_cases z <;> simp [ordinaryPrimitiveMass,primitiveErasure] <;> nlinarith [hq.1,hq.2]

theorem primitive_product_mass_pos {q : ℝ} (hq : q∈Set.Ioo 0 1) {l : ℕ}
    (x : Fin l → PrimitiveMark) : 0 < ((primitiveMarkLaw q hq false).product l).mass x :=
by
  change 0 < ∏ i, (primitiveMarkLaw q hq false).mass (x i)
  exact Finset.prod_pos (fun _ _ => primitive_reference_mass_pos hq _)

/-- The density in the actual base experiment, not an independent model. -/
def initialMotifDensity {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (s : ℕ) (τ q : ℝ) : (Fin l → PrimitiveMark) → ℝ :=
  multilinear (mixedMotifCoefficient hl off hsafe π s τ) (primitiveScore q)

theorem initialMotifDensity_nonneg {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q : ℝ} (hq : q∈Set.Ioo 0 1) (x : Fin l → PrimitiveMark) :
    0 ≤ initialMotifDensity hl off hsafe π s τ q x := by
  have h := (conditionalMotifLaw hl off hsafe hq π hπ hπsum s τ).nonneg x
  rw [conditionalMotifLaw_density] at h
  exact nonneg_of_mul_nonneg_right h (primitive_product_mass_pos hq x)

theorem initialMotifDensity_mean {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    ((primitiveMarkLaw q hq false).product l).expect (initialMotifDensity hl off hsafe π s τ q)=1 := by
  have h := (conditionalMotifLaw hl off hsafe hq π hπ hπsum s τ).total
  simpa only [conditionalMotifLaw_density,FiniteLaw.expect,initialMotifDensity] using h

theorem initialMotifLaw_withDensity {u m l : ℕ} (hl : l ≤ u*m) (off : Fin m)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    conditionalMotifLaw hl off hsafe hq π hπ hπsum s τ =
      ((primitiveMarkLaw q hq false).product l).withDensity
        (initialMotifDensity hl off hsafe π s τ q)
        (initialMotifDensity_nonneg hl off hsafe π hπ hπsum s τ hq)
        (initialMotifDensity_mean hl off hsafe π hπ hπsum s τ hq) := by
  apply FiniteLaw.ext
  funext x
  exact conditionalMotifLaw_density hl off hsafe hq π hπ hπsum s τ x

theorem multilinear_sub {α : Type*} {l : ℕ} (A B : (Fin l → Bool) → ℝ)
    (Z : α → ℝ) (x : Fin l → α) :
    multilinear (fun σ => A σ-B σ) Z x = multilinear A Z x-multilinear B Z x := by
  simp only [multilinear,sub_mul,Finset.sum_sub_distrib]

/-- The constant-term deletion of a polynomial. -/
def nonconstantCoefficient {l : ℕ} (A : (Fin l → Bool) → ℝ) (σ : Fin l → Bool) : ℝ :=
  if σ=(fun _ => false) then 0 else A σ

theorem nonconstant_multilinear {α : Type*} {l : ℕ} (A : (Fin l → Bool) → ℝ)
    (Z : α → ℝ) (x : Fin l → α) :
    multilinear (nonconstantCoefficient A) Z x=multilinear A Z x-A (fun _ => false) := by
  have he : ∀σ, nonconstantCoefficient A σ=A σ-(if σ=(fun _ => false) then A σ else 0) := by
    intro σ
    by_cases h : σ=(fun _ => false) <;> simp [nonconstantCoefficient,h]
  rw [show nonconstantCoefficient A = (fun σ => A σ-(if σ=(fun _ => false) then A σ else 0)) from funext he, multilinear_sub]
  congr 1
  simp [multilinear,ite_mul]

theorem nonconstant_degree_zero {l : ℕ} (A : (Fin l → Bool) → ℝ) :
    (∑σ : Fin l → Bool, if monomialDegree σ=0 then (nonconstantCoefficient A σ)^2 else 0)=0 := by
  simp [monomialDegree_eq_zero_iff,nonconstantCoefficient]

theorem nonconstant_degree_pos {l r : ℕ} (A : (Fin l → Bool) → ℝ) (hr : 0 < r) :
    (∑σ : Fin l → Bool, if monomialDegree σ=r then (nonconstantCoefficient A σ)^2 else 0)=
      ∑σ : Fin l → Bool, if monomialDegree σ=r then (A σ)^2 else 0 := by
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : σ=(fun _ => false)
  · subst σ
    simp [monomialDegree,Ne.symm (Nat.ne_of_gt hr)]
  · simp [nonconstantCoefficient,h]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem mixedMotif_degree_geometric {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q θ : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (w : ℝ) :
    w^(2*r)*(∑σ : Fin l → Bool, if monomialDegree σ=r then
      mixedMotifCoefficient hl off hsafe π s τ σ^2 else 0) ≤
      (w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^r := by
  have hw : 0 ≤ w^(2*r) := by rw [pow_mul]; positivity
  have hp : 0 ≤ 3*rankSchurConstant/q := by positivity [rankSchurConstant_pos,hq.1]
  by_cases hru : r ≤ u
  · have hb := mixedMotif_degree_le hl hr hru hm hum off hi hoff hsafe π hπ hπsum
      s τ hq hθ hmean hv
    have hsqrt : Real.sqrt ((u:ℝ)/((m:ℝ)*r)) ≤ Real.sqrt ((u:ℝ)/m) := by
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < m by omega))
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    calc
      _ ≤ w^(2*r)*((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r :=
        mul_le_mul_of_nonneg_left hb hw
      _ ≤ w^(2*r)*((3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m))^r := by gcongr
      _ = _ := by rw [pow_mul,mul_pow,mul_pow]; ring
  · rw [mixedMotif_degree_vanish hl (by omega) off hsafe π hπ hπsum s τ,mul_zero]
    positivity

/-- Clipping input: the actual conditional density is close to one. -/
theorem initial_centered_energy {u m l : ℕ} (hl : l ≤ u*m)
    (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s : ℕ) (τ : ℝ) {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw : 0 ≤ w) (ha : w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m) < 1) :
    multilinearEnergy (nonconstantCoefficient (mixedMotifCoefficient hl off hsafe π s τ)) w ≤
      (w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)) /
        (1-w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)) := by
  have H := multilinearEnergy_low_high (R:=1)
    (nonconstantCoefficient (mixedMotifCoefficient hl off hsafe π s τ)) w _ 1 hw
    (by positivity [rankSchurConstant_pos,hq.1]) ha (by norm_num) (fun _ => 0)
    (fun r hr => by
      have he : r=0 := by omega
      subst r
      rw [nonconstant_degree_zero])
    (fun r hr => by
      rw [nonconstant_degree_pos _ (by omega)]
      simpa only [one_mul] using mixedMotif_degree_geometric hl (by omega) hm hum off
        hi hoff hsafe π hπ hπsum s τ hq hθ hmean hv w)
    (fun _ => le_rfl)
  simpa using H

theorem initial_centered_moment {u m l : ℕ} (hl : l ≤ u*m)
    (hm : 32 ≤ m) (hum : u ≤ m) (off : Fin m)
    (hi : 1 ≤ off.val ∧ off.val+1 < m) (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=u) (fun _ => off)))
    (π : IntSeries) (hπ : ∀X, 0 ≤ π.coeff X) (hπsum : ∑X∈π.coeff.support,π.coeff X=1)
    (s k : ℕ) (hk : 1 ≤ k) (τ : ℝ) {q θ w : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hθ : θ∈Set.Icc (1-q^2) (1-q^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (ha : w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m) < 1) :
    ((primitiveMarkLaw q ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ false).product l).evenMomentSq
      (fun x => initialMotifDensity hl off hsafe π s τ q x-1) k ≤
      (w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)) /
        (1-w^2*(3*rankSchurConstant/q)*Real.sqrt ((u:ℝ)/m)) := by
  have hq' : q∈Set.Ioo 0 1 := ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  have he : (fun x => initialMotifDensity hl off hsafe π s τ q x-1) =
      multilinear (nonconstantCoefficient (mixedMotifCoefficient hl off hsafe π s τ))
        (primitiveScore q) := by
    funext x
    rw [nonconstant_multilinear,mixedMotifCoefficient_empty hl off hsafe π hπsum]
    rfl
  rw [he]
  apply (multilinear_moment_sq_scaled (primitiveMarkLaw q hq' false) (primitiveScore q) k hk (primitive_score_centered hq')
    (div_pos (by norm_num) hq.1) (primitive_score_evenMoment hq' k) l _).trans
  rw [←hw]
  apply initial_centered_energy hl hm hum off hi hoff hsafe π hπ hπsum s τ hq hθ hmean hv _ ha
  rw [hw]; positivity [hq.1]

end TraceReconstruction

end
end
end
end
end
end
end
end

end OAI
