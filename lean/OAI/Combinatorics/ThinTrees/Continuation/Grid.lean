import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Margin

namespace OAI

/-! Continuation grid. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise
variable {n m : ℕ}

namespace StepFree

def canonical (x : StepFree n m) : StepFree n m := (x.matrix,x.2)

lemma canonical_matrix (x : StepFree n m) (hn : 0 < n) :
    x.canonical.matrix=x.matrix :=
  responseMatrix_fixed (responseMatrix_hermitian x.1) (responseMatrix_ones hn x.1)

lemma canonical_core (H : MultiGraph n m) (hn : 0 < n)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m}
    (hx : x ∈ stepCore H s κ t u) : x.canonical ∈ stepCore H s κ t u := by
  simpa only [stepCore,Set.mem_ofPred_eq,lowerPencil,upperPencil,edgePencil,
    canonical_matrix x hn,
    show x.canonical.multiplier=x.multiplier from rfl,
    show x.canonical.y=x.y from rfl,show x.canonical.z=x.z from rfl] using hx

lemma canonical_feasible (H : MultiGraph n m) (hn : 0 < n)
    {s κ t q : ℝ} {u : Fin m → ℝ} {x : StepFree n m}
    (hx : x ∈ stepFeasible H s κ t q u) : x.canonical ∈ stepFeasible H s κ t q u :=
  ⟨canonical_core H hn hx.1,hx.2⟩

def Bounded (x : StepFree n m) (R : ℝ) : Prop :=
  (∀i j, |x.1 i j| ≤ R) ∧ (∀ijk, |x.multiplier ijk| ≤ R) ∧
    (∀e, |x.y e| ≤ R) ∧ (∀e, |x.z e| ≤ R)

lemma Bounded.combo {x z : StepFree n m} {R a b : ℝ}
    (hx : x.Bounded R) (hz : z.Bounded R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (a • x+b • z).Bounded R := by
  have he (v w : ℝ) (hv : |v| ≤ R) (hw : |w| ≤ R) : |a*v+b*w| ≤ R := by
    calc
      _ ≤ |a*v|+|b*w| := abs_add_le _ _
      _ = a*|v|+b*|w| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
      _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hw hb)
      _ = R := by rw [←add_mul,hab,one_mul]
  exact ⟨fun i j => he _ _ (hx.1 i j) (hz.1 i j),
    fun ijk => he _ _ (hx.2.1 ijk) (hz.2.1 ijk),
    fun e => he _ _ (hx.2.2.1 e) (hz.2.2.1 e),
    fun e => he _ _ (hx.2.2.2 e) (hz.2.2.2 e)⟩

lemma canonical_bound (H : MultiGraph n m) (hn : 0 < n)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m} (hκ : κ ≤ 1)
    (hx : x ∈ stepCore H s κ t u) : x.canonical.Bounded (6*graphSize n m) := by
  have hd := stepCore_domain H hn hx
  have hp := domain_psd H hd
  have ht := domain_trace_size H hn hd
  have hmP : (m:ℝ) ≤ graphSize n m := by
    unfold graphSize
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hP : 2 ≤ graphSize n m := by
    unfold graphSize
    linarith [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) m]
  have h6 : 0 ≤ (6:ℝ)*m := by positivity
  have hdiag (i : Fin n) : x.matrix i i ≤ 6*m :=
    (single_le_sum (fun j _ => hp.diag_nonneg (i:=j)) (mem_univ i)).trans ht
  refine ⟨fun i j => (psd_entry_bound hp h6 hdiag i j).trans (by linarith only [hmP]),?_,?_,?_⟩
  · intro ijk
    change |x.multiplier ijk| ≤ _
    rw [abs_of_nonneg (hx.2.2.1 ijk)]
    have hsum := domain_multiplier_bound H hp x.multiplier hx.2.1
    have hle := single_le_sum (fun j _ => hx.2.2.1 j) (mem_univ ijk)
    linarith only [hle,hsum,hmP,graphSize_pos (n:=n) (m:=m)]
  · intro e
    change |x.y e| ≤ _
    rw [abs_of_nonneg (hx.2.2.2.1 e).1]
    linarith only [(hx.2.2.2.1 e).2,hP]
  · intro e
    change |x.z e| ≤ _
    rw [abs_of_nonneg (hx.2.2.2.2.1 e).1]
    linarith only [(hx.2.2.2.2.1 e).2,hκ,hP]

end StepFree

lemma auxiliaryPoint_canonical (H : MultiGraph n m) (_hn : 0 < n) (κ : ℝ) :
    (auxiliaryPoint H κ).canonical=auxiliaryPoint H κ := by
  change ((auxiliaryPoint H κ).matrix,(auxiliaryPoint H κ).2)=((auxiliaryPoint H κ).1,(auxiliaryPoint H κ).2)
  rw [auxiliaryPoint_matrix]
  rfl

lemma baseline_le_one : continuationBaseline m ≤ 1 := by
  unfold continuationBaseline
  exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) m])

theorem bounded_step_inner_cube (H : MultiGraph n m) (hn : 2 ≤ n) (hconn : H.Connected univ)
    {s q β : ℝ} (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
    (hq : q ≤ m) (hβ : (graphSize n m)⁻¹/32 ≤ β)
    (u : Fin m → ℝ) (hu0 : ∀e, 0 ≤ u e)
    {z : StepFree n m}
    (hz : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) (q+β) u) :
    ∃c : StepFree n m, c.Bounded (6*graphSize n m) ∧
      ∀x, x.Close c ((graphSize n m)^(-30:ℤ)) →
        x ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) q u := by
  have hn0 : 0 < n := by omega
  let θ := (graphSize n m)^(-8:ℤ)
  let aux := auxiliaryPoint H (continuationBaseline m)
  have hθ : 0 ≤ θ := (zpow_pos graphSize_pos _).le
  have hθ1 : θ ≤ 1 := by
    have hP : 1 ≤ graphSize n m := by
      unfold graphSize
      linarith [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) m]
    exact (inverse_power_mono hP (by norm_num : 0 ≤ 8)).trans_eq (by simp)
  have ha : aux ∈ stepCore H s (continuationBaseline m) (continuationStep m) u :=
    auxiliary_cube H hn hconn hs hsP u hu0 (StepFree.Close.refl aux (zpow_pos graphSize_pos _).le)
  have hab := StepFree.canonical_bound H hn0 baseline_le_one ha
  rw [auxiliaryPoint_canonical H hn0] at hab
  refine ⟨(1-θ) • z.canonical+θ • aux,?_,?_⟩
  · exact (StepFree.canonical_bound H hn0 baseline_le_one hz.1).combo hab
      (sub_nonneg.mpr hθ1) hθ (by ring)
  · exact step_inner_cube H hn hconn hs hsP hq hβ u hu0 (z.canonical_feasible H hn0 hz)

abbrev StepIntegers (n m : ℕ) :=
  Matrix (Fin n) (Fin n) ℤ × (DistinctTriple n → ℤ) × (Fin m → ℤ) × (Fin m → ℤ)

abbrev StepRational (n m : ℕ) :=
  Matrix (Fin n) (Fin n) ℚ × (DistinctTriple n → ℚ) × (Fin m → ℚ) × (Fin m → ℚ)

namespace StepRational

def real (x : StepRational n m) : StepFree n m :=
  (fun i j => (x.1 i j:ℝ),fun ijk => (x.2.1 ijk:ℝ),
    fun e => (x.2.2.1 e:ℝ),fun e => (x.2.2.2 e:ℝ))

end StepRational

namespace StepIntegers

def onGrid (D : ℕ) (a : StepIntegers n m) : StepRational n m :=
  (fun i j => (a.1 i j:ℚ)/D,fun ijk => (a.2.1 ijk:ℚ)/D,
    fun e => (a.2.2.1 e:ℚ)/D,fun e => (a.2.2.2 e:ℚ)/D)

def Bounded (a : StepIntegers n m) (N : ℕ) : Prop :=
  (∀i j, |a.1 i j| ≤ N) ∧ (∀ijk, |a.2.1 ijk| ≤ N) ∧
    (∀e, |a.2.2.1 e| ≤ N) ∧ (∀e, |a.2.2.2 e| ≤ N)

end StepIntegers

def roundStep (D : ℕ) (x : StepFree n m) : StepIntegers n m :=
  (fun i j => ⌊(D:ℝ)*x.1 i j⌋,fun ijk => ⌊(D:ℝ)*x.multiplier ijk⌋,
    fun e => ⌊(D:ℝ)*x.y e⌋,fun e => ⌊(D:ℝ)*x.z e⌋)

lemma floorGrid_error {D : ℕ} (hD : 0 < D) (x : ℝ) :
    |((⌊(D:ℝ)*x⌋:ℤ):ℝ)/(D:ℝ)-x| ≤ (D:ℝ)⁻¹ := by
  have hDr : 0 < (D:ℝ) := by exact_mod_cast hD
  have hlo := Int.floor_le ((D:ℝ)*x)
  have hhi := Int.lt_floor_add_one ((D:ℝ)*x)
  have h1 : ((⌊(D:ℝ)*x⌋:ℤ):ℝ)/(D:ℝ) ≤ x := (div_le_iff₀ hDr).mpr (by linarith only [hlo])
  have h2 : x < (((⌊(D:ℝ)*x⌋:ℤ):ℝ)+1)/(D:ℝ) := (lt_div_iff₀ hDr).mpr (by linarith only [hhi])
  rw [abs_of_nonpos (sub_nonpos.mpr h1)]
  rw [add_div,one_div] at h2
  linarith only [h2]

lemma roundStep_error {D : ℕ} (hD : 0 < D) (x : StepFree n m) :
    ((roundStep D x).onGrid D).real.Close x (D:ℝ)⁻¹ := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i j
    simpa only [StepFree.Close,StepRational.real,StepIntegers.onGrid,roundStep,
      Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using floorGrid_error hD (x.1 i j)
  · intro ijk
    simpa only [StepFree.multiplier,StepRational.real,StepIntegers.onGrid,roundStep,
      Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using floorGrid_error hD (x.multiplier ijk)
  · intro e
    simpa only [StepFree.y,StepRational.real,StepIntegers.onGrid,roundStep,
      Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using floorGrid_error hD (x.y e)
  · intro e
    simpa only [StepFree.z,StepRational.real,StepIntegers.onGrid,roundStep,
      Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using floorGrid_error hD (x.z e)

lemma floorGrid_bound {D P : ℕ} {x : ℝ} (hP : 1 ≤ P) (hD : D=P^32)
    (hx : |x| ≤ 6*(P:ℝ)) : |⌊(D:ℝ)*x⌋| ≤ (7*P^33:ℕ) := by
  have hPr : (1:ℝ) ≤ P := by exact_mod_cast hP
  have hlo := Int.floor_le ((D:ℝ)*x)
  have hhi := Int.lt_floor_add_one ((D:ℝ)*x)
  have hmul := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg (α:=ℝ) D)
  have hmul' : |(D:ℝ)*x| ≤ 6*(P:ℝ)^33 := by
    calc
      _ = (D:ℝ)*|x| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) D)]
      _ ≤ (D:ℝ)*(6*(P:ℝ)) := hmul
      _ = _ := by rw [hD,Nat.cast_pow]; ring
  have hPl : (1:ℝ) ≤ (P:ℝ)^33 := one_le_pow₀ hPr
  have hb : |(⌊(D:ℝ)*x⌋:ℝ)| ≤ 7*(P:ℝ)^33 := by
    obtain ⟨hm1,hm2⟩ := abs_le.mp hmul'
    apply abs_le.mpr
    constructor <;> linarith only [hlo,hhi,hm1,hm2,hPl]
  exact_mod_cast hb

lemma roundStep_bound (x : StepFree n m) (hx : x.Bounded (6*graphSize n m)) :
    (roundStep ((n+m+2)^32) x).Bounded (7*(n+m+2)^33) := by
  have he (v : ℝ) (hv : |v| ≤ 6*graphSize n m) :
      |⌊((n+m+2)^32:ℕ)*v⌋| ≤ (7*(n+m+2)^33:ℕ) := by
    apply floorGrid_bound (by omega : 1 ≤ n+m+2) rfl
    simpa only [graphSize,Nat.cast_add,Nat.cast_ofNat] using hv
  exact ⟨fun i j => he _ (hx.1 i j),fun ijk => he _ (hx.2.1 ijk),
    fun e => he _ (hx.2.2.1 e),fun e => he _ (hx.2.2.2 e)⟩

theorem bounded_grid_step (H : MultiGraph n m) (hn : 2 ≤ n) (hconn : H.Connected univ)
    {s q β : ℝ} (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
    (hq : q ≤ m) (hβ : (graphSize n m)⁻¹/32 ≤ β)
    (u : Fin m → ℝ) (hu0 : ∀e, 0 ≤ u e)
    {z : StepFree n m}
    (hz : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) (q+β) u) :
    ∃a : StepIntegers n m, a.Bounded (7*(n+m+2)^33) ∧
      (a.onGrid ((n+m+2)^32)).real ∈
        stepFeasible H s (continuationBaseline m) (continuationStep m) q u := by
  obtain ⟨c,hc,hball⟩ := bounded_step_inner_cube H hn hconn hs hsP hq hβ u hu0 hz
  refine ⟨roundStep ((n+m+2)^32) c,roundStep_bound c hc,hball _ ?_⟩
  apply (roundStep_error (by positivity) c).mono
  have hP : 1 ≤ graphSize n m := by
    unfold graphSize
    linarith [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) m]
  convert inverse_power_mono hP (by norm_num : 30 ≤ 32) using 1
  simp only [graphSize,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,_root_.zpow_neg]
  rfl

theorem uniform_continuation_grid :
    ∃r0 : ℕ, 8 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ → r ≤ m →
      ∀(u : Fin m → ℝ), (∀e, 0 ≤ u e) → (∀e, u e ≤ 1) →
      ∀(s Q g : ℝ), 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      3*(r:ℝ)/4 ≤ Q → Q ≤ r →
      (r:ℝ)^(-1/8:ℝ) ≤ g → g ≤ 2*(r:ℝ)^(-1/8:ℝ) →
      (∀p, 0 ≤ slack H.left H.right (fun e => u e+continuationBaseline m) Q p) →
      ∃a : StepIntegers n m, a.Bounded (7*(n+m+2)^33) ∧
        (a.onGrid ((n+m+2)^32)).real ∈ stepFeasible H s (continuationBaseline m) (continuationStep m)
          (Q-2*g*r*continuationStep m) u := by
  obtain ⟨r0,hr0,hr⟩ := feasible_continuation_response
  refine ⟨r0,hr0,?_⟩
  intro r hrr n m H hn hconn hrm u hu0 hu1 s Q g hs hsr hQ hQr hg hgg hinv
  have hr1 : 1 ≤ r := by omega
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr1
  have hsP : s ≤ graphSize n m := by
    calc
      s ≤ (r:ℝ)^(1/4:ℝ) := hsr
      _ ≤ (r:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hrR (by norm_num)
      _ = r := Real.rpow_one _
      _ ≤ m := by exact_mod_cast hrm
      _ ≤ _ := by unfold graphSize; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hβ := continuation_margin_lower (n:=n) (m:=m) hr1 hg
  have hβ0 : 0 ≤ g*r*continuationStep m := (div_nonneg (inv_nonneg.mpr (graphSize_pos (n:=n) (m:=m)).le) (by norm_num) : 0 ≤ (graphSize n m)⁻¹/32).trans hβ
  obtain ⟨w,hw,hp⟩ := hr r hrr n m H hn hconn u hu0 hu1 s Q g hs hsr hQ hQr hg hgg hinv
  obtain ⟨z,hz,_,_⟩ := response_to_stepFeasible H (by omega)
    (continuation_parameters m).2.2.2.1 (continuation_parameters m).2.2.2.2.2.1 hw hp
  have hq : Q-2*g*r*continuationStep m ≤ m := by
    have hh : (r:ℝ) ≤ m := by exact_mod_cast hrm
    linarith only [hβ0,hh,hQr]
  have hz' : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m)
      ((Q-2*g*r*continuationStep m)+(g*r*continuationStep m)) u := by
    rw [show (Q-2*g*r*continuationStep m)+(g*r*continuationStep m) =
      Q-g*r*continuationStep m by ring]
    exact hz
  exact bounded_grid_step H hn hconn hs.le hsP hq hβ u hu0 hz'

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
