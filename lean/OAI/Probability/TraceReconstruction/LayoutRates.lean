import OAI.Probability.TraceReconstruction.InitialRates

namespace OAI

/-!
# LayoutRates

Integer block schedules, rounding, length and trial margins, sparse gaps, and forced-anchor decay.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The source integer window size, with zero-based nesting index. -/
def sourceWindowSize (N : ℝ) (b : ℕ) (ε : ℝ) (j : ℕ) : ℕ :=
  4*⌊N^(scaleKappa b (j+1) ε)/4⌋₊

/-- At a nonroot node the source trial count is an even integer. -/
def sourceLocalTrials (P h : ℕ) : ℕ := 2*(P/(100*(2*h+1)))

/-- The root schedule count: the literal floor after subtracting its window. -/
def sourceRootTrials (N : ℝ) (S T h : ℕ) : ℕ :=
  (⌊N/(S:ℝ)⌋₊-T)/(2*h+1)

/-- Literal length and overlap-count state of one nested source block.
 `copies` and `trials` refer to the transition into this state. -/
structure SourceArithmeticStage where
  length : ℕ
  count : ℕ
  copies : ℕ
  trials : ℕ

def sourceArithmeticStages (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) :
    ℕ → SourceArithmeticStage
  | 0 => ⟨ell,k,1,0⟩
  | j+1 =>
    let prev := sourceArithmeticStages C N b ε ell k j
    let T := sourceWindowSize N b ε j
    let J := sourceRootTrials N prev.length T prev.count
    let P := if j+1=b then J*(2*prev.count+1)+T
      else ⌊N^(scaleA b (j+1) ε)/(prev.length:ℝ)⌋₊
    let m := if j+1=b then J else sourceLocalTrials P prev.count
    ⟨prev.length*P,⌈C*prev.count*P⌉₊,P,m⟩

def sourceArithmeticP (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) (j : ℕ) : ℕ :=
  (sourceArithmeticStages C N b ε ell k (j+1)).copies

def sourceArithmeticTrials (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) (j : ℕ) : ℕ :=
  (sourceArithmeticStages C N b ε ell k (j+1)).trials

def sourceArithmeticLength (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) (j : ℕ) : ℕ :=
  (sourceArithmeticStages C N b ε ell k j).length

def sourceArithmeticCount (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) (j : ℕ) : ℕ :=
  (sourceArithmeticStages C N b ε ell k j).count

theorem sourceLocalTrials_even (P h : ℕ) : Even (sourceLocalTrials P h) :=
  even_two_mul _

theorem sourceLocalTrials_budget (P h : ℕ) :
    50*sourceLocalTrials P h*(2*h+1) ≤ P := by
  have H := Nat.mul_div_le P (100*(2*h+1))
  unfold sourceLocalTrials
  nlinarith only [H]

theorem sourceLocalTrials_reserves (P T h : ℕ) (hT : 2*T ≤ P) :
    2*sourceLayoutReserve (sourceLocalTrials P h) h ≤ (P-T)/2 ∧
    2*sourceLayoutReserve (sourceLocalTrials P h) h ≤ P-T-(P-T)/2 := by
  have H := sourceLocalTrials_budget P h
  rw [mul_assoc] at H
  have he : sourceLocalTrials P h/2=P/(100*(2*h+1)) := by
    unfold sourceLocalTrials
    omega
  have hr : 2*sourceLayoutReserve (sourceLocalTrials P h) h=
      sourceLocalTrials P h*(2*h+1) := by
    unfold sourceLayoutReserve
    rw [he]
    unfold sourceLocalTrials
    ring
  rw [hr]
  have hm : 2*(sourceLocalTrials P h*(2*h+1)) ≤ P-T := by omega
  constructor <;> omega

theorem sourceWindowSize_even (N : ℝ) (b : ℕ) (ε : ℝ) (j : ℕ) :
    Even (sourceWindowSize N b ε j) := by
  unfold sourceWindowSize
  exact ⟨2*⌊N^(scaleKappa b (j+1) ε)/4⌋₊,by ring⟩

theorem sourceArithmeticLength_step (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    sourceArithmeticLength C N b ε ell k (j+1)=
      sourceArithmeticLength C N b ε ell k j*sourceArithmeticP C N b ε ell k j := rfl

theorem sourceArithmeticCount_step (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    sourceArithmeticCount C N b ε ell k (j+1)=
      ⌈C*sourceArithmeticCount C N b ε ell k j*sourceArithmeticP C N b ε ell k j⌉₊ := rfl

theorem sourceArithmetic_inner_trials (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ)
    (hj : j+1≠b) : sourceArithmeticTrials C N b ε ell k j=
      sourceLocalTrials (sourceArithmeticP C N b ε ell k j) (sourceArithmeticCount C N b ε ell k j) := by
  simp only [sourceArithmeticTrials,sourceArithmeticP,sourceArithmeticCount,sourceArithmeticStages,ite_eq_right hj]

theorem sourceArithmetic_root_copies (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k : ℕ) (hb : 1 ≤ b) :
    sourceArithmeticP C N b ε ell k (b-1)=
      sourceArithmeticTrials C N b ε ell k (b-1)*(2*sourceArithmeticCount C N b ε ell k (b-1)+1)+
        sourceWindowSize N b ε (b-1) := by
  simp only [sourceArithmeticP,sourceArithmeticTrials,sourceArithmeticCount,sourceArithmeticStages,
    Nat.sub_add_cancel hb,ite_true]

theorem sourceArithmetic_count_lift (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ) :
    C*sourceArithmeticCount C N b ε ell k j*sourceArithmeticP C N b ε ell k j ≤
      sourceArithmeticCount C N b ε ell k (j+1) := Nat.le_ceil _

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Rounding the source windows loses at most a factor two. -/
theorem sourceWindowSize_bounds {N ε : ℝ} {b j : ℕ}
    (h : 8 ≤ N^(scaleKappa b (j+1) ε)) :
    N^(scaleKappa b (j+1) ε)/2 ≤ (sourceWindowSize N b ε j:ℝ) ∧
      (sourceWindowSize N b ε j:ℝ) ≤ N^(scaleKappa b (j+1) ε) := by
  have hlo := Nat.lt_floor_add_one (N^(scaleKappa b (j+1) ε)/4)
  have hhi := Nat.floor_le (show 0 ≤ N^(scaleKappa b (j+1) ε)/4 by linarith)
  unfold sourceWindowSize
  push_cast
  constructor <;> linarith only [h,hlo,hhi]

/-- The nonroot even trial count is between one and two times its unrounded
 quotient once the quotient is at least two. -/
theorem sourceLocalTrials_bounds (P h : ℕ) (hlarge : (200:ℝ)*(2*h+1) ≤ P) :
    (P:ℝ)/(100*(2*h+1)) ≤ (sourceLocalTrials P h:ℝ) ∧
      (sourceLocalTrials P h:ℝ) ≤ (P:ℝ)/(50*(2*h+1)) := by
  have hd : 0 < (100:ℝ)*(2*h+1) := by positivity
  have hx : (2:ℝ) ≤ (P:ℝ)/(100*(2*h+1)) := (le_div_iff₀ hd).mpr (by linarith only [hlarge])
  have he : (sourceLocalTrials P h:ℝ)=2*(⌊(P:ℝ)/(100*(2*h+1))⌋₊:ℝ) := by
    unfold sourceLocalTrials
    rw [show (100:ℝ)*(2*h+1)=((100*(2*h+1):ℕ):ℝ) by push_cast; ring,Nat.floor_div_eq_div]
    norm_cast
  rw [he]
  have hlo := Nat.lt_floor_add_one ((P:ℝ)/(100*(2*h+1)))
  have hhi := Nat.floor_le (div_nonneg (Nat.cast_nonneg P) hd.le)
  constructor
  · linarith only [hx,hlo]
  · have heq : (P:ℝ)/(50*(2*h+1))=2*((P:ℝ)/(100*(2*h+1))) := by field_simp; ring
    rw [heq]
    linarith only [hhi]

theorem source_floor_length_bounds {X : ℝ} {S : ℕ} (hS : 0 < S) (hX : 2*(S:ℝ) ≤ X) :
    X/2 ≤ ((S*⌊X/(S:ℝ)⌋₊:ℕ):ℝ) ∧ ((S*⌊X/(S:ℝ)⌋₊:ℕ):ℝ) ≤ X := by
  have hs : (0:ℝ) < S := by exact_mod_cast hS
  have hlo := Nat.lt_floor_add_one (X/(S:ℝ))
  have hhi := Nat.floor_le (div_nonneg (show 0 ≤ X by linarith only [hX,hs]) hs.le)
  have hh := mul_lt_mul_of_pos_left hlo hs
  have hh' := mul_le_mul_of_nonneg_left hhi hs.le
  rw [mul_add,mul_div_cancel₀ _ hs.ne'] at hh
  rw [mul_div_cancel₀ _ hs.ne'] at hh'
  push_cast
  constructor <;> nlinarith only [hX,hh,hh']

/-- The real floor and integer division versions of the root are identical
 whenever its remaining ambient count is nonnegative. -/
theorem sourceRootTrials_floor {N : ℝ} {S T h : ℕ}
    (hT : T ≤ ⌊N/(S:ℝ)⌋₊) :
    sourceRootTrials N S T h=⌊((⌊N/(S:ℝ)⌋₊:ℝ)-T)/(2*h+1)⌋₊ := by
  unfold sourceRootTrials
  rw [←Nat.cast_sub hT]
  rw [show (2:ℝ)*h+1=((2*h+1:ℕ):ℝ) by push_cast; ring,Nat.floor_div_eq_div]

theorem source_root_length_bounds {N : ℝ} {S T h : ℕ} (hS : 0 < S)
    (hT : T ≤ ⌊N/(S:ℝ)⌋₊) (hN : (2*h+2:ℝ)*S ≤ N/2) :
    N/2 ≤ (S:ℝ)*(sourceRootTrials N S T h*(2*h+1)+T) ∧
      (S:ℝ)*(sourceRootTrials N S T h*(2*h+1)+T) ≤ N := by
  have hs : (0:ℝ)<S := by exact_mod_cast hS
  have hd : 0 < 2*h+1 := by omega
  have hi := Nat.div_mul_le_self (⌊N/(S:ℝ)⌋₊-T) (2*h+1)
  have hj := Nat.lt_mul_div_succ (⌊N/(S:ℝ)⌋₊-T) hd
  rw [Nat.mul_comm (2*h+1)] at hj
  have hp : sourceRootTrials N S T h*(2*h+1)+T ≤ ⌊N/(S:ℝ)⌋₊ := by
    unfold sourceRootTrials
    omega
  have hp' : ⌊N/(S:ℝ)⌋₊ < (sourceRootTrials N S T h+1)*(2*h+1)+T := by
    unfold sourceRootTrials
    omega
  have hN0 : 0 ≤ N := by
    have hh : (0:ℝ) ≤ (2*h+2:ℝ)*S := by positivity
    linarith only [hN,hh]
  have hfloor := Nat.floor_le (div_nonneg hN0 hs.le)
  have hfloor' := Nat.lt_floor_add_one (N/(S:ℝ))
  have hpr : (sourceRootTrials N S T h:ℝ)*(2*h+1)+T ≤ (⌊N/(S:ℝ)⌋₊:ℝ) := by exact_mod_cast hp
  have hpr' : (⌊N/(S:ℝ)⌋₊:ℝ) < (sourceRootTrials N S T h+1:ℝ)*(2*h+1)+T := by exact_mod_cast hp'
  constructor
  · have hf : N/(S:ℝ) < (sourceRootTrials N S T h:ℝ)*(2*h+1)+T+(2*h+2) := by
      nlinarith only [hfloor',hpr']
    have hh := mul_lt_mul_of_pos_left hf hs
    rw [mul_div_cancel₀ _ hs.ne'] at hh
    nlinarith only [hh,hN]
  · have hh := mul_le_mul_of_nonneg_left (hpr.trans hfloor) hs.le
    simpa only [mul_div_cancel₀ _ hs.ne'] using hh

theorem source_ceil_count_bounds {C F : ℝ} {S h P : ℕ} (hC : 2 ≤ C) (hF : 1 ≤ F)
    (hS : 1 ≤ S) (hP : 1 ≤ P) (hlo : S ≤ h) (hhi : (h:ℝ) ≤ F*S) :
    S*P ≤ ⌈C*h*P⌉₊ ∧ (⌈C*h*P⌉₊:ℝ) ≤ C^2*F*(S*P) := by
  have hs : (1:ℝ) ≤ S := by exact_mod_cast hS
  have hp : (1:ℝ) ≤ P := by exact_mod_cast hP
  have hh : (S:ℝ) ≤ h := by exact_mod_cast hlo
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ C*(h:ℝ)*P by positivity)
  constructor
  · have hbound : (S:ℝ)*P ≤ C*h*P := by
      have hh' := mul_le_mul_of_nonneg_right hh (by positivity : (0:ℝ) ≤ P)
      have hc := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ C by linarith) (show 0 ≤ (h:ℝ)*P by positivity)
      nlinarith only [hh',hc]
    exact_mod_cast hbound.trans (Nat.le_ceil (C*(h:ℝ)*P))
  · have hmul := mul_le_mul_of_nonneg_left hhi (show 0 ≤ C*(P:ℝ) by positivity)
    have hbase : (1:ℝ) ≤ F*(S*P) := one_le_mul_of_one_le_of_one_le hF (one_le_mul_of_one_le_of_one_le hs hp)
    have hgain : 1 ≤ C*(C-1) := by nlinarith only [hC]
    have hgap := mul_le_mul hgain hbase (by norm_num) (by linarith only [hgain])
    nlinarith only [hceil,hmul,hgap]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_scale_target_step {N ε : ℝ} (b j : ℕ) (hN : 0 < N) :
    N^(scaleA b (j+1) ε)=(N^(scaleA b j ε))^2*N^ε := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_add hN]
  congr 1
  have hh := scaleA_step b j ε
  norm_num only [Nat.cast_ofNat]
  linarith only [hh]

theorem sourceWindowSize_le_previous {N ε : ℝ} {b j : ℕ}
    (hN : 1 ≤ N) (he : 0 ≤ ε) :
    (sourceWindowSize N b ε j:ℝ) ≤ N^(scaleA b j ε) := by
  have hf := Nat.floor_le (show 0 ≤ N^(scaleKappa b (j+1) ε)/4 by positivity)
  have hk : scaleKappa b (j+1) ε ≤ scaleA b j ε := by
    unfold scaleKappa
    simp only [Nat.add_sub_cancel]
    have hh : (1:ℝ) ≤ 2^(j+1) := one_le_pow₀ (by norm_num)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh) he]
  apply le_trans _ (Real.rpow_le_rpow_of_exponent_le hN hk)
  unfold sourceWindowSize
  push_cast
  linarith only [hf]

/-- The root's subtraction and rounding margins follow from the one
 subpower comparison N^epsilon >= 8F. -/
theorem source_root_margins {N X u F : ℝ} {S h T : ℕ}
    (hS : 1 ≤ S) (hX : (S:ℝ) ≤ X) (hF : 1 ≤ F) (hu : 8*F ≤ u)
    (hh : (h:ℝ) ≤ F*S) (hT : (T:ℝ) ≤ X) (hrel : X^2*u=N) :
    T ≤ ⌊N/(S:ℝ)⌋₊ ∧ (2*(h:ℝ)+2)*S ≤ N/2 := by
  have hs : (1:ℝ) ≤ S := by exact_mod_cast hS
  have hx : 1 ≤ X := hs.trans hX
  have hx0 : 0 ≤ X := by linarith only [hx]
  have hs0 : (0:ℝ) < S := by linarith only [hs]
  have hfs : 1 ≤ F*S := by nlinarith only [hF,hs]
  have hsX : (S:ℝ)^2 ≤ X^2 := sq_le_sq₀ hs0.le hx0 |>.mpr hX
  have h8 : 8*F*X^2 ≤ N := by nlinarith only [mul_le_mul_of_nonneg_right hu (sq_nonneg X),hrel]
  constructor
  · apply Nat.le_floor
    apply (le_div_iff₀ hs0).mpr
    have htX := mul_le_mul hT hX hs0.le hx0
    nlinarith only [htX,h8,mul_le_mul_of_nonneg_right hF (sq_nonneg X)]
  · have hhS := mul_le_mul_of_nonneg_right hh hs0.le
    have hS2 := mul_le_mul_of_nonneg_right hfs hs0.le
    have hFsq := mul_le_mul_of_nonneg_left hsX (by linarith only [hF] : 0 ≤ F)
    nlinarith only [hhS,hS2,hFsq,h8]

theorem source_arithmetic_inner_copies (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ)
    (hj : j+1≠b) : sourceArithmeticP C N b ε ell k j=
      ⌊N^(scaleA b (j+1) ε)/(sourceArithmeticLength C N b ε ell k j:ℝ)⌋₊ := by
  simp only [sourceArithmeticP,sourceArithmeticLength,sourceArithmeticStages,ite_eq_right hj]

theorem source_arithmetic_root_copies (C N : ℝ) (b : ℕ) (ε : ℝ) (ell k j : ℕ)
    (hj : j+1=b) : sourceArithmeticP C N b ε ell k j=
      sourceRootTrials N (sourceArithmeticLength C N b ε ell k j) (sourceWindowSize N b ε j)
        (sourceArithmeticCount C N b ε ell k j)*
          (2*sourceArithmeticCount C N b ε ell k j+1)+sourceWindowSize N b ε j := by
  simp only [sourceArithmeticP,sourceArithmeticLength,sourceArithmeticCount,sourceArithmeticStages,ite_eq_left hj]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- All nested lengths and overlap counts for the literal floors/ceilings.
 Only the scalar subpower margin is needed for every rounding step. -/
theorem source_arithmetic_lengths {C N F ε : ℝ} {b ell k : ℕ}
    (hC : 2 ≤ C) (hN : 1 ≤ N) (hF : 1 ≤ F) (he : 0 ≤ ε)
    (ha : ∀j ≤ b,0 ≤ scaleA b j ε)
    (hsmall : 8*C^(2*b)*F ≤ N^ε)
    (hell : N^(scaleA b 0 ε)/2 ≤ (ell:ℝ)) (hell' : (ell:ℝ) ≤ N^(scaleA b 0 ε))
    (hk : ell ≤ k) (hk' : (k:ℝ) ≤ F*ell) :
    ∀j ≤ b,
      N^(scaleA b j ε)/2 ≤ (sourceArithmeticLength C N b ε ell k j:ℝ) ∧
      (sourceArithmeticLength C N b ε ell k j:ℝ) ≤ N^(scaleA b j ε) ∧
      sourceArithmeticLength C N b ε ell k j ≤ sourceArithmeticCount C N b ε ell k j ∧
      (sourceArithmeticCount C N b ε ell k j:ℝ) ≤
        C^(2*j)*F*sourceArithmeticLength C N b ε ell k j := by
  have hN0 : 0 < N := by linarith only [hN]
  have hC1 : 1 ≤ C := by linarith only [hC]
  intro j
  induction j with
  | zero =>
    intro _
    simpa only [sourceArithmeticLength,sourceArithmeticCount,sourceArithmeticStages,
      Nat.mul_zero,pow_zero,one_mul] using And.intro hell (And.intro hell' (And.intro hk hk'))
  | succ j ih =>
    intro hj
    obtain ⟨hlo,hhi,hcount,hcount'⟩ := ih (by omega)
    let S := sourceArithmeticLength C N b ε ell k j
    let H := sourceArithmeticCount C N b ε ell k j
    let P := sourceArithmeticP C N b ε ell k j
    let Fj := C^(2*j)*F
    have hFj : 1 ≤ Fj := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) hF
    have hS0 : (0:ℝ)<S := lt_of_lt_of_le (by positivity) hlo
    have hS : 1 ≤ S := by exact_mod_cast (show 0 < S from Nat.cast_pos.mp hS0)
    have hfactor : Fj ≤ C^(2*b)*F := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hC1 (by omega)) (by linarith only [hF])
    have hu : 8*Fj ≤ N^ε := (mul_le_mul_of_nonneg_left hfactor (by norm_num)).trans (by simpa only [mul_assoc] using hsmall)
    have hx : 1 ≤ N^(scaleA b j ε) := Real.one_le_rpow hN (ha j (by omega))
    have hlength : N^(scaleA b (j+1) ε)/2 ≤ ((S*P:ℕ):ℝ) ∧
        ((S*P:ℕ):ℝ) ≤ N^(scaleA b (j+1) ε) := by
      by_cases hr : j+1=b
      · have hrel : (N^(scaleA b j ε))^2*N^ε=N := by
          rw [←source_scale_target_step b j hN0,hr,scaleA_top,Real.rpow_one]
        have hmargin := source_root_margins hS hhi hFj hu hcount'
          (sourceWindowSize_le_previous (b:=b) (j:=j) hN he) hrel
        have hlen := source_root_length_bounds (Nat.pos_of_ne_zero (by omega : S≠0)) hmargin.1 hmargin.2
        have hp : P=sourceRootTrials N S (sourceWindowSize N b ε j) H*(2*H+1)+sourceWindowSize N b ε j :=
          source_arithmetic_root_copies C N b ε ell k j hr
        rw [hp,hr,scaleA_top,Real.rpow_one]
        simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hlen
      · have hstep := source_scale_target_step (ε:=ε) b j hN0
        have hX : 2*(S:ℝ) ≤ N^(scaleA b (j+1) ε) := by
          rw [hstep]
          have hu' : 2 ≤ N^ε := by linarith only [hu,hFj]
          have hxx : N^(scaleA b j ε) ≤ (N^(scaleA b j ε))^2 := by nlinarith only [hx]
          nlinarith only [hhi,hxx,mul_le_mul_of_nonneg_left hu' (sq_nonneg (N^(scaleA b j ε)))]
        have hp : P=⌊N^(scaleA b (j+1) ε)/(S:ℝ)⌋₊ :=
          source_arithmetic_inner_copies C N b ε ell k j hr
        rw [hp]
        exact source_floor_length_bounds (by omega) hX
    have hP : 1 ≤ P := by
      have hp : (0:ℝ)<(S*P:ℕ) := lt_of_lt_of_le (by positivity) hlength.1
      have hp' : 0<S*P := Nat.cast_pos.mp hp
      by_contra hp0
      have he : P=0 := by omega
      simp only [he,Nat.mul_zero,lt_self_iff_false] at hp'
    have hceil := source_ceil_count_bounds hC hFj hS hP hcount hcount'
    rw [sourceArithmeticLength_step,sourceArithmeticCount_step]
    refine ⟨hlength.1,hlength.2,hceil.1,?_⟩
    have heq : C^2*Fj=C^(2*(j+1))*F := by
      dsimp [Fj]
      rw [show 2*(j+1)=2+2*j by omega,pow_add]
      ring
    simpa only [←Nat.cast_mul,heq] using hceil.2

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_copies_bounds {X u : ℝ} {S P : ℕ} (hX : 0 < X)
    (hSlo : X/2 ≤ S) (hShi : (S:ℝ) ≤ X)
    (hlo : X^2*u/2 ≤ ((S*P:ℕ):ℝ)) (hhi : ((S*P:ℕ):ℝ) ≤ X^2*u) :
    X*u/2 ≤ (P:ℝ) ∧ (P:ℝ) ≤ 2*X*u := by
  have hp := (Nat.cast_nonneg P : (0:ℝ) ≤ P)
  have hlo' := mul_le_mul_of_nonneg_right hShi hp
  have hhi' := mul_le_mul_of_nonneg_right hSlo hp
  push_cast at hlo hhi
  constructor <;> nlinarith only [hX,hlo,hhi,hlo',hhi']

theorem source_inner_trials_scale {X u F : ℝ} {S P h : ℕ}
    (hX : 1 ≤ X) (hF : 1 ≤ F) (hu : 1200*F ≤ u)
    (hSlo : X/2 ≤ S) (hShi : (S:ℝ) ≤ X) (hhlo : S ≤ h) (hhhi : (h:ℝ) ≤ F*S)
    (hPlo : X*u/2 ≤ (P:ℝ)) (hPhi : (P:ℝ) ≤ 2*X*u) :
    u/(600*F) ≤ (sourceLocalTrials P h:ℝ) ∧ (sourceLocalTrials P h:ℝ) ≤ 2*u := by
  have hx : 0<X := by linarith only [hX]
  have hf : 0<F := by linarith only [hF]
  have hfx : 1 ≤ F*X := one_le_mul_of_one_le_of_one_le hF hX
  have hhu : (h:ℝ) ≤ F*X := hhhi.trans (mul_le_mul_of_nonneg_left hShi hf.le)
  have hhl : X ≤ 2*(h:ℝ)+1 := by exact_mod_cast (show X ≤ 2*(h:ℝ)+1 by
    have hh : (S:ℝ) ≤ h := by exact_mod_cast hhlo
    linarith only [hh,hSlo])
  have hhh : 2*(h:ℝ)+1 ≤ 3*F*X := by linarith only [hhu,hfx]
  have hlarge : (200:ℝ)*(2*h+1) ≤ P := by
    have hum := mul_le_mul_of_nonneg_left hu hx.le
    nlinarith only [hhh,hPlo,hum]
  obtain ⟨hlo,hhi⟩ := sourceLocalTrials_bounds P h hlarge
  have hd : 0 < (100:ℝ)*(2*h+1) := by positivity
  constructor
  · apply le_trans _ hlo
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<600*F) hd).mpr
    have hum := mul_le_mul_of_nonneg_left hhh (by linarith only [hu,hF] : 0 ≤ u)
    have hpm := mul_le_mul_of_nonneg_left hPlo hf.le
    nlinarith only [hum,hpm]
  · apply hhi.trans
    apply (div_le_iff₀ (by positivity : (0:ℝ)<50*(2*h+1))).mpr
    have hmm := mul_le_mul_of_nonneg_left hhl (by linarith only [hu,hF] : 0 ≤ u)
    nlinarith only [hPhi,hmm]

theorem source_root_trials_scale {X u F : ℝ} {S P h J T : ℕ}
    (hX : 1 ≤ X) (hF : 1 ≤ F) (hu : 1200*F ≤ u)
    (hSlo : X/2 ≤ S) (hShi : (S:ℝ) ≤ X) (hhlo : S ≤ h) (hhhi : (h:ℝ) ≤ F*S)
    (hPlo : X*u/2 ≤ (P:ℝ)) (hPhi : (P:ℝ) ≤ 2*X*u)
    (hT : (T:ℝ) ≤ X) (hP : P=J*(2*h+1)+T) :
    u/(600*F) ≤ (J:ℝ) ∧ (J:ℝ) ≤ 2*u := by
  have hx : 0<X := by linarith only [hX]
  have hf : 0<F := by linarith only [hF]
  have hfx : 1 ≤ F*X := one_le_mul_of_one_le_of_one_le hF hX
  have hhu : (h:ℝ) ≤ F*X := hhhi.trans (mul_le_mul_of_nonneg_left hShi hf.le)
  have hhl : X ≤ 2*(h:ℝ)+1 := by
    have hh : (S:ℝ) ≤ h := by exact_mod_cast hhlo
    linarith only [hh,hSlo]
  have hhh : 2*(h:ℝ)+1 ≤ 3*F*X := by linarith only [hhu,hfx]
  have hp : (P:ℝ)=(J:ℝ)*(2*h+1)+T := by exact_mod_cast hP
  have hj : (0:ℝ) ≤ J := Nat.cast_nonneg _
  have hupper := mul_le_mul_of_nonneg_left hhl hj
  have hlower := mul_le_mul_of_nonneg_left hhh hj
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<600*F)).mpr
    have hu' : 4 ≤ u := by linarith only [hu,hF]
    nlinarith only [hp,hT,hPlo,hlower,mul_le_mul_of_nonneg_left hu' hx.le,hx]
  · nlinarith only [hupper,hp,hPhi,(Nat.cast_nonneg T : (0:ℝ) ≤ T),hx]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

def sourceDegreeCutoff (B : ℕ) : ℕ := 2^(10*B+40)

def sourceCancellationOrder (B D : ℕ) : ℕ :=
  ⌈100*(totalScoreExponent B D+(sourceDegreeCutoff B:ℝ)+B+10)/sourceEpsilon B D⌉₊

def sourceChannelLogConstant : ℝ := (2:ℝ)^40+1536+(32+3*primitivePeriodConstant)+1

theorem sourceChannelLogConstant_pos : 0 < sourceChannelLogConstant := by
  unfold sourceChannelLogConstant primitivePeriodConstant
  positivity

theorem deletion_inverse_cube_ge_one {q : ℝ} (hq : q∈Set.Ioc 0 1) :
    1 ≤ q^(-3:ℤ) := by
  rw [zpow_neg,zpow_ofNat,one_le_inv₀ (pow_pos hq.1 _)]
  exact pow_le_one₀ hq.1.le hq.2

theorem deletion_inverse_le_cube {q : ℝ} (hq : q∈Set.Ioc 0 1) :
    q⁻¹ ≤ q^(-3:ℤ) := by
  rw [zpow_neg,zpow_ofNat]
  apply inv_anti₀ (pow_pos hq.1 3)
  calc
    q^3=q*q^2 := by ring
    _ ≤ q*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hq.1.le hq.2) hq.1.le
    _=q := mul_one _

theorem sourceOverlapConstant_log_bound {q : ℝ} (hq : q∈Set.Ioc 0 1) :
    Real.log (sourceOverlapConstant q) ≤ sourceChannelLogConstant*q^(-3:ℤ) := by
  have hΛ := deletion_inverse_cube_ge_one hq
  have hlogq : -Real.log q ≤ q^(-3:ℤ) := (neg_le_neg (Real.neg_inv_le_log hq.1.le)).trans
    (by simpa only [neg_neg] using deletion_inverse_le_cube hq)
  have hω : 0 < initialOverlapLower q := initialOverlapLower_pos q
  have hlogC : Real.log (sourceOverlapConstant q)=
      Real.log ((2:ℝ)^40)+Real.log 1536+(32+3*primitivePeriodConstant)*q^(-3:ℤ)-Real.log q := by
    rw [sourceOverlapConstant,Real.log_div (by positivity) (mul_pos hq.1 hω).ne',
      Real.log_mul hq.1.ne' hω.ne',initialOverlapLower,
      Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp]
    rw [zpow_neg,zpow_ofNat]
    ring
  rw [hlogC]
  have htwo := Real.log_le_self (by positivity : (0:ℝ) ≤ (2:ℝ)^40)
  have h1536 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 1536)
  have hc := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ (2:ℝ)^40+1536 by positivity)
  unfold sourceChannelLogConstant
  nlinarith only [hlogq,htwo,h1536,hc]

theorem sourceOverlapConstant_ge_two {q : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) :
    2 ≤ sourceOverlapConstant q := by
  have hC := sourceOverlapConstant_pos hq.1
  have hω := initialOverlapLower_lt_eighth hq.1
  have hlarge := sourceOverlapConstant_large hq
  nlinarith only [hC,hω,hlarge]

/-- The whole block-count loss, including every nesting and every earlier
 block, is bounded by a single exp(O_B((D+1)Lambda)). -/
theorem source_count_factor_exp_bound {q : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (B D b i : ℕ) (hb : b ≤ B) (hi : i ≤ D) :
    8*(sourceOverlapConstant q)^(2*b)*(sourceOverlapConstant q)^(2*B*i+2) ≤
      Real.exp ((8+sourceChannelLogConstant*(2*B+2))*((D:ℝ)+1)*q^(-3:ℤ)) := by
  let C := sourceOverlapConstant q
  have hC : 0<C := sourceOverlapConstant_pos hq.1
  have hC1 : 1 ≤ C := (by norm_num : (1:ℝ) ≤ 2).trans (sourceOverlapConstant_ge_two hq)
  have hq' : q∈Set.Ioc 0 1 := ⟨hq.1,by linarith only [hq.2]⟩
  have hΛ := deletion_inverse_cube_ge_one hq'
  have hk := sourceChannelLogConstant_pos
  have hlog := sourceOverlapConstant_log_bound hq'
  have hm : 2*b+(2*B*i+2) ≤ (2*B+2)*(D+1) := by nlinarith only [hb,hi]
  have hpow := pow_le_pow_right₀ hC1 hm
  have hlog2 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (((2*B+2)*(D+1):ℕ):ℝ) by positivity)
  have he : C^((2*B+2)*(D+1)) ≤
      Real.exp (sourceChannelLogConstant*(2*B+2)*((D:ℝ)+1)*q^(-3:ℤ)) := by
    rw [←Real.log_le_iff_le_exp (pow_pos hC _),Real.log_pow]
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,
      mul_assoc,mul_left_comm,mul_comm] using hlog2
  have h8 : (8:ℝ) ≤ Real.exp (8*((D:ℝ)+1)*q^(-3:ℤ)) := by
    apply le_trans (by norm_num : (8:ℝ) ≤ 1+8)
    apply le_trans _ (Real.add_one_le_exp _)
    have hd : (1:ℝ) ≤ (D:ℝ)+1 := by linarith only [Nat.cast_nonneg D (α:=ℝ)]
    have hh := one_le_mul_of_one_le_of_one_le hd hΛ
    linarith only [hh]
  calc
    8*C^(2*b)*C^(2*B*i+2)=8*C^(2*b+(2*B*i+2)) := by rw [pow_add]; ring
    _ ≤ 8*C^((2*B+2)*(D+1)) := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ Real.exp (8*((D:ℝ)+1)*q^(-3:ℤ))*
        Real.exp (sourceChannelLogConstant*(2*B+2)*((D:ℝ)+1)*q^(-3:ℤ)) :=
      mul_le_mul h8 he (pow_nonneg hC.le _) (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

theorem source_uniform_count_margin (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,∀i ≤ sourceDepth B ζ ((q t)^3*Real.log (n t)),∀b ≤ B,
      8*(sourceOverlapConstant (q t))^(2*b)*(sourceOverlapConstant (q t))^(2*B*i+2) ≤
        (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) (i+1))^
          (sourceEpsilon B (sourceDepth B ζ ((q t)^3*Real.log (n t)))) := by
  let K := 8+sourceChannelLogConstant*(2*B+2)
  have hK : 0 ≤ K := by dsimp [K]; positivity [sourceChannelLogConstant_pos]
  have hrel (t) : Real.log (n t)=(q t)^(-3:ℤ)*((q t)^3*Real.log (n t)) := by
    rw [zpow_neg,zpow_ofNat]
    field_simp [(hq t).1.ne']
  have H := source_uniform_exp_absorption B 1 ζ K 1 hB hζ hK (by norm_num) hn hH
    (fun t=>zpow_pos (hq t).1 _) hrel
  filter_upwards [H] with t ht i hi b hb
  have hh := source_count_factor_exp_bound (hq t) B (sourceDepth B ζ ((q t)^3*Real.log (n t))) b i hb hi
  exact hh.trans (by simpa only [pow_one,one_mul] using ht (i+1))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Tiny epsilon estimates are uniform in the varying block depth. -/
theorem sourceEpsilon_power_small (B D m : ℕ) (hm : m ≤ 4*B+100) :
    (2:ℝ)^m*sourceEpsilon B D ≤ 1 := by
  have hp : (2:ℝ)^m ≤ 2^(4*B+100) := pow_le_pow_right₀ (by norm_num) hm
  have hd : (1:ℝ) ≤ (D:ℝ)+1 := by linarith only [Nat.cast_nonneg D (α:=ℝ)]
  have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ (2:ℝ)^(4*B+100) by positivity)
  unfold sourceEpsilon
  rw [mul_one_div]
  exact (div_le_one (by positivity)).mpr (hp.trans (by simpa only [mul_one] using hmul))

theorem scaleA_mono_index (b j k : ℕ) (ε : ℝ) (he : 0 ≤ ε) (hjk : j ≤ k) :
    scaleA b j ε ≤ scaleA b k ε := by
  unfold scaleA
  exact sub_le_sub_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hjk) (by linarith only [he]))
      (by positivity)) _

theorem scaleA_le_geometric (b j : ℕ) (ε : ℝ) (he : 0 ≤ ε) (hj : j ≤ b) :
    scaleA b j ε ≤ (2:ℝ)^j/2^b := by
  have hp : (2:ℝ)^j ≤ 2^b := pow_le_pow_right₀ (by norm_num) hj
  have hh := mul_le_mul_of_nonneg_left hp he
  unfold scaleA
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ (by positivity)).mpr
  simp only [add_mul]
  rw [div_mul_cancel₀ _ (by positivity : (2:ℝ)^b ≠ 0)]
  nlinarith only [hh]

theorem sourceKappa_three_epsilon (B D b j : ℕ) (hb : b ≤ B) (_hj : 1 ≤ j) (hj' : j ≤ b) :
    3*sourceEpsilon B D ≤ scaleKappa b j (sourceEpsilon B D) := by
  let ε := sourceEpsilon B D
  let X := (2:ℝ)^B
  have he : 0 < ε := sourceEpsilon_pos _ _
  have hx : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hsmall := sourceEpsilon_power_small B D (2*B+4) (by omega)
  have hsmall' : 16*X^2*ε ≤ 1 := by
    rw [show 2*B+4=B*2+4 by omega,pow_add,pow_mul] at hsmall
    norm_num only [show (2:ℝ)^4=16 by norm_num] at hsmall
    dsimp [X,ε]
    nlinarith only [hsmall]
  have hgeom := scaleA_zero_lower b B ε hb he.le
  have hmono := scaleA_mono_index b 0 (j-1) ε he.le (Nat.zero_le _)
  have hp : (2:ℝ)^j ≤ X := pow_le_pow_right₀ (by norm_num) (hj'.trans hb)
  have hprod : (3*X+4)*X*ε ≤ 1 := by
    have hxx : 0 ≤ X*(X-1) := mul_nonneg (by linarith only [hx]) (by linarith only [hx])
    have hcmp : (3*X+4)*X ≤ 16*X^2 := by nlinarith only [hxx,sq_nonneg X]
    exact (mul_le_mul_of_nonneg_right hcmp he.le).trans hsmall'
  have hq : (3*X+4)*ε ≤ 1/X := (le_div_iff₀ (by linarith only [hx])).mpr (by nlinarith only [hprod])
  have hzero : 1/X-ε ≤ scaleA b 0 ε := by
    have hh : (1/X)*(1-(X-1)*ε)=1/X-ε+ε/X := by field_simp; ring
    dsimp [X] at hh
    rw [hh] at hgeom
    exact (le_add_of_nonneg_right (div_nonneg he.le (by positivity))).trans hgeom
  have hpk := mul_le_mul_of_nonneg_right hp he.le
  unfold scaleKappa
  change 3*ε ≤ scaleA b (j-1) ε-3*(2^j-1)*ε
  nlinarith only [hzero,hmono,hq,hpk,he]

theorem sourceA_nonneg (B D b j : ℕ) (hb : b ≤ B) (hb0 : 1 ≤ b) :
    0 ≤ scaleA b j (sourceEpsilon B D) := by
  have h := sourceKappa_three_epsilon B D b 1 hb (by omega) hb0
  unfold scaleKappa at h
  norm_num only [Nat.sub_self,pow_one] at h
  have hm := scaleA_mono_index b 0 j (sourceEpsilon B D) (sourceEpsilon_pos B D).le (Nat.zero_le _)
  linarith only [h,hm,sourceEpsilon_pos B D]

/-- The interior scale mass excludes the bottom window, as required by the
 sparse role count rather than the much larger total leaf count. -/
def sourceInteriorExponent (b : ℕ) (ε : ℝ) : ℝ :=
  ∑j∈Finset.range (b-1),scaleKappa b (j+2) ε

theorem two_power_sum_shift (m : ℕ) :
    (∑j∈Finset.range m,(2:ℝ)^(j+1))=2^(m+1)-2 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [Finset.sum_range_succ,ih,pow_succ (2:ℝ) (m+1)]; ring

theorem sourceInteriorExponent_upper (b : ℕ) (ε : ℝ) (hb : 1 ≤ b) (he : 0 ≤ ε) :
    sourceInteriorExponent b ε ≤ 1-2/(2:ℝ)^b := by
  have hterm (j : ℕ) (hj : j∈Finset.range (b-1)) :
      scaleKappa b (j+2) ε ≤ (2:ℝ)^(j+1)/2^b := by
    have hj' := Finset.mem_range.mp hj
    have ha := scaleA_le_geometric b (j+1) ε he (by omega)
    have hp : (1:ℝ) ≤ 2^(j+2) := one_le_pow₀ (by norm_num)
    unfold scaleKappa
    simp only [show j+2-1=j+1 by omega]
    linarith only [ha,mul_nonneg (sub_nonneg.mpr hp) he]
  apply (Finset.sum_le_sum hterm).trans_eq
  rw [←Finset.sum_div,two_power_sum_shift,Nat.sub_add_cancel hb]
  field_simp

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem scaleA_zero_simple_lower (b : ℕ) (ε : ℝ) (he : 0 ≤ ε) :
    1/(2:ℝ)^b-ε ≤ scaleA b 0 ε := by
  unfold scaleA
  norm_num only [pow_zero,mul_one]
  exact sub_le_sub_right (div_le_div_of_nonneg_right (by linarith only [he]) (by positivity)) _

/-- Quantitative sparse gap, keeping its growth in d. Both the two-dimensional
 warmup and the post-warmup dimension satisfy this common estimate. -/
theorem source_sparse_gap (B D b : ℕ) (d : ℝ) (hb1 : 1 ≤ b) (_hb : b ≤ B)
    (hd : 11/5 ≤ d) (hcases : b=2 ∨ (b=B ∧ (2:ℝ)^B+2 ≤ d)) :
    (d+1)/(128*(2:ℝ)^(2*B)) ≤
      scaleA b 0 (sourceEpsilon B D)*d-sourceInteriorExponent b (sourceEpsilon B D) := by
  let X := (2:ℝ)^B
  let ε := sourceEpsilon B D
  have hx : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hx0 : 0 < X := by linarith only [hx]
  have hd0 : 0 ≤ d := by linarith only [hd]
  have he : 0 < ε := sourceEpsilon_pos B D
  have hA := mul_le_mul_of_nonneg_right (scaleA_zero_simple_lower b ε he.le) hd0
  have hI := sourceInteriorExponent_upper b ε hb1 he.le
  have hcoeff : (d+1)/(64*X^2) ≤ (d+2)/(2:ℝ)^b-1 := by
    rcases hcases with htwo | ⟨hmain,hdmain⟩
    · rw [htwo]
      have hstep : (d+1)/(64*X^2) ≤ (d+1)/64 := by
        apply div_le_div_of_nonneg_left (by linarith only [hd]) (by norm_num)
        nlinarith only [hx,sq_nonneg (X-1)]
      apply hstep.trans
      norm_num only [show (2:ℝ)^2=4 by norm_num]
      linarith only [hd]
    · rw [hmain]
      change (d+1)/(64*X^2) ≤ (d+2)/X-1
      apply (div_le_iff₀ (by positivity : (0:ℝ)<64*X^2)).mpr
      have heq : ((d+2)/X-1)*(64*X^2)=64*X*(d+2-X) := by field_simp
      rw [heq]
      have hh : 0 ≤ (d-X-2)*(64*X-1) := mul_nonneg (by dsimp [X]; linarith only [hdmain])
        (by linarith only [hx])
      nlinarith only [hh,hx]
  have hsmall := sourceEpsilon_power_small B D (2*B+8) (by omega)
  have hsmall' : 256*X^2*ε ≤ 1 := by
    rw [show 2*B+8=B*2+8 by omega,pow_add,pow_mul] at hsmall
    norm_num only [show (2:ℝ)^8=256 by norm_num] at hsmall
    dsimp [X,ε]
    nlinarith only [hsmall]
  have herr : ε*d ≤ (d+1)/(256*X^2) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<256*X^2)).mpr
    have hh := mul_le_mul_of_nonneg_right hsmall' hd0
    nlinarith only [hh]
  have hpow : (2:ℝ)^(2*B)=X^2 := by dsimp [X]; rw [Nat.mul_comm,pow_mul]
  rw [hpow]
  change (d+1)/(128*X^2) ≤ scaleA b 0 ε*d-sourceInteriorExponent b ε
  have hp : 0 < (2:ℝ)^b := by positivity
  have hc : (1/(2:ℝ)^b-ε)*d-(1-2/(2:ℝ)^b)=((d+2)/(2:ℝ)^b-1)-ε*d := by ring
  have hbase := sub_le_sub hA hI
  rw [hc] at hbase
  have hident : (d+1)/(64*X^2)-(d+1)/(256*X^2)=3*(d+1)/(256*X^2) := by ring
  have hlo := (sub_le_sub hcoeff herr).trans hbase
  rw [hident] at hlo
  have hcompare : (d+1)/(128*X^2) ≤ 3*(d+1)/(256*X^2) := by
    have hh : (d+1)/128 ≤ 3*(d+1)/256 := by linarith only [hd]
    simpa only [div_div] using div_le_div_of_nonneg_right hh (sq_nonneg X)
  exact hcompare.trans hlo

theorem totalScoreExponent_step (B i : ℕ) :
    totalScoreExponent B (i+1)=totalScoreExponent B i+blockGain (sourceDimension B i) := by
  unfold totalScoreExponent sourceDimension
  rw [Finset.sum_range_succ]
  ring

theorem totalScoreExponent_after_warmup (B i : ℕ) (hB : 2 ≤ B) (hi : warmupBlocks B ≤ i) :
    (2:ℝ)^B+11/5 ≤ totalScoreExponent B i := by
  rw [totalScoreExponent_exact B i hi]
  have hm : (0:ℝ) ≤ ((i:ℝ)-warmupBlocks B)*blockGain B :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hi)) (blockGain_pos B hB).le
  unfold warmupBlocks at *
  push_cast at *
  linarith only [hm]

theorem source_level_sparse_gap (B D i : ℕ) (hB : 2 ≤ B) :
    (totalScoreExponent B i+1)/(128*(2:ℝ)^(2*B)) ≤
      scaleA (sourceDimension B i) 0 (sourceEpsilon B D)*totalScoreExponent B i-
        sourceInteriorExponent (sourceDimension B i) (sourceEpsilon B D) := by
  have hb : 2 ≤ sourceDimension B i ∧ sourceDimension B i ≤ B := by
    unfold sourceDimension
    split_ifs <;> omega
  apply source_sparse_gap B D _ _ (by omega) hb.2 (totalScoreExponent_bounds B i hB).1
  unfold sourceDimension
  split_ifs with hi
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl,by linarith only [totalScoreExponent_after_warmup B i hB (by omega)]⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Levels outside the finite source block are irrelevant. Their harmless
 positive extension permits the global-index API of the finite tree lemmas. -/
def sourceBlockWindows (N : ℝ) (b : ℕ) (ε : ℝ) (j : ℕ) : ℕ :=
  if j<b then sourceWindowSize N b ε j else 24

structure SourceArithmeticBounds (C N F ε : ℝ) (s b ell k : ℕ) : Prop where
  lengths : ∀j ≤ b,N^(scaleA b j ε)/2 ≤ (sourceArithmeticLength C N b ε ell k j:ℝ) ∧
    (sourceArithmeticLength C N b ε ell k j:ℝ) ≤ N^(scaleA b j ε)
  counts : ∀j ≤ b,sourceArithmeticLength C N b ε ell k j ≤ sourceArithmeticCount C N b ε ell k j ∧
    (sourceArithmeticCount C N b ε ell k j:ℝ) ≤ C^(2*j)*F*sourceArithmeticLength C N b ε ell k j
  copies : ∀j<b,N^(scaleA b j ε)*N^ε/2 ≤ (sourceArithmeticP C N b ε ell k j:ℝ) ∧
    (sourceArithmeticP C N b ε ell k j:ℝ) ≤ 2*N^(scaleA b j ε)*N^ε
  trials : ∀j<b,N^ε/(600*(C^(2*b)*F)) ≤ (sourceArithmeticTrials C N b ε ell k j:ℝ) ∧
    (sourceArithmeticTrials C N b ε ell k j:ℝ) ≤ 2*N^ε
  windows : ∀j<b,24 ≤ sourceBlockWindows N b ε j ∧ 24*2^s ≤ sourceBlockWindows N b ε j ∧
    2*sourceBlockWindows N b ε j ≤ sourceArithmeticP C N b ε ell k j ∧
    4*(sourceArithmeticTrials C N b ε ell k j+1) ≤ sourceBlockWindows N b ε j

/-- Exact layout inequalities for the literal recursive integer construction.
 The hypotheses are just two scalar subpower margins and the exact scale
 identities, not any probabilistic producer or new overlap premise. -/
theorem source_arithmetic_geometry {C N F ε : ℝ} {s b ell k : ℕ}
    (hC : 2 ≤ C) (hN : 1 ≤ N) (hF : 1 ≤ F) (he : 0 ≤ ε)
    (ha : ∀j ≤ b,0 ≤ scaleA b j ε) (hκ : ∀j<b,3*ε ≤ scaleKappa b (j+1) ε)
    (hsmall : 1200*C^(2*b)*F ≤ N^ε) (hmotif : 48*((2^s:ℕ):ℝ) ≤ N^ε)
    (hell : N^(scaleA b 0 ε)/2 ≤ (ell:ℝ)) (hell' : (ell:ℝ) ≤ N^(scaleA b 0 ε))
    (hk : ell ≤ k) (hk' : (k:ℝ) ≤ F*ell) :
    SourceArithmeticBounds C N F ε s b ell k := by
  let G := C^(2*b)*F
  let u := N^ε
  have hC1 : 1 ≤ C := by linarith only [hC]
  have hN0 : 0 < N := by linarith only [hN]
  have hG : 1 ≤ G := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) hF
  have hG0 : 0 < G := by linarith only [hG]
  have hu : 1200*G ≤ u := by simpa only [G,u,mul_assoc] using hsmall
  have hu8 : 8 ≤ u := by linarith only [hu,hG]
  have H := source_arithmetic_lengths hC hN hF he ha
    (show 8*C^(2*b)*F ≤ N^ε by
      have hh : 8*G ≤ u := by linarith only [hu,hG]
      simpa only [G,u,mul_assoc] using hh) hell hell' hk hk'
  have hcopies (j : ℕ) (hj : j<b) :
      N^(scaleA b j ε)*u/2 ≤ (sourceArithmeticP C N b ε ell k j:ℝ) ∧
      (sourceArithmeticP C N b ε ell k j:ℝ) ≤ 2*N^(scaleA b j ε)*u := by
    have hlen := H j (by omega)
    have hnext := H (j+1) (by omega)
    rw [source_scale_target_step b j hN0,sourceArithmeticLength_step] at hnext
    exact source_copies_bounds (Real.rpow_pos_of_pos hN0 _) hlen.1 hlen.2.1 hnext.1 hnext.2.1
  have htrials (j : ℕ) (hj : j<b) :
      u/(600*G) ≤ (sourceArithmeticTrials C N b ε ell k j:ℝ) ∧
      (sourceArithmeticTrials C N b ε ell k j:ℝ) ≤ 2*u := by
    have hlen := H j (by omega)
    have hcp := hcopies j hj
    have hX : 1 ≤ N^(scaleA b j ε) := Real.one_le_rpow hN (ha j (by omega))
    have hcount : (sourceArithmeticCount C N b ε ell k j:ℝ) ≤
        G*sourceArithmeticLength C N b ε ell k j := by
      apply hlen.2.2.2.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1 (by omega)) (by linarith only [hF])
    by_cases hjroot : j+1=b
    · have hp : sourceArithmeticP C N b ε ell k j=
          sourceArithmeticTrials C N b ε ell k j*(2*sourceArithmeticCount C N b ε ell k j+1)+
            sourceWindowSize N b ε j := by
        simp only [sourceArithmeticP,sourceArithmeticTrials,sourceArithmeticCount,sourceArithmeticStages,ite_eq_left hjroot]
      exact source_root_trials_scale hX hG hu hlen.1 hlen.2.1 hlen.2.2.1 hcount hcp.1 hcp.2
        (sourceWindowSize_le_previous hN he) hp
    · rw [sourceArithmetic_inner_trials C N b ε ell k j hjroot]
      exact source_inner_trials_scale hX hG hu hlen.1 hlen.2.1 hlen.2.2.1 hcount hcp.1 hcp.2
  refine ⟨fun j hj => ⟨(H j hj).1,(H j hj).2.1⟩,fun j hj => (H j hj).2.2,hcopies,htrials,?_⟩
  intro j hj
  rw [sourceBlockWindows,ite_eq_left hj]
  have hp := hcopies j hj
  have ht := htrials j hj
  have hu3 : u^3 ≤ N^(scaleKappa b (j+1) ε) := by
    dsimp [u]
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    apply Real.rpow_le_rpow_of_exponent_le hN
    linarith only [hκ j hj]
  have hu32 : 64*u ≤ u^3 := by
    have hu_sq : 64 ≤ u^2 := by nlinarith only [hu8,sq_nonneg (u-8)]
    nlinarith only [mul_le_mul_of_nonneg_right hu_sq (by linarith only [hu8] : 0 ≤ u)]
  have hw := sourceWindowSize_bounds (show 8 ≤ N^(scaleKappa b (j+1) ε) by linarith only [hu32,hu8,hu3])
  have hwbig : u^3/2 ≤ (sourceWindowSize N b ε j:ℝ) := le_trans (by linarith only [hu3] : u^3/2 ≤ N^(scaleKappa b (j+1) ε)/2) hw.1
  have hwp := sourceWindowSize_le_previous (b:=b) (j:=j) hN he
  have hX : 0 ≤ N^(scaleA b j ε) := (Real.rpow_pos_of_pos hN0 _).le
  have hambient : (2:ℝ)*(sourceWindowSize N b ε j:ℝ) ≤ sourceArithmeticP C N b ε ell k j := by
    have hh := mul_le_mul_of_nonneg_right hu8 hX
    nlinarith only [hp.1,hwp,hh]
  have h24 : (24:ℝ) ≤ sourceWindowSize N b ε j := by linarith only [hwbig,hu32,hu8]
  have hmot : (24:ℝ)*((2^s:ℕ):ℝ) ≤ sourceWindowSize N b ε j := by
    have hu' : 48*((2^s:ℕ):ℝ) ≤ u := hmotif
    linarith only [hwbig,hu32,hu']
  have hroot : (4:ℝ)*((sourceArithmeticTrials C N b ε ell k j:ℝ)+1) ≤ sourceWindowSize N b ε j := by
    linarith only [hwbig,hu32,hu8,ht.2]
  exact ⟨by exact_mod_cast h24,by exact_mod_cast hmot,by exact_mod_cast hambient,by exact_mod_cast hroot⟩

theorem SourceArithmeticBounds.layout {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) :
    SourceLayoutMargins s (sourceArithmeticP C N b ε ell k) (sourceBlockWindows N b ε)
      (sourceArithmeticTrials C N b ε ell k) (sourceArithmeticCount C N b ε ell k) (b-1) := by
  constructor
  · intro j hj
    have hh := (H.windows j (by omega)).1
    omega
  · intro j hj
    have hh := (H.windows j (by omega)).1
    omega
  · intro j hj
    rw [sourceBlockWindows,ite_eq_left (by omega)]
    exact sourceWindowSize_even N b ε j
  · intro j hj
    exact (H.windows j (by omega)).2.2.1
  · intro j hj
    have hh := (H.windows j (by omega)).2.1
    omega
  · intro j hj
    rw [sourceArithmetic_inner_trials C N b ε ell k j (by omega)]
    exact sourceLocalTrials_even _ _
  · intro j hj
    rw [sourceArithmetic_inner_trials C N b ε ell k j (by omega)]
    exact (sourceLocalTrials_reserves _ _ _ (H.windows j (by omega)).2.2.1).1
  · intro j hj
    rw [sourceArithmetic_inner_trials C N b ε ell k j (by omega)]
    exact (sourceLocalTrials_reserves _ _ _ (H.windows j (by omega)).2.2.1).2

theorem SourceArithmeticBounds.window_positive {C N F ε : ℝ} {s b ell k : ℕ}
    (H : SourceArithmeticBounds C N F ε s b ell k) (j : ℕ) :
    0 < sourceBlockWindows N b ε j := by
  by_cases hj : j<b
  · have hh := (H.windows j hj).1
    omega
  · simp only [sourceBlockWindows,ite_eq_right hj]
    norm_num

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact exponent of the full binary forced skeleton, in the same bottom-up
 order as `binaryTreeBudget`. -/
def binaryTreeExponent (e : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | b+1 => e b+2*binaryTreeExponent e b

theorem binaryTreeExponent_sum (e : ℕ → ℝ) (b : ℕ) :
    binaryTreeExponent e b=∑j∈Finset.range b,((2:ℝ)^b/2^(j+1))*e j := by
  induction b with
  | zero => simp [binaryTreeExponent]
  | succ b ih =>
    rw [binaryTreeExponent,ih,Finset.sum_range_succ,Finset.mul_sum]
    have he : (∑j∈Finset.range b,((2:ℝ)^(b+1)/2^(j+1))*e j)=
        ∑j∈Finset.range b,2*((2^b/2^(j+1))*e j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    rw [he]
    simp only [div_self (by positivity : (2:ℝ)^(b+1)≠0),one_mul]
    ring

theorem binaryTreeBudget_mono {C D : ℕ → ℝ} (b : ℕ)
    (hC : ∀j < b,0 ≤ C j) (hCD : ∀j < b,C j ≤ D j) :
    binaryTreeBudget C b ≤ binaryTreeBudget D b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have hc : 0 ≤ binaryTreeBudget C b := by
      cases b with
      | zero => norm_num [binaryTreeBudget]
      | succ j => exact mul_nonneg (hC j (by omega)) (sq_nonneg _)
    have hd := ih (fun j hj=>hC j (by omega)) (fun j hj=>hCD j (by omega))
    rw [binaryTreeBudget,binaryTreeBudget]
    exact mul_le_mul (hCD b (by omega)) (pow_le_pow_left₀ hc hd 2)
      (sq_nonneg _) ((hC b (by omega)).trans (hCD b (by omega)))

theorem binaryTreeBudget_scaled (A N : ℝ) (hN : 0 < N) (e : ℕ → ℝ) (b : ℕ) :
    binaryTreeBudget (fun j => A*N^(-e j)) b=
      binaryTreeBudget (fun _=>A) b*N^(-binaryTreeExponent e b) := by
  induction b with
  | zero => simp [binaryTreeBudget,binaryTreeExponent]
  | succ b ih =>
    rw [binaryTreeBudget,ih,binaryTreeBudget,binaryTreeExponent,mul_pow]
    have hr : N^(-e b)*(N^(-binaryTreeExponent e b))^2=
        N^(-(e b+2*binaryTreeExponent e b)) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_add hN]
      congr 1
      norm_num only [Nat.cast_ofNat]
      ring
    calc
      _ = (A*(binaryTreeBudget (fun _=>A) b)^2)*
        (N^(-e b)*(N^(-binaryTreeExponent e b))^2) := by ring
      _ = _ := by rw [hr]

theorem binaryTreeBudget_const (A : ℝ) (b : ℕ) :
    binaryTreeBudget (fun _=>A) b=A^(2^b-1) := by
  induction b with
  | zero => simp [binaryTreeBudget]
  | succ b ih =>
    rw [binaryTreeBudget,ih,←pow_mul,←pow_succ']
    congr 1
    have hp : 1 ≤ 2^b := Nat.one_le_pow b 2 (by omega)
    rw [pow_succ]
    omega

theorem source_interior_product (T : ℕ → ℕ) (b : ℕ) :
    (∏j : Fin (b+1),if j.val=0 then 1 else T j.val)=∏j∈Finset.range b,T (j+1) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero,ite_true,Fin.val_succ,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,one_mul]
  exact Fin.prod_univ_eq_prod_range (fun j => T (j+1)) b

/-- Pull all extra selected leaves into the sparse-degree small factor.
 Only the mandatory 2^(b+1) bottom leaves pay the old score exponent. -/
theorem sourceForcedBudget_degree_factor (T n : ℕ → ℕ) (s b r : ℕ) (ω w : ℝ)
    (hr : 2^(b+1) ≤ r) :
    w^(2*r)*sourceForcedBudget T n s b r ω=
      (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)*
      (w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ))^(r-2^(b+1))*
      (w^2)^(2^(b+1))*
      ((2*((2^s:ℕ):ℝ)^3*hiddenBinomialCap (n b) ω)*
        binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*
          hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω) b) := by
  unfold sourceForcedBudget interiorLabelBudget sourceSparseCount
  rw [source_interior_product]
  push_cast
  have hwr : w^(2*r)=(w^2)^(r-2^(b+1))*(w^2)^(2^(b+1)) := by
    rw [←pow_add,Nat.sub_add_cancel hr,pow_mul]
  rw [hwr]
  simp only [mul_pow,pow_mul]
  ring

/-- The remaining extra-degree factor costs no scale power. -/
theorem sourceForcedBudget_degree_le (T n : ℕ → ℕ) (s b r : ℕ) (ω w : ℝ)
    (hr : 2^(b+1) ≤ r)
    (hsmall : w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ) ≤ 1) :
    w^(2*r)*sourceForcedBudget T n s b r ω ≤
      (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)*(w^2)^(2^(b+1))*
      ((2*((2^s:ℕ):ℝ)^3*hiddenBinomialCap (n b) ω)*
        binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*
          hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω) b) := by
  rw [sourceForcedBudget_degree_factor T n s b r ω w hr]
  have hfac : (w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ))^(r-2^(b+1)) ≤ 1 :=
    pow_le_one₀ (by positivity) hsmall
  have htree := binaryTreeBudget_nonneg
    (fun j => 4*((2^s:ℕ):ℝ)^6*hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω)
    (fun j => mul_nonneg (mul_nonneg (by positivity) (hiddenBinomialCap_nonneg _ _))
      (hiddenBinomialCap_nonneg _ _)) b
  have hroot := hiddenBinomialCap_nonneg (n b) ω
  have hmul := mul_le_mul_of_nonneg_left hfac
    (show 0 ≤ (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ) by positivity)
  simp only [mul_one] at hmul
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmul (by positivity)) (by positivity)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem hiddenBinomialCap_rpow {N e F K ω : ℝ} {m : ℕ}
    (hN : 0 < N) (hF : 0 < F) (hK : 0 ≤ K)
    (hm : N^e/F ≤ (m:ℝ)) (hcoef : 4*F ≤ K^2*ω^2) :
    hiddenBinomialCap m ω ≤ K*N^(-e/2) := by
  have hpow : (N^(-e/2))^2=N^(-e) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hprod : N^(-e)*N^e=1 := by rw [←Real.rpow_add hN,neg_add_cancel,Real.rpow_zero]
  unfold hiddenBinomialCap
  apply (Real.sqrt_le_left (mul_nonneg hK (Real.rpow_nonneg hN.le _))).mpr
  rw [mul_pow,hpow]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(m:ℝ)*ω^2+2)).mpr
  have hh : 4 ≤ K^2*ω^2/F := (le_div_iff₀ hF).mpr hcoef
  calc
    4 ≤ K^2*ω^2/F := hh
    _ = K^2*N^(-e)*(N^e/F*ω^2) := by
      calc
        _ = (K^2*ω^2/F)*(N^(-e)*N^e) := by rw [hprod,mul_one]
        _ = _ := by ring
    _ ≤ K^2*N^(-e)*((m:ℝ)*ω^2+2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh' := mul_le_mul_of_nonneg_right hm (sq_nonneg ω)
      linarith only [hh']

/-- The exact exponent in the skeleton budget equals the manuscript's
 forcedDecay, not an arbitrary favorable surrogate. -/
theorem forcedDecay_binary (b : ℕ) (ε d : ℝ) (hb : 1 ≤ b) :
    forcedDecay b ε d=ε/2+
      binaryTreeExponent (fun j=>scaleKappa b (j+2) ε/2+ε) (b-1)+
      (2:ℝ)^b*scaleA b 0 ε*d := by
  rw [forcedDecay,binaryTreeExponent_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  have he : (2:ℝ)^b/2^(j+2)=2^(b-1)/2^(j+1) := by
    rw [show b=(b-1)+1 by omega,pow_succ]
    simp only [Nat.add_sub_cancel]
    rw [show j+2=(j+1)+1 by omega,pow_succ]
    field_simp
  rw [he]

def sourceSkeletonPrefactor (s b : ℕ) (K : ℝ) : ℝ :=
  (2*((2^s:ℕ):ℝ)^3*K)*binaryTreeBudget (fun _=>4*((2^s:ℕ):ℝ)^6*K^2) b

theorem sourceSkeletonPrefactor_nonneg (s b : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ sourceSkeletonPrefactor s b K := by
  have h := binaryTreeBudget_nonneg (fun _=>4*((2^s:ℕ):ℝ)^6*K^2) (fun _=>by positivity) b
  unfold sourceSkeletonPrefactor
  positivity

theorem source_forced_core_bound (T n : ℕ → ℕ) (s b : ℕ) (ω N ε K : ℝ)
    (hN : 0 < N) (hK : 0 ≤ K)
    (hn : ∀j ≤ b,hiddenBinomialCap (n j) ω ≤ K*N^(-ε/2))
    (hg : ∀j < b,hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω ≤
      K*N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)) :
    (2*((2^s:ℕ):ℝ)^3*hiddenBinomialCap (n b) ω)*
      binaryTreeBudget (fun j=>4*((2^s:ℕ):ℝ)^6*
        hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω) b ≤
      sourceSkeletonPrefactor s b K*
        N^(-(ε/2+binaryTreeExponent (fun j=>scaleKappa (b+1) (j+2) ε/2+ε) b)) := by
  let A := 4*((2^s:ℕ):ℝ)^6*K^2
  let e := fun j=>scaleKappa (b+1) (j+2) ε/2+ε
  have hpoints (j : ℕ) (hj : j<b) :
      4*((2^s:ℕ):ℝ)^6*hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*
          hiddenBinomialCap (n j) ω ≤ A*N^(-e j) := by
    calc
      _ ≤ 4*((2^s:ℕ):ℝ)^6*(K*N^(-(scaleKappa (b+1) (j+2) ε+ε)/2))*(K*N^(-ε/2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hg j hj) (by positivity)) (hn j (by omega))
          (hiddenBinomialCap_nonneg _ _) (by positivity)
      _ = _ := by
        have hr : N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)*N^(-ε/2)=N^(-e j) := by
          rw [←Real.rpow_add hN]
          congr 1
          dsimp [e]
          ring
        dsimp [A]
        calc
          _ = 4*((2^s:ℕ):ℝ)^6*K^2*
            (N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)*N^(-ε/2)) := by ring
          _ = _ := by rw [hr]
  have htree := binaryTreeBudget_mono b
    (fun j _=>mul_nonneg (mul_nonneg (by positivity) (hiddenBinomialCap_nonneg _ _))
      (hiddenBinomialCap_nonneg _ _)) hpoints
  rw [binaryTreeBudget_scaled A N hN e b] at htree
  have ht0 := binaryTreeBudget_nonneg (fun j=>4*((2^s:ℕ):ℝ)^6*
      hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω)
    (fun j=>mul_nonneg (mul_nonneg (by positivity) (hiddenBinomialCap_nonneg _ _))
      (hiddenBinomialCap_nonneg _ _)) b
  calc
    _ ≤ (2*((2^s:ℕ):ℝ)^3*(K*N^(-ε/2)))*
        (binaryTreeBudget (fun _=>A) b*N^(-binaryTreeExponent e b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hn b le_rfl) (by positivity)) htree ht0 (by positivity)
    _ = _ := by
      have hr : N^(-ε/2)*N^(-binaryTreeExponent e b)=N^(-(ε/2+binaryTreeExponent e b)) := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      dsimp [sourceSkeletonPrefactor]
      calc
        _ = (2*((2^s:ℕ):ℝ)^3*K)*binaryTreeBudget (fun _=>A) b*
          (N^(-ε/2)*N^(-binaryTreeExponent e b)) := by ring
        _ = _ := by rw [hr]

/-- The sharp forced degree has the full decay gain, after all actual
 source caps and the old-score factor have been multiplied. -/
theorem source_forced_degree_decay (T n : ℕ → ℕ) (s b r : ℕ) (ω N ε d K W w : ℝ)
    (hN : 0 < N) (hK : 0 ≤ K) (hW : 0 ≤ W) (hr : 2^(b+1) ≤ r)
    (hsmall : w^2*((2^s:ℕ):ℝ)*(sourceSparseCount T s b:ℝ) ≤ 1)
    (hw : w^2 ≤ W*N^(-scaleA (b+1) 0 ε*d))
    (hn : ∀j ≤ b,hiddenBinomialCap (n j) ω ≤ K*N^(-ε/2))
    (hg : ∀j < b,hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω ≤
      K*N^(-(scaleKappa (b+1) (j+2) ε+ε)/2)) :
    w^(2*r)*sourceForcedBudget T n s b r ω ≤
      (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)*W^(2^(b+1))*
        sourceSkeletonPrefactor s b K*N^(-forcedDecay (b+1) ε d) := by
  have hstart := sourceForcedBudget_degree_le T n s b r ω w hr hsmall
  have hcore := source_forced_core_bound T n s b ω N ε K hN hK hn hg
  have hpow := pow_le_pow_left₀ (sq_nonneg w) hw (2^(b+1))
  have hpref := sourceSkeletonPrefactor_nonneg s b hK
  have hcore0 := sourceForcedBudget_nonneg T n s b r ω
  have ht := binaryTreeBudget_nonneg (fun j=>4*((2^s:ℕ):ℝ)^6*
      hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω)
    (fun j=>mul_nonneg (mul_nonneg (by positivity) (hiddenBinomialCap_nonneg _ _))
      (hiddenBinomialCap_nonneg _ _)) b
  have hroot := hiddenBinomialCap_nonneg (n b) ω
  apply hstart.trans
  apply le_trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hpow (by positivity)) hcore (by positivity) (by positivity))
  apply le_of_eq
  rw [mul_pow]
  have hrp : (N^(-scaleA (b+1) 0 ε*d))^(2^(b+1))*
      N^(-(ε/2+binaryTreeExponent (fun j=>scaleKappa (b+1) (j+2) ε/2+ε) b))=
      N^(-forcedDecay (b+1) ε d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_add hN,
      forcedDecay_binary (b+1) ε d (by omega)]
    simp only [Nat.add_sub_cancel,Nat.cast_pow,Nat.cast_ofNat]
    congr 1
    ring
  calc
    _ = (OccupiedParityTree.shapeRoleConstant r (b+1):ℝ)*W^(2^(b+1))*sourceSkeletonPrefactor s b K*
      ((N^(-scaleA (b+1) 0 ε*d))^(2^(b+1))*
        N^(-(ε/2+binaryTreeExponent (fun j=>scaleKappa (b+1) (j+2) ε/2+ε) b))) := by ring
    _ = _ := by rw [hrp]

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
