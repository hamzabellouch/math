import OAI.Probability.EntangledGames.ExposureErrors

namespace OAI

universe u_R u_m u_n u_A u_B u_T u_U

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

def Game.questionLaw {x y a b : ℕ} (G : Game x y a b) : Law (Fin (x+1)×Fin (y+1)) :=
  ⟨G.questionProb, G.questionProb_nonneg, G.questionProb_sum⟩

namespace QuantumSampling
lemma rounding_value_rect {m n : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n]
    {x y a b : ℕ} (G : Game x y a b)
    (D : Fin (x+1)×Fin (y+1) → Matrix m n ℂ)
    (M : Fin (x+1) → Matrix m n ℂ) (N : Fin (y+1) → Matrix m n ℂ)
    (hM : ∀ x, hsSq (M x) = 1) (hN : ∀ y, hsSq (N y) = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM n (Fin (b+1)))
    {eA eB : ℝ}
    (hA : G.questionLaw.avg (fun z => hsSq (D z-M z.1)) ≤ eA)
    (hB : G.questionLaw.avg (fun z => hsSq (D z-N z.2)) ≤ eB)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    G.questionLaw.avg (fun z => payoff (D z) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤
      entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (4*(eA+eB))) +
        2*Real.sqrt eA+eA := by
  have hη : G.questionLaw.avg (fun z => hsSq (M z.1-N z.2)) ≤ 2*(eA+eB) := by
    have he := G.questionLaw.avg_mono (fun z => hsSq_triangle (M z.1) (D z) (N z.2))
    have heq : G.questionLaw.avg (fun z => 2*(hsSq (M z.1-D z)+hsSq (D z-N z.2))) =
        2*(G.questionLaw.avg (fun z => hsSq (D z-M z.1))+G.questionLaw.avg (fun z => hsSq (D z-N z.2))) := by
      simp only [hsSq_sub_comm (M _), show (fun z => 2*(hsSq (D z-M z.1)+hsSq (D z-N z.2))) =
        (fun z => (2:ℝ) • (hsSq (D z-M z.1)+hsSq (D z-N z.2))) from rfl, avg_smul, avg_add, smul_eq_mul]
    rw [heq] at he
    linarith
  have hround := correlated_sampling_value_rect G M N hM hN P Q hε hε1
  change G.questionLaw.avg (fun z => payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤
    entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*G.questionLaw.avg (fun z => hsSq (M z.1-N z.2)))) at hround
  have hloss := avg_payoff_difference_unbounded G.questionLaw D (fun z => M z.1)
    (fun z => (hM z.1).le) (fun z => P z.1) (fun z => Q z.2) (fun z => G.accepts z.1 z.2)
  have hsA := Real.sqrt_le_sqrt hA
  have hsη : Real.sqrt (2*G.questionLaw.avg (fun z => hsSq (M z.1-N z.2))) ≤
      Real.sqrt (4*(eA+eB)) := Real.sqrt_le_sqrt (by linarith)
  have hsamp : Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*G.questionLaw.avg (fun z => hsSq (M z.1-N z.2)))) ≤
      Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (4*(eA+eB))) := by
    apply Real.sqrt_le_sqrt
    linarith [mul_le_mul_of_nonneg_left hsη (show (0:ℝ) ≤ 12/ε from div_nonneg (by norm_num) hε.le)]
  linarith

lemma rounding_value_modes {m n R : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n] [Fintype R] [DecidableEq R] [Nonempty R]
    {x y a b : ℕ} (G : Game x y a b) (ρ : Law R)
    (D : R → Fin (x+1)×Fin (y+1) → Matrix m n ℂ)
    (M : R → Fin (x+1) → Matrix m n ℂ) (N : R → Fin (y+1) → Matrix m n ℂ)
    (hM : ∀ r x, hsSq (M r x) = 1) (hN : ∀ r y, hsSq (N r y) = 1)
    (P : R → Fin (x+1) → POVM m (Fin (a+1))) (Q : R → Fin (y+1) → POVM n (Fin (b+1)))
    {eA eB : ℝ}
    (hA : ρ.avg (fun r => G.questionLaw.avg (fun z => hsSq (D r z-M r z.1))) ≤ eA)
    (hB : ρ.avg (fun r => G.questionLaw.avg (fun z => hsSq (D r z-N r z.2))) ≤ eB)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ρ.avg (fun r => G.questionLaw.avg (fun z => payoff (D r z) (P r z.1) (Q r z.2) (G.accepts z.1 z.2))) ≤
      entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (4*(eA+eB))) +
        2*Real.sqrt eA+eA := by
  let D' := fun z => weightedBlock ρ.weight (fun r => D r z)
  let M' := fun x => weightedBlock ρ.weight (fun r => M r x)
  let N' := fun y => weightedBlock ρ.weight (fun r => N r y)
  have hm : ∀ x, hsSq (M' x) = 1 := by
    intro x
    simp only [M', hsSq_weightedBlock _ ρ.nonneg, hM, mul_one, ρ.total]
  have hn : ∀ y, hsSq (N' y) = 1 := by
    intro y
    simp only [N', hsSq_weightedBlock _ ρ.nonneg, hN, mul_one, ρ.total]
  have ha : G.questionLaw.avg (fun z => hsSq (D' z-M' z.1)) ≤ eA := by
    simp only [D', M', hsSq_weightedBlock_sub _ ρ.nonneg]
    change G.questionLaw.avg (fun z => ρ.avg (fun r => hsSq (D r z-M r z.1))) ≤ _
    rw [avg_comm]; exact hA
  have hb : G.questionLaw.avg (fun z => hsSq (D' z-N' z.2)) ≤ eB := by
    simp only [D', N', hsSq_weightedBlock_sub _ ρ.nonneg]
    change G.questionLaw.avg (fun z => ρ.avg (fun r => hsSq (D r z-N r z.2))) ≤ _
    rw [avg_comm]; exact hB
  have hh := rounding_value_rect G D' M' N' hm hn
    (fun x => POVM.blocks (fun r => P r x)) (fun y => POVM.blocks (fun r => Q r y)) ha hb hε hε1
  simp only [D', payoff_weightedBlock _ ρ.nonneg] at hh
  change G.questionLaw.avg (fun z => ρ.avg (fun r => payoff (D r z) (P r z.1) (Q r z.2) (G.accepts z.1 z.2))) ≤ _ at hh
  rw [avg_comm] at hh
  exact hh
end QuantumSampling
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {R : Type u_R} [Fintype R] [Nonempty R]
def uniform : Law R where
  weight _ := 1/(Fintype.card R : ℝ)
  nonneg _ := by positivity
  total := by simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
lemma uniform_avg (f : R → ℝ) : (uniform (R := R)).avg f = (1/(Fintype.card R : ℝ))*∑ r, f r := by
  simp only [uniform, avg, smul_eq_mul, Finset.mul_sum]
end ThresholdParallelRepetition.FiniteProbability.Law

end

noncomputable section
namespace ThresholdParallelRepetition
lemma rounding_loss_small {δ τ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (_hτ : 0 ≤ τ)
    (hsmall : τ ≤ δ^8/(2:ℝ)^80) :
    4*Real.sqrt (2*(δ^2/1024)^2+(12/(δ^2/1024))*Real.sqrt (32*τ)) +
      2*Real.sqrt (4*τ)+4*τ ≤ δ/4 := by
  have hδ2 : 0 < δ^2 := sq_pos_of_pos hδ
  have h24 : δ^4 ≤ δ^2 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h48 : δ^8 ≤ δ^4 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have hs32 : Real.sqrt (32*τ) ≤ δ^4/(2:ℝ)^36 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hterm : (12/(δ^2/1024))*Real.sqrt (32*τ) ≤ δ^2/2048 := by
    have hmul := mul_le_mul_of_nonneg_left hs32 (show 0 ≤ 12/(δ^2/1024) by positivity)
    have he : (12/(δ^2/1024))*(δ^4/(2:ℝ)^36) = (3/(2:ℝ)^24)*δ^2 := by
      field_simp; ring
    rw [he] at hmul
    nlinarith
  have hinner : 2*(δ^2/1024)^2+(12/(δ^2/1024))*Real.sqrt (32*τ) ≤ δ^2/1024 := by
    nlinarith
  have hsout : Real.sqrt (2*(δ^2/1024)^2+(12/(δ^2/1024))*Real.sqrt (32*τ)) ≤ δ/32 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hs4 : Real.sqrt (4*τ) ≤ δ/64 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have ht4 : 4*τ ≤ δ/32 := by nlinarith
  linarith
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {I R m n : Type} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (S : EventSystem (Fin (x+1)) (Fin (y+1)) I R m n)
  (hμ : S.μ = G.questionLaw)
  (T : Refinement S (Fin (a+1)) (Fin (b+1)))

include hμ
lemma conditional_rounding_bound (hl : 0 < S.l.length) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (1/(S.l.length : ℝ))*∑ j : Fin S.l.length, T.score S.l[j.val] G.accepts ≤
      entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (32*(Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)))) +
        2*Real.sqrt (4*(Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)))+
          4*(Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)) := by
  have : Nonempty (Fin S.l.length) := ⟨⟨0,hl⟩⟩
  let E : Matrix ((S.J×m)×(R×Profile I (Fin (x+1)) (Fin (y+1))))
      ((S.J×n)×(R×Profile I (Fin (x+1)) (Fin (y+1)))) ℂ :=
    basisState (Classical.arbitrary _) (Classical.arbitrary _)
  have hE : hsSq E = 1 := hsSq_basisState _ _
  let τ := Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)
  have hb := S.normalized_error_bounds E hE
  have hA : (uniform (R := Fin S.l.length)).avg (fun j => G.questionLaw.avg
      (fun q => hsSq (S.D j q-S.M j E q.1))) ≤ 4*τ := by
    rw [← hμ, uniform_avg, Fintype.card_fin]
    have hh := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ 1/(S.l.length : ℝ) by positivity)
    exact hh.trans_eq (by dsimp only [τ]; ring)
  have hB : (uniform (R := Fin S.l.length)).avg (fun j => G.questionLaw.avg
      (fun q => hsSq (S.D j q-S.N j E q.2))) ≤ 4*τ := by
    rw [← hμ, uniform_avg, Fintype.card_fin]
    have hh := mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ 1/(S.l.length : ℝ) by positivity)
    exact hh.trans_eq (by dsimp only [τ]; ring)
  have hr := rounding_value_modes G uniform S.D (fun j => S.M j E) (fun j => S.N j E)
    (fun j => S.M_unit j E hE) (fun j => S.N_unit j E hE) (T.P 0) (T.Q 0) hA hB hε hε1
  rw [← hμ] at hr
  simp only [T.payoff_D_eq_score, uniform_avg, Fintype.card_fin] at hr
  have he : 4*(4*τ+4*τ)=32*τ := by ring
  simpa only [he, τ] using hr

lemma conditional_rounding_small (hl : 0 < S.l.length) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (1/(S.l.length : ℝ))*∑ j : Fin S.l.length, T.score S.l[j.val] G.accepts ≤ entangledValue G+δ/4 := by
  have hn : 0 ≤ Real.log ((Fintype.card R : ℝ)/S.p) := by
    have he := S.raw_error_bounds.1
    have hz : 0 ≤ ∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1)) :=
      Finset.sum_nonneg (fun j _ => S.μ.avg_nonneg (fun q => hsSq_nonneg _))
    exact hz.trans he
  have ht : 0 ≤ Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ) := div_nonneg hn (Nat.cast_nonneg _)
  have he0 : 0 < δ^2/1024 := by positivity
  have he1 : δ^2/1024 ≤ 1 := by nlinarith
  have hh := conditional_rounding_bound G S hμ T hl he0 he1
  have hnum := rounding_loss_small hδ hδ1 ht hsmall
  linarith
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law OperatorEntropy
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} {T : Type u_T} {U : Type u_U} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [Fintype B] [Fintype R] [Fintype T] [Fintype U]

lemma coarsen_prob_sum (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (f : A → R) (g : B → T) (w : R → T → ℝ) :
    (∑ r, ∑ t, w r t * prob C ((P.coarsen f).effect r) ((Q.coarsen g).effect t)) =
      ∑ a, ∑ b, w (f a) (g b) * prob C (P.effect a) (Q.effect b) := by
  classical
  have hR (r : R) : (∑ t, w r t * prob C ((P.coarsen f).effect r) ((Q.coarsen g).effect t)) =
      ∑ b, w r (g b)*prob C ((P.coarsen f).effect r) (Q.effect b) :=
    Q.coarsen_sum g (fun t => w r t • probRight C ((P.coarsen f).effect r))
  simp only [hR]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b, ∑ a, w (f a) (g b)*prob C (P.effect a) (Q.effect b) := by
      apply Finset.sum_congr rfl; intro b _
      exact P.coarsen_sum f (fun r => w r (g b) • probLeft C (Q.effect b))
    _ = _ := Finset.sum_comm

lemma POVM.coarsen_slice (P : POVM m A) (f : A → R) (g : A → T) (r : R) :
    (∑ t, (P.coarsen (fun a => (f a,g a))).effect (r,t)) = (P.coarsen f).effect r := by
  classical
  simp only [POVM.coarsen, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  simp only [Prod.mk.injEq]
  by_cases hr : f a = r
  · simp [hr]
  · simp [hr]

lemma prob_POVM_total (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) :
    (∑ a, ∑ b, prob C (P.effect a) (Q.effect b)) = hsSq C := by
  simp only [← prob_sum_right, ← prob_sum_left, P.total, Q.total, prob_one]

def outcomeLaw (C : Matrix m n ℂ) (hC : hsSq C = 1) (P : POVM m A) (Q : POVM n B) : Law (A×B) where
  weight z := prob C (P.effect z.1) (Q.effect z.2)
  nonneg z := prob_nonneg (P.pos z.1) (Q.pos z.2)
  total := by rw [Fintype.sum_prod_type, prob_POVM_total, hC]

lemma outcomeLaw_avg (C : Matrix m n ℂ) (hC : hsSq C = 1) (P : POVM m A) (Q : POVM n B) (f : A×B → ℝ) :
    (outcomeLaw C hC P Q).avg f = ∑ a, ∑ b, prob C (P.effect a) (Q.effect b)*f (a,b) := by
  simp only [avg, outcomeLaw, smul_eq_mul, Fintype.sum_prod_type]
end ThresholdParallelRepetition.QuantumSampling

end

end OAI
