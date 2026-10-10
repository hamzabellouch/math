import OAI.Probability.EntangledGames.ExposureData

namespace OAI

universe u_m u_n u_A u_X u_Y u_I u_R u_B

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law MeasurementTransport
namespace QuantumSampling.POVM
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]
def transport (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (hGT : ∑ a, G a = Fᴴ*F) (a₀ : A) : POVM m A where
  effect := transportedEffect F G a₀
  pos := transportedEffect_pos F G hG a₀
  total := transportedEffect_sum F G hGT a₀
lemma transport_pullback (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (hGT : ∑ a, G a = Fᴴ*F) (a₀ a : A) :
    Fᴴ*(transport F G hG hGT a₀).effect a*F = G a :=
  transportedEffect_pullback F G hG hGT a₀ a
end QuantumSampling.POVM
namespace MixedExposure
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

structure Refinement (S : EventSystem X Y I R m n) (A : Type u_A) (B : Type u_B) [Fintype A] [Fintype B] where
  left : I → R → Profile I X Y → A → Matrix m m ℂ
  right : I → R → Profile I X Y → B → Matrix n n ℂ
  left_pos : ∀ i r z a, (left i r z a).PosSemidef
  right_pos : ∀ i r z b, (right i r z b).PosSemidef
  left_total : ∀ i r z, ∑ a, left i r z a = S.F r z
  right_total : ∀ i r z, ∑ b, right i r z b = S.H r z
  left_local : ∀ i r a j, IgnoresRight (fun z => left i r z a) j
  right_local : ∀ i r b j, IgnoresLeft (fun z => right i r z b) j
namespace Refinement
variable {S : EventSystem X Y I R m n} (T : Refinement S A B)
def leftFine (j : Fin S.l.length) (r : R) (z : Profile I X Y) (a : A) : Matrix m m ℂ :=
  S.μ.lefts S.x₀ (S.l.drop (j+1)) (fun z => T.left S.l[j.val] r z a) z
def rightFine (j : Fin S.l.length) (r : R) (z : Profile I X Y) (b : B) : Matrix n n ℂ :=
  S.μ.rights S.y₀ (S.l.take j).reverse (fun z => T.right S.l[j.val] r z b) z
omit [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma leftFine_pos (j : Fin S.l.length) (r : R) (z : Profile I X Y) (a : A) : (T.leftFine j r z a).PosSemidef :=
  lefts_posSemidef S.μ S.x₀ _ _ (fun z => T.left_pos _ r z a) z
omit [DecidableEq X] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma rightFine_pos (j : Fin S.l.length) (r : R) (z : Profile I X Y) (b : B) : (T.rightFine j r z b).PosSemidef :=
  rights_posSemidef S.μ S.y₀ _ _ (fun z => T.right_pos _ r z b) z
omit [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma leftFine_total (j : Fin S.l.length) (r : R) (z : Profile I X Y) :
    ∑ a, T.leftFine j r z a = S.f (j+1) r z := by
  simp only [leftFine]
  rw [← lefts_sum]
  simp only [T.left_total]
  rfl
omit [DecidableEq X] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma rightFine_total (j : Fin S.l.length) (r : R) (z : Profile I X Y) :
    ∑ b, T.rightFine j r z b = S.h j r z := by
  simp only [rightFine]
  rw [← rights_sum]
  simp only [T.right_total]
  rfl
omit [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma leftFine_local (j : Fin S.l.length) (r : R) (a : A) : IgnoresRight (fun z => T.leftFine j r z a) S.l[j.val] :=
  lefts_ignoresRight_notMem S.μ S.x₀ _ (list_fresh_not_suffix S.l S.nodup j j.isLt) (T.left_local _ r a _)
omit [DecidableEq X] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma rightFine_local (j : Fin S.l.length) (r : R) (b : B) : IgnoresLeft (fun z => T.rightFine j r z b) S.l[j.val] :=
  rights_ignoresLeft_notMem S.μ S.y₀ _ (list_fresh_not_prefix S.l S.nodup j j.isLt) (T.right_local _ r b _)

def leftPOVM (a₀ : A) (j : Fin S.l.length) (r : R) (z : Profile I X Y) : POVM (S.J×m) A :=
  POVM.transport (S.U (j+1) r z) (T.leftFine j r z) (T.leftFine_pos j r z)
    ((T.leftFine_total j r z).trans (S.U_gram (by omega) r z).symm) a₀
def rightPOVM (b₀ : B) (j : Fin S.l.length) (r : R) (z : Profile I X Y) : POVM (S.J×n) B :=
  POVM.transport (S.V j r z) (T.rightFine j r z) (T.rightFine_pos j r z)
    ((T.rightFine_total j r z).trans (S.V_gram (by omega) r z).symm) b₀

omit [DecidableEq B] in
lemma leftPOVM_local (a₀ : A) (j : Fin S.l.length) (r : R) : IgnoresRight (T.leftPOVM a₀ j r) S.l[j.val] := by
  intro z y
  have hU : S.U (j+1) r (updateRight z S.l[j.val] y) = S.U (j+1) r z :=
    congrArg (commonMap S.A) (chainLeft_next_local S.μ S.x₀ S.l S.nodup S.F S.localF j j.isLt r z y)
  have hF : T.leftFine j r (updateRight z S.l[j.val] y) = T.leftFine j r z := by
    funext a; exact T.leftFine_local j r a z y
  simp only [leftPOVM, hU, hF]
omit [DecidableEq A] in
lemma rightPOVM_local (b₀ : B) (j : Fin S.l.length) (r : R) : IgnoresLeft (T.rightPOVM b₀ j r) S.l[j.val] := by
  intro z x
  have hV : S.V j r (updateLeft z S.l[j.val] x) = S.V j r z :=
    congrArg (commonMap S.B) (chainRight_prev_local S.μ S.y₀ S.l S.nodup S.H S.localH j j.isLt r z x)
  have hH : T.rightFine j r (updateLeft z S.l[j.val] x) = T.rightFine j r z := by
    funext b; exact T.rightFine_local j r b z x
  simp only [rightPOVM, hV, hH]

instance coherentDecEq (l : List I) : DecidableEq (((ExposureIndex (R := R) (X := X) (Y := Y) l)×m)×(R×Profile I X Y)) :=
  @instDecidableEqProd _ _ (inferInstance : DecidableEq ((ExposureIndex (R := R) (X := X) (Y := Y) l)×m))
    (inferInstance : DecidableEq (R×Profile I X Y))

def P (a₀ : A) (j : Fin S.l.length) (x : X) : POVM ((S.J×m)×(R×Profile I X Y)) A := by
  classical
  exact POVM.blocks (fun t : R×Profile I X Y => T.leftPOVM a₀ j t.1 (Function.update t.2 S.l[j.val] (x,S.y₀)))
def Q (b₀ : B) (j : Fin S.l.length) (y : Y) : POVM ((S.J×n)×(R×Profile I X Y)) B := by
  classical
  exact POVM.blocks (fun t : R×Profile I X Y => T.rightPOVM b₀ j t.1 (Function.update t.2 S.l[j.val] (S.x₀,y)))

omit [DecidableEq B] in
lemma P_effect (a₀ : A) (j : Fin S.l.length) (q : X×Y) (a : A) :
    (T.P a₀ j q.1).effect a =
      Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.leftPOVM a₀ j t.1 (Function.update t.2 S.l[j.val] q)).effect a) := by
  change Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.leftPOVM a₀ j t.1 (Function.update t.2 S.l[j.val] (q.1,S.y₀))).effect a) = _
  apply congrArg Matrix.blockDiagonal
  funext t
  rw [ignoresRight_update (T.leftPOVM_local a₀ j t.1) t.2 q.1 S.y₀ q.2]
omit [DecidableEq A] in
lemma Q_effect (b₀ : B) (j : Fin S.l.length) (q : X×Y) (b : B) :
    (T.Q b₀ j q.2).effect b =
      Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.rightPOVM b₀ j t.1 (Function.update t.2 S.l[j.val] q)).effect b) := by
  change Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.rightPOVM b₀ j t.1 (Function.update t.2 S.l[j.val] (S.x₀,q.2))).effect b) = _
  apply congrArg Matrix.blockDiagonal
  funext t
  rw [ignoresLeft_update (T.rightPOVM_local b₀ j t.1) t.2 S.x₀ q.1 q.2]

lemma transported_prob (a₀ : A) (b₀ : B) (j : Fin S.l.length) (r : R) (z : Profile I X Y) (a : A) (b : B) :
    prob (S.U (j+1) r z*S.C*(S.V j r z)ᵀ) ((T.leftPOVM a₀ j r z).effect a) ((T.rightPOVM b₀ j r z).effect b) =
      prob S.C (T.leftFine j r z a) (T.rightFine j r z b) := by
  rw [← prob_pullback]
  simp only [leftPOVM, rightPOVM, POVM.transport_pullback]
end Refinement
end MixedExposure
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law MeasurementTransport
namespace QuantumSampling
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
lemma prob_weightedBlock (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C : R → Matrix m n ℂ)
    (P : R → Matrix m m ℂ) (Q : R → Matrix n n ℂ) :
    prob (weightedBlock w C) (Matrix.blockDiagonal P) (Matrix.blockDiagonal Q) = ∑ r, w r*prob (C r) (P r) (Q r) := by
  simp only [weightedBlock, prob_blockDiagonal, prob_smul, Real.sq_sqrt (hw _)]
end QuantumSampling
namespace MixedExposure
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
namespace Refinement
variable {S : EventSystem X Y I R m n} (T : Refinement S A B)

lemma prob_D (a₀ : A) (b₀ : B) (j : Fin S.l.length) (q : X×Y) (a : A) (b : B) :
    prob (S.D j q) ((T.P a₀ j q.1).effect a) ((T.Q b₀ j q.2).effect b) =
      massAt S.μ S.θ S.p S.l[j.val] S.C (fun r z => T.left S.l[j.val] r z a) (fun r z => T.right S.l[j.val] r z b) q := by
  rw [T.P_effect a₀ j q a, T.Q_effect b₀ j q b]
  simp only [EventSystem.D, stateAt]
  rw [prob_weightedBlock (fun t : R×Profile I X Y => (pi (fun _ : I => S.μ)).weight t.2*S.θ t.1 t.2/S.p)
    (fun t => div_nonneg (mul_nonneg ((pi (fun _ : I => S.μ)).nonneg t.2) (S.hθ t.1 t.2)) S.hp.le)]
  simp only [T.transported_prob, Fintype.sum_prod_type]
  have he : (∑ r, ∑ z, (pi (fun _ : I => S.μ)).weight z*S.θ r z/S.p *
      prob S.C (T.leftFine j r (Function.update z S.l[j.val] q) a) (T.rightFine j r (Function.update z S.l[j.val] q) b)) =
      massAt S.μ S.θ S.p S.l[j.val] S.C
        (chainLeft S.μ S.x₀ S.l (fun r z => T.left S.l[j.val] r z a) (j+1))
        (chainRight S.μ S.y₀ S.l (fun r z => T.right S.l[j.val] r z b) j) q := by
    unfold massAt
    simp only [avg, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro z _
    change _ = (1/S.p)*((pi (fun _ : I => S.μ)).weight z*(_*_))
    simp only [leftFine, rightFine, chainLeft, chainRight]
    ring
  rw [he]
  exact chain_fixed_mass S.μ S.x₀ S.y₀ S.l S.nodup S.C _ _
    (fun r i => T.left_local _ r a i) (fun r i => T.right_local _ r b i)
    S.θ S.localθL S.localθR S.p j q

def score (i : I) (V : X → Y → A → B → Bool) : ℝ :=
  (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
    ∑ a, ∑ b, if V (z i).1 (z i).2 a b then prob S.C (T.left i r z a) (T.right i r z b) else 0)

omit [DecidableEq X] [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] in
lemma avg_if_massAt (i : I) (hi : i ∈ S.l) (V : X×Y → Bool)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ) :
    S.μ.avg (fun q => if V q then massAt S.μ S.θ S.p i S.C F H q else 0) =
      (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
        (if V (z i) then prob S.C (F r z) (H r z) else 0)) := by
  have he : (fun q => if V q then massAt S.μ S.θ S.p i S.C F H q else 0) =
      (fun q => (1/S.p) • ∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
        (if V ((Function.update z i q) i) then prob S.C (F r (Function.update z i q)) (H r (Function.update z i q)) else 0))) := by
    funext q
    simp only [Function.update_self]
    split <;> simp_all [massAt, avg, smul_eq_mul]
  rw [he, avg_smul]
  congr 1
  exact fresh_avg_weighted S.μ i S.θ
    (fun r => S.localθL r i hi) (fun r => S.localθR r i hi)
    (fun r z => if V (z i) then prob S.C (F r z) (H r z) else 0)

lemma payoff_D_eq_score (a₀ : A) (b₀ : B) (j : Fin S.l.length) (V : X → Y → A → B → Bool) :
    S.μ.avg (fun q => payoff (S.D j q) (T.P a₀ j q.1) (T.Q b₀ j q.2) (V q.1 q.2)) = T.score S.l[j.val] V := by
  simp only [payoff, T.prob_D, avg_sum]
  simp only [avg_if_massAt (S := S) S.l[j.val] (List.getElem_mem j.isLt)]
  unfold score
  simp only [Finset.mul_sum, avg_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end Refinement
end MixedExposure
end ThresholdParallelRepetition

end

end OAI
