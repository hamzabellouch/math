import OAI.Probability.EntangledGames.Rounding

namespace OAI

universe u_X u_Y u_A u_B u_I u_m u_n

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

structure RepeatedModel (X : Type u_X) (Y : Type u_Y) (A : Type u_A) (B : Type u_B) (I : Type u_I) (m : Type u_m) (n : Type u_n) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] where
  μ : Law (X×Y)
  C : Matrix m n ℂ
  hC : hsSq C = 1
  P : (I → X) → POVM m (I → A)
  Q : (I → Y) → POVM n (I → B)
  V : X → Y → A → B → Bool

namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (M : RepeatedModel X Y A B I m n)
abbrev Result := Profile I X Y × ((I→A)×(I→B))
def answers (z : Profile I X Y) : Law ((I→A)×(I→B)) :=
  outcomeLaw M.C M.hC (M.P (fun i => (z i).1)) (M.Q (fun i => (z i).2))
def joint : Law (Result (X := X) (Y := Y) (A := A) (B := B) (I := I)) where
  weight t := (pi (fun _ : I => M.μ)).weight t.1 * (M.answers t.1).weight t.2
  nonneg t := mul_nonneg ((pi _).nonneg t.1) ((M.answers t.1).nonneg t.2)
  total := by simp only [Fintype.sum_prod_type, ← Finset.mul_sum, (M.answers _).total, mul_one, (pi _).total]
lemma joint_avg (f : Result (X := X) (Y := Y) (A := A) (B := B) (I := I) → ℝ) :
    M.joint.avg f = (pi (fun _ : I => M.μ)).avg (fun z => (M.answers z).avg (fun w => f (z,w))) := by
  simp only [avg, joint, smul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
def winsAt (t : Result (X := X) (Y := Y) (A := A) (B := B) (I := I)) (i : I) : Bool :=
  M.V (t.1 i).1 (t.1 i).2 (t.2.1 i) (t.2.2 i)
def indicator (c : Finset I) (t : Result (X := X) (Y := Y) (A := A) (B := B) (I := I)) : ℝ :=
  if ∀ i ∈ c, M.winsAt t i then 1 else 0
def mass (c : Finset I) : ℝ := M.joint.avg (M.indicator c)
lemma indicator_nonneg (c : Finset I) (t) : 0 ≤ M.indicator c t := by
  unfold indicator; split_ifs <;> norm_num
lemma indicator_le_one (c : Finset I) (t) : M.indicator c t ≤ 1 := by
  unfold indicator; split_ifs <;> norm_num
lemma mass_nonneg (c : Finset I) : 0 ≤ M.mass c := M.joint.avg_nonneg (M.indicator_nonneg c)
lemma mass_le_one (c : Finset I) : M.mass c ≤ 1 := M.joint.avg_le_const (M.indicator_le_one c)
lemma mass_empty : M.mass ∅ = 1 := by
  have he : M.indicator ∅ = fun _ => (1:ℝ) := by funext t; simp [indicator]
  rw [mass, he, avg_const]
lemma indicator_insert (c : Finset I) (i : I) (t) :
    M.indicator (insert i c) t = M.indicator c t * (if M.winsAt t i then 1 else 0) := by
  simp only [indicator, Finset.forall_mem_insert]
  split_ifs <;> simp_all
lemma mass_insert_le (c : Finset I) (i : I) : M.mass (insert i c) ≤ M.mass c := by
  apply M.joint.avg_mono
  intro t
  rw [indicator_insert]
  split_ifs <;> simp [M.indicator_nonneg]

abbrev Records (c : Finset I) := (c → A)×(c → B)
def restrictA (c : Finset I) (a : I→A) : c → A := fun i => a i
def restrictB (c : Finset I) (b : I→B) : c → B := fun i => b i
def mask (c : Finset I) (r : Records (A := A) (B := B) c) (z : Profile I X Y) : ℝ :=
  if ∀ i : c, M.V (z i).1 (z i).2 (r.1 i) (r.2 i) then 1 else 0
def coarseA (c : Finset I) (z : Profile I X Y) : POVM m (c → A) :=
  (M.P (fun i => (z i).1)).coarsen (restrictA c)
def coarseB (c : Finset I) (z : Profile I X Y) : POVM n (c → B) :=
  (M.Q (fun i => (z i).2)).coarsen (restrictB c)
lemma mask_restrict (c : Finset I) (z : Profile I X Y) (a : I→A) (b : I→B) :
    M.mask c (restrictA c a,restrictB c b) z = M.indicator c (z,a,b) := by
  simp only [mask, indicator, winsAt, restrictA, restrictB]
  congr 1
  exact propext Subtype.forall
lemma coarse_event (c : Finset I) (z : Profile I X Y) :
    (∑ r : Records (A := A) (B := B) c, M.mask c r z * prob M.C ((M.coarseA c z).effect r.1) ((M.coarseB c z).effect r.2)) =
      (M.answers z).avg (fun w => M.indicator c (z,w)) := by
  rw [Fintype.sum_prod_type, coarseA, coarseB, coarsen_prob_sum]
  simp only [mask_restrict, answers, outcomeLaw_avg, mul_comm]
lemma mask_nonneg (c : Finset I) (r) (z) : 0 ≤ M.mask c r z := by
  unfold mask; split_ifs <;> norm_num
lemma mask_le_one (c : Finset I) (r) (z) : M.mask c r z ≤ 1 := by
  unfold mask; split_ifs <;> norm_num
lemma coarse_event_le_one (c : Finset I) (z : Profile I X Y) :
    (∑ r : Records (A := A) (B := B) c, M.mask c r z * prob M.C ((M.coarseA c z).effect r.1) ((M.coarseB c z).effect r.2)) ≤ 1 := by
  rw [M.coarse_event]
  exact (M.answers z).avg_le_const (fun w => M.indicator_le_one c (z,w))
lemma mass_coarse (c : Finset I) :
    (∑ r : Records (A := A) (B := B) c, (pi (fun _ : I => M.μ)).avg (fun z => M.mask c r z *
      prob M.C ((M.coarseA c z).effect r.1) ((M.coarseB c z).effect r.2))) = M.mass c := by
  rw [← avg_sum]
  simp only [M.coarse_event]
  exact (M.joint_avg _).symm
end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace FiniteProbability.Law
variable {I : Type u_I} {X : Type u_X} {Y : Type u_Y} [DecidableEq I]
lemma firsts_updateRight (z : Profile I X Y) (i : I) (y : Y) :
    (fun j => (updateRight z i y j).1) = fun j => (z j).1 := by
  funext j
  by_cases h : j=i
  · subst j; simp [updateRight]
  · simp [updateRight, Function.update_of_ne h]
lemma seconds_updateLeft (z : Profile I X Y) (i : I) (x : X) :
    (fun j => (updateLeft z i x j).2) = fun j => (z j).2 := by
  funext j
  by_cases h : j=i
  · subst j; simp [updateLeft]
  · simp [updateLeft, Function.update_of_ne h]
end FiniteProbability.Law
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma coarseA_local (c : Finset I) (r : c→A) (i : I) : IgnoresRight (fun z => (M.coarseA c z).effect r) i := by
  intro z y
  simp only [coarseA, firsts_updateRight]
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma coarseB_local (c : Finset I) (r : c→B) (i : I) : IgnoresLeft (fun z => (M.coarseB c z).effect r) i := by
  intro z x
  simp only [coarseB, seconds_updateLeft]
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma mask_congr (c : Finset I) (r : Records (A := A) (B := B) c) {z z' : Profile I X Y}
    (hz : ∀ i ∈ c, z i = z' i) : M.mask c r z = M.mask c r z' := by
  simp only [mask]
  congr 1
  apply propext
  exact forall_congr' (fun i => by rw [hz i i.property])
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma mask_local_left (c : Finset I) (r : Records (A := A) (B := B) c) (i : I) (hi : i ∉ c) : IgnoresLeft (M.mask c r) i := by
  intro z x
  apply M.mask_congr
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _
omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma mask_local_right (c : Finset I) (r : Records (A := A) (B := B) c) (i : I) (hi : i ∉ c) : IgnoresRight (M.mask c r) i := by
  intro z y
  apply M.mask_congr
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _

def exposure (c : Finset I) (hp : 0 < M.mass c) : EventSystem X Y I (Records (A := A) (B := B) c) m n where
  μ := M.μ
  x₀ := Classical.arbitrary X
  y₀ := Classical.arbitrary Y
  l := cᶜ.toList
  nodup := cᶜ.nodup_toList
  C := M.C
  hC := M.hC
  F r z := (M.coarseA c z).effect r.1
  H r z := (M.coarseB c z).effect r.2
  hF r z := (M.coarseA c z).pos r.1
  hF1 r z := (M.coarseA c z).le_one r.1
  hH r z := (M.coarseB c z).pos r.2
  hH1 r z := (M.coarseB c z).le_one r.2
  localF r i := M.coarseA_local c r.1 i
  localH r i := M.coarseB_local c r.2 i
  θ := M.mask c
  hθ := M.mask_nonneg c
  hθ1 := M.mask_le_one c
  localθL r i hi := M.mask_local_left c r i (by simpa only [Finset.mem_toList, Finset.mem_compl] using hi)
  localθR r i hi := M.mask_local_right c r i (by simpa only [Finset.mem_toList, Finset.mem_compl] using hi)
  event_le_one := M.coarse_event_le_one c
  p := M.mass c
  hp := hp
  mass := M.mass_coarse c

def fineA (c : Finset I) (i : I) (z : Profile I X Y) : POVM m ((c→A)×A) :=
  (M.P (fun j => (z j).1)).coarsen (fun a => (restrictA c a,a i))
def fineB (c : Finset I) (i : I) (z : Profile I X Y) : POVM n ((c→B)×B) :=
  (M.Q (fun j => (z j).2)).coarsen (fun b => (restrictB c b,b i))

def refinement (c : Finset I) (hp : 0 < M.mass c) : Refinement (M.exposure c hp) A B where
  left i r z a := (M.fineA c i z).effect (r.1,a)
  right i r z b := (M.fineB c i z).effect (r.2,b)
  left_pos i r z a := (M.fineA c i z).pos (r.1,a)
  right_pos i r z b := (M.fineB c i z).pos (r.2,b)
  left_total i r z := POVM.coarsen_slice _ (restrictA c) (fun a => a i) r.1
  right_total i r z := POVM.coarsen_slice _ (restrictB c) (fun b => b i) r.2
  left_local i r a j := by intro z y; simp only [fineA, firsts_updateRight]
  right_local i r b j := by intro z x; simp only [fineB, seconds_updateLeft]
end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma fine_event (c : Finset I) (i : I) (z : Profile I X Y) :
    (∑ r : Records (A := A) (B := B) c, M.mask c r z *
      ∑ a, ∑ b, if M.V (z i).1 (z i).2 a b then
        prob M.C ((M.fineA c i z).effect (r.1,a)) ((M.fineB c i z).effect (r.2,b)) else 0) =
      (M.answers z).avg (fun w => M.indicator (insert i c) (z,w)) := by
  have hh := coarsen_prob_sum M.C (M.P (fun j => (z j).1)) (M.Q (fun j => (z j).2))
    (fun a => (restrictA c a,a i)) (fun b => (restrictB c b,b i))
    (fun ra rb => M.mask c (ra.1,rb.1) z * (if M.V (z i).1 (z i).2 ra.2 rb.2 then (1:ℝ) else 0))
  simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul] at hh
  simp only [Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]
  conv_lhs => arg 2; ext ra; rw [Finset.sum_comm]
  rw [show (∑ ra, ∑ a, ∑ rb, ∑ b, if M.V (z i).1 (z i).2 a b then
      M.mask c (ra,rb) z * prob M.C ((M.fineA c i z).effect (ra,a)) ((M.fineB c i z).effect (rb,b)) else 0) =
      ∑ a, ∑ b, if M.V (z i).1 (z i).2 (a i) (b i) then
        M.mask c (restrictA c a,restrictB c b) z * prob M.C ((M.P (fun j => (z j).1)).effect a) ((M.Q (fun j => (z j).2)).effect b) else 0 from hh]
  simp only [answers, outcomeLaw_avg, M.indicator_insert, M.mask_restrict, winsAt]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  split_ifs with h <;> simp [h, mul_comm]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B] in
lemma score_eq_mass_ratio (c : Finset I) (hp : 0 < M.mass c) (i : I) :
    (M.refinement c hp).score i M.V = M.mass (insert i c)/M.mass c := by
  unfold Refinement.score
  change (1/M.mass c)*∑ r : Records (A := A) (B := B) c,
    (pi (fun _ : I => M.μ)).avg (fun z => M.mask c r z *
      ∑ a, ∑ b, if M.V (z i).1 (z i).2 a b then
        prob M.C ((M.fineA c i z).effect (r.1,a)) ((M.fineB c i z).effect (r.2,b)) else 0) = _
  rw [← avg_sum]
  simp only [M.fine_event]
  rw [← M.joint_avg]
  change (1/M.mass c)*M.mass (insert i c) = _
  ring

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
omit [Fintype I] in
lemma card_records (c : Finset I) : Fintype.card (Records (A := A) (B := B) c) = (Fintype.card A*Fintype.card B)^c.card := by
  simp only [Records, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, mul_pow]

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI
