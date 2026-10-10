import OAI.Probability.EntangledGames.FreshStates

namespace OAI

universe u_X u_Y u_I u_R u_m u_n

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable (X : Type u_X) (Y : Type u_Y) (I : Type u_I) (R : Type u_R) (m : Type u_m) (n : Type u_n) [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

structure EventSystem where
  μ : Law (X×Y)
  x₀ : X
  y₀ : Y
  l : List I
  nodup : l.Nodup
  C : Matrix m n ℂ
  hC : hsSq C = 1
  F : R → Profile I X Y → Matrix m m ℂ
  H : R → Profile I X Y → Matrix n n ℂ
  hF : ∀ r z, (F r z).PosSemidef
  hF1 : ∀ r z, F r z ≤ 1
  hH : ∀ r z, (H r z).PosSemidef
  hH1 : ∀ r z, H r z ≤ 1
  localF : ∀ r i, IgnoresRight (F r) i
  localH : ∀ r i, IgnoresLeft (H r) i
  θ : R → Profile I X Y → ℝ
  hθ : ∀ r z, 0 ≤ θ r z
  hθ1 : ∀ r z, θ r z ≤ 1
  localθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i
  localθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i
  event_le_one : ∀ z, (∑ r, θ r z*prob C (F r z) (H r z)) ≤ 1
  p : ℝ
  hp : 0 < p
  mass : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*prob C (F r z) (H r z))) = p

variable {X Y I R m n} [Nonempty X] [Nonempty Y] [Nonempty R]
namespace EventSystem
variable (S : EventSystem X Y I R m n)
abbrev J := ExposureIndex (R := R) (X := X) (Y := Y) S.l
abbrev f := chainLeft S.μ S.x₀ S.l S.F
abbrev h := chainRight S.μ S.y₀ S.l S.H
abbrev A := chainLeftFamily S.μ S.x₀ S.l S.F
abbrev B := chainRightFamily S.μ S.y₀ S.l S.H

def U (j : ℕ) (r : R) (z : Profile I X Y) : Matrix (S.J×m) m ℂ := commonMap S.A (S.f j r z)
def V (j : ℕ) (r : R) (z : Profile I X Y) : Matrix (S.J×n) n ℂ := commonMap S.B (S.h j r z)

omit [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma f_pos (j : ℕ) (r : R) (z : Profile I X Y) : (S.f j r z).PosSemidef :=
  lefts_posSemidef S.μ S.x₀ _ _ (S.hF r) z
omit [DecidableEq X] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma h_pos (j : ℕ) (r : R) (z : Profile I X Y) : (S.h j r z).PosSemidef :=
  rights_posSemidef S.μ S.y₀ _ _ (S.hH r) z
lemma U_gram {j : ℕ} (hj : j ≤ S.l.length) (r : R) (z : Profile I X Y) :
    (S.U j r z)ᴴ*S.U j r z = S.f j r z :=
  commonMap_gram S.A (fun t => S.f_pos _ _ _) ⟨(⟨j, by omega⟩,r,z),rfl⟩
lemma V_gram {j : ℕ} (hj : j ≤ S.l.length) (r : R) (z : Profile I X Y) :
    (S.V j r z)ᴴ*S.V j r z = S.h j r z :=
  commonMap_gram S.B (fun t => S.h_pos _ _ _) ⟨(⟨j, by omega⟩,r,z),rfl⟩

def D (j : Fin S.l.length) : X×Y → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V j)
def rawA (j : Fin S.l.length) : X → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  fun x => stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V (j+1)) (x,S.y₀)
def rawB (j : Fin S.l.length) : Y → Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ :=
  fun y => stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U j) (S.V j) (S.x₀,y)

lemma rawA_eq (j : Fin S.l.length) (q : X×Y) : S.rawA j q.1 =
    stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V (j+1)) q := by
  apply stateAt_right_local
  · intro r z y
    exact congrArg (commonMap S.A) (chainLeft_next_local S.μ S.x₀ S.l S.nodup S.F S.localF j j.isLt r z y)
  · intro r z y
    apply congrArg (commonMap S.B)
    rw [h, chainRight_step S.μ S.y₀ S.l S.H j j.isLt r]
    exact right_ignoresRight S.μ S.y₀ _ _ z y
lemma rawB_eq (j : Fin S.l.length) (q : X×Y) : S.rawB j q.2 =
    stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U j) (S.V j) q := by
  apply stateAt_left_local
  · intro r z x
    apply congrArg (commonMap S.A)
    rw [f, chainLeft_step S.μ S.x₀ S.l S.F j j.isLt r]
    exact left_ignoresLeft S.μ S.x₀ _ _ z x
  · intro r z x
    exact congrArg (commonMap S.B) (chainRight_prev_local S.μ S.y₀ S.l S.nodup S.H S.localH j j.isLt r z x)

def density : Profile I X Y → ℝ := eventDensity S.θ S.p S.C S.F S.H
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_nonneg : ∀ z, 0 ≤ S.density z := eventDensity_nonneg S.θ S.hθ S.hp S.C S.F S.H S.hF S.hH
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_total : (pi (fun _ : I => S.μ)).avg S.density = 1 :=
  eventDensity_total S.μ S.θ S.hp S.C S.F S.H S.mass
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_le (z : Profile I X Y) : S.density z ≤ 1/S.p := by
  exact (mul_le_mul_of_nonneg_left (S.event_le_one z) (div_nonneg zero_le_one S.hp.le)).trans_eq (mul_one _)

lemma D_norm (j : Fin S.l.length) (q : X×Y) : hsSq (S.D j q) = coordDensity (fun _ : I => S.μ) S.density S.l[j.val] q := by
  rw [D, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  change massAt S.μ S.θ S.p S.l[j.val] S.C (S.f (j+1)) (S.h j) q = _
  rw [chain_fixed_mass S.μ S.x₀ S.y₀ S.l S.nodup S.C S.F S.H S.localF S.localH S.θ S.localθL S.localθR]
  exact massAt_eq_coordDensity S.μ S.θ S.p S.C S.F S.H _
    (fun r => S.localθL r _ (List.getElem_mem j.isLt)) (fun r => S.localθR r _ (List.getElem_mem j.isLt)) q

lemma rawA_norm (j : Fin S.l.length) (x : X) : hsSq (S.rawA j x) =
    (S.μ.givenFirst S.y₀ x).avg (fun y => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] (x,y)) := by
  rw [rawA, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h (j+1))
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  change massAt S.μ S.θ S.p S.l[j.val] S.C (S.f (j+1)) (S.h (j+1)) (x,S.y₀) = _
  have he : S.h (j+1) = fun r => S.μ.right S.y₀ S.l[j.val] (S.h j r) := by
    funext r; exact chainRight_step S.μ S.y₀ S.l S.H j j.isLt r
  rw [he, massAt_right S.μ S.y₀ S.θ S.p _ S.C _ _
    (chainLeft_next_local S.μ S.x₀ S.l S.nodup S.F S.localF j j.isLt)]
  congr 1; funext y
  rw [← S.D_norm j (x,y), D, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  rfl
lemma rawB_norm (j : Fin S.l.length) (y : Y) : hsSq (S.rawB j y) =
    (S.μ.givenSecond S.x₀ y).avg (fun x => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] (x,y)) := by
  rw [rawB, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f j) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  change massAt S.μ S.θ S.p S.l[j.val] S.C (S.f j) (S.h j) (S.x₀,y) = _
  have he : S.f j = fun r => S.μ.left S.x₀ S.l[j.val] (S.f (j+1) r) := by
    funext r; exact chainLeft_step S.μ S.x₀ S.l S.F j j.isLt r
  rw [he, massAt_left S.μ S.x₀ S.θ S.p _ S.C _ _
    (chainRight_prev_local S.μ S.y₀ S.l S.nodup S.H S.localH j j.isLt)]
  congr 1; funext x
  rw [← S.D_norm j (x,y), D, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  rfl
end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI
