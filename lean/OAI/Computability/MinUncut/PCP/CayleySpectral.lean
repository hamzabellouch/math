import Mathlib
import OAI.Computability.MinUncut.PCP.CayleySampling

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open MinUncutGames.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}

def zeroFrequency : Cube I := fun _ => false

theorem cubeXor_cancel_right (x y : Cube I) :
    cubeXor (cubeXor x y) y = x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [cubeXor, hx, hy]

theorem cubeXor_assoc (x y z : Cube I) :
    cubeXor (cubeXor x y) z = cubeXor x (cubeXor y z) := by
  funext i
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
    simp [cubeXor, hx, hy, hz]

@[simp] theorem cubeXor_zeroFrequency (x : Cube I) :
    cubeXor x zeroFrequency = x := by
  funext i
  cases hx : x i <;> simp [cubeXor, zeroFrequency, hx]

def xorTranslation (y : Cube I) : Cube I ≃ Cube I where
  toFun x := cubeXor x y
  invFun x := cubeXor x y
  left_inv x := cubeXor_cancel_right x y
  right_inv x := cubeXor_cancel_right x y

def rotate (g : D → Cube I) (p : Cube I × D) : Cube I × D :=
  (cubeXor p.1 (g p.2), p.2)

theorem rotate_involutive (g : D → Cube I) : Function.Involutive (rotate g) := by
  rintro ⟨x, d⟩
  change (cubeXor (cubeXor x (g d)) (g d), d) = (x, d)
  rw [cubeXor_cancel_right]

def cayleyGraph (g : D → Cube I) : PortGraph (Cube I) D where
  rot :=
    { toFun := rotate g
      invFun := rotate g
      left_inv := rotate_involutive g
      right_inv := rotate_involutive g }
  rot_involutive := rotate_involutive g

@[simp] theorem cayleyGraph_rot (g : D → Cube I) (x : Cube I) (d : D) :
    (cayleyGraph g).rot (x, d) = (cubeXor x (g d), d) := rfl

def splitPortWord (n : Nat) : (Fin (n + 1) → D) ≃ D × (Fin n → D) where
  toFun p := (p 0, fun j => p j.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv p := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def powerGenerators (g : D → Cube I) : (n : Nat) → (Fin n → D) → Cube I
  | 0, _ => zeroFrequency
  | n + 1, p => cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ))

theorem wordEnd_eq_powerGenerators (g : D → Cube I) (n : Nat)
    (x : Cube I) (p : Fin n → D) :
    wordEnd (cayleyGraph g) n x p = cubeXor x (powerGenerators g n p) := by
  induction n generalizing x with
  | zero => simp [wordEnd, powerGenerators]
  | succ n ih =>
    change wordEnd (cayleyGraph g) n (cubeXor x (g (p 0))) (fun j => p j.succ) =
      cubeXor x (cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ)))
    rw [ih, cubeXor_assoc]


variable [Fintype I] [DecidableEq I] [Fintype D]

def cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (x : Cube I) : ℝ :=
  𝔼 d, f ((cayleyGraph g).rot (x, d)).1

def eigenvalue (g : D → Cube I) (s : Cube I) : ℝ :=
  𝔼 d, walsh s (g d)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem averagingOperator_cayleyGraph (g : D → Cube I) (f : Cube I → ℝ) :
    SpectralReturn.averagingOperator (cayleyGraph g) f = cayleyAverage g f := rfl

@[simp] theorem coefficient_zeroFrequency (f : Cube I → ℝ) :
    coefficient f zeroFrequency = 𝔼 x, f x := by
  simp [coefficient, zeroFrequency, walsh, bitSign]

theorem coefficient_xorTranslation (f : Cube I → ℝ) (s v : Cube I) :
    coefficient (fun x => f (cubeXor x v)) s = walsh s v * coefficient f s := by
  calc
    coefficient (fun x => f (cubeXor x v)) s =
        𝔼 x, f x * walsh s (cubeXor x v) := by
      unfold coefficient
      apply Fintype.expect_equiv (xorTranslation v)
      intro x
      change f (cubeXor x v) * walsh s x =
        f (cubeXor x v) * walsh s (cubeXor (cubeXor x v) v)
      rw [cubeXor_cancel_right]
    _ = 𝔼 x, (f x * walsh s x) * walsh s v := by
      apply Finset.expect_congr rfl
      intro x _
      rw [walsh_xor]
      ring
    _ = coefficient f s * walsh s v := by
      rw [← Finset.expect_mul]
      rfl
    _ = walsh s v * coefficient f s := mul_comm _ _

theorem cayleyAverage_walsh (g : D → Cube I) (s x : Cube I) :
    cayleyAverage g (walsh s) x = eigenvalue g s * walsh s x := by
  unfold cayleyAverage
  simp only [cayleyGraph_rot, walsh_xor]
  rw [← Finset.mul_expect]
  rw [mul_comm]
  rfl

theorem coefficient_cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (cayleyAverage g f) s = eigenvalue g s * coefficient f s := by
  calc
    coefficient (cayleyAverage g f) s =
        𝔼 x, 𝔼 d, f (cubeXor x (g d)) * walsh s x := by
      unfold coefficient cayleyAverage
      simp only [cayleyGraph_rot, Finset.expect_mul]
    _ = 𝔼 d, 𝔼 x, f (cubeXor x (g d)) * walsh s x := by
      rw [Finset.expect_comm]
    _ = 𝔼 d, walsh s (g d) * coefficient f s := by
      apply Finset.expect_congr rfl
      intro d _
      exact coefficient_xorTranslation f s (g d)
    _ = eigenvalue g s * coefficient f s := by
      rw [← Finset.expect_mul]
      rfl

theorem eigenvalue_powerGenerators (g : D → Cube I) (n : Nat) (s : Cube I) :
    eigenvalue (powerGenerators g n) s = eigenvalue g s ^ n := by
  induction n with
  | zero =>
    let : Nonempty (Fin 0 → D) := ⟨fun i => Fin.elim0 i⟩
    simp [eigenvalue, powerGenerators, zeroFrequency, walsh, bitSign]
  | succ n ih =>
    calc
      eigenvalue (powerGenerators g (n + 1)) s =
          𝔼 z : D × (Fin n → D),
            walsh s (cubeXor (g z.1) (powerGenerators g n z.2)) := by
        unfold eigenvalue
        apply Fintype.expect_equiv (splitPortWord n)
        intro p
        rfl
      _ = 𝔼 d, 𝔼 p : Fin n → D,
          walsh s (cubeXor (g d) (powerGenerators g n p)) := by
        exact SpectralReturn.mean_prod _
      _ = eigenvalue g s * eigenvalue (powerGenerators g n) s := by
        simp_rw [walsh_xor, ← Finset.mul_expect]
        rw [← Finset.expect_mul]
        rfl
      _ = eigenvalue g s ^ (n + 1) := by
        rw [ih, pow_succ, mul_comm]

theorem power_port_card (n : Nat) :
    Fintype.card (Fin n → D) = Fintype.card D ^ n := by
  simp only [Fintype.card_fun, Fintype.card_fin]

theorem seven_power_port_card :
    Fintype.card (Fin 7 → Fin (2 ^ 16)) = (2 ^ 16) ^ 7 := by
  simp only [Fintype.card_fun, Fintype.card_fin]

theorem cayley_energy_contraction (g : D → Cube I) (lambda : ℝ) (_hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (f : Cube I → ℝ) (hmean : (𝔼 x, f x) = 0) :
    (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2) := by
  classical
  have hzero : coefficient f zeroFrequency = 0 := by
    rw [coefficient_zeroFrequency]
    exact hmean
  calc
    (𝔼 x, cayleyAverage g f x ^ 2) =
        ∑ s, coefficient (cayleyAverage g f) s ^ 2 := (walsh_parseval _).symm
    _ = ∑ s, (eigenvalue g s * coefficient f s) ^ 2 := by
      simp only [coefficient_cayleyAverage]
    _ ≤ ∑ s, lambda ^ 2 * coefficient f s ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s = zeroFrequency
      · subst s
        simp [hzero]
      · have hb := hbias s hs
        have hlo : -lambda ≤ eigenvalue g s := (abs_le.mp hb).1
        have hhi : eigenvalue g s ≤ lambda := (abs_le.mp hb).2
        have hprod : 0 ≤ (lambda - eigenvalue g s) * (lambda + eigenvalue g s) :=
          mul_nonneg (sub_nonneg.mpr hhi) (by linarith)
        have hsq : eigenvalue g s ^ 2 ≤ lambda ^ 2 := by nlinarith
        calc
          (eigenvalue g s * coefficient f s) ^ 2 =
              eigenvalue g s ^ 2 * coefficient f s ^ 2 := by rw [mul_pow]
          _ ≤ lambda ^ 2 * coefficient f s ^ 2 :=
            mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = lambda ^ 2 * (𝔼 x, f x ^ 2) := by
      rw [← Finset.mul_sum, walsh_parseval]

theorem cayley_spectralCertificate (g : D → Cube I) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambdaone : lambda < 1)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda) :
    SpectralReturn.SpectralCertificate (cayleyGraph g) lambda where
  nonnegative := hlambda
  lt_one := hlambdaone
  contraction := by
    intro f hf
    change (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2)
    exact cayley_energy_contraction g lambda hlambda hbias f hf

theorem power_eigenvalue_bound (g : D → Cube I) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (n : Nat) (s : Cube I) (hs : s ≠ zeroFrequency) :
    |eigenvalue (powerGenerators g n) s| ≤ lambda ^ n := by
  rw [eigenvalue_powerGenerators, abs_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih (hbias s hs) (abs_nonneg _) (pow_nonneg hlambda _)

theorem sevenStep_halfCertificate (g : D → Cube I)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ (1 / 2 : ℝ)) :
    SpectralReturn.SpectralCertificate (cayleyGraph (powerGenerators g 7))
      ((1 / 2 : ℝ) ^ 7) := by
  apply cayley_spectralCertificate
  · norm_num
  · norm_num
  · intro s hs
    exact power_eigenvalue_bound g (1 / 2) (by norm_num) hbias 7 s hs


end MinUncutGames.Foundations.PCP.CayleySpectral


namespace MinUncutGames.Foundations.PCP.Expanders

open scoped BigOperators
open MinUncutGames.Foundations.Hastad
open CayleySpectral

abbrev Generators (n m : Nat) := Fin (4 * m) → Cube (Fin n)

def badFrequency {n m : Nat} (g : Generators n m) (s : Cube (Fin n)) : ℝ :=
  if s = zeroFrequency then 0 else
    if CayleyTailCount.badWord m (fun d => AssignmentTester.parity s (g d)) then 1 else 0

def badMass {n m : Nat} (g : Generators n m) : ℝ :=
  ∑ s : Cube (Fin n), badFrequency g s

theorem badFrequency_nonnegative {n m : Nat}
    (g : Generators n m) (s : Cube (Fin n)) : 0 ≤ badFrequency g s := by
  unfold badFrequency
  split_ifs <;> norm_num

theorem mean_badFrequency_le {n m : Nat} (s : Cube (Fin n)) :
    (𝔼 g : Generators n m, badFrequency g s) ≤ 2 * (2 / 3 : ℝ) ^ m := by
  classical
  by_cases hs : s = zeroFrequency
  · simp only [badFrequency, ite_eq_left hs, Finset.expect_const_zero]
    positivity
  · have hs' : s ≠ (fun _ => false) := hs
    simp only [badFrequency, ite_eq_right hs]
    rw [CayleySampling.expect_parity_samples s hs'
      (fun w : Fin (4 * m) → Bool => if CayleyTailCount.badWord m w then (1 : ℝ) else 0)]
    exact CayleyTailCount.twoTail_probability m (by simp)

theorem mean_badMass_le (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    (𝔼 g : Generators n m, badMass g) ≤ 1 / 2 := by
  calc
    _ = ∑ s : Cube (Fin n), 𝔼 g : Generators n m, badFrequency g s := by
      unfold badMass
      rw [Finset.expect_sum_comm]
    _ ≤ ∑ _s : Cube (Fin n), 2 * (2 / 3 : ℝ) ^ m :=
      Finset.sum_le_sum (fun s _ => mean_badFrequency_le s)
    _ = (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) := by
      simp [Cube]
    _ ≤ 1 / 2 := CayleyTailCount.union_bound_le_half n m hm

theorem exists_generators (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    ∃ g : Generators n m, ∀ s : Cube (Fin n),
      s ≠ zeroFrequency → |eigenvalue g s| ≤ (1 / 2 : ℝ) := by
  classical
  have hmpos : 0 < m := by omega
  let : Nonempty (Fin (4 * m)) := ⟨⟨0, by omega⟩⟩
  have havg : (𝔼 g : Generators n m, badMass g) < (1 : ℝ) :=
    lt_of_le_of_lt (mean_badMass_le n m hm) (by norm_num)
  obtain ⟨g, _, hg⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty havg
  refine ⟨g, fun s hs => ?_⟩
  have hgood : ¬ CayleyTailCount.badWord m
      (fun d => AssignmentTester.parity s (g d)) := by
    intro hbad
    have hsingle : badFrequency g s ≤ badMass g :=
      Finset.single_le_sum (fun t _ => badFrequency_nonnegative g t) (Finset.mem_univ s)
    simp only [badFrequency, ite_eq_right hs, ite_eq_left hbad] at hsingle
    exact (not_le_of_gt hg) hsingle
  unfold eigenvalue
  simp_rw [← AssignmentTester.bitSign_parity]
  exact CayleyTailCount.not_badWord_bias m (by simp) hmpos _ hgood

def baseDimension : Nat := 448
def initialDegree : Nat := 2 ^ 16
def initialQuarterDegree : Nat := 2 ^ 14
def basePower : Nat := 7

theorem base_arithmetic :
    4 * initialQuarterDegree = initialDegree ∧
    3 * (baseDimension + 2) ≤ initialQuarterDegree ∧
    (2 : Nat) ^ baseDimension = (initialDegree ^ basePower) ^ 4 ∧
    (1 / 2 : ℝ) ^ basePower ≤ 1 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [initialDegree, initialQuarterDegree]
  · norm_num [baseDimension, initialQuarterDegree]
  · simpa only [baseDimension, initialDegree, basePower] using
      CayleyTailCount.seventh_power_size
  · norm_num [basePower]

theorem exists_initial_generators :
    ∃ g : Generators baseDimension initialQuarterDegree,
      ∀ s : Cube (Fin baseDimension), s ≠ zeroFrequency →
        |eigenvalue g s| ≤ (1 / 2 : ℝ) :=
  exists_generators _ _ base_arithmetic.2.1

abbrev BaseVertex := Cube (Fin baseDimension)
abbrev BasePort := Fin basePower → Fin (4 * initialQuarterDegree)
def baseDegree : Nat := initialDegree ^ basePower

theorem card_basePort : Fintype.card BasePort = baseDegree := by
  simp only [BasePort, Fintype.card_fun, Fintype.card_fin]
  rw [base_arithmetic.1]
  rfl

theorem card_baseVertex : Fintype.card BaseVertex = baseDegree ^ 4 := by
  simpa only [BaseVertex, Cube, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, baseDegree] using base_arithmetic.2.2.1

theorem exists_baseGraph :
    ∃ H : PoweringWalks.PortGraph BaseVertex BasePort,
      SpectralReturn.SpectralCertificate H (1 / 100 : ℝ) := by
  obtain ⟨g, hg⟩ := exists_initial_generators
  refine ⟨cayleyGraph (powerGenerators g basePower), ?_⟩
  apply cayley_spectralCertificate
  · norm_num
  · norm_num
  · intro s hs
    exact (power_eigenvalue_bound g (1 / 2) (by norm_num) hg basePower s hs).trans
      base_arithmetic.2.2.2

end MinUncutGames.Foundations.PCP.Expanders

end
namespace MinUncutGames.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

def reindex (G : PortGraph V D) (vertices : V ≃ W) (ports : D ≃ E) :
    PortGraph W E where
  rot := (Equiv.prodCongr vertices ports).symm.trans
    (G.rot.trans (Equiv.prodCongr vertices ports))
  rot_involutive := by
    intro x
    change (Equiv.prodCongr vertices ports)
        (G.rot ((Equiv.prodCongr vertices ports).symm
          ((Equiv.prodCongr vertices ports)
            (G.rot ((Equiv.prodCongr vertices ports).symm x))))) = x
    rw [Equiv.symm_apply_apply, G.rot_involutive, Equiv.apply_symm_apply]

@[simp] theorem reindex_rot (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (v : V) (d : D) :
    (reindex G vertices ports).rot (vertices v, ports d) =
      (vertices (G.rot (v, d)).1, ports (G.rot (v, d)).2) := by
  simp [reindex, Equiv.trans_apply, Prod.map]


variable [Fintype V] [Fintype W] [Fintype D] [Fintype E]

omit [Fintype V] [Fintype W] in
theorem operator_reindex (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (f : W → ℝ) (w : W) :
    averagingOperator (reindex G vertices ports) f w =
      averagingOperator G (fun v => f (vertices v)) (vertices.symm w) := by
  unfold averagingOperator
  apply Fintype.expect_equiv ports.symm
  intro e
  rfl

theorem energy_reindex (vertices : V ≃ W) (f : W → ℝ) :
    energy (fun v => f (vertices v)) = energy f :=
  mean_equiv vertices (fun w => f w ^ 2)

theorem reindex_spectralCertificate (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (lambda : ℝ) (certificate : SpectralCertificate G lambda) :
    SpectralCertificate (reindex G vertices ports) lambda where
  nonnegative := certificate.nonnegative
  lt_one := certificate.lt_one
  contraction := by
    intro f hf
    have hf' : mean (fun v => f (vertices v)) = 0 :=
      (mean_equiv vertices f).trans hf
    have h := certificate.contraction (fun v => f (vertices v)) hf'
    have hout : energy (averagingOperator (reindex G vertices ports) f) =
        energy (averagingOperator G (fun v => f (vertices v))) := by
      rw [← energy_reindex vertices]
      congr 1
      funext v
      rw [operator_reindex, vertices.symm_apply_apply]
    rw [hout, ← energy_reindex vertices f]
    exact h


end MinUncutGames.Foundations.PCP.GraphTransport

namespace MinUncutGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

def squareFirst (G : PortGraph V D) (s : V × (D × D)) : V × (D × D) :=
  let step := G.rot (s.1, s.2.1)
  (step.1, (step.2, s.2.2))

theorem squareFirst_involutive (G : PortGraph V D) : Function.Involutive (squareFirst G) := by
  rintro ⟨v, d₁, d₂⟩
  change ((G.rot (G.rot (v, d₁))).1, ((G.rot (G.rot (v, d₁))).2, d₂)) =
    (v, (d₁, d₂))
  rw [G.rot_involutive]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

def square (G : PortGraph V D) : PortGraph V (D × D) := by
  let B := involutionEquiv (squareFirst G) (squareFirst_involutive G)
  let P := involutionEquiv (squareSwap (V := V) (D := D)) squareSwap_involutive
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (squareFirst_involutive G) squareSwap_involutive }

@[simp] theorem square_rot_apply (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    (square G).rot (v, (d₁, d₂)) =
      let first := G.rot (v, d₁)
      let second := G.rot (first.1, d₂)
      (second.1, (second.2, first.2)) := rfl

@[simp] theorem square_next (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    next (square G) v (d₁, d₂) = next G (next G v d₁) d₂ := rfl

def cloudFirst (H : PortGraph D E) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) :=
  let step := H.rot (s.1.2, s.2.1)
  ((s.1.1, step.1), (step.2, s.2.2))

theorem cloudFirst_involutive (H : PortGraph D E) :
    Function.Involutive (cloudFirst (V := V) H) := by
  rintro ⟨⟨v, d⟩, ⟨e₁, e₂⟩⟩
  change ((v, (H.rot (H.rot (d, e₁))).1), ((H.rot (H.rot (d, e₁))).2, e₂)) =
    ((v, d), (e₁, e₂))
  rw [H.rot_involutive]

def crossCloud (G : PortGraph V D) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) := (G.rot s.1, (s.2.2, s.2.1))

theorem crossCloud_involutive (G : PortGraph V D) :
    Function.Involutive (crossCloud (E := E) G) := by
  rintro ⟨x, e₁, e₂⟩
  change (G.rot (G.rot x), (e₁, e₂)) = (x, (e₁, e₂))
  rw [G.rot_involutive]

def zigzag (G : PortGraph V D) (H : PortGraph D E) : PortGraph (V × D) (E × E) := by
  let B := involutionEquiv (cloudFirst (V := V) H) (cloudFirst_involutive H)
  let P := involutionEquiv (crossCloud (E := E) G) (crossCloud_involutive G)
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (cloudFirst_involutive H) (crossCloud_involutive G) }

@[simp] theorem zigzag_rot_apply (G : PortGraph V D) (H : PortGraph D E)
    (v : V) (d : D) (e₁ e₂ : E) :
    (zigzag G H).rot ((v, d), (e₁, e₂)) =
      let first := H.rot (d, e₁)
      let middle := G.rot (v, first.1)
      let last := H.rot (middle.2, e₂)
      ((middle.1, last.1), (last.2, first.2)) := rfl

theorem natCard_square_ports : Nat.card (D × D) = Nat.card D ^ 2 := by
  simp [Nat.card_prod, pow_two]

theorem natCard_square_edges :
    Nat.card (Edge V (D × D)) = Nat.card V * Nat.card D ^ 2 := by
  simp [Edge, Nat.card_prod, pow_two]

theorem natCard_zigzag_vertices :
    Nat.card (V × D) = Nat.card V * Nat.card D := Nat.card_prod V D

theorem natCard_zigzag_ports : Nat.card (E × E) = Nat.card E ^ 2 := by
  simp [Nat.card_prod, pow_two]

theorem natCard_zigzag_edges :
    Nat.card (Edge (V × D) (E × E)) =
      Nat.card V * Nat.card D * Nat.card E ^ 2 := by
  simp [Edge, Nat.card_prod, pow_two]

noncomputable section

def cloudOperator [Fintype E] (H : PortGraph D E) (f : V × D → ℝ) (x : V × D) : ℝ :=
  SpectralReturn.mean (fun e => f (x.1, (H.rot (x.2, e)).1))

def graphPermutation (G : PortGraph V D) (f : V × D → ℝ) (x : V × D) : ℝ :=
  f (G.rot x)

theorem averagingOperator_square [Fintype D] (G : PortGraph V D) (f : V → ℝ) :
    SpectralReturn.averagingOperator (square G) f =
      SpectralReturn.averagingOperator G (SpectralReturn.averagingOperator G f) := by
  funext v
  let w : D × D → ℝ := fun ds => f (G.rot ((G.rot (v, ds.1)).1, ds.2)).1
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun d₁ => SpectralReturn.mean (fun d₂ => w (d₁, d₂)))
  exact SpectralReturn.mean_prod w

theorem averagingOperator_zigzag [Fintype E] (G : PortGraph V D)
    (H : PortGraph D E) (f : V × D → ℝ) :
    SpectralReturn.averagingOperator (zigzag G H) f =
      cloudOperator H (graphPermutation G (cloudOperator H f)) := by
  funext x
  rcases x with ⟨v, d⟩
  let w : E × E → ℝ := fun es =>
    let first := H.rot (d, es.1)
    let middle := G.rot (v, first.1)
    let last := H.rot (middle.2, es.2)
    f (middle.1, last.1)
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun e₁ => SpectralReturn.mean (fun e₂ => w (e₁, e₂)))
  exact SpectralReturn.mean_prod w

end

end MinUncutGames.Foundations.PCP.ZigzagGraphs

namespace MinUncutGames.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def liftCloud (f : V → ℝ) (x : V × D) : ℝ := f x.1

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

theorem mean_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    mean (liftCloud (D := D) f) = mean f := by
  change mean (fun x : V × D => f x.1) = mean f
  rw [mean_prod]
  simp only [mean_const]

theorem energy_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    energy (liftCloud (D := D) f) = energy f :=
  mean_liftCloud (D := D) (fun v => f v ^ 2)

theorem mean_cloudMean [Fintype V] [Fintype D] (f : V × D → ℝ) :
    mean (cloudMean f) = mean f := (mean_prod f).symm

theorem energy_prod [Fintype V] [Fintype D] (f : V × D → ℝ) :
    energy f = mean (fun v => energy (fun d => f (v, d))) :=
  mean_prod (fun x => f x ^ 2)

theorem cloudMean_centered_zero [Fintype D] [Nonempty D]
    (f : V × D → ℝ) (v : V) : cloudMean (centered f) v = 0 := by
  change mean (fun d => f (v, d) - cloudMean f v) = 0
  rw [mean_sub, mean_const]
  exact sub_self _

theorem energy_centered_eq_sub [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) = energy f - energy (projection f) := by
  have hpoint (v : V) : energy (fun d => centered f (v, d)) =
      energy (fun d => f (v, d)) - (cloudMean f v) ^ 2 := by
    change energy (fun d => f (v, d) - cloudMean f v) = _
    rw [energy_sub_const]
    change energy (fun d => f (v, d)) - 2 * cloudMean f v * cloudMean f v +
      (cloudMean f v) ^ 2 = _
    ring
  have hproj : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  calc
    energy (centered f) = mean (fun v => energy (fun d => centered f (v, d))) :=
      energy_prod _
    _ = mean (fun v => energy (fun d => f (v, d)) - (cloudMean f v) ^ 2) := by
      congr 1
      funext v
      exact hpoint v
    _ = mean (fun v => energy (fun d => f (v, d))) -
        mean (fun v => (cloudMean f v) ^ 2) := mean_sub _ _
    _ = energy f - energy (projection f) := by
      rw [← energy_prod f, hproj]
      rfl

theorem projection_energy_decomposition [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy f = energy (projection f) + energy (centered f) := by
  rw [energy_centered_eq_sub]
  ring

theorem energy_projection_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (projection f) ≤ energy f := by
  have h := projection_energy_decomposition f
  have hn := energy_nonnegative (centered f)
  linarith

theorem energy_centered_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) ≤ energy f := by
  rw [energy_centered_eq_sub]
  exact sub_le_self _ (energy_nonnegative _)

theorem mean_sq_le_energy {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    mean f ^ 2 ≤ energy f := by
  have h := correlation_sq_le f (fun _ => 1)
  simpa [correlation, energy] using h

theorem averaging_energy_le [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) : energy (averagingOperator G f) ≤ energy f := by
  calc
    energy (averagingOperator G f) ≤ mean (averagingOperator G (fun v => f v ^ 2)) := by
      apply mean_mono
      intro v
      exact mean_sq_le_energy (fun d => f (G.rot (v, d)).1)
    _ = energy f := mean_operator G _

theorem cloudOperator_add [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f + g) = cloudOperator H f + cloudOperator H g := by
  funext x
  exact mean_add _ _

theorem cloudOperator_sub [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f - g) = cloudOperator H f - cloudOperator H g := by
  funext x
  exact mean_sub _ _

theorem cloudOperator_projection [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) : cloudOperator H (projection f) = projection f := by
  funext x
  change mean (fun _ : E => cloudMean f x.1) = cloudMean f x.1
  exact mean_const _

theorem cloudOperator_centered [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) :
    cloudOperator H (centered f) = cloudOperator H f - projection f := by
  unfold centered
  rw [cloudOperator_sub, cloudOperator_projection]

theorem graphPermutation_energy [Fintype V] [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) : energy (graphPermutation G f) = energy f :=
  mean_equiv G.rot (fun x => f x ^ 2)

theorem cloud_energy_le [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (f : V × D → ℝ) :
    energy (cloudOperator H f) ≤ energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => energy (fun d => f (v, d))) :=
      mean_mono (fun v => averaging_energy_le H _)
    _ = energy f := (energy_prod f).symm

theorem cloud_centered_contraction [Fintype V] [Fintype D] [Fintype E]
    (H : PortGraph D E) (lambda : ℝ) (hH : SpectralCertificate H lambda)
    (f : V × D → ℝ) (hzero : ∀ v, cloudMean f v = 0) :
    energy (cloudOperator H f) ≤ lambda ^ 2 * energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => lambda ^ 2 * energy (fun d => f (v, d))) :=
      mean_mono (fun v => hH.contraction _ (hzero v))
    _ = lambda ^ 2 * mean (fun v => energy (fun d => f (v, d))) := mean_mul_left _ _
    _ = lambda ^ 2 * energy f := by rw [← energy_prod f]

theorem cloud_residual_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (lambda : ℝ)
    (hH : SpectralCertificate H lambda) (f : V × D → ℝ) :
    energy (cloudOperator H f - projection f) ≤ lambda ^ 2 * energy f := by
  rw [← cloudOperator_centered H f]
  exact (cloud_centered_contraction H lambda hH (centered f)
    (cloudMean_centered_zero f)).trans
      (mul_le_mul_of_nonneg_left (energy_centered_le f) (sq_nonneg lambda))

theorem projection_graphPermutation_projection [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) :
    projection (graphPermutation G (projection f)) =
      liftCloud (averagingOperator G (cloudMean f)) := rfl

theorem projected_outer_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (projection (graphPermutation G (projection f))) ≤
      lambda ^ 2 * energy (projection f) := by
  have hzero : mean (cloudMean f) = 0 := (mean_cloudMean f).trans hf
  have hleft : energy (projection (graphPermutation G (projection f))) =
      energy (averagingOperator G (cloudMean f)) := by
    rw [projection_graphPermutation_projection]
    exact energy_liftCloud _
  have hright : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  rw [hleft, hright]
  exact hG.contraction _ hzero

theorem energy_add_three_le {A : Type*} [Fintype A] (a b c : A → ℝ) :
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := by
  calc
    energy (a + b + c) ≤ mean (fun x => 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)) := by
      apply mean_mono
      intro x
      change (a x + b x + c x) ^ 2 ≤ 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - c x), sq_nonneg (b x - c x)]
    _ = 3 * (energy a + energy b + energy c) := by
      rw [mean_mul_left, mean_add, mean_add]
      rfl

theorem zigzag_energy_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph D E) (lambdaG lambdaH : ℝ)
    (hG : SpectralCertificate G lambdaG) (hH : SpectralCertificate H lambdaH)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (zigzag G H) f) ≤
      3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
  let u := projection f
  let v := centered f
  let a := projection (graphPermutation G u)
  let b := cloudOperator H (graphPermutation G u) - a
  let c := cloudOperator H (graphPermutation G (cloudOperator H v))
  have hfactor : averagingOperator (zigzag G H) f = a + b + c := by
    rw [averagingOperator_zigzag]
    have hf' : f = u + v := by
      funext x
      change f x = projection f x + (f x - projection f x)
      ring
    have hbu : cloudOperator H u = u := cloudOperator_projection H f
    have hbf : cloudOperator H f = u + cloudOperator H v := by
      rw [hf', cloudOperator_add, hbu]
    rw [hbf]
    have hp : graphPermutation G (u + cloudOperator H v) =
        graphPermutation G u + graphPermutation G (cloudOperator H v) := rfl
    rw [hp, cloudOperator_add]
    change cloudOperator H (graphPermutation G u) + c =
      a + (cloudOperator H (graphPermutation G u) - a) + c
    funext x
    change cloudOperator H (graphPermutation G u) x + c x =
      a x + (cloudOperator H (graphPermutation G u) x - a x) + c x
    ring
  have ha : energy a ≤ lambdaG ^ 2 * energy u := projected_outer_bound G lambdaG hG f hf
  have hb : energy b ≤ lambdaH ^ 2 * energy u := by
    have h := cloud_residual_bound H lambdaH hH (graphPermutation G u)
    simpa only [graphPermutation_energy] using h
  have hc : energy c ≤ lambdaH ^ 2 * energy v := by
    calc
      energy c ≤ energy (graphPermutation G (cloudOperator H v)) := cloud_energy_le H _
      _ = energy (cloudOperator H v) := graphPermutation_energy G _
      _ ≤ lambdaH ^ 2 * energy v :=
        cloud_centered_contraction H lambdaH hH v (cloudMean_centered_zero f)
  rw [hfactor]
  calc
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := energy_add_three_le _ _ _
    _ ≤ 3 * (lambdaG ^ 2 * energy u + lambdaH ^ 2 * energy u + lambdaH ^ 2 * energy v) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha hb) hc) (by norm_num)
    _ ≤ 3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
      have hdecomp : energy f = energy u + energy v := projection_energy_decomposition f
      rw [hdecomp]
      have hn := mul_nonneg (sq_nonneg lambdaG) (energy_nonnegative v)
      nlinarith

theorem square_certificate [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda) :
    SpectralCertificate (square G) (lambda ^ 2) where
  nonnegative := sq_nonneg lambda
  lt_one := by
    have hprod := mul_pos (sub_pos.mpr hG.lt_one)
      (show 0 < 1 + lambda by linarith [hG.nonnegative])
    nlinarith
  contraction f hf := by
    rw [averagingOperator_square]
    calc
      energy (averagingOperator G (averagingOperator G f)) ≤
          lambda ^ 2 * energy (averagingOperator G f) :=
        hG.contraction _ ((mean_operator G f).trans hf)
      _ ≤ lambda ^ 2 * (lambda ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (hG.contraction f hf) (sq_nonneg lambda)
      _ = (lambda ^ 2) ^ 2 * energy f := by ring

theorem square_zigzag_halfCertificate [Fintype V] [Fintype D] [Fintype E]
    [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph (D × D) E)
    (hG : SpectralCertificate G (1 / 2)) (hH : SpectralCertificate H (1 / 100)) :
    SpectralCertificate (zigzag (square G) H) (1 / 2) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := zigzag_energy_bound (square G) H ((1 / 2 : ℝ) ^ 2) (1 / 100)
      (square_certificate G (1 / 2) hG) hH f hf
    have hcoef : 3 * (((1 / 2 : ℝ) ^ 2) ^ 2 + (1 / 100) ^ 2) ≤ (1 / 2 : ℝ) ^ 2 := by
      norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end MinUncutGames.Foundations.PCP.ZigzagSpectral

end OAI
