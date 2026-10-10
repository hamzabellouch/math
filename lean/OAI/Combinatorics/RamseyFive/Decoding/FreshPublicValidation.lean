import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.PredictorReverseCap
import OAI.Combinatorics.RamseyFive.Entropy.OptionComposition
import OAI.Combinatorics.RamseyFive.Entropy.TwoCapCost
import OAI.Combinatorics.RamseyFive.Entropy.FreshPublicFamily

namespace OAI

namespace SharpRamseyFive.ReverseCap

section
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

theorem fresh_public_validation (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hC : C.Nonempty) (hW : W.Nonempty) (hCW : C⊆W)
    (n : ℕ) (q M : ℝ) (_hq : 0<q)
    (hE : (9:ℝ)/10≤eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows R S U C n q M)) :
    let p := map (freshTapeLaw W hW n q)
      (fun t=>Option.map (freshDecoded R W n q t) (freshEncoded R S U C W hCW n q M t))
    p none≤Real.exp (-q) ∧ ∀Y,0<p (some Y)→ValidCap S U M (U∩Y) := by
  dsimp only
  rw [fresh_public_law]
  refine ⟨?_,fun Y hY=>ambientCapLaw_positive R S U C W hW n q M Y hY⟩
  rw [ambientCapLaw_none]
  exact publicCapLaw_failure R S U C W hC hW hCW n q M hE

theorem fresh_public_domination (R : A→B→Prop) (S U : Finset A)
    (C X W : Finset B) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCW : C⊆W) (hCX : C⊆X) (n : ℕ) (hn : 0<n)
    (q c M : ℝ) (hq : 0<q) (hc : 0<c) (hsize : c*X.card≤C.card)
    (hE : (9:ℝ)/10≤eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows R S U C n q M)) (a : A) :
    eventMass (map (freshTapeLaw W hW n q)
      (fun t=>Option.map (freshDecoded R W n q t) (freshEncoded R S U C W hCW n q M t)))
      (Finset.univ.filter (Excludes a))≤(50*q/(9*c))*(((X.filter (R a)).card:ℝ)/X.card) := by
  rw [fresh_public_law]
  exact ambientCapLaw_domination R S U C X W hC hW hCW hCX n hn q c M hq hc hsize hE a
end

open FiniteEntropy
open scoped Classical
variable {A : Type*} [Fintype A]

def CaptureBound (T U : Finset A) (c M : ℝ) (W : Finset A) : Prop :=
  W⊆U ∧ (W.card:ℝ)≤M ∧ c*T.card≤(T∩W).card

omit [Fintype A] in
lemma CaptureBound.nonempty {T U W : Finset A} {c M : ℝ}
    (h : CaptureBound T U c M W) (hT : T.Nonempty) (hc : 0<c) :
    (T∩W).Nonempty := by
  apply Finset.card_pos.mp
  have ht : (0:ℝ)<T.card := by exact_mod_cast hT.card_pos
  exact_mod_cast (lt_of_lt_of_le (mul_pos hc ht) h.2.2)
end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def generalNextCapLaw (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (c : ℝ) (hc : 0<c) (n : ℕ) (q M MT : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) : Law (Option (Finset (ℙ K V))) :=
  match Y with
  | none => pureLaw none
  | some W => if hW : CaptureBound T UT c MT W then
      publicCapLaw Incident S U (T∩W) W
        ((hW.nonempty hT hc).mono Finset.inter_subset_right) n q M
    else pureLaw none

theorem reverse_after_general_capture {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty) (c : ℝ) (hc : 0<c) (hc1 : c≤1)
    (MT ε : ℝ) (p : Law (Option (Finset (ℙ K (Dual K V)))))
    (hp : p none≤ε) (hgood : ∀W,0<p (some W)→CaptureBound T UT c MT W)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences S T≤c*S.card*T.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card)≤n) :
    let M := (320/c+320)*(Nat.card K:ℝ)^(d+1)/T.card
    let out := optionCompose p (generalNextCapLaw S U T UT hT c hc n (Nat.card K) M MT)
    out none≤ε+Real.exp (-(Nat.card K:ℝ)) ∧
    (∀Z,0<out (some Z)→ValidCap S U M Z) := by
  dsimp only
  let M := (320/c+320)*(Nat.card K:ℝ)^(d+1)/T.card
  let next := generalNextCapLaw S U T UT hT c hc n (Nat.card K) M MT
  have hnext (W) (hW : 0<p (some W)) : next (some W) none≤Real.exp (-(Nat.card K:ℝ)) := by
    have hv := hgood W hW
    dsimp only [next,generalNextCapLaw]
    rw [dite_eq_left hv]
    apply publicCapLaw_failure _ _ _ _ _ (hv.nonempty hT hc) _ Finset.inter_subset_right
    exact geometric_validation_mass hdim hd hq S U hS hSU T (T∩W)
      (hv.nonempty hT hc) Finset.inter_subset_left c hc hc1 hv.2.2 hsparse n hn hlen
  refine ⟨optionCompose_failure p next ε _ (Real.exp_pos _).le hp hnext,?_⟩
  intro Z hZ
  obtain ⟨W,hW,hWZ⟩ := optionCompose_positive p next Z hZ
  have hv := hgood W hW
  dsimp only [next,generalNextCapLaw] at hWZ
  rw [dite_eq_left hv] at hWZ
  exact publicCapLaw_positive _ _ _ _ _ _ _ _ _ _ hWZ

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
theorem general_reverse_payload (T UT W : Finset (ℙ K (Dual K V)))
    (hT : T.Nonempty) (c B P : ℝ) (hc : 0<c)
    (hv : CaptureBound T UT c ((T.card:ℝ)*Real.exp (B*P)) W)
    (q : ℝ) (hq : 1≤q) (n : ℕ) :
    Real.log (Fintype.card (Fin (cardCutoff q (T∩W).card W.card n)):ℝ)≤
      Real.log (2*q)-Real.log ((9:ℝ)/10)+n*(B*P-Real.log c) := by
  have hC := hv.nonempty hT hc
  have hW := hC.mono Finset.inter_subset_right
  have hu := fresh_payload_cost q hq (T∩W) W hC hW Finset.inter_subset_right n
  have hr := capture_log_ratio T.card c W.card (T∩W).card (B*P)
    (by exact_mod_cast hT.card_pos) hc (by exact_mod_cast hW.card_pos)
    (by exact_mod_cast hC.card_pos) hv.2.2 hv.2.1
  have hm := mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤n by positivity)
  linarith

end SharpRamseyFive.ProjectiveIncidence

end OAI
