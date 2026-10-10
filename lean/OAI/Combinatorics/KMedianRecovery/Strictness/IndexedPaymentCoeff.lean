import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EnumeratedRow

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability
lemma payment_coeff_bid {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (b : Fin d) :
    (payment distances F W v z i).coeff (.inl b)=
      if active distances v z W b then if distances i b≤v*z then 1 else 0 else 0 := by
  have he : (payment distances F W v z i).coeff (.inl b)=
      ∑ j, if active distances v z W j then
        if distances i j≤v*z then (if b=j then (1:ℚ) else 0) else 0 else 0 := by
    simp only [payment,Form.sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp_all [Form.sub,Form.const,bid,Form.coord]
  rw [he,Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp
lemma payment_coeff_slack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (f : F) (a b : Fin d) :
    (payment distances F W v z i).coeff (.inr (f,a,b))=0 := by
  simp only [payment,Form.sum]
  apply Finset.sum_eq_zero
  intro j _
  split_ifs <;> simp_all [Form.sub,Form.const,bid,Form.coord]
lemma dual_coeff_bid {m d : ℕ} (F : Finset (Fin m)) (f : F) (a b : Fin d) :
    (Form.sum (fun j : Fin d=>slack F f a j)).coeff (.inl b)=0 := by
  simp only [Form.sum,slack,Form.coord,Sum.inl_ne_inr,ite_false,Finset.sum_const_zero]
lemma dual_coeff_slack {m d : ℕ} (F : Finset (Fin m)) (f g : F) (a b u : Fin d) :
    (Form.sum (fun j : Fin d=>slack F f a j)).coeff (.inr (g,b,u))=
      if g=f ∧ b=a then 1 else 0 := by
  simp only [Form.sum,slack,Form.coord,Sum.inr.injEq,Prod.mk.injEq]
  by_cases hf : g=f <;> by_cases ha : b=a <;> simp [hf,ha]

def indexedPaymentCoeff {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) : Variables (Fin d) F → ℚ
  | .inl b=>if active distances v z W b then if distances i b≤v*z then 1 else 0 else 0
  | .inr _=>0

def indexedDualCoeff {m d : ℕ} (F : Finset (Fin m)) (f : F) (a : Fin d) : Variables (Fin d) F → ℚ
  | .inl _=>0
  | .inr (g,b,_)=>if g=f ∧ b=a then 1 else 0
lemma payment_coeff {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (u : Variables (Fin d) F) :
    (payment distances F W v z i).coeff u=indexedPaymentCoeff distances F W v z i u := by
  cases u with
  | inl b=>exact payment_coeff_bid distances F W v z i b
  | inr p=>exact payment_coeff_slack distances F W v z i p.1 p.2.1 p.2.2
lemma dual_coeff {m d : ℕ} (F : Finset (Fin m)) (f : F) (a : Fin d) (u : Variables (Fin d) F) :
    (Form.sum (fun j : Fin d=>slack F f a j)).coeff u=indexedDualCoeff F f a u := by
  cases u with
  | inl b=>exact dual_coeff_bid F f a b
  | inr p=>exact dual_coeff_slack F f p.1 a p.2.1 p.2.2

def indexedCoeff {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (r : Kind (Fin d) W F) (u : Variables (Fin d) F) : ℚ :=
  match r with
  | .lower j=>if active distances v z W j then -(if u=.inl j then 1 else 0) else 0
  | .upper j=>if active distances v z W j then (if u=.inl j then 1 else 0) else 0
  | .cap j _=>if active distances v z W j then (if u=.inl j then 1 else 0) else 0
  | .far j=>if active distances v z W j then
      if distances i j≤v*z then 0 else (if u=.inl j then 1 else 0) else 0
  | .payment=>-indexedPaymentCoeff distances F W v z i u
  | .slackZero f a j=>if active distances v z W a then -(if u=.inr (f,a,j) then 1 else 0) else 0
  | .slackTerm f a j=>if active distances v z W a then
      (if active distances v z W j then (if u=.inl j then 1 else 0) else (if u=.inl a then 1 else 0)) -
        (if u=.inr (f,a,j) then 1 else 0) else 0
  | .dual f a=>if active distances v z W a then indexedDualCoeff F f a u else 0

lemma indexedCoeff_eq {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) (u : Variables (Fin d) F) :
    indexedCoeff distances F W v z i r u=(forms distances F W v z lam eta i r).coeff u := by
  cases r <;> simp only [indexedCoeff,forms]
  all_goals (try split_ifs)
  all_goals (try simp only [Form.sub,Form.const,payment_coeff,dual_coeff])
  all_goals simp_all [dual,bid,slack,Form.coord,Form.sub,Form.const]
  all_goals linarith

end MetricKMedianRecovery.EffectiveOpenability

end OAI
