import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeDestinationInjective

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
variable {h ℓ : ℕ}

@[reducible] def Topology (ℓ r : ℕ) :=
  (R : {R : Finset (Fin ℓ) // R.card=r}) × ((Fin ℓ → Bool) × (↥R.val → Fin (ℓ+1)))

lemma topology_card (ℓ r : ℕ) : Fintype.card (Topology ℓ r) ≤ 4^ℓ*(ℓ+1)^r := by
  rw [Fintype.card_sigma]
  have he : ∀ R : {R : Finset (Fin ℓ) // R.card=r},
      Fintype.card ((Fin ℓ → Bool) × (↥R.val → Fin (ℓ+1))) = 2^ℓ*(ℓ+1)^r := by
    intro R
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
      Fintype.card_coe,R.property]
  simp_rw [he]
  rw [sum_const,nsmul_eq_mul,Nat.cast_id,card_univ]
  have hc : Fintype.card {R : Finset (Fin ℓ) // R.card=r} ≤ 2^ℓ := by
    simpa only [Fintype.card_finset,Fintype.card_fin] using
      Fintype.card_subtype_le (fun R : Finset (Fin ℓ) => R.card=r)
  calc
    _ ≤ 2^ℓ*(2^ℓ*(ℓ+1)^r) := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← mul_assoc,← mul_pow]; norm_num

lemma exists_return_target (w : ClosedLine h ℓ) (e : Fin ℓ) (he : e ∈ returnSteps w) :
    ∃ j : Fin (ℓ+1), j.val ≤ e.val ∧ w.offset j = w.offset e.succ := by
  have hn : ¬∀ j : Fin (ℓ+1), j.val ≤ e.val → w.offset j ≠ w.offset e.succ := by
    intro ht
    exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨mem_univ _,ht⟩)
  push Not at hn
  exact hn

def returnTarget (w : ClosedLine h ℓ) (e : Fin ℓ) (he : e ∈ returnSteps w) : Fin (ℓ+1) :=
  Classical.choose (exists_return_target w e he)

lemma returnTarget_spec (w : ClosedLine h ℓ) (e : Fin ℓ) (he : e ∈ returnSteps w) :
    (returnTarget w e he).val ≤ e.val ∧ w.offset (returnTarget w e he) = w.offset e.succ :=
  Classical.choose_spec (exists_return_target w e he)

def signBit (w : ClosedLine h ℓ) (e : Fin ℓ) : Bool := decide (w.sign e=1)

lemma signBit_decode (w : ClosedLine h ℓ) (e : Fin ℓ) :
    w.sign e = if signBit w e then 1 else -1 := by
  rcases w.sign_mem e with hs | hs <;> simp [signBit,hs]

def encodeTopology (w : ClosedLine h ℓ) (r : ℕ) (hr : (returnSteps w).card=r) : Topology ℓ r :=
  ⟨⟨returnSteps w,hr⟩, signBit w, fun e => returnTarget w e.val e.property⟩

def topologyTarget {r : ℕ} (t : Topology ℓ r) (e : Fin ℓ) : Fin (ℓ+1) :=
  if he : e ∈ t.1.val then t.2.2 ⟨e,he⟩ else 0

lemma topologyTarget_encode (w : ClosedLine h ℓ) (r : ℕ) (hr : (returnSteps w).card=r)
    (e : Fin ℓ) (he : e ∈ returnSteps w) :
    topologyTarget (encodeTopology w r hr) e = returnTarget w e he := by
  dsimp only [topologyTarget,encodeTopology]
  rw [dite_eq_left he]

lemma ClosedLine.ext_values (w v : ClosedLine h ℓ)
    (ho : w.offset=v.offset) (hl : w.label=v.label) (hs : w.sign=v.sign) : w=v := by
  cases w
  cases v
  simp_all

theorem topology_tree_labels_injective (w v : ClosedLine h ℓ) (hh : 0 < h)
    (r : ℕ) (hwr : (returnSteps w).card=r) (hvr : (returnSteps v).card=r)
    (ht : encodeTopology w r hwr=encodeTopology v r hvr)
    (hl : ∀ e ∈ w.treeSteps, w.label e=v.label e) : w=v := by
  have hR : returnSteps w=returnSteps v := congrArg (fun t : Topology ℓ r => t.1.val) ht
  have hs : ∀ e, w.sign e=v.sign e := by
    intro e
    have hb : signBit w e=signBit v e := congrArg (fun t : Topology ℓ r => t.2.1 e) ht
    rw [signBit_decode w e,signBit_decode v e,hb]
  have htar : ∀ e (he : e ∈ returnSteps w),
      returnTarget w e he=returnTarget v e (hR ▸ he) := by
    intro e he
    have hte := congrArg (fun t : Topology ℓ r => topologyTarget t e) ht
    simpa only [topologyTarget_encode w r hwr e he,
      topologyTarget_encode v r hvr e (hR ▸ he)] using hte
  have ho : ∀ j, w.offset j=v.offset j := by
    have hd : ∀ n : ℕ, ∀ j : Fin (ℓ+1), j.val=n → w.offset j=v.offset j := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro j hj
        by_cases hj0 : j=0
        · subst j
          rw [w.start_zero,v.start_zero]
        · obtain ⟨e,rfl⟩ := Fin.exists_succ_eq.mpr hj0
          have heprev := ih e.val (by simpa only [← hj,Fin.val_succ] using Nat.lt_succ_self e.val)
            e.castSucc rfl
          by_cases het : e ∈ w.treeSteps
          · have hw := w.step e
            have hv := v.step e
            rw [hl e het,hs e] at hw
            linarith only [hw,hv,heprev]
          · have her : e ∈ returnSteps w := mem_sdiff.mpr ⟨mem_univ _,het⟩
            have hert : (returnTarget w e her).val<n := by
              have hle := (returnTarget_spec w e her).1
              simp only [Fin.val_succ] at hj
              omega
            have hi := ih _ hert (returnTarget w e her) rfl
            rw [(returnTarget_spec w e her).2,htar e her,
              (returnTarget_spec v e (hR ▸ her)).2] at hi
            exact hi
    intro j
    exact hd j.val j rfl
  have hall : ∀ e, w.label e=v.label e := by
    intro e
    have hw := w.step e
    have hv := v.step e
    rw [ho e.succ,ho e.castSucc,hs e] at hw
    have hn : v.sign e*(h : ℤ) ≠ 0 := mul_ne_zero
      (by rcases v.sign_mem e with hs | hs <;> rw [hs] <;> norm_num)
      (by exact_mod_cast ne_of_gt hh)
    have hm : (v.sign e*(h : ℤ))*(w.label e : ℤ) =
        (v.sign e*(h : ℤ))*(v.label e : ℤ) := hw.symm.trans hv
    have he := mul_left_cancel₀ hn hm
    exact_mod_cast he
  exact ClosedLine.ext_values w v (funext ho) (funext hall) (funext hs)

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
