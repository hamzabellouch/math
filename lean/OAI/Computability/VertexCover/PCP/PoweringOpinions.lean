import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringLazy
import OAI.Computability.VertexCover.PCP.PoweringLabels
import OAI.Computability.VertexCover.PCP.PoweringDecoding
import OAI.Computability.VertexCover.PCP.PoweringReturn

namespace OAI

                                                                                         

noncomputable section

namespace UniqueGames.Foundations.PCP.PoweringOpinions

open PoweringWalks PoweringLabels SpectralReturn
open PoweringMoment (bit)

variable {V D A : Type*}

def opinionAt (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : A := by
  classical
  exact if h : ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u then
    decode (selectors v) (labels v) ⟨u, h⟩ else fallback

theorem opinionAt_eq_decode (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors labels fallback u.val v = decode (selectors v) (labels v) u := by
  classical
  simp [opinionAt, u.property]
  rfl

def honestLabels (G : PortGraph V D) (t : Nat) (assignment : V → A) :
    V → PaddedLabel D t A := fun v => encode G t v (fun u => assignment u.val)

theorem opinionAt_honest (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (assignment : V → A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors (honestLabels G t assignment) fallback u.val v =
      assignment u.val := by
  rw [opinionAt_eq_decode]
  exact congrFun (decode_encode (selectors v) (fun u => assignment u.val)) u

variable [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]

def sampleOpinion (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) (p : Fin N → D) : A :=
  opinionAt G t selectors labels fallback u (wordEnd G N u p)

def decoded (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) : A :=
  PoweringDecoding.mode (sampleOpinion G t N selectors labels fallback u)

def matchFn (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : ℝ :=
  bit (opinionAt G t selectors labels fallback u v = decoded G t N selectors labels fallback u)

omit [Nonempty D] in
theorem matchFn_mem_Icc (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) :
    matchFn G t N selectors labels fallback u v ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · exact PoweringMoment.bit_nonneg _
  · unfold matchFn bit
    split <;> simp

theorem decoded_modal_baseline (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) :
    1 / (Fintype.card A : ℝ) ≤
      iterateOperator G N (matchFn G t N selectors labels fallback u) u := by
  have h := PoweringDecoding.mode_mass_lower (sampleOpinion G t N selectors labels fallback u)
  change 1 / (Fintype.card A : ℝ) ≤ mean (fun p : Fin N → D =>
    matchFn G t N selectors labels fallback u (wordEnd G N u p)) at h
  rwa [PoweringReturn.mean_wordEnd] at h

theorem decoded_modal_near (G : PortGraph V D) (t M m : Nat)
    (selectors : ∀ v, AddressSelector (lazyGraph G) t v)
    (labels : V → PaddedLabel (Bool × D) t A) (fallback : A)
    (hM : 1 ≤ M)
    (hlo : (4 * Fintype.card A * M) ^ 2 - M ≤ m)
    (hhi : m ≤ (4 * Fintype.card A * M) ^ 2 + M) (u : V) :
    1 / (2 * (Fintype.card A : ℝ)) ≤
      iterateOperator (lazyGraph G) m
        (matchFn (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
          selectors labels fallback u) u := by
  exact PoweringLazy.lazy_endpoint_modal_transfer G (Fintype.card A) M m
    Fintype.card_pos hM hlo hhi _
    (matchFn_mem_Icc (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
      selectors labels fallback u) u
    (decoded_modal_baseline (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
      selectors labels fallback u)

end UniqueGames.Foundations.PCP.PoweringOpinions
end

end OAI
