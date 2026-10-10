import OAI.Geometry.NodalSets.Elliptic.CoordinatePartialJets
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakUniqueness
import OAI.Geometry.NodalSets.Elliptic.RealTransportDerivatives

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis
open scoped ContDiff
noncomputable section

lemma partialJet_append_word {n : ℕ} (f : Coord n → ℝ) (ds es : List (Fin n)) :
    partialJet f (ds++es) = partialJet (partialJet f es) ds := by
  induction ds with
  | nil => rfl
  | cons i ds ih => simp only [List.cons_append,partialJet,ih]

lemma partialJet_tsupport_subset {n : ℕ} (f : Coord n → ℝ) (ds : List (Fin n)) :
    tsupport (partialJet f ds) ⊆ tsupport f := by
  induction ds with
  | nil => exact Subset.rfl
  | cons i ds ih =>
    exact (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans ih

lemma partialJet_compactSupport {n : ℕ} (f : Coord n → ℝ)
    (hf : HasCompactSupport f) (ds : List (Fin n)) :
    HasCompactSupport (partialJet f ds) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (partialJet_tsupport_subset f ds)

lemma partialJet_perm_word {n : ℕ} (f : Coord n → ℝ) (hf : ContDiff ℝ ∞ f)
    {ds es : List (Fin n)} (h : ds.Perm es) : partialJet f ds = partialJet f es := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [partialJet,ih]
  | swap i j ds =>
    funext x
    exact real_coordPartial_commute (partialJet f ds) (partialJet_smooth f hf ds) x j i
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem real_weak_jet_test_reversal {n : ℕ} {Q : Set (Coord n)}
    (U : List (Fin n) → Coord n → ℝ) (M : ℕ)
    (hweak : ∀ es, es.length < M → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    (ds : List (Fin n)) (hlen : ds.length ≤ M)
    (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ Q) :
    (∫ x in Q, U ds x*psi x) = (-1:ℝ)^ds.length *
      (∫ x in Q, U [] x*partialJet psi ds.reverse x) := by
  induction ds generalizing psi with
  | nil => simp [partialJet]
  | cons i ds ih =>
    have hlt : ds.length < M := by simp only [List.length_cons] at hlen; omega
    have hw := hweak ds hlt i psi hp hc hs
    have hi := ih (by omega) (fun x ↦ coordPartial psi x i)
      (real_coordPartial_smooth psi hp i) (hc.fderiv_apply ℝ (Pi.single i 1))
      ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs)
    have hr : partialJet psi (i::ds).reverse =
        partialJet (fun x ↦ coordPartial psi x i) ds.reverse := by
      rw [List.reverse_cons,partialJet_append_word]
      rfl
    rw [hr,List.length_cons,pow_succ]
    rw [hi] at hw
    linarith only [hw]

theorem real_weak_jet_pairing_perm {n : ℕ} {Q : Set (Coord n)}
    (U : List (Fin n) → Coord n → ℝ) (M : ℕ)
    (hweak : ∀ es, es.length < M → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    {ds es : List (Fin n)} (hlen : ds.length ≤ M) (hperm : ds.Perm es)
    (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ Q) :
    (∫ x in Q, U ds x*psi x)=(∫ x in Q, U es x*psi x) := by
  rw [real_weak_jet_test_reversal U M hweak ds hlen psi hp hc hs,
    real_weak_jet_test_reversal U M hweak es (by simpa only [← hperm.length_eq] using hlen) psi hp hc hs,
    hperm.length_eq,partialJet_perm_word psi hp
      ((List.reverse_perm ds).trans (hperm.trans (List.reverse_perm es).symm))]

theorem real_weak_jet_perm_ae {n : ℕ} {Q : Set (Coord n)} (hQ : IsCompact Q)
    (U : List (Fin n) → Coord n → ℝ) (M : ℕ)
    (hU : ∀ es, es.length ≤ M → MemLp (U es) 2 (volume.restrict Q))
    (hweak : ∀ es, es.length < M → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    {ds es : List (Fin n)} (hlen : ds.length ≤ M) (hperm : ds.Perm es) :
    U ds =ᵐ[volume.restrict (interior Q)] U es := by
  apply real_interior_L2_eq_of_test_pairings hQ _ _ (hU ds hlen)
    (hU es (by simpa only [← hperm.length_eq] using hlen))
  exact real_weak_jet_pairing_perm U M hweak hlen hperm

end
end Yau

end OAI
