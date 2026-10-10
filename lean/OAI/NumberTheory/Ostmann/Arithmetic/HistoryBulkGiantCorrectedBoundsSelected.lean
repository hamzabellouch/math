import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsPlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsRegularity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantSourceBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped ContDiff
namespace Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds
open Construction Conclusion HistoryPairPattern HistoryPairGiantCoordinates HistoryPairBulkCoordinates
open HistoryPairSmoothXi HistorySymbolicEncoding HistoryBulkIntegralReplacement
open HistorySelectedPairDerivativeBounds PrimeCellFreezing

theorem selected_corrected_bulkBounds {d : Decomposition} {Bs BD Bz : ℝ} {k₀ : ℕ}
    {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hBs : 0≤Bs) (hk₀ : 0<k₀) (hm : 1≤bulkSize k₀ L)
    (s : ℕ) (outside : List ℕ) (houtside : ∀q∈outside,0<q) (hout : outside.length=2*s)
    (l : ℕ) (hl : l < k₀)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k₀ L/2))))
    (x : OuterSample C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant)
    (p q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (hx : (outerPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c≠0)
    (he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e≠0)
    {κ : Type*} [Fintype κ] [DecidableEq κ] :
    let V := frequencyBound Bs BD Bz k₀ L
    let h := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant x p) c
    let k := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant
        (selectedPermutedOuter C l σ x) q) e
    ∀(hs : h.Supported V outside) (ks : k.Supported V outside)
      (eG : κ ≃ giantCoordinates h k) (z : κ→ℝ),
      z ∈ logRectangle (fun _=>C.giantCenter-1) (fun _=>C.giantCenter+1) →
      BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
        (jointCorrectedScalar C s h k hs ks eG
          (selectedOrderedEquiv C V l outside σ x p q c e hs) (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs ks eG z hz
  have hy : (outerPrior C.sources
      (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant).mass
      (selectedPermutedOuter C l σ x)≠0 := by
    rwa [selectedPermutedOuter_mass]
  have hsrc := HistoryGiantSourceBounds.selected_decoded_pair_giant_sourceBounds C
    (frequencyBound Bs BD Bz k₀ L) l x (selectedPermutedOuter C l σ x) p q c e hx hy hc he
  apply corrected_bulkBounds C hBs hk₀ hm s houtside hout _ _ hs ks hl _ _
    (selectedMatching C (frequencyBound Bs BD Bz k₀ L) l σ x p q c e) hsrc.1 hsrc.2 eG
    (selectedOrderedEquiv C (frequencyBound Bs BD Bz k₀ L) l outside σ x p q c e hs) z hz
  · exact decoded_tree_source_labels _ _ _ _ _ _
      (Template.assignedSlots_matches C.sources _ x.2.2)
  · exact decoded_tree_source_labels _ _ _ _ _ _
      (Template.assignedSlots_matches C.sources _ (selectedPermutedOuter C l σ x).2.2)

theorem selected_plain_bulkBounds {d : Decomposition} {Bs BD Bz : ℝ} {k₀ : ℕ}
    {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hBs : 0≤Bs) (hk₀ : 0<k₀) (hm : 1≤bulkSize k₀ L)
    (s : ℕ) (outside : List ℕ) (houtside : ∀q∈outside,0<q) (hout : outside.length=2*s)
    (l : ℕ) (hl : l ≤ k₀)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k₀ L/2))))
    (x : OuterSample C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant)
    (p q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (hx : (outerPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c≠0)
    (he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e≠0)
    {κ : Type*} [Fintype κ] [DecidableEq κ] :
    let V := frequencyBound Bs BD Bz k₀ L
    let h := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant x p) c
    let k := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant
        (selectedPermutedOuter C l σ x) q) e
    ∀(hs : h.Supported V outside) (ks : k.Supported V outside)
      (eG : κ ≃ giantCoordinates h k) (z : κ→ℝ),
      z ∈ logRectangle (fun _=>C.giantCenter-1) (fun _=>C.giantCenter+1) →
      BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
        (jointScalar C s h k hs ks eG
          (selectedOrderedEquiv C V l outside σ x p q c e hs) (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs ks eG z hz
  have hy : (outerPrior C.sources
      (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant).mass
      (selectedPermutedOuter C l σ x)≠0 := by
    rwa [selectedPermutedOuter_mass]
  have hsrc := HistoryGiantSourceBounds.selected_decoded_pair_giant_sourceBounds C
    (frequencyBound Bs BD Bz k₀ L) l x (selectedPermutedOuter C l σ x) p q c e hx hy hc he
  apply plain_bulkBounds C hBs hk₀ hm s houtside hout _ _ hs ks hl _ _
    (selectedMatching C (frequencyBound Bs BD Bz k₀ L) l σ x p q c e) hsrc.1 hsrc.2 eG
    (selectedOrderedEquiv C (frequencyBound Bs BD Bz k₀ L) l outside σ x p q c e hs) z hz
  · exact decoded_tree_source_labels _ _ _ _ _ _
      (Template.assignedSlots_matches C.sources _ x.2.2)
  · exact decoded_tree_source_labels _ _ _ _ _ _
      (Template.assignedSlots_matches C.sources _ (selectedPermutedOuter C l σ x).2.2)

theorem selected_corrected_joint_bounds {d : Decomposition} {Bs BD Bz : ℝ} {k₀ : ℕ}
    {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hBs : 0≤Bs) (hk₀ : 0<k₀) (hm : 1≤bulkSize k₀ L)
    (s : ℕ) (outside : List ℕ) (houtside : ∀q∈outside,0<q) (hout : outside.length=2*s)
    (l : ℕ) (hl : l < k₀)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k₀ L/2))))
    (x : OuterSample C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant)
    (p q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (hx : (outerPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c≠0)
    (he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e≠0)
    {κ : Type*} [Fintype κ] [DecidableEq κ] :
    let V := frequencyBound Bs BD Bz k₀ L
    let h := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant x p) c
    let k := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant
        (selectedPermutedOuter C l σ x) q) e
    ∀(hs : h.Supported V outside) (ks : k.Supported V outside)
      (eG : κ ≃ giantCoordinates h k),
      ContDiff ℝ ∞ (fun z : (κ→ℝ)×(Fin (2^l)×Fin (2*(bulkSize k₀ L/2))→ℝ)=>
        jointCorrectedScalar C s h k hs ks eG
          (selectedOrderedEquiv C V l outside σ x p q c e hs)
          (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
      ∀z : κ→ℝ, z ∈ logRectangle (fun _=>C.giantCenter-1) (fun _=>C.giantCenter+1) →
        BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
          (jointCorrectedScalar C s h k hs ks eG
            (selectedOrderedEquiv C V l outside σ x p q c e hs) (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs ks eG
  have hy : (outerPrior C.sources
      (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant).mass
      (selectedPermutedOuter C l σ x)≠0 := by
    rwa [selectedPermutedOuter_mass]
  have hsrc := HistoryGiantSourceBounds.selected_decoded_pair_giant_sourceBounds C
    (frequencyBound Bs BD Bz k₀ L) l x (selectedPermutedOuter C l σ x) p q c e hx hy hc he
  exact ⟨jointCorrectedScalar_log_contDiff C s houtside _ _ hs ks hsrc.1 hsrc.2 eG
      (selectedOrderedEquiv C (frequencyBound Bs BD Bz k₀ L) l outside σ x p q c e hs),
    selected_corrected_bulkBounds C hBs hk₀ hm s outside houtside hout l hl σ x p q c e hx hc he hs ks eG⟩

theorem selected_plain_joint_bounds {d : Decomposition} {Bs BD Bz : ℝ} {k₀ : ℕ}
    {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hBs : 0≤Bs) (hk₀ : 0<k₀) (hm : 1≤bulkSize k₀ L)
    (s : ℕ) (outside : List ℕ) (houtside : ∀q∈outside,0<q) (hout : outside.length=2*s)
    (l : ℕ) (hl : l ≤ k₀)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k₀ L/2))))
    (x : OuterSample C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant)
    (p q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (hx : (outerPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c≠0)
    (he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e≠0)
    {κ : Type*} [Fintype κ] [DecidableEq κ] :
    let V := frequencyBound Bs BD Bz k₀ L
    let h := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant x p) c
    let k := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) V l
      (outerState C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant
        (selectedPermutedOuter C l σ x) q) e
    ∀(hs : h.Supported V outside) (ks : k.Supported V outside)
      (eG : κ ≃ giantCoordinates h k),
      ContDiff ℝ ∞ (fun z : (κ→ℝ)×(Fin (2^l)×Fin (2*(bulkSize k₀ L/2))→ℝ)=>
        jointScalar C s h k hs ks eG
          (selectedOrderedEquiv C V l outside σ x p q c e hs)
          (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
      ∀z : κ→ℝ, z ∈ logRectangle (fun _=>C.giantCenter-1) (fun _=>C.giantCenter+1) →
        BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
          (jointScalar C s h k hs ks eG
            (selectedOrderedEquiv C V l outside σ x p q c e hs) (fun i=>Real.exp (z i))) := by
  dsimp only
  intro hs ks eG
  have hy : (outerPrior C.sources
      (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l) C.giant).mass
      (selectedPermutedOuter C l σ x)≠0 := by
    rwa [selectedPermutedOuter_mass]
  have hsrc := HistoryGiantSourceBounds.selected_decoded_pair_giant_sourceBounds C
    (frequencyBound Bs BD Bz k₀ L) l x (selectedPermutedOuter C l σ x) p q c e hx hy hc he
  exact ⟨jointScalar_log_contDiff C s houtside _ _ hs ks hsrc.1 hsrc.2 eG
      (selectedOrderedEquiv C (frequencyBound Bs BD Bz k₀ L) l outside σ x p q c e hs),
    selected_plain_bulkBounds C hBs hk₀ hm s outside houtside hout l hl σ x p q c e hx hc he hs ks eG⟩

end Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds

end

end OAI
