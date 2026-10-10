import Mathlib
import OAI.Geometry.Borsuk.Simplicial.SignedVertex
import OAI.Geometry.Borsuk.SmithTheory.CharacteristicCochains

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open BorsukNine.SmithTheory

section CharacteristicDegree
variable {V : Type*} [DecidableEq V]
variable (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
variable (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
variable (hfree : ∀ s ∈ K, s.image e ≠ s)

noncomputable def characteristicAugmentation : SmithCocycle (boundary K) (normMap K e) :=
  ⟨augmentation K, augmentation_normMap K e (fun s hs => (he s).mp hs),
    augmentation_boundary K⟩

include he hi hfree in
lemma normMap_exact : LinearMap.ker (normMap K e) ≤ LinearMap.range (normMap K e) := by
  rw [normMap_eq K e he]
  exact involutionNorm_exact _ (faceEquiv_involutive K e he hi)
    (faceEquiv_free K e he hfree)

noncomputable def characteristicDegree (n : ℕ) : Chain K →ₗ[F₂] F₂ :=
  smithDegree (boundary K) (normMap K e) (boundary_sq K)
    (boundary_normMap K e (fun s hs => (he s).mp hs)) (normMap_exact K e he hi hfree)
    (characteristicAugmentation K e he) n

end CharacteristicDegree

end BorsukNine.SimplicialChains

namespace BorsukNine.SimplicialChains
open Finset BorsukNine.SmithTheory

section NaturalDegree
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma characteristicDegree_natural
    (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
    (hfree : ∀ s ∈ K, s.image e ≠ s)
    (L : PreAbstractSimplicialComplex W) (d : W ≃ W)
    (hd : ∀ s, s ∈ L ↔ s.image d ∈ L) (hdi : Function.Involutive d)
    (hdfree : ∀ s ∈ L, s.image d ≠ s)
    (T : Chain K →ₗ[F₂] Chain L)
    (hTbd : (boundary L).comp T = T.comp (boundary K))
    (hTN : (normMap L d).comp T = T.comp (normMap K e))
    (hTa : (augmentation L).comp T = augmentation K)
    (n : ℕ) (c : Chain K) (hcN : normMap K e c = 0) (hcb : boundary K c = 0) :
    characteristicDegree L d hd hdi hdfree n (T c) =
      characteristicDegree K e he hi hfree n c := by
  exact smithDegree_natural (boundary K) (normMap K e) (boundary_sq K)
    (boundary_normMap K e (fun s hs => (he s).mp hs)) (normMap_exact K e he hi hfree)
    (characteristicAugmentation K e he) (boundary L) (normMap L d) (boundary_sq L)
    (boundary_normMap L d (fun s hs => (hd s).mp hs)) (normMap_exact L d hd hdi hdfree)
    (characteristicAugmentation L d hd) T hTbd hTN hTa n c hcN hcb

lemma characteristicDegree_vanish_of_equivariant_projection
    (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
    (hfree : ∀ s ∈ K, s.image e ≠ s)
    (m h : ℕ) (T : Chain K →ₗ[F₂] Chain (cross m))
    (P : Chain K →ₗ[F₂] Chain (cross h))
    (hTbd : (boundary (cross m)).comp T = T.comp (boundary K))
    (hTN : (normMap (cross m) flip).comp T = T.comp (normMap K e))
    (hTa : (augmentation (cross m)).comp T = augmentation K)
    (hPbd : (boundary (cross h)).comp P = P.comp (boundary K))
    (hPN : (normMap (cross h) flip).comp P = P.comp (normMap K e))
    (hPa : (augmentation (cross h)).comp P = augmentation K)
    (n : ℕ) (c : Chain K) (hcN : normMap K e c = 0) (hcb : boundary K c = 0)
    (hPc : P c = 0) :
    characteristicDegree (cross m) flip (cross_flip m) flip_involutive (cross_free m)
      n (T c) = 0 := by
  rw [characteristicDegree_natural K e he hi hfree (cross m) flip (cross_flip m)
    flip_involutive (cross_free m) T hTbd hTN hTa n c hcN hcb,
    ← characteristicDegree_natural K e he hi hfree (cross h) flip (cross_flip h)
      flip_involutive (cross_free h) P hPbd hPN hPa n c hcN hcb, hPc, map_zero]

end NaturalDegree

noncomputable def crossFundamental (n : ℕ) : Chain (cross n) :=
  normMap (cross n) flip (crossTower n (n-1))

lemma crossFundamental_norm (n : ℕ) : normMap (cross n) flip (crossFundamental n) = 0 :=
  LinearMap.congr_fun (normMap_sq (cross n) flip (cross_flip n) flip_involutive) _

lemma crossFundamental_boundary (n : ℕ) (hn : 0 < n) :
    boundary (cross n) (crossFundamental n) = 0 :=
  crossTower_norm_boundary n (n-1) (by omega)

lemma crossFundamental_degree (n : ℕ) (hn : 0 < n) :
    crossFundamental n ∈ degreeChains (cross n) n := by
  have h := normMap_degree (cross n) flip (cross_flip_forward n) (n-1+1)
    (crossTower_degree n (n-1))
  change normMap (cross n) flip (crossTower n (n-1)) ∈
    degreeChains (cross n) (n-1+1) at h
  simpa only [crossFundamental, Nat.sub_add_cancel (by omega : 1 ≤ n)] using h

lemma characteristicCochain_crossTower (n i : ℕ) (hi : i < n) :
    (smithCochain (boundary (cross n)) (normMap (cross n) flip) (boundary_sq (cross n))
      (boundary_normMap (cross n) flip (cross_flip_forward n))
      (normMap_exact (cross n) flip (cross_flip n) flip_involutive (cross_free n))
      (characteristicAugmentation (cross n) flip (cross_flip n)) i).val
        (crossTower n i) = 1 := by
  induction i with
  | zero => exact crossTower_augmentation n (by omega)
  | succ i ih =>
    rw [smithCochain_succ, crossTower_boundary n i hi, smithDegree_norm]
    exact ih (by omega)

lemma characteristicDegree_crossFundamental (n : ℕ) (hn : 0 < n) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) (crossFundamental n) = 1 := by
  unfold characteristicDegree crossFundamental
  rw [smithDegree_norm]
  exact characteristicCochain_crossTower n (n-1) (by omega)

lemma cross_equivariant_degree_one (n : ℕ) (hn : 0 < n)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross n))
    (hTbd : (boundary (cross n)).comp T = T.comp (boundary (cross n)))
    (hTN : (normMap (cross n) flip).comp T = T.comp (normMap (cross n) flip))
    (hTa : (augmentation (cross n)).comp T = augmentation (cross n)) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) (T (crossFundamental n)) = 1 := by
  rw [characteristicDegree_natural (cross n) flip (cross_flip n) flip_involutive
    (cross_free n) (cross n) flip (cross_flip n) flip_involutive (cross_free n)
    T hTbd hTN hTa (n-1) (crossFundamental n) (crossFundamental_norm n)
    (crossFundamental_boundary n hn), characteristicDegree_crossFundamental n hn]

end BorsukNine.SimplicialChains

end OAI
