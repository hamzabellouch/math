import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialPencils
import OAI.Combinatorics.SharpRamsey.Geometry.SourceRadialUniform

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedSpatialRadial_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedPreparedSpatialRadial_2 : Fintype (Projectivization K V) := Fintype.ofFinite _
local instance flat_JoinedPreparedSpatialRadial_3 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedPreparedSpatialRadial_4 : Fintype (Submodule K V) := Fintype.ofFinite _

theorem list_radial_exceptions (F : Finset (Submodule K V)) (m : ℕ)
    (S : Finset (Projectivization K V)) (bs : List (Submodule K V))
    (h : GreedyPreparation.Complete F planePoints m S bs)
    (c K₀ : ℝ) (hc : 0<c) (hK : 0≤K₀) (T : Finset I) (a : I→ℝ)
    (ha : ∀ i∈T,0<a i)
    (hJ : ∀ i∈T,K₀<c*(GreedyPreparation.removed S planePoints bs).card*a i^99 →
      2*bs.length≤⌈a i/c⌉₊)
    (hM : ∀ i∈T,K₀<c*(GreedyPreparation.removed S planePoints bs).card*a i^99 →
      4≤⌈a i/c⌉₊) :
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*K₀≤8*(c*(GreedyPreparation.removed S planePoints bs).card)^2*∑ i∈T,a i^98 ∧
      ∀ x,x∉D → ∀ i∈T,
      ((richRadials (GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})) x c (a i)).card:ℝ)*a i^100≤K₀ := by
  let X := fun x => GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})
  let r := fun x i => (richRadials (X x) x c (a i)).card
  apply RadialExceptions.radial_exceptions T a ha r
    (c*(GreedyPreparation.removed S planePoints bs).card) K₀
    (8*(c*(GreedyPreparation.removed S planePoints bs).card)^2) hK (by positivity)
  · intro x i _
    apply (richRadials_mul_le (X x) x c (a i) hc.le).trans
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card sdiff_subset)) hc.le
  · intro i hi hk
    exact list_radial_pairs F m S bs h c (a i) hc (ha i hi).le
      (hJ i hi hk) (hM i hi hk)

theorem list_strong_exceptions (F : Finset (Submodule K V)) (m : ℕ)
    (S : Finset (Projectivization K V)) (bs : List (Submodule K V))
    (h : GreedyPreparation.Complete F planePoints m S bs)
    (c a : ℝ) (hc : 0<c) (ha : 0≤a)
    (hJ : 2*bs.length≤⌈a/c⌉₊) (hM : 4≤⌈a/c⌉₊) :
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*a^2≤8*(c*(GreedyPreparation.removed S planePoints bs).card)^2 ∧
      ∀ x,x∉D → (richRadials (GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})) x c a).card=0 := by
  exact RadialExceptions.strong_exceptions _ a _ (list_radial_pairs F m S bs h c a hc ha hJ hM)

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PreparedRadialResidual
open Finset PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {q : ℕ} [Fact q.Prime]
local instance flat_JoinedPreparedSpatialRadial_5 : Fintype (Projectivization (ZMod q) (Fin 4→ZMod q)) := Fintype.ofFinite _

theorem residual_radial_exceptions {I : Type} (hq : 3≤q)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (hS : S.Nonempty)
    (X : Projectivization (ZMod q) (Fin 4→ZMod q)→Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
    (hX : ∀ x,X x⊆S) (c K₀ : ℝ) (hc : 0<c) (hK : 0≤K₀)
    (Kp : ℕ) (hcap : ∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q, f≠0 →
       (S.filter (fun P => f P.rep=0)).card≤Kp)
    (T : Finset I) (a : I→ℝ) (ha : ∀ i∈T,0<a i) (ha2 : ∀ i∈T,a i≤2)
    (htests : ∀ i∈T,K₀<c*S.card*a i^99 →
      let M := ⌈a i/c⌉₊
      4≤M ∧ M≤S.card ∧
      198*Real.sqrt ((S.card:ℝ)/M)<M ∧
      33*Real.sqrt ((S.card:ℝ)/M)<q ∧
      (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/M))<1/2 ∧
      8*Kp≤M^2) :
    ∃ D : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)),
      (D.card:ℝ)*K₀≤17436*((q:ℝ)+1)*(c*S.card)*∑ i∈T,a i^98 ∧
      ∀ x,x∉D → ∀ i∈T,((richRadials (X x) x c (a i)).card:ℝ)*a i^100≤K₀ := by
  apply RadialExceptions.radial_exceptions T a ha (fun x i => (richRadials (X x) x c (a i)).card)
    (c*S.card) K₀ (17436*((q:ℝ)+1)*(c*S.card)) hK (by positivity)
  · intro x i _
    exact (richRadials_mul_le (X x) x c (a i) hc.le).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card (hX x))) hc.le)
  · intro i hi hk
    obtain ⟨hM,hMN,hs,hch,hp,hKM⟩ := htests i hi hk
    have hh := residual_radial_pairs hq S hS X hX c (a i) hc
      (ha i hi).le Kp (by omega) hMN hcap hs hch hp hKM
    have hz := mul_nonneg
      (show 0≤((q:ℝ)+1)*(c*S.card) by positivity) (sub_nonneg.mpr (ha2 i hi))
    exact hh.trans (by nlinarith only [hz])

theorem residual_strong_exceptions (hq : 3≤q)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (hS : S.Nonempty)
    (X : Projectivization (ZMod q) (Fin 4→ZMod q)→Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
    (hX : ∀ x,X x⊆S) (c a : ℝ) (hc : 0<c) (ha : 0≤a)
    (Kp : ℕ) (hM2 : 2≤⌈a/c⌉₊) (hMN : ⌈a/c⌉₊≤S.card)
    (hcap : ∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q, f≠0 →
       (S.filter (fun P => f P.rep=0)).card≤Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊)<⌈a/c⌉₊)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊)<q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/⌈a/c⌉₊))<1/2)
    (hKM : 8*Kp≤⌈a/c⌉₊^2) :
    ∃ D : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)),
      (D.card:ℝ)*a^2≤8718*((q:ℝ)+1)*(c*S.card)*a ∧
      ∀ x,x∉D → (richRadials (X x) x c a).card=0 := by
  exact RadialExceptions.strong_exceptions _ a _
    (residual_radial_pairs hq S hS X hX c a hc ha Kp hM2 hMN hcap hsmall hchar hprob hKM)

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
