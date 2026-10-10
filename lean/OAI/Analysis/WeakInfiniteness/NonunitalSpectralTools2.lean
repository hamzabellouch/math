import Mathlib
import OAI.Analysis.WeakInfiniteness.SpectralWindows

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma map_mem_hereditary (φ : A →⋆ₙₐ[ℂ] B) {h x : A} (hh : IsSelfAdjoint h)
    (hx : x ∈ hereditarySubalgebra h hh) :
    φ x ∈ hereditarySubalgebra (φ h) (hh.map φ) := by
  apply closure_minimal _ ((NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage
    (map_continuous φ)) hx
  rintro _ ⟨b,rfl⟩
  change φ (h*b*h) ∈ hereditarySubalgebra (φ h) (hh.map φ)
  rw [map_mul,map_mul]
  exact sandwich_mem (φ h) (φ b) (hh.map φ)

lemma continuouslySupported_hereditary_nonunital (U u : A) (hu : IsSelfAdjoint u) (S : Set ℝ)
    (hs : ContinuouslySupported (U : Unitization ℂ A) (u : Unitization ℂ A) S)
    {v : A} (hv : v ∈ hereditarySubalgebra u hu) :
    ContinuouslySupported (U : Unitization ℂ A) (v : Unitization ℂ A) S :=
  continuouslySupported_hereditary (U : Unitization ℂ A) (u : Unitization ℂ A)
    (hu.map (Unitization.inrNonUnitalStarAlgHom ℂ A)) S hs
    (map_mem_hereditary (Unitization.inrNonUnitalStarAlgHom ℂ A) hu hv)

def unitizationSubalgebra (D : NonUnitalStarSubalgebra ℂ A) : StarSubalgebra ℂ (Unitization ℂ A) where
  carrier := {z | z.snd ∈ D}
  algebraMap_mem' z := by change (0 : A) ∈ D; exact D.zero_mem
  add_mem' ha hb := D.add_mem ha hb
  mul_mem' {a b} ha hb := by
    change a.fst • b.snd+b.fst • a.snd+a.snd*b.snd ∈ D
    exact D.add_mem (D.add_mem (D.smul_mem _ hb) (D.smul_mem _ ha)) (D.mul_mem ha hb)
  star_mem' ha := star_mem (s := D) ha

lemma unitizationSubalgebra_closed (D : NonUnitalStarSubalgebra ℂ A)
    (hD : IsClosed (D : Set A)) : IsClosed (unitizationSubalgebra D : Set (Unitization ℂ A)) :=
  hD.preimage Unitization.continuous_snd

lemma unitizationSubalgebra_inr_mem (D : NonUnitalStarSubalgebra ℂ A) {a : A} (ha : a ∈ D) :
    (a : Unitization ℂ A) ∈ unitizationSubalgebra D := ha

omit [NonUnitalCStarAlgebra A] in
lemma unitization_inr_snd_of_fst_eq_zero {z : Unitization ℂ A} (hz : z.fst=0) :
    (z.snd : Unitization ℂ A)=z := by
  ext <;> simp [hz]

end

end WeakPureInfiniteness
end

end OAI
