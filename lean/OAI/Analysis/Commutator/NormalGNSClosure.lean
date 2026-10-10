import Mathlib
import OAI.Analysis.Commutator.KaplanskyNet
import OAI.Analysis.Commutator.NormalGNSContinuity
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

open Filter

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hnormal : BoundedWOTContinuous M τ)
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
  (hSM : S≤M.toStarSubalgebra)
  (N : VonNeumannAlgebra τ.GNS)
  (hSN : ∀ a : M,(a:H →L[ℂ] H)∈S → τ.gnsStarAlgHom a∈N)

include hnormal hS hSM hSN in
lemma contraction_image_bicommutant (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hna : ‖a‖≤1) : τ.gnsStarAlgHom a∈N := by
  classical
  let net := Kaplansky.approximationNet S hS (a:H →L[ℂ] H) ha hna
  have hnet (j : Finset H × ℕ) := Kaplansky.approximationNet_spec S hS (a:H →L[ℂ] H) ha hna j
  let u : Finset H × ℕ → M := fun j => ⟨net j,hSM (hnet j).1⟩
  have hu : ∀ j,‖u j‖≤1 := fun j => (hnet j).2.1
  have hlim (x y : H) : Tendsto (fun j => inner ℂ ((u j:H →L[ℂ] H) x) y) atTop
      (𝓝 (inner ℂ ((a:H →L[ℂ] H) x) y)) :=
    (Kaplansky.approximationNet_tendsto S hS (a:H →L[ℂ] H) ha hna x).inner tendsto_const_nhds
  have hgns (x y : τ.GNS) : Tendsto (fun j => inner ℂ (τ.gnsStarAlgHom (u j) x) y) atTop
      (𝓝 (inner ℂ (τ.gnsStarAlgHom a x) y)) := by
    simpa only [RCLike.star_def,inner_conj_symm] using
      (tendsto_gns M τ hnormal u a 1 hu hna hlim y x).star
  exact WeakOperatorLimit.mem_vonNeumann hgns N (Eventually.of_forall fun j => hSN (u j) (hnet j).1)

include hnormal hS hSM hSN in
lemma image_bicommutant (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    τ.gnsStarAlgHom a∈N := by
  by_cases hz : a=0
  · subst a
    exact hSN 0 S.zero_mem
  let c : ℂ := (‖a‖:ℂ)
  have hc : c≠0 := by
    dsimp [c]
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  let b : M := c⁻¹ • a
  have hb : (b:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    intro x hx
    change x*(c⁻¹ • (a:H →L[ℂ] H))=(c⁻¹ • (a:H →L[ℂ] H))*x
    rw [mul_smul_comm,smul_mul_assoc,ha x hx]
  have hnb : ‖b‖≤1 := by
    change ‖c⁻¹ • a‖≤1
    rw [norm_smul,norm_inv]
    change ‖(‖a‖:ℂ)‖⁻¹ * ‖a‖≤1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg a),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  have hN := contraction_image_bicommutant M τ hnormal S hS hSM N hSN b hb hnb
  have hab : c • b=a := by dsimp [b]; rw [smul_smul,mul_inv_cancel₀ hc,one_smul]
  rw [←hab]
  exact (N.toStarSubalgebra.comap τ.gnsStarAlgHom).smul_mem hN c

include hnormal hSM hSN in
lemma image_bicommutant_general (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    τ.gnsStarAlgHom a∈N := by
  let C : Set M := {a | τ.gnsStarAlgHom a∈N}
  have hC : IsClosed C := (VonNeumannCStar.isClosed N).preimage (map_continuous τ.gnsStarAlgHom)
  have hvalC : IsClosed ((Subtype.val : M → (H →L[ℂ] H)) '' C) :=
    (VonNeumannCStar.isClosed M).isClosedMap_subtype_val C hC
  have hSC : (S : Set (H →L[ℂ] H)) ⊆ (Subtype.val : M → (H →L[ℂ] H)) '' C := by
    intro a ha
    exact ⟨⟨a,hSM ha⟩,hSN ⟨a,hSM ha⟩ ha,rfl⟩
  have hcl := closure_minimal hSC hvalC
  have hSM' : S.topologicalClosure≤M.toStarSubalgebra :=
    S.topologicalClosure_minimal hSM (VonNeumannCStar.isClosed M)
  have hSN' (b : M) (hb : (b:H →L[ℂ] H)∈S.topologicalClosure) : τ.gnsStarAlgHom b∈N := by
    have hbcl : (b:H →L[ℂ] H)∈closure (S : Set (H →L[ℂ] H)) := hb
    obtain ⟨c,hc,hcb⟩ := hcl hbcl
    have he : c=b := Subtype.ext hcb
    change τ.gnsStarAlgHom c∈N at hc
    simpa only [he] using hc
  apply image_bicommutant M τ hnormal S.topologicalClosure S.isClosed_topologicalClosure hSM' N hSN' a
  intro T hT
  apply ha T
  intro b hb
  exact hT b (S.le_topologicalClosure hb)

end Kadison.NormalGNS

end

end
end

end OAI
