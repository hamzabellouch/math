import OAI.Probability.CubeShuffle.FiniteKernel
import OAI.RepresentationTheory.FiniteUnitary.Sampling

namespace OAI

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X Ω : Type*} [Group G] [Fintype G] [Fintype X] [Fintype Ω]

noncomputable def actionKernel (a : G →* Equiv.Perm X) (P : Ω → G) (x y : X) : ℝ :=
  finiteMean (fun ω => if a (P ω) x=y then 1 else 0)

omit [Fintype G] in
lemma actionKernel_apply (a : G →* Equiv.Perm X) (P : Ω → G)
    (v : EuclideanSpace ℂ X) (x : X) :
    DensityTransfer.applyKernel (actionKernel a P) v x =
      (Fintype.card Ω:ℂ)⁻¹ * ∑ ω, v (a (P ω) x) := by
  simp only [DensityTransfer.applyKernel_apply,actionKernel,finiteMean,
    Complex.ofReal_sum,div_eq_mul_inv,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ ω, (Fintype.card Ω:ℂ)⁻¹ * ∑ y : X, if a (P ω) x=y then v y else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp_all
    _ = _ := by simp [Finset.mul_sum]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def randomOperator (ρ : Representation ℂ G V) (P : Ω → G) : Module.End ℂ V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω, ρ (P ω)⁻¹

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma coefficient_random (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (P : Ω → G) (w : V) (hw : IsFixed a x₀ ρ w) (v : V) :
    DensityTransfer.applyKernel (actionKernel a P) (normalizedCoefficient a x₀ ha ρ w v) =
      normalizedCoefficient a x₀ ha ρ w (randomOperator ρ P v) := by
  ext x
  rw [actionKernel_apply]
  simp only [normalizedCoefficient,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum,
    coefficient,randomOperator,LinearMap.smul_apply,LinearMap.sum_apply,
    inner_smul_right,inner_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have h := coefficient_action a x₀ ha ρ hρ w hw v (P ω) x
  change inner ℂ (ρ (representative a x₀ ha (a (P ω) x)) w) v =
    inner ℂ (ρ (representative a x₀ ha x) w) (ρ (P ω)⁻¹ v) at h
  rw [h]
  ring

noncomputable def fixedSpace (a : G →* Equiv.Perm X) (x₀ : X) (ρ : Representation ℂ G V) :
    Submodule ℂ V where
  carrier := {w | IsFixed a x₀ ρ w}
  zero_mem' := fun g hg => map_zero _
  add_mem' := fun hw hz g hg => by rw [map_add,hw g hg,hz g hg]
  smul_mem' := fun c w hw g hg => by rw [map_smul,hw g hg]

/-- Genuine multiplicity amplification: the family is produced from the
stabilizer-fixed space by unitary Schur orthogonality, not assumed. -/
theorem operator_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (P : Ω → G)
    (hsym : ∀ x y, actionKernel a P x y=actionKernel a P y x)
    (hrow : ∀ x, ∑ y, actionKernel a P x y=1)
    (b z M : ℝ) (hb : 0≤b) (hz : 0<z) (hM0 : 0≤M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*actionKernel a P x y)^(1+b)) ≤ M)
    (hm : 0 < Module.finrank ℂ (fixedSpace a x₀ ρ)) (v : V) (hv : ‖v‖=1) :
    ‖randomOperator ρ P v‖ ≤ M*z^(-b)+Real.sqrt (z/(Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ)) := by
  let K := fixedSpace a x₀ ρ
  let m := Module.finrank ℂ K
  let : Nonempty X := ⟨x₀⟩
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let B := stdOrthonormalBasis ℂ K
  let w : Fin m → V := fun i => (B i : V)
  have hfix (i : Fin m) : IsFixed a x₀ ρ (w i) := (B i).2
  have hw : Orthonormal ℂ w := B.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hc := normalizedCoefficient_orthonormal a x₀ ha ρ hρ w hw hfix v hv
  have hn (i : Fin m) : ‖DensityTransfer.applyKernel (actionKernel a P)
      (normalizedCoefficient a x₀ ha ρ (w i) v)‖ = ‖randomOperator ρ P v‖ := by
    rw [coefficient_random a x₀ ha ρ hρ P (w i) (hfix i),
      normalizedCoefficient_norm a x₀ ha ρ hρ (w i) (hfix i) (hw.norm_eq_one i)]
  have h := DensityTransfer.multiplicity_amplification (actionKernel a P)
    (fun x y => sampleLaw_nonneg (fun ω => a (P ω) x) y) hsym hrow
    b z M hb hz hM0 hM _ hc (‖randomOperator ρ P v‖) (fun i => (hn i).ge)
  simpa only [Fintype.card_fin] using h

end CubeShuffle.UnitaryFinite

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical

variable {G H X Ω : Type*} [Group G] [Group H] [Fintype G] [Fintype X] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] in
lemma sampleOperator_inv_apply (ρ : Representation ℂ G V) (P : Ω → G) (v : V) :
    sampleOperator ρ (fun ω => (P ω)⁻¹) v=randomOperator ρ P v := by
  simp only [sampleOperator,randomOperator,smul_apply,
    sum_apply,continuousRepresentation_apply,LinearMap.smul_apply,LinearMap.sum_apply]

/-- FAC.7 as a genuine operator-norm bound for sample averages in an irrep. -/
theorem sampleOperator_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (P : Ω → G)
    (hsym : ∀ x y, actionKernel a P x y=actionKernel a P y x)
    (hrow : ∀ x, ∑ y, actionKernel a P x y=1)
    (b z M : ℝ) (hb : 0≤b) (hz : 0<z) (hM0 : 0≤M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*actionKernel a P x y)^(1+b)) ≤ M)
    (hm : 0 < Module.finrank ℂ (fixedSpace a x₀ ρ)) :
    ‖sampleOperator ρ P‖ ≤ M*z^(-b)+Real.sqrt (z/(Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ)) := by
  rw [←ContinuousLinearMap.adjoint.norm_map (sampleOperator ρ P),←sampleOperator_inv ρ hρ]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  rw [sampleOperator_inv_apply]
  exact operator_amplification a x₀ ha ρ hρ P hsym hrow b z M hb hz hM0 hM hm v hv

omit [Fintype G] [Fintype X] [Fintype Ω] [FiniteDimensional ℂ V] in
noncomputable def subrepresentationEquiv (ρ : Representation ℂ G V) (e : H ≃* G) :
    Subrepresentation (ρ.comp e.toMonoidHom) ≃o Subrepresentation ρ where
  toFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun g v hv => by
        have h := U.apply_mem_toSubmodule (e.symm g) hv
        change ρ (e (e.symm g)) v∈U.toSubmodule at h
        simpa only [e.apply_symm_apply] using h }
  invFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun h _ hv => U.apply_mem_toSubmodule (e h) hv }
  left_inv U := by apply Subrepresentation.toSubmodule_injective; rfl
  right_inv U := by apply Subrepresentation.toSubmodule_injective; rfl
  map_rel_iff' := Iff.rfl

omit [Fintype G] [Fintype X] [Fintype Ω] [FiniteDimensional ℂ V] in
lemma irreducible_comp_equiv (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (e : H ≃* G) : Representation.IsIrreducible (ρ.comp e.toMonoidHom) := by
  exact (subrepresentationEquiv ρ e).isSimpleOrder_iff.mpr inferInstance

end CubeShuffle.UnitaryFinite

end OAI
