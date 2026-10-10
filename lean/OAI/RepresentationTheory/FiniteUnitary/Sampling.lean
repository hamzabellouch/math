import OAI.Probability.CubeShuffle.Basic
import OAI.RepresentationTheory.FiniteUnitary.Averaging

namespace OAI

namespace CubeShuffle
open scoped BigOperators Classical
variable {Ω G : Type*} [Fintype Ω] [Fintype G]

noncomputable def sampleLaw (P : Ω → G) (g : G) : ℝ :=
  finiteMean (fun ω => if P ω=g then 1 else 0)

omit [Fintype G] in
lemma sampleLaw_nonneg (P : Ω → G) (g : G) : 0 ≤ sampleLaw P g :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (Nat.cast_nonneg _)

lemma sampleLaw_sum [Nonempty Ω] (P : Ω → G) : ∑ g,sampleLaw P g=1 := by
  unfold sampleLaw
  rw [←finiteMean_sum]
  simp [finiteMean, Fintype.card_ne_zero]

omit [Fintype G] in
lemma sampleLaw_pos_iff [Nonempty Ω] (P : Ω → G) (g : G) :
    0<sampleLaw P g ↔ ∃ ω,P ω=g := by
  unfold sampleLaw finiteMean
  rw [div_pos_iff_of_pos_right (Nat.cast_pos.mpr Fintype.card_pos)]
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => by split_ifs <;> norm_num)]
  simp only [Finset.mem_univ,true_and]
  apply exists_congr
  intro ω
  split_ifs <;> simp_all

omit [Fintype G] in
lemma sampleLaw_equiv {Ω' : Type*} [Fintype Ω'] (P : Ω → G) (e : Ω' ≃ Ω) :
    sampleLaw (P ∘ e)=sampleLaw P := by
  funext g
  simpa only [sampleLaw,Function.comp_apply,Equiv.apply_symm_apply] using
    finiteMean_equiv e (fun ω => if P (e ω)=g then (1:ℝ) else 0)

variable [Group G]
omit [Fintype G] in
lemma sampleLaw_inverse (P : Ω → G) (g : G) :
    sampleLaw (fun ω => (P ω)⁻¹) g=sampleLaw P g⁻¹ := by
  apply finiteMean_congr
  intro ω
  rw [inv_eq_iff_eq_inv]

omit [Fintype G] in
lemma sampleLaw_symmetric (P : Ω → G) (e : Equiv.Perm Ω)
    (he : ∀ ω,P (e ω)=(P ω)⁻¹) (g : G) : sampleLaw P g⁻¹=sampleLaw P g := by
  rw [←sampleLaw_inverse]
  have hh : (fun ω => (P ω)⁻¹)=P ∘ e := funext (fun ω => (he ω).symm)
  rw [hh,sampleLaw_equiv]

end CubeShuffle

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sampleOperator (ρ : Representation ℂ G V) (P : Ω → G) : V →L[ℂ] V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,continuousRepresentation ρ (P ω)

omit [Fintype G] in
lemma continuousRepresentation_comp {H : Type*} [Group H]
    (ρ : Representation ℂ G V) (φ : H →* G) (h : H) :
    continuousRepresentation (ρ.comp φ) h=continuousRepresentation ρ (φ h) := rfl

omit [Fintype G] in
lemma sampleOperator_comp {H : Type*} [Group H]
    (ρ : Representation ℂ G V) (φ : H →* G) (P : Ω → H) :
    sampleOperator (ρ.comp φ) P=sampleOperator ρ (φ ∘ P) := rfl

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_comp {H : Type*} [Group H]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (φ : H →* G) :
    IsUnitary (ρ.comp φ) := fun h v w => hρ (φ h) v w

omit [Fintype G] in
lemma sampleOperator_commute (ρ : Representation ℂ G V) (P : Ω → G) (Q : Ξ → G)
    (h : ∀ ω ξ, Commute (P ω) (Q ξ)) :
    Commute (sampleOperator ρ P) (sampleOperator ρ Q) := by
  unfold sampleOperator
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sum_left
  intro ω _
  apply Commute.sum_right
  intro ξ _
  exact (h ω ξ).map (continuousRepresentation ρ)

lemma sampleOperator_weighted (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ P=weightedOperator ρ (sampleLaw P) := by
  unfold sampleOperator weightedOperator sampleLaw finiteMean
  simp only [Complex.ofReal_sum,div_eq_mul_inv,Finset.sum_mul,Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ g, if P ω=g then (Fintype.card Ω:ℂ)⁻¹ • continuousRepresentation ρ g else 0 := by
      symm
      simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp_all

lemma sampleOperator_norm_le [Nonempty Ω] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    ‖sampleOperator ρ P‖≤1 := by
  rw [sampleOperator_weighted]
  exact (weightedOperator_norm_le ρ hρ _ (sampleLaw_nonneg _)).trans_eq (sampleLaw_sum P)

omit [Fintype G] in
lemma sampleOperator_equiv (ρ : Representation ℂ G V) (P : Ω → G) (e : Ξ ≃ Ω) :
    sampleOperator ρ (P ∘ e)=sampleOperator ρ P := by
  simp only [sampleOperator,Fintype.card_congr e,Function.comp_apply]
  rw [Equiv.sum_comp e (fun ω => continuousRepresentation ρ (P ω))]

omit [Fintype G] in
lemma sampleOperator_prod (ρ : Representation ℂ G V) (P : Ω → G) (Q : Ξ → G) :
    sampleOperator ρ (fun ω : Ω × Ξ => P ω.1*Q ω.2)=sampleOperator ρ P*sampleOperator ρ Q := by
  simp only [sampleOperator,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,map_mul,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum,smul_mul_smul,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ξ _
  rw [mul_comm]

omit [Fintype G] in
lemma sampleOperator_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    sampleOperator ρ (fun ω => (P ω)⁻¹)=(sampleOperator ρ P).adjoint := by
  simp only [sampleOperator,map_smulₛₗ,map_sum,map_inv₀,map_natCast,
    continuousRepresentation_adjoint ρ hρ]

omit [Fintype G] in
lemma sampleOperator_one [Nonempty Ω] (ρ : Representation ℂ G V) :
    sampleOperator ρ (fun _ : Ω => 1)=1 := by
  simp only [sampleOperator,map_one,Finset.sum_const,Finset.card_univ,←Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]

lemma sampleOperator_uniform (ρ : Representation ℂ G V) : sampleOperator ρ (id : G → G)=uniformOperator ρ := by
  simp only [sampleOperator,uniformOperator,weightedOperator,Complex.ofReal_inv,Complex.ofReal_natCast,
    Finset.smul_sum,id_eq]

lemma sampleOperator_uniform_mul [Nonempty Ω] (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ (fun ω : Ω × G => P ω.1*ω.2⁻¹)=uniformOperator ρ := by
  rw [sampleOperator_prod]
  have he : sampleOperator ρ (fun g : G => g⁻¹)=uniformOperator ρ := by
    rw [←sampleOperator_uniform]
    exact sampleOperator_equiv ρ id (Equiv.inv G)
  rw [he,sampleOperator_weighted,weighted_uniform_left,sampleLaw_sum,one_smul]

end CubeShuffle.UnitaryFinite

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ V] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma averageMap_zero (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hne : ¬Nonempty (Representation.Equiv ρ σ)) (A : V →ₗ[ℂ] W) :
    averageMap ρ σ A=0 := by
  rcases Representation.IsIrreducible.bijective_or_eq_zero (averageMap ρ σ A) with h|h
  · exact (hne ⟨Representation.IntertwiningMap.ofBijective _ h⟩).elim
  · exact h

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma coefficient_cross_orthogonality (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hρ : IsUnitary ρ) (hne : ¬Nonempty (Representation.Equiv ρ σ))
    (u z : W) (v w : V) :
    ∑ g, inner ℂ u (σ g z)*inner ℂ (ρ g w) v=0 := by
  have he := averageMap_zero ρ σ hne (InnerProductSpace.rankOne ℂ z w).toLinearMap
  have hv := congrArg (fun T : Representation.IntertwiningMap ρ σ => inner ℂ u (T v)) he
  change inner ℂ u ((∑ g, (σ g).comp ((InnerProductSpace.rankOne ℂ z w).toLinearMap.comp (ρ g⁻¹))) v)=_ at hv
  simpa only [LinearMap.sum_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply,map_smul,unitary_inner_inv ρ hρ,inner_sum,
    inner_smul_right,Representation.IntertwiningMap.coe_zero,Pi.zero_apply,inner_zero_right,mul_comm] using hv

end CubeShuffle.UnitaryFinite
namespace CubeShuffle.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]

def regularAction : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

omit [Fintype G] in
lemma regular_transitive (x : G) : ∃ g,regularAction g (1:G)=x := ⟨x,mul_one x⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma regular_fixed (ρ : Representation ℂ G V) (w : V) : IsFixed regularAction (1:G) ρ w := by
  intro g hg
  have he : g=1 := by simpa only [regularAction,MonoidHom.coe_mk,OneHom.coe_mk,Equiv.coe_mulLeft,mul_one] using hg
  subst g
  simp

noncomputable def regularCoefficient (ρ : Representation ℂ G V) (w v : V) : EuclideanSpace ℂ G :=
  normalizedCoefficient regularAction 1 regular_transitive ρ w v

omit [FiniteDimensional ℂ V] in
lemma regularCoefficient_apply (ρ : Representation ℂ G V) (w v : V) (g : G) :
    regularCoefficient ρ w v g = (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card G:ℝ)):ℂ)*inner ℂ (ρ g w) v := by
  unfold regularCoefficient normalizedCoefficient
  simp only [PiLp.smul_apply,smul_eq_mul]
  congr 1
  have he := coefficient_at regularAction 1 regular_transitive ρ w (regular_fixed ρ w) v g
  simpa only [regularAction,MonoidHom.coe_mk,OneHom.coe_mk,Equiv.coe_mulLeft,mul_one] using he

lemma regularCoefficient_inner (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (w z v t : V) :
    inner ℂ (regularCoefficient ρ w v) (regularCoefficient ρ z t)=inner ℂ z w*inner ℂ v t :=
  normalizedCoefficient_inner regularAction 1 regular_transitive ρ hρ w z
    (regular_fixed ρ w) (regular_fixed ρ z) v t

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma regularCoefficient_cross (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hσ : IsUnitary σ) (hne : ¬Nonempty (Representation.Equiv σ ρ))
    (w v : V) (z t : W) : inner ℂ (regularCoefficient ρ w v) (regularCoefficient σ z t)=0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,regularCoefficient_apply,map_mul,Complex.conj_ofReal,
    inner_conj_symm]
  have he := coefficient_cross_orthogonality σ ρ hσ hne v w t z
  calc
    _ = ((Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card G:ℝ)):ℂ)*
        (Real.sqrt ((Module.finrank ℂ W:ℝ)/(Fintype.card G:ℝ)):ℂ)) *
        ∑ g,inner ℂ v (ρ g w)*inner ℂ (σ g z) t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = 0 := by rw [he,mul_zero]

end CubeShuffle.UnitaryFinite

end OAI
