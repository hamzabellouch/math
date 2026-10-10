import Mathlib
import OAI.Probability.ThorpRouting.Harmonic.Shapes

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

noncomputable def averageMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A : V →ₗ[ℂ] W) : Representation.IntertwiningMap ρ σ where
  toLinearMap := ∑ g, (σ g).comp (A.comp (ρ g⁻¹))
  isIntertwining' h := by
    ext v
    simp only [LinearMap.comp_apply,LinearMap.sum_apply,map_sum]
    apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
    intro g
    simp only [Equiv.coe_mulLeft,mul_inv_rev,inv_inv,map_mul,Module.End.mul_apply]
    have hh (w : W) : σ h (σ h⁻¹ w)=w := by
      change (σ h*σ h⁻¹) w=w
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl
    rw [hh]

omit [FiniteDimensional ℂ V] in
lemma averageMap_self_trace (ρ : Representation ℂ G V) (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (averageMap ρ ρ A).toLinearMap =
      (Fintype.card G:ℂ) * LinearMap.trace ℂ V A := by
  change LinearMap.trace ℂ V (∑ g, ρ g * A * ρ g⁻¹) = _
  rw [map_sum]
  have hj (g : G) : LinearMap.trace ℂ V (ρ g*A*ρ g⁻¹) = LinearMap.trace ℂ V A := by
    rw [LinearMap.trace_mul_cycle,←map_mul,inv_mul_cancel,map_one,one_mul]
  simp only [hj,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

lemma averageMap_scalar (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (A : Module.End ℂ V) :
    ∃ c : ℂ, (averageMap ρ ρ A).toLinearMap = c • LinearMap.id ∧
      c * (Module.finrank ℂ V:ℂ) = (Fintype.card G:ℂ)*LinearMap.trace ℂ V A := by
  obtain ⟨c,hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective (averageMap ρ ρ A)
  have he : (averageMap ρ ρ A).toLinearMap = c • LinearMap.id := by
    rw [←hc]
    rfl
  refine ⟨c,he,?_⟩
  rw [←averageMap_self_trace ρ A,he,map_smul,LinearMap.trace_id,smul_eq_mul]

theorem coefficient_orthogonality (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (u v w z : V) :
    (Module.finrank ℂ V:ℂ) * ∑ g, inner ℂ u (ρ g v) * inner ℂ (ρ g w) z =
      (Fintype.card G:ℂ) * inner ℂ w v * inner ℂ u z := by
  obtain ⟨c,hc,htrace⟩ := averageMap_scalar ρ (InnerProductSpace.rankOne ℂ v w).toLinearMap
  rw [InnerProductSpace.trace_rankOne] at htrace
  have happ := congrArg (fun A : Module.End ℂ V => inner ℂ u (A z)) hc
  change inner ℂ u ((∑ g, ρ g * (InnerProductSpace.rankOne ℂ v w).toLinearMap * ρ g⁻¹) z) = _ at happ
  simp only [LinearMap.sum_apply,Module.End.mul_apply,ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply,map_smul,unitary_inner_inv ρ hρ,inner_sum,
    inner_smul_right,LinearMap.smul_apply,LinearMap.id_apply] at happ
  have hsum : ∑ g, inner ℂ u (ρ g v) * inner ℂ (ρ g w) z = c * inner ℂ u z := by
    simpa only [mul_comm] using happ
  rw [hsum]
  calc
    _ = (c*(Module.finrank ℂ V:ℂ))*inner ℂ u z := by ring
    _ = _ := by rw [htrace]

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀=x)

noncomputable def representative (x : X) : G := Classical.choose (ha x)

omit [Fintype G] [Fintype X] in
lemma representative_apply (x : X) : a (representative a x₀ ha x) x₀=x :=
  Classical.choose_spec (ha x)

include ha in
lemma orbit_sum (F : X → ℂ) :
    (Fintype.card X:ℂ)*∑ g, F (a g x₀) = (Fintype.card G:ℂ)*∑ x, F x := by
  have ht (x : X) : ∑ g, F (a g x)=∑ g, F (a g x₀) := by
    obtain ⟨t,rfl⟩ := ha x
    symm
    apply Fintype.sum_equiv (Equiv.mulRight t⁻¹)
    intro g
    simp
  calc
    _ = ∑ x : X, ∑ g : G, F (a g x) := by simp only [ht,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ = ∑ g : G, ∑ x : X, F (a g x) := Finset.sum_comm
    _ = ∑ g : G, ∑ x : X, F x := by
      apply Finset.sum_congr rfl
      intro g _
      exact Equiv.sum_comp (a g) F
    _ = _ := by simp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

def IsFixed (w : V) : Prop := ∀ g, a g x₀=x₀ → ρ g w=w

noncomputable def coefficient (w v : V) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => inner ℂ (ρ (representative a x₀ ha x) w) v)

omit [Fintype G] [Fintype X] [FiniteDimensional ℂ V] in
lemma coefficient_at (w : V) (hw : IsFixed a x₀ ρ w) (v : V) (g : G) :
    coefficient a x₀ ha ρ w v (a g x₀) = inner ℂ (ρ g w) v := by
  let r := representative a x₀ ha (a g x₀)
  have hr : a r x₀=a g x₀ := representative_apply a x₀ ha _
  have hs : a (g⁻¹*r) x₀=x₀ := by
    simp only [map_mul,Equiv.Perm.mul_apply]
    rw [hr,←Equiv.Perm.mul_apply,←map_mul,inv_mul_cancel,map_one]
    rfl
  have he := congrArg (ρ g) (hw (g⁻¹*r) hs)
  have hh : ρ r w=ρ g w := by
    simpa only [map_mul,Module.End.mul_apply,←Module.End.mul_apply,←map_mul,
      mul_inv_cancel_left] using he
  change inner ℂ (ρ r w) v= _
  rw [hh]

lemma coefficient_inner [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w z : V) (hw : IsFixed a x₀ ρ w) (hz : IsFixed a x₀ ρ z) (v t : V) :
    (Module.finrank ℂ V:ℂ)*inner ℂ (coefficient a x₀ ha ρ w v) (coefficient a x₀ ha ρ z t) =
      (Fintype.card X:ℂ)*inner ℂ z w*inner ℂ v t := by
  have hs := orbit_sum a x₀ ha (fun x => star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x)
  simp only [coefficient_at a x₀ ha ρ w hw,coefficient_at a x₀ ha ρ z hz] at hs
  simp only [←starRingEnd_apply,inner_conj_symm] at hs
  simp only [starRingEnd_apply] at hs
  have ho := coefficient_orthogonality ρ hρ v w z t
  have hcard : (Fintype.card G:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  have hsum : ∑ x, coefficient a x₀ ha ρ z t x * star (coefficient a x₀ ha ρ w v x) =
      ∑ x, star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  calc
    _ = (Module.finrank ℂ V:ℂ)*((Fintype.card G:ℂ)*∑ x,
        star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x) := by ring
    _ = (Fintype.card X:ℂ)*((Module.finrank ℂ V:ℂ)*∑ g,
        inner ℂ v (ρ g w)*inner ℂ (ρ g z) t) := by rw [←hs]; ring
    _ = _ := by rw [ho]; ring

omit [Fintype G] [Fintype X] [FiniteDimensional ℂ V] in
lemma coefficient_action (hρ : IsUnitary ρ) (w : V) (hw : IsFixed a x₀ ρ w)
    (v : V) (g : G) (x : X) :
    coefficient a x₀ ha ρ w v (a g x) = coefficient a x₀ ha ρ w (ρ g⁻¹ v) x := by
  obtain ⟨r,rfl⟩ := ha x
  rw [←Equiv.Perm.mul_apply,←map_mul,coefficient_at a x₀ ha ρ w hw,
    coefficient_at a x₀ ha ρ w hw]
  simp only [map_mul,Module.End.mul_apply,unitary_inner_inv ρ hρ]

noncomputable def normalizedCoefficient (w v : V) : EuclideanSpace ℂ X :=
  (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card X:ℝ)) : ℂ) • coefficient a x₀ ha ρ w v

lemma normalizedCoefficient_inner [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w z : V) (hw : IsFixed a x₀ ρ w) (hz : IsFixed a x₀ ρ z) (v t : V) :
    inner ℂ (normalizedCoefficient a x₀ ha ρ w v) (normalizedCoefficient a x₀ ha ρ z t) =
      inner ℂ z w*inner ℂ v t := by
  let : Nonempty X := ⟨x₀⟩
  have hX : (Fintype.card X:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card X:ℝ)) : ℂ)^2 =
      (Module.finrank ℂ V:ℂ)/(Fintype.card X:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
    simp
  simp only [normalizedCoefficient,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal]
  rw [←mul_assoc,←pow_two,hs]
  have hi := coefficient_inner a x₀ ha ρ hρ w z hw hz v t
  field_simp
  simpa only [mul_assoc] using hi

lemma normalizedCoefficient_orthonormal [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    {I : Type*} (w : I → V) (hw : Orthonormal ℂ w)
    (hfix : ∀ i, IsFixed a x₀ ρ (w i)) (v : V) (hv : ‖v‖=1) :
    Orthonormal ℂ (fun i => normalizedCoefficient a x₀ ha ρ (w i) v) := by
  rw [orthonormal_iff_ite] at hw ⊢
  intro i j
  rw [normalizedCoefficient_inner a x₀ ha ρ hρ _ _ (hfix i) (hfix j),hw,
    inner_self_eq_norm_sq_to_K,hv]
  simp [eq_comm]

lemma normalizedCoefficient_norm [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w : V) (hw : IsFixed a x₀ ρ w) (hn : ‖w‖=1) (v : V) :
    ‖normalizedCoefficient a x₀ ha ρ w v‖=‖v‖ := by
  have he := normalizedCoefficient_inner a x₀ ha ρ hρ w w hw hw v v
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,hn] at he
  simp only [inner_self_eq_norm_sq_to_K] at he
  norm_num at he
  have hs : ‖normalizedCoefficient a x₀ ha ρ w v‖^2=‖v‖^2 := by exact_mod_cast he
  nlinarith [norm_nonneg (normalizedCoefficient a x₀ ha ρ w v),norm_nonneg v]

end Thorp.UnitaryFinite

namespace Thorp.FiniteConvolution
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]

noncomputable def conv (p q : G → ℝ) (g : G) : ℝ := ∑ h, p h*q (h⁻¹*g)
noncomputable def power (p : G → ℝ) : ℕ → G → ℝ
  | 0 => fun g => if g=1 then 1 else 0
  | n+1 => conv p (power p n)

lemma conv_nonneg {p q : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g) :
    ∀ g, 0 ≤ conv p q g := fun _ => Finset.sum_nonneg (fun h _ => mul_nonneg (hp h) (hq _))

lemma conv_pos_of {p q : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g)
    {a b : G} (ha : 0 < p a) (hb : 0 < q b) : 0 < conv p q (a*b) := by
  apply lt_of_lt_of_le (mul_pos ha hb)
  have h := Finset.single_le_sum (fun g _ => mul_nonneg (hp g) (hq (g⁻¹*(a*b))))
    (Finset.mem_univ a)
  simpa [conv] using h

lemma sum_conv (p q : G → ℝ) : ∑ g, conv p q g=(∑ g,p g)*(∑ g,q g) := by
  unfold conv
  rw [Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [←Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun _ => rfl)

lemma power_nonneg {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) : ∀ n g, 0 ≤ power p n g := by
  intro n
  induction n with
  | zero => intro g; simp only [power]; split_ifs  <;> norm_num
  | succ n ih => exact conv_nonneg hp ih

lemma sum_power {p : G → ℝ} (hp : ∑ g,p g=1) : ∀ n, ∑ g,power p n g=1 := by
  intro n
  induction n with
  | zero => simp [power]
  | succ n ih => rw [power,sum_conv,hp,ih,one_mul]

lemma power_list_pos {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (l : List G)
    (hl : ∀ g ∈ l, 0 < p g) : 0 < power p l.length l.prod := by
  induction l with
  | nil => simp [power]
  | cons a l ih =>
    simpa only [List.length_cons,List.prod_cons,power] using
      conv_pos_of hp (power_nonneg hp l.length) (hl a (by simp))
        (ih (fun g hg => hl g (by simp [hg])))

lemma power_pos_mono {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (h1 : 0 < p 1)
    {n m : ℕ} (hnm : n ≤ m) {g : G} (hg : 0 < power p n g) : 0 < power p m g := by
  induction m, hnm using Nat.le_induction with
  | base => exact hg
  | succ m _ ih =>
    simpa only [one_mul,power] using conv_pos_of hp (power_nonneg hp m) h1 ih

theorem exists_positive_power {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (h1 : 0 < p 1)
    (hgen : Subgroup.closure {g | 0 < p g}=⊤) :
    ∃ n : ℕ, ∀ g, 0 < power p (2^n) g := by
  have hx (g : G) : g ∈ Submonoid.closure {g | 0 < p g} := by
    rw [←Subgroup.closure_toSubmonoid_of_finite,hgen]
    trivial
  choose l hl hprod using fun g => Submonoid.exists_list_of_mem_closure (hx g)
  let n := Finset.univ.sup (fun g => (l g).length)
  refine ⟨n,fun g => ?_⟩
  have hlen : (l g).length ≤ n := Finset.le_sup (f := fun g => (l g).length) (Finset.mem_univ g)
  have hpow : n ≤ 2^n := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hpos := power_list_pos hp (l g) (hl g)
  rw [hprod g] at hpos
  exact power_pos_mono hp h1 (hlen.trans hpow) hpos

structure Minorant (p : G → ℝ) where
  exponent : ℕ
  mass : ℝ
  mass_pos : 0 < mass
  mass_le_one : mass ≤ 1
  lower : ∀ g, mass/(Fintype.card G:ℝ) ≤ power p (2^exponent) g

noncomputable def minorant {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hsum : ∑ g,p g=1)
    (h1 : 0 < p 1) (hgen : Subgroup.closure {g | 0 < p g}=⊤) : Minorant p := by
  let n := Classical.choose (exists_positive_power hp h1 hgen)
  have hn := Classical.choose_spec (exists_positive_power hp h1 hgen)
  let a := Finset.univ.inf' Finset.univ_nonempty (power p (2^n))
  have ha : 0 < a := (Finset.lt_inf'_iff _).mpr (fun g _ => hn g)
  have hag (g : G) : a ≤ power p (2^n) g := Finset.inf'_le _ (Finset.mem_univ g)
  have hN : (0:ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hsum' := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hag g)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sum_power hsum] at hsum'
  refine ⟨n,(Fintype.card G:ℝ)*a,mul_pos hN ha,hsum',fun g => ?_⟩
  have he : (Fintype.card G:ℝ)*a/(Fintype.card G:ℝ)=a := by field_simp
  rw [he]
  exact hag g

end Thorp.FiniteConvolution
namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] in
@[simp] lemma continuousRepresentation_apply (ρ : Representation ℂ G V) (g : G) (v : V) :
    continuousRepresentation ρ g v=ρ g v := rfl

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_norm (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v : V) :
    ‖ρ g v‖=‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),hρ,norm_eq_sqrt_re_inner (𝕜 := ℂ)]

omit [Fintype G] in
lemma continuousRepresentation_norm_le (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    ‖continuousRepresentation ρ g‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [continuousRepresentation_apply,unitary_norm ρ hρ,one_mul,le_refl]

omit [Fintype G] in
lemma continuousRepresentation_adjoint (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    (continuousRepresentation ρ g).adjoint=continuousRepresentation ρ g⁻¹ := by
  ext w
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (unitary_inner_inv ρ hρ g v w).symm

noncomputable def weightedOperator (ρ : Representation ℂ G V) (p : G → ℝ) : V →L[ℂ] V :=
  ∑ g, (p g : ℂ) • continuousRepresentation ρ g

lemma weightedOperator_norm_le (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∀ g, 0≤p g) : ‖weightedOperator ρ p‖ ≤ ∑ g, p g := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp g)]
  exact mul_le_of_le_one_right (hp g) (continuousRepresentation_norm_le ρ hρ g)

lemma weightedOperator_symmetric (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∀ g, p g⁻¹=p g) : IsSelfAdjoint (weightedOperator ρ p) := by
  change (weightedOperator ρ p).adjoint=weightedOperator ρ p
  unfold weightedOperator
  rw [map_sum]
  simp only [map_smulₛₗ,Complex.conj_ofReal,continuousRepresentation_adjoint ρ hρ]
  apply Fintype.sum_equiv (Equiv.inv G)
  intro g
  simp [hp]

noncomputable def uniformOperator (ρ : Representation ℂ G V) : V →L[ℂ] V :=
  weightedOperator ρ (fun _ => (Fintype.card G:ℝ)⁻¹)

lemma uniformOperator_symmetric (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) :
    IsSelfAdjoint (uniformOperator ρ) := weightedOperator_symmetric ρ hρ _ (fun _ => rfl)

lemma uniformOperator_left (ρ : Representation ℂ G V) (g : G) :
    continuousRepresentation ρ g * uniformOperator ρ=uniformOperator ρ := by
  unfold uniformOperator weightedOperator
  rw [Finset.mul_sum]
  simp only [mul_smul_comm,←map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

lemma uniformOperator_right (ρ : Representation ℂ G V) (g : G) :
    uniformOperator ρ * continuousRepresentation ρ g=uniformOperator ρ := by
  unfold uniformOperator weightedOperator
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,←map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

lemma uniformOperator_idempotent (ρ : Representation ℂ G V) :
    IsIdempotentElem (uniformOperator ρ) := by
  change uniformOperator ρ * uniformOperator ρ=uniformOperator ρ
  nth_rw 1 [uniformOperator,weightedOperator]
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,uniformOperator_left,Finset.sum_const,Finset.card_univ,
    ←Nat.cast_smul_eq_nsmul ℂ,smul_smul,Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]

lemma uniformOperator_projection (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) :
    IsStarProjection (uniformOperator ρ) :=
  ⟨uniformOperator_idempotent ρ,uniformOperator_symmetric ρ hρ⟩

lemma weighted_uniform_left (ρ : Representation ℂ G V) (p : G → ℝ) :
    weightedOperator ρ p * uniformOperator ρ=(∑ g,p g : ℝ) • uniformOperator ρ := by
  unfold weightedOperator
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,uniformOperator_left,←Finset.sum_smul,←Complex.ofReal_sum]
  rfl

lemma weighted_uniform_right (ρ : Representation ℂ G V) (p : G → ℝ) :
    uniformOperator ρ * weightedOperator ρ p=(∑ g,p g : ℝ) • uniformOperator ρ := by
  unfold weightedOperator
  rw [Finset.mul_sum]
  simp only [mul_smul_comm,uniformOperator_right,←Finset.sum_smul,←Complex.ofReal_sum]
  rfl

theorem doeblin_off_invariants (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∑ g,p g=1) (ε : ℝ)
    (hminor : ∀ g, ε/(Fintype.card G:ℝ)≤p g) :
    ‖weightedOperator ρ p * (1-uniformOperator ρ)‖≤1-ε := by
  let q : G → ℝ := fun g => p g-ε/(Fintype.card G:ℝ)
  have hq : ∀ g, 0≤q g := fun g => sub_nonneg.mpr (hminor g)
  have hcard : (Fintype.card G:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ g,q g=1-ε := by
    simp only [q,Finset.sum_sub_distrib,hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have he : weightedOperator ρ p=weightedOperator ρ q+(ε:ℂ) • uniformOperator ρ := by
    simp only [uniformOperator,weightedOperator]
    rw [Finset.smul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    simp only [q,Complex.ofReal_sub,Complex.ofReal_div,smul_smul,←add_smul,
      Complex.ofReal_inv,Complex.ofReal_natCast]
    congr 1
    field_simp
    ring
  have hz : uniformOperator ρ*(1-uniformOperator ρ)=0 := by
    rw [mul_sub,mul_one,(uniformOperator_idempotent ρ).eq,sub_self]
  rw [he,add_mul,smul_mul_assoc,hz,smul_zero,add_zero]
  calc
    _ ≤ ‖weightedOperator ρ q‖*‖1-uniformOperator ρ‖ := norm_mul_le _ _
    _ ≤ (1-ε)*1 := mul_le_mul (by rw [←hsum]; exact weightedOperator_norm_le ρ hρ q hq)
      ((uniformOperator_projection ρ hρ).one_sub.norm_le _) (norm_nonneg _)
      (by rw [←hsum]; exact Finset.sum_nonneg (fun g _ => hq g))
    _ = _ := mul_one _

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma weightedOperator_conv (ρ : Representation ℂ G V) (p q : G → ℝ) :
    weightedOperator ρ (FiniteConvolution.conv p q)=weightedOperator ρ p*weightedOperator ρ q := by
  unfold weightedOperator FiniteConvolution.conv
  simp only [Complex.ofReal_sum,Finset.sum_smul]
  rw [Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,←map_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
  intro g
  simp [Complex.ofReal_mul,mul_comm]

lemma weightedOperator_power (ρ : Representation ℂ G V) (p : G → ℝ) (n : ℕ) :
    weightedOperator ρ (FiniteConvolution.power p n)=(weightedOperator ρ p)^n := by
  induction n with
  | zero => simp [FiniteConvolution.power,weightedOperator]
  | succ n ih => rw [FiniteConvolution.power,weightedOperator_conv,ih,pow_succ']

lemma off_invariants_pow (ρ : Representation ℂ G V) (p : G → ℝ)
    (hp : ∑ g,p g=1) (n : ℕ) (hn : n≠0) :
    (weightedOperator ρ p-uniformOperator ρ)^n=
      (weightedOperator ρ p)^n*(1-uniformOperator ρ) := by
  have hAP := weighted_uniform_left ρ p
  have hPA := weighted_uniform_right ρ p
  rw [hp,one_smul] at hAP hPA
  have hc : Commute (weightedOperator ρ p) (1-uniformOperator ρ) := by
    show _*_= _*_
    rw [mul_sub,sub_mul,mul_one,one_mul,hAP,hPA]
  have he : weightedOperator ρ p-uniformOperator ρ=
      weightedOperator ρ p*(1-uniformOperator ρ) := by rw [mul_sub,mul_one,hAP]
  rw [he,hc.mul_pow,((uniformOperator_idempotent ρ).one_sub).pow_eq hn]

noncomputable def minorantGap {p : G → ℝ} (c : FiniteConvolution.Minorant p) : ℝ :=
  1-c.mass/(2*(2:ℝ)^c.exponent)

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] in
lemma minorantGap_pos {p : G → ℝ} (c : FiniteConvolution.Minorant p) : 0 < minorantGap c := by
  have hn : (1:ℝ) ≤ 2^c.exponent := one_le_pow₀ (by norm_num)
  have hq : c.mass/(2*(2:ℝ)^c.exponent) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [c.mass_le_one]
  unfold minorantGap
  linarith

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] in
lemma minorantGap_lt_one {p : G → ℝ} (c : FiniteConvolution.Minorant p) : minorantGap c < 1 := by
  unfold minorantGap
  exact sub_lt_self _ (div_pos c.mass_pos (by positivity))

theorem norm_off_invariants_le_gap (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∑ g,p g=1) (hsym : ∀ g,p g⁻¹=p g)
    (c : FiniteConvolution.Minorant p) :
    ‖weightedOperator ρ p-uniformOperator ρ‖ ≤ minorantGap c := by
  have hself := (weightedOperator_symmetric ρ hρ p hsym).sub (uniformOperator_symmetric ρ hρ)
  have hbound := doeblin_off_invariants ρ hρ (FiniteConvolution.power p (2^c.exponent))
    (FiniteConvolution.sum_power hp _) c.mass c.lower
  rw [weightedOperator_power,←off_invariants_pow ρ p hp _ (by positivity),
    hself.norm_pow_two_pow] at hbound
  have hn : (1:ℝ) ≤ 2^c.exponent := one_le_pow₀ (by norm_num)
  have hq : c.mass/(2*(2:ℝ)^c.exponent) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [c.mass_le_one]
  have hbern := one_add_mul_le_pow
    (a := -(c.mass/(2*(2:ℝ)^c.exponent))) (by linarith : (-2:ℝ) ≤ -(c.mass/(2*(2:ℝ)^c.exponent)))
    (2^c.exponent)
  have he : 1+(2^c.exponent:ℕ)*(-(c.mass/(2*(2:ℝ)^c.exponent)))=1-c.mass/2 := by
    push_cast
    field_simp
    ring
  rw [he,show 1+ -(c.mass/(2*(2:ℝ)^c.exponent))=minorantGap c by rfl] at hbern
  by_contra h
  have hlt : minorantGap c < ‖weightedOperator ρ p-uniformOperator ρ‖ := lt_of_not_ge h
  have hpows := pow_lt_pow_left₀ hlt (minorantGap_pos c).le (by positivity : (2^c.exponent:ℕ)≠0)
  linarith [c.mass_pos]

end Thorp.UnitaryFinite
namespace Thorp
open scoped BigOperators Classical

def butterflyIdentity : (d : ℕ) → Butterfly d
  | 0 => ()
  | d+1 => (fun _ => false,fun _ => butterflyIdentity d)

lemma pairSwitch_false (d : ℕ) : pairSwitch (d := d) (fun _ => false)=1 := by
  apply Equiv.ext
  intro x
  change switchFun (fun _ => false) x=x
  simp [switchFun]

lemma childLift_one (d : ℕ) : childLift (d := d) (fun _ => 1)=1 := by
  ext x i
  simp [childLift]

lemma butterflyIdentity_perm (d : ℕ) : butterflyPerm d (butterflyIdentity d)=1 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [butterflyIdentity,butterflyPerm,ih,pairSwitch_false,childLift_one,mul_one]

noncomputable def childInjection (d : ℕ) (b : Bool) : Equiv.Perm (Card d) →* Equiv.Perm (Card (d+1)) where
  toFun p := childLift (fun c => if c=b then p else 1)
  map_one' := by simpa only [ite_self] using childLift_one d
  map_mul' p q := by
    rw [childLift_mul]
    congr 1
    funext c
    split_ifs <;> simp

lemma childInjection_swap (d : ℕ) (b : Bool) (u v : Card d) :
    childInjection d b (Equiv.swap u v)=Equiv.swap (Fin.cons b u) (Fin.cons b v) := by
  apply Equiv.ext
  intro x
  obtain ⟨c,w,rfl⟩ : ∃ c w, x=Fin.cons c w := ⟨x 0,Fin.tail x,(Fin.cons_self_tail x).symm⟩
  change (Fin.cons c ((if c=b then Equiv.swap u v else 1) w) : Card (d+1))=_
  by_cases hc : c=b
  · subst c
    simp only [↓reduceIte]
    rw [Equiv.swap_apply_def]
    split_ifs with h₁ h₂
    · subst w; simp
    · subst w; simp
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · exact fun h => h₁ (by simpa using congrArg Fin.tail h)
      · exact fun h => h₂ (by simpa using congrArg Fin.tail h)
  · rw [ite_eq_right hc,Equiv.Perm.one_apply,Equiv.swap_apply_of_ne_of_ne]
    · intro h; exact hc (by simpa using congrArg (fun z => z 0) h)
    · intro h; exact hc (by simpa using congrArg (fun z => z 0) h)

lemma pairSwitch_single (d : ℕ) (u : Card d) :
    pairSwitch (fun v => decide (v=u))=Equiv.swap (Fin.cons false u) (Fin.cons true u) := by
  apply Equiv.ext
  intro x
  obtain ⟨c,w,rfl⟩ : ∃ c w, x=Fin.cons c w := ⟨x 0,Fin.tail x,(Fin.cons_self_tail x).symm⟩
  change switchFun (fun v => decide (v=u)) (Fin.cons c w)=_
  by_cases h : w=u
  · subst w
    cases c <;> simp [switchFun]
  · have ha : (Fin.cons c w : Card (d+1))≠Fin.cons false u := fun he => h (by simpa using congrArg Fin.tail he)
    have hb : (Fin.cons c w : Card (d+1))≠Fin.cons true u := fun he => h (by simpa using congrArg Fin.tail he)
    simp [switchFun,h,Equiv.swap_apply_of_ne_of_ne ha hb]

theorem butterfly_generates (d : ℕ) (H : Subgroup (Equiv.Perm (Card d)))
    (hH : ∀ ω : Butterfly d, butterflyPerm d ω∈H) : H=⊤ := by
  induction d with
  | zero =>
    apply top_unique
    intro p _
    have hp : p=1 := Subsingleton.elim _ _
    rw [hp]
    exact H.one_mem
  | succ d ih =>
    have hchild (b : Bool) (p : Equiv.Perm (Card d)) : childInjection d b p∈H := by
      have hc : H.comap (childInjection d b)=⊤ := by
        apply ih
        intro ω
        change childLift (fun c => if c=b then butterflyPerm d ω else 1)∈H
        have h := hH ((fun _ => false),fun c => if c=b then ω else butterflyIdentity d)
        simpa only [butterflyPerm,pairSwitch_false,one_mul,apply_ite,butterflyIdentity_perm] using h
      have hp : p∈H.comap (childInjection d b) := by rw [hc]; trivial
      exact hp
    have hpair (u : Card d) : Equiv.swap (Fin.cons false u) (Fin.cons true u)∈H := by
      rw [←pairSwitch_single]
      have h := hH ((fun v => decide (v=u)),fun _ => butterflyIdentity d)
      simpa only [butterflyPerm,butterflyIdentity_perm,childLift_one,mul_one] using h
    have hswap (x y : Card (d+1)) : Equiv.swap x y∈H := by
      have ht (a b : Bool) (u : Card d) : Equiv.swap (Fin.cons a u) (Fin.cons b u)∈H := by
        cases a <;> cases b
        · rw [Equiv.swap_self]; exact H.one_mem
        · exact hpair _
        · rw [Equiv.swap_comm]; exact hpair _
        · rw [Equiv.swap_self]; exact H.one_mem
      have h₁ : Equiv.swap x (Fin.cons (y 0) (Fin.tail x))∈H := by
        convert ht (x 0) (y 0) (Fin.tail x) using 1
        rw [Fin.cons_self_tail]
      have h₂ := hchild (y 0) (Equiv.swap (Fin.tail x) (Fin.tail y))
      rw [childInjection_swap,Fin.cons_self_tail] at h₂
      exact SubmonoidClass.swap_mem_trans H h₁ h₂
    rw [eq_top_iff,←Equiv.Perm.closure_isSwap,Subgroup.closure_le]
    rintro _ ⟨x,y,_,rfl⟩
    exact hswap x y

lemma butterfly_closure (d : ℕ) : Subgroup.closure (Set.range (butterflyPerm d))=⊤ :=
  butterfly_generates d _ (fun ω => Subgroup.subset_closure ⟨ω,rfl⟩)

variable {Ω G : Type*} [Fintype Ω] [Fintype G]

noncomputable def sampleLaw (P : Ω → G) (g : G) : ℝ :=
  finiteMean (fun ω => if P ω=g then 1 else 0)

omit [Fintype G] in
lemma sampleLaw_nonneg (P : Ω → G) (g : G) : 0 ≤ sampleLaw P g :=
  finiteMean_nonneg (fun _ => by split_ifs <;> norm_num)

lemma sampleLaw_sum [Nonempty Ω] (P : Ω → G) : ∑ g,sampleLaw P g=1 := by
  unfold sampleLaw
  rw [←finiteMean_sum]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,finiteMean_const]

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

end Thorp

namespace Thorp
open scoped BigOperators Classical

lemma palindrome_identity (d : ℕ) : ∃ ω,palindromePerm d ω=1 := by
  refine ⟨((butterflyCoinEquiv d).symm (butterflyIdentity d),
    (butterflyCoinEquiv d).symm (butterflyIdentity d)),?_⟩
  exact mul_inv_cancel _

lemma palindrome_range_contains_butterfly (d : ℕ) (ω : Butterfly d) :
    ∃ ξ,palindromePerm d ξ=butterflyPerm d ω := by
  refine ⟨((butterflyCoinEquiv d).symm ω,(butterflyCoinEquiv d).symm (butterflyIdentity d)),?_⟩
  unfold palindromePerm
  have h (β : Butterfly d) : decodeButterfly d ((butterflyCoinEquiv d).symm β)=β :=
    (butterflyCoinEquiv d).apply_symm_apply β
  rw [h,h,butterflyIdentity_perm,show (1 : Equiv.Perm (Card d)).symm=1 from rfl,mul_one]

lemma palindrome_support_generates (d : ℕ) :
    Subgroup.closure {g | 0<sampleLaw (palindromePerm d) g}=⊤ := by
  apply butterfly_generates
  intro ω
  apply Subgroup.subset_closure
  exact (sampleLaw_pos_iff _ _).mpr (palindrome_range_contains_butterfly d ω)

noncomputable def palindromeMinorant (d : ℕ) :
    FiniteConvolution.Minorant (sampleLaw (palindromePerm d)) :=
  FiniteConvolution.minorant (sampleLaw_nonneg _) (sampleLaw_sum _)
    ((sampleLaw_pos_iff _ _).mpr (palindrome_identity d)) (palindrome_support_generates d)

noncomputable def blockGap (d : ℕ) : ℝ := UnitaryFinite.minorantGap (palindromeMinorant d)

lemma blockGap_pos (d : ℕ) : 0<blockGap d := UnitaryFinite.minorantGap_pos _
lemma blockGap_lt_one (d : ℕ) : blockGap d<1 := UnitaryFinite.minorantGap_lt_one _

theorem palindrome_off_invariants_gap (d : ℕ) {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) (hρ : UnitaryFinite.IsUnitary ρ) :
    ‖UnitaryFinite.weightedOperator ρ (sampleLaw (palindromePerm d))-
      UnitaryFinite.uniformOperator ρ‖≤blockGap d := by
  apply UnitaryFinite.norm_off_invariants_le_gap ρ hρ _ (sampleLaw_sum _)
  exact sampleLaw_symmetric _ (Equiv.prodComm _ _) (palindromePerm_reverse d)

end Thorp

namespace Thorp.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι]

omit [CompleteSpace V] in
lemma orthogonal_sum_norm_sq (v : ι → V) (hv : ∀ i j, i≠j → inner ℂ (v i) (v j)=0) :
    ‖∑ i,v i‖^2=∑ i,‖v i‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),sum_inner]
  simp only [inner_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact (norm_sq_eq_re_inner (𝕜 := ℂ) (v i)).symm
  · intro j _ hji
    rw [hv i j hji.symm]
    rfl
  · simp

lemma projection_inner_zero (P Q : V →L[ℂ] V) (hP : IsStarProjection P)
    (hPQ : P*Q=0) (v w : V) : inner ℂ (P v) (Q w)=0 := by
  rw [←ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ v ((star P*Q) w)=0
  rw [hP.isSelfAdjoint.star_eq,hPQ]
  simp

lemma projection_sandwich_norm (P B : V →L[ℂ] V) (hP : IsStarProjection P) :
    ‖B.adjoint*P*B‖=‖P*B‖^2 := by
  have he : star (P*B)*(P*B)=B.adjoint*P*B := by
    rw [star_mul,hP.isSelfAdjoint.star_eq]
    change B.adjoint*P*(P*B)=_
    rw [←mul_assoc,mul_assoc B.adjoint P P,hP.isIdempotentElem.eq]
  rw [←he,CStarRing.norm_star_mul_self]
  ring

theorem resolution_norm_bound (P : ι → V →L[ℂ] V)
    (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i≠j → P i*P j=0) (hsum : ∑ i,P i=1)
    (A : V →L[ℂ] V) (hcomm : ∀ i, Commute A (P i))
    (c : ℝ) (hc : 0≤c) (hbound : ∀ i, ‖A*P i‖≤c) : ‖A‖≤c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro v
  have hsplit (w : V) : ∑ i,P i w=w := by
    rw [←sum_apply,hsum]
    rfl
  have hp := orthogonal_sum_norm_sq (fun i => P i v)
    (fun i j hij => projection_inner_zero _ _ (hP i) (horth i j hij) v v)
  rw [hsplit] at hp
  have ha := orthogonal_sum_norm_sq (fun i => P i (A v))
    (fun i j hij => projection_inner_zero _ _ (hP i) (horth i j hij) (A v) (A v))
  rw [hsplit] at ha
  have he (i : ι) : P i (A v)=(A*P i) (P i v) := by
    change (P i*A) v=(A*P i*P i) v
    rw [mul_assoc,(hP i).isIdempotentElem.eq,(hcomm i).eq]
  have hh (i : ι) : ‖P i (A v)‖≤c*‖P i v‖ := by
    rw [he]
    exact ((A*P i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg _))
  have hsq := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hh i) 2)
  simp_rw [mul_pow] at hsq
  rw [←Finset.mul_sum,←hp,←ha,←mul_pow] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp hsq

theorem sector_sandwich_le (T P A B : V →L[ℂ] V)
    (hT : IsStarProjection T) (hP : IsStarProjection P)
    (hTP : T*P=T) (hcomm : Commute A T) (hA : ‖A‖≤1) :
    ‖B.adjoint*A*T*B‖≤‖B.adjoint*P*B‖ := by
  have he : B.adjoint*A*T*B=(T*B).adjoint*A*(T*B) := by
    change _=star (T*B)*A*(T*B)
    rw [star_mul,hT.isSelfAdjoint.star_eq]
    change _=B.adjoint*T*A*(T*B)
    rw [mul_assoc B.adjoint T A,←hcomm.eq]
    simp only [mul_assoc]
    rw [←mul_assoc T T B,hT.isIdempotentElem.eq]
  have hTB : ‖T*B‖≤‖P*B‖ := by
    have he : T*B=T*(P*B) := by rw [←mul_assoc,hTP]
    rw [he]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (hT.norm_le _) (norm_nonneg _)).trans_eq (one_mul _))
  rw [he,projection_sandwich_norm P B hP]
  calc
    _ ≤ ‖(T*B).adjoint‖*‖A‖*‖T*B‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖T*B‖^2 := by rw [ContinuousLinearMap.adjoint.norm_map]; nlinarith [norm_nonneg (T*B)]
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) hTB 2

omit [CompleteSpace V] [Fintype ι] in
lemma resolution_commute (P : ι → V →L[ℂ] V)
    (horth : ∀ i j, i≠j → P i*P j=0) (i j : ι) : Commute (P i) (P j) := by
  by_cases hij : i=j
  · subst j; exact Commute.refl _
  · exact (horth i j hij).trans (horth j i (Ne.symm hij)).symm

omit [Fintype ι] in
lemma resolution_sum_mul (P : ι → V →L[ℂ] V) (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i≠j → P i*P j=0) (S : Finset ι) (j : ι) :
    (∑ i∈S,P i)*P j=if j∈S then P j else 0 := by
  rw [Finset.sum_mul]
  have he (i : ι) : P i*P j=if i=j then P j else 0 := by
    split_ifs with h
    · subst i; exact (hP j).isIdempotentElem.eq
    · exact horth i j h
  simp only [he,Finset.sum_ite_eq']

lemma resolution_truncated_norm (P : ι → V →L[ℂ] V)
    (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i≠j → P i*P j=0) (hsum : ∑ i,P i=1)
    (A : V →L[ℂ] V) (hcomm : ∀ i, Commute A (P i))
    (S : Finset ι) (c : ℝ) (hc : 0≤c) (hbound : ∀ i∈S, ‖A*P i‖≤c) :
    ‖A*(∑ i∈S,P i)‖≤c := by
  apply resolution_norm_bound P hP horth hsum _ _ c hc
  · intro i
    rw [mul_assoc,resolution_sum_mul P hP horth]
    split_ifs with hi
    · exact hbound i hi
    · simp [hc]
  · intro i
    exact (hcomm i).mul_left (Commute.sum_left S P (P i) fun j _ => resolution_commute P horth j i)

theorem resolution_exception_bound (T Q : ι → V →L[ℂ] V)
    (hT : ∀ i, IsStarProjection (T i))
    (horth : ∀ i j, i≠j → T i*T j=0) (hsum : ∑ i,T i=1)
    (hQ : ∀ i, IsStarProjection (Q i)) (hTQ : ∀ i,T i*Q i=T i)
    (A B : V →L[ℂ] V) (hcomm : ∀ i, Commute A (T i))
    (hA : ‖A‖≤1) (hB : ‖B‖≤1)
    (S : Finset ι) (c : ℝ) (hc : 0≤c) (hbound : ∀ i∉S, ‖A*T i‖≤c) :
    ‖B.adjoint*A*B‖≤c+∑ i∈S,‖B.adjoint*Q i*B‖ := by
  have hhigh : ‖A*(∑ i∈Sᶜ,T i)‖≤c := resolution_truncated_norm T hT horth hsum A hcomm
    Sᶜ c hc (fun i hi => hbound i (Finset.mem_compl.mp hi))
  have hsplit : (∑ i∈Sᶜ,T i)+(∑ i∈S,T i)=1 := by
    rw [Finset.sum_compl_add_sum,hsum]
  have he : B.adjoint*A*B=B.adjoint*(A*(∑ i∈Sᶜ,T i))*B+
      ∑ i∈S,B.adjoint*A*T i*B := by
    rw [←Finset.sum_mul,←Finset.mul_sum]
    rw [←add_mul]
    simp only [mul_assoc]
    rw [←mul_add,←mul_add,hsplit]
    simp only [mul_one,mul_assoc]
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ‖B.adjoint‖*‖A*(∑ i∈Sᶜ,T i)‖*‖B‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*c*1 := mul_le_mul (mul_le_mul (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hB)
        hhigh (norm_nonneg _) zero_le_one) hB (norm_nonneg _) (by simpa using hc)
      _ = c := by ring
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun i _ => sector_sandwich_le _ _ _ _ (hT i) (hQ i) (hTQ i) (hcomm i) hA

variable [DecidableEq ι]
variable (P : ι → V →L[ℂ] V) (hcomm : ∀ i j, Commute (P i) (P j))

noncomputable def choice (E : Finset ι) (i : ι) : V →L[ℂ] V :=
  if i∈E then 1-P i else P i

include hcomm
omit [CompleteSpace V] [Fintype ι] in
lemma choice_commute (E F : Finset ι) (i j : ι) :
    Commute (choice P E i) (choice P F j) := by
  unfold choice
  split_ifs
  · exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (hcomm i j))
  · exact (Commute.one_left _).sub_left (hcomm i j)
  · exact (Commute.one_right _).sub_right (hcomm i j)
  · exact hcomm i j

noncomputable def sector (s E : Finset ι) : V →L[ℂ] V :=
  s.noncommProd (choice P E) (fun i _ j _ _ => choice_commute P hcomm E E i j)

omit [CompleteSpace V] [Fintype ι] in
lemma sector_insert (s E : Finset ι) (a : ι) (ha : a∉s) :
    sector P hcomm (insert a s) E=choice P E a*sector P hcomm s E := by
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ ha

end Thorp.CommutingBlocks

end ThorpNine.Harmonic

end OAI
