import Mathlib
import OAI.NumberTheory.PrimePackets.PacketMoments

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
namespace PrimeDegreePackets

lemma integer_squares_sum_one {I : Type*} [Fintype I] (c : I → ℤ)
    (hc : ∑ i, (c i)^2 = 1) :
    ∃ i, (c i = 1 ∨ c i = -1) ∧ ∀ j, j ≠ i → c j = 0 := by
  classical
  have hb (i : I) : (c i)^2 ≤ 1 := by
    rw [← hc]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (c j)) (Finset.mem_univ i)
  obtain ⟨i,hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hc
  have hci : c i = 1 ∨ c i = -1 := by
    have := hb i
    have hp : c i ≤ 1 := by nlinarith
    have hn : -1 ≤ c i := by nlinarith
    omega
  have hsq : (c i)^2 = 1 := by rcases hci with h|h <;> rw [h] <;> norm_num
  have he : ∑ j ∈ Finset.univ.erase i, (c j)^2 = 0 := by
    have h := Finset.sum_erase_add Finset.univ (fun j => (c j)^2) (Finset.mem_univ i)
    rw [hc,hsq] at h
    linarith
  refine ⟨i,hci,fun j hj => ?_⟩
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp he
    j (by simp [hj])
  exact sq_eq_zero_iff.mp hz

 

def characterPair {G : Type*} [Group G] [Fintype G] (f h : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g, f g * h g⁻¹

lemma characterPair_sum_left {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (f : I → G → ℂ) (h : G → ℂ) :
    characterPair (fun g => ∑ i, f i g) h = ∑ i, characterPair (f i) h := by
  classical
  simp only [characterPair,Finset.sum_mul]
  rw [Finset.sum_comm,Finset.mul_sum]

lemma characterPair_sum_right {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (f : G → ℂ) (h : I → G → ℂ) :
    characterPair f (fun g => ∑ i, h i g) = ∑ i, characterPair f (h i) := by
  classical
  simp only [characterPair,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma characterPair_mul_left {G : Type*} [Group G] [Fintype G]
    (a : ℂ) (f h : G → ℂ) :
    characterPair (fun g => a * f g) h = a * characterPair f h := by
  unfold characterPair
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

lemma characterPair_mul_right {G : Type*} [Group G] [Fintype G]
    (a : ℂ) (f h : G → ℂ) :
    characterPair f (fun g => a * h g) = a * characterPair f h := by
  unfold characterPair
  simp_rw [mul_left_comm (f _) a]
  rw [← Finset.mul_sum]
  ring

 

lemma characterPair_virtual {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (V : I → FDRep ℂ G) [∀ i, Simple (V i)]
    (hV : ∀ i j, i ≠ j → ¬ Nonempty (V i ≅ V j)) (c : I → ℤ) :
    characterPair (fun g => ∑ i, (c i : ℂ) * (V i).character g)
      (fun g => ∑ i, (c i : ℂ) * (V i).character g) = ∑ i, (c i : ℂ)^2 := by
  classical
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card G).ne')
  have ho (i j : I) : characterPair (V i).character (V j).character =
      if i = j then 1 else 0 := by
    unfold characterPair
    rw [FDRep.char_orthonormal]
    by_cases h : i = j
    · subst j; simp
    · simp [h,hV i j h]
  rw [characterPair_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [characterPair_sum_right]
  simp_rw [characterPair_mul_left,characterPair_mul_right,ho]
  simp [sq]

 

theorem heilbronn_degree_one_character {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (V : I → FDRep ℂ G) [∀ i, Simple (V i)]
    (hV : ∀ i j, i ≠ j → ¬ Nonempty (V i ≅ V j)) (c : I → ℤ)
    (hdeg : ∑ i, (c i : ℂ) * (V i).character 1 = 1)
    (hcyclic : ∀ g : G,
      (∑ i, (c i : ℂ) * (V i).character g) *
        (∑ i, (c i : ℂ) * (V i).character g⁻¹) = 1) :
    ∃ i, c i = 1 ∧ finrank ℂ (V i) = 1 ∧
      (∀ j, j ≠ i → c j = 0) ∧
      ∀ g, (∑ j, (c j : ℂ) * (V j).character g) = (V i).character g := by
  classical
  have hn : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card G).ne'
  have hs : ∑ i, (c i : ℂ)^2 = 1 := by
    rw [← characterPair_virtual V hV c]
    simp only [characterPair,hcyclic,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    rw [Fintype.card_eq_nat_card,inv_mul_cancel₀ hn]
  have hs' : ∑ i, (c i)^2 = 1 := by exact_mod_cast hs
  obtain ⟨i,hi,hzero⟩ := integer_squares_sum_one c hs'
  have heq (g : G) : (∑ j, (c j : ℂ) * (V j).character g) =
      (c i : ℂ) * (V i).character g := by
    apply Finset.sum_eq_single i
    · intro j _ hji; simp [hzero j hji]
    · simp
  rw [heq,FDRep.char_one] at hdeg
  have hdn : (c i) * (finrank ℂ (V i) : ℤ) = 1 := by exact_mod_cast hdeg
  have hci : c i = 1 := by
    rcases hi with hi|hi
    · exact hi
    · have : (0 : ℤ) ≤ finrank ℂ (V i) := Int.natCast_nonneg _
      rw [hi] at hdn
      linarith
  have hd : finrank ℂ (V i) = 1 := by
    rw [hci,one_mul] at hdn
    exact_mod_cast hdn
  refine ⟨i,hci,hd,hzero,fun g => ?_⟩
  rw [heq,hci]
  simp

 

lemma eq_trace_smul_id_of_finrank_one {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (hd : finrank ℂ W = 1) (T : W →ₗ[ℂ] W) :
    T = LinearMap.trace ℂ W T • LinearMap.id := by
  obtain ⟨a,ha,_⟩ := T.existsUnique_eq_smul_id_of_finrank_eq_one hd
  rw [ha]
  simp [LinearMap.trace_id,hd]

def degreeOneCharacterHom {G : Type*} [Group G] (V : FDRep ℂ G)
    (hd : finrank ℂ V = 1) : G →* ℂ where
  toFun := V.character
  map_one' := by simp [hd]
  map_mul' g h := by
    change LinearMap.trace ℂ V (V.ρ (g*h)) =
      LinearMap.trace ℂ V (V.ρ g) * LinearMap.trace ℂ V (V.ρ h)
    rw [map_mul,eq_trace_smul_id_of_finrank_one hd (V.ρ g),
      eq_trace_smul_id_of_finrank_one hd (V.ρ h)]
    have hid : (LinearMap.id : V →ₗ[ℂ] V) * LinearMap.id = LinearMap.id := by
      ext v; rfl
    simp [hid,LinearMap.trace_id,hd,mul_comm]

def realDegreeOneCharacter {G : Type*} [Group G] (V : FDRep ℂ G)
    (hd : finrank ℂ V = 1) (hreal : ∀ g, (V.character g).im = 0) : G →* ℝ where
  toFun g := (V.character g).re
  map_one' := by simp [hd]
  map_mul' g h := by
    have hm := (degreeOneCharacterHom V hd).map_mul g h
    change V.character (g*h) = V.character g * V.character h at hm
    rw [hm,Complex.mul_re,hreal g,hreal h]
    ring

lemma degreeOneCharacter_eq_one_of_fixed_vector {G : Type*} [Group G]
    (V : FDRep ℂ G) (hd : finrank ℂ V = 1) {g : G} {v : V}
    (hv : v ≠ 0) (hfix : V.ρ g v = v) : V.character g = 1 := by
  have he := congrArg (fun T : V →ₗ[ℂ] V => T v)
    (eq_trace_smul_id_of_finrank_one hd (V.ρ g))
  change V.ρ g v = V.character g • v at he
  have hz : (V.character g - 1) • v = 0 := by
    rw [sub_smul,one_smul,← he,hfix,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv)

lemma realFiniteCharacter_values {G : Type*} [Group G] [Finite G]
    (χ : G →* ℝˣ) (g : G) : χ g = 1 ∨ χ g = -1 := by
  have hn := (((Units.coeHom ℝ).comp χ).isOfFinOrder
    (isOfFinOrder_of_finite g)).norm_eq_one
  change ‖(χ g : ℝ)‖ = 1 at hn
  rw [Real.norm_eq_abs] at hn
  rcases (abs_eq (show (0:ℝ) ≤ 1 by norm_num)).mp hn with h|h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

 

lemma realFiniteCharacter_kernel_index {G : Type*} [Group G] [Finite G]
    (χ : G →* ℝˣ) {g : G} (hg : χ g ≠ 1) : χ.ker.index = 2 := by
  have hgm : χ g = -1 := (realFiniteCharacter_values χ g).resolve_left hg
  rw [Subgroup.index_ker]
  apply Nat.card_eq_two_iff.mpr
  let a : χ.range := ⟨1,⟨1,χ.map_one⟩⟩
  let b : χ.range := ⟨-1,⟨g,hgm⟩⟩
  refine ⟨a,b,?_,?_⟩
  · intro h
    have h' := congrArg (fun z : χ.range => ((z : ℝˣ) : ℝ)) h
    change (1:ℝ) = -1 at h'
    norm_num at h'
  · ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_univ,iff_true]
    obtain ⟨t,ht⟩ := x.property
    rcases realFiniteCharacter_values χ t with h|h
    · left; apply Subtype.ext; exact ht.symm.trans h
    · right; apply Subtype.ext; exact ht.symm.trans h

lemma realFiniteCharacter_trivial_of_odd_index {G : Type*} [Group G] [Finite G]
    (χ : G →* ℝˣ) (H : Subgroup G) (hodd : Odd H.index) (hH : H ≤ χ.ker) :
    ∀ g, χ g = 1 := by
  intro g
  by_contra hg
  have hdiv := Subgroup.index_dvd_of_le hH
  rw [realFiniteCharacter_kernel_index χ hg] at hdiv
  obtain ⟨k,hk⟩ := hodd
  obtain ⟨l,hl⟩ := hdiv
  omega

 

theorem realGaloisCharacter_trivial_of_odd_degree {F K N : Type*}
    [Field F] [Field K] [Field N] [Algebra F K] [Algebra F N]
    [FiniteDimensional F K] [FiniteDimensional F N] [IsGalois F N]
    (f : K →ₐ[F] N) (hodd : Odd (finrank F K)) (χ : (N ≃ₐ[F] N) →* ℝˣ)
    (hfix : ∀ g ∈ f.fieldRange.fixingSubgroup, χ g = 1) : ∀ g, χ g = 1 := by
  apply realFiniteCharacter_trivial_of_odd_index χ f.fieldRange.fixingSubgroup
  · rw [← IntermediateField.finrank_eq_fixingSubgroup_index,
      ← f.equivFieldRange.toLinearEquiv.finrank_eq]
    exact hodd
  · intro g hg
    exact hfix g hg

 

theorem heilbronn_principal_of_odd_index {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (V : I → FDRep ℂ G) [∀ i, Simple (V i)]
    (hV : ∀ i j, i ≠ j → ¬ Nonempty (V i ≅ V j)) (c : I → ℤ)
    (H : Subgroup G) (hodd : Odd H.index)
    (hdeg : ∑ i, (c i : ℂ) * (V i).character 1 = 1)
    (hcyclic : ∀ g : G,
      (∑ i, (c i : ℂ) * (V i).character g) *
        (∑ i, (c i : ℂ) * (V i).character g⁻¹) = 1)
    (hreal : ∀ g, (∑ i, (c i : ℂ) * (V i).character g).im = 0)
    (hsub : ∑ i, c i * (finrank ℂ (Representation.invariants
      ((V i).ρ.comp H.subtype)) : ℤ) = 1) :
    ∀ g, (∑ i, (c i : ℂ) * (V i).character g) = 1 := by
  classical
  obtain ⟨i,hci,hdi,hzero,heq⟩ := heilbronn_degree_one_character V hV c hdeg hcyclic
  have hir : ∀ g, ((V i).character g).im = 0 := by
    intro g; rw [← heq g]; exact hreal g
  have hiW : finrank ℂ (Representation.invariants ((V i).ρ.comp H.subtype)) = 1 := by
    have hs : (∑ j, c j * (finrank ℂ (Representation.invariants
        ((V j).ρ.comp H.subtype)) : ℤ)) =
        (finrank ℂ (Representation.invariants ((V i).ρ.comp H.subtype)) : ℤ) := by
      rw [Finset.sum_eq_single i]
      · rw [hci,one_mul]
      · intro j _ hji; rw [hzero j hji,zero_mul]
      · simp
    rw [hs] at hsub
    exact_mod_cast hsub
  obtain ⟨v,hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)
    (M := Representation.invariants ((V i).ρ.comp H.subtype))).mp
      (show 0 < finrank ℂ (Representation.invariants ((V i).ρ.comp H.subtype)) by
        rw [hiW]; exact Nat.zero_lt_one)
  let χ := (realDegreeOneCharacter (V i) hdi hir).toHomUnits
  have hH : H ≤ χ.ker := by
    intro g hg
    apply Units.ext
    change ((V i).character g).re = 1
    have hi : (V i).character g = 1 :=
      degreeOneCharacter_eq_one_of_fixed_vector (V i) hdi (g := g)
        (show (v : V i) ≠ 0 from fun he => hv (Subtype.ext he))
        (show (V i).ρ g v = v from v.property ⟨g,hg⟩)
    rw [hi]
    rfl
  have hprincipal := realFiniteCharacter_trivial_of_odd_index χ H hodd hH
  intro g
  rw [heq g]
  apply Complex.ext
  · have ht := congrArg (fun z : ℝˣ => (z : ℝ)) (hprincipal g)
    exact ht
  · exact hir g

 

lemma cyclic_degree_one_identity {G I : Type*} [Group G] [Fintype I]
    (V : I → FDRep ℂ G) (c : I → ℤ)
    (hcyclic : ∀ g : G, ∃ W : FDRep ℂ (Subgroup.zpowers g),
      finrank ℂ W = 1 ∧ ∀ t : Subgroup.zpowers g,
        (∑ i, (c i : ℂ) * (V i).character t) = W.character t) :
    ∀ g : G, (∑ i, (c i : ℂ) * (V i).character g) *
      (∑ i, (c i : ℂ) * (V i).character g⁻¹) = 1 := by
  intro g
  obtain ⟨W,hd,hW⟩ := hcyclic g
  let t : Subgroup.zpowers g := ⟨g,Subgroup.mem_zpowers g⟩
  rw [show (∑ i, (c i : ℂ) * (V i).character g) = W.character t from hW t,
    show (∑ i, (c i : ℂ) * (V i).character g⁻¹) = W.character t⁻¹ from hW t⁻¹]
  change (degreeOneCharacterHom W hd) t * (degreeOneCharacterHom W hd) t⁻¹ = 1
  rw [← map_mul,mul_inv_cancel,map_one]

 

theorem nonprincipal_realGaloisCharacter_quadratic_subfield {F K N : Type*}
    [Field F] [Field K] [Field N] [Algebra F K] [Algebra F N]
    [FiniteDimensional F N] [IsGalois F N]
    (f : K →ₐ[F] N) (χ : (N ≃ₐ[F] N) →* ℝˣ)
    (hfix : ∀ g ∈ f.fieldRange.fixingSubgroup, χ g = 1)
    {g : N ≃ₐ[F] N} (hg : χ g ≠ 1) :
    ∃ E : IntermediateField F K, finrank F E = 2 := by
  let D := IntermediateField.fixedField χ.ker
  have hdim : finrank F D = 2 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField,
      realFiniteCharacter_kernel_index χ hg]
  have hD : D ≤ f.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup f.fieldRange]
    apply IntermediateField.fixedField_le
    intro σ hσ
    exact hfix σ hσ
  have he : (D.comap f).map f = D := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      obtain ⟨y,rfl⟩ := hD hx
      exact ⟨y,hx,rfl⟩
  refine ⟨D.comap f,?_⟩
  have h := ((D.comap f).equivMap f).toLinearEquiv.finrank_eq
  rw [he] at h
  exact h.trans hdim

end PrimeDegreePackets

open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem linear_covolume_vector_outside_subspace {n : ℕ} (hdim : finrank ℝ E = n+1)
    (V : ℝ) (hV : 0 ≤ V) :
    ∀ b : Basis (Fin (n+1)) ℝ E,
      volume (ZSpan.fundamentalDomain b) ≤ ENNReal.ofReal V →
      (∀ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 → 1 ≤ ‖v‖) →
      ∀ W : Submodule ℝ E, W ≠ ⊤ →
        ∃ v ∈ Submodule.span ℤ (Set.range b), v ∉ W ∧ ‖v‖ ≤ (2 / (1 / (2*(n+1)))^n + n / (2*(n+1))) * (V+1) := by
  let s : ℝ := 1 / (2*(n+1))
  have hs : 0 < s := by positivity
  let R : ℝ := 2*(V+1)/s^n
  have hR : 0 < R := by positivity
  intro b hb hshort W hW
  obtain ⟨u,hu⟩ := exists_orthonormal_first_perp hdim W hW
  let a : Fin (n+1) → ℝ := Fin.cons R (fun _ => s)
  have hvol : (volume (ZSpan.fundamentalDomain b))*2^(finrank ℝ E) <
      volume (orthoBox u a) := by
    apply lt_of_le_of_lt (mul_le_mul' hb (le_refl _))
    rw [hdim,orthoBox_volume,Fin.prod_univ_succ]
    simp only [a,Fin.cons_zero,Fin.cons_succ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*s),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*R)]
    have H : (2*R)*(2*s)^n = (2:ℝ)^(n+1)*(2*(V+1)) := by
      dsimp [R]
      rw [mul_pow,pow_succ]
      field_simp
    rw [H,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [mul_comm (ENNReal.ofReal V)]
    apply ENNReal.mul_lt_mul_right (by positivity : (2:ℝ≥0∞)^(n+1) ≠ 0) (by finiteness)
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  let L := Submodule.span ℤ (Set.range b)
  have : Countable L := inferInstance
  obtain ⟨v,hv0,hv⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := L.toAddSubgroup)
    (ZSpan.isAddFundamentalDomain b volume) (fun x hx => orthoBox_symmetric u a hx)
    (orthoBox_convex u a) hvol
  have hvE : (v : E) ≠ 0 := by exact_mod_cast hv0
  refine ⟨v,v.property,?_,?_⟩
  · intro hvW
    have H := orthoBox_norm_le_of_zero_first u a hv (hu _ hvW)
    simp only [a,Fin.cons_succ,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul] at H
    have hsε : s ≤ 1/(2*(n+1)) := le_rfl
    have Hs : (n:ℝ)*s < 1 := by
      have Hn : (n:ℝ)*s ≤ ((n:ℝ)+1)*s := by nlinarith
      have Hs : ((n:ℝ)+1)*s ≤ 1/2 := by
        have := (le_div_iff₀ (by positivity : 0 < 2*((n:ℝ)+1))).mp hsε
        nlinarith
      linarith
    exact (hshort v v.property hvE).not_gt (lt_of_le_of_lt H Hs)
  · have H := orthoBox_norm_le u a hv
    have H' : ‖(v : E)‖ ≤ R + n*s := by simpa [a,Fin.sum_univ_succ] using H
    apply H'.trans
    dsimp [R,s]
    have hns : (0:ℝ) ≤ n / (2*(n+1)) := by positivity
    have hh := mul_nonneg hns hV
    calc
      _ = (2/(1/(2*(n+1)))^n)*(V+1) + n/(2*(n+1)) := by ring
      _ ≤ (2/(1/(2*(n+1)))^n)*(V+1) + n/(2*(n+1))*(V+1) := by nlinarith
      _ = _ := by ring

theorem linear_covolume_real_basis_in_lattice {n : ℕ} (hdim : finrank ℝ E = n+1)
    (V : ℝ) (hV : 0 ≤ V) :
    ∀ b : Basis (Fin (n+1)) ℝ E,
      volume (ZSpan.fundamentalDomain b) ≤ ENNReal.ofReal V →
      (∀ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 → 1 ≤ ‖v‖) →
      ∃ c : Basis (Fin (n+1)) ℝ E,
        ∀ i, c i ∈ Submodule.span ℤ (Set.range b) ∧ ‖c i‖ ≤ (2 / (1 / (2*(n+1)))^n + n / (2*(n+1))) * (V+1) := by
  let B : ℝ := (2 / (1 / (2*(n+1)))^n + n / (2*(n+1))) * (V+1)
  have H := linear_covolume_vector_outside_subspace hdim V hV
  intro b hb hshort
  let S : Set E := {x | x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ B}
  have hsp : Submodule.span ℝ S = ⊤ := by
    by_contra hne
    obtain ⟨v,hv,hvW,hvB⟩ := H b hb hshort (Submodule.span ℝ S) hne
    exact hvW (Submodule.subset_span (show v ∈ S from ⟨hv,hvB⟩))
  obtain ⟨T,hTS,hTspan,hTind⟩ := exists_linearIndependent ℝ S
  have hTtop : Submodule.span ℝ T = ⊤ := hTspan.trans hsp
  let c₀ : Basis T ℝ E := Basis.mk hTind (by
    rw [Subtype.range_coe_subtype]
    change ⊤ ≤ Submodule.span ℝ T
    rw [hTtop])
  have : Finite T := hTind.finite
  let : Fintype T := Fintype.ofFinite T
  have hcard : Fintype.card T = n+1 := (finrank_eq_card_basis c₀).symm.trans hdim
  let e : T ≃ Fin (n+1) := Fintype.equivFinOfCardEq hcard
  refine ⟨c₀.reindex e,?_⟩
  intro i
  have H := hTS (e.symm i).property
  simpa [c₀,Basis.coe_reindex,S,B] using H

end PrimeDegreePackets
end
end

end OAI
