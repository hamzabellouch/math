import Mathlib
import OAI.Analysis.BoundedHochschild.Corners
import OAI.Analysis.BoundedHochschild.RankOneQuantization

namespace OAI

/-! Relative small corners, root phases and weak powers of unitaries. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildQuantization
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems HochschildCorners
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma corner_norm_sq (a : Corner p hp) :
    ‖(cornerTrace p hp τ).toPreGNS a‖^2=(τ p).re⁻¹*‖τ.toPreGNS (a:M)‖^2 := by
  rw [MatrixSystem.norm_sq,cornerTrace_apply,corner_coe_mul,corner_coe_star,MatrixSystem.norm_sq]
  simp only [← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

lemma corner_trace_re (a : Corner p hp) :
    (cornerTrace p hp τ a).re=(τ p).re⁻¹*(τ (a:M)).re := by
  rw [cornerTrace_apply]
  simp only [← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

variable {I : Type v} [Fintype I]
include e hp in
 

theorem exists_relative_small_corner
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M) (hp0 : p ≠ 0)
    (x : I → M) {δ η : ℝ} (hδ : 0<δ) (hη : 0<η) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ (τ q).re<η ∧
      ∀ i, ‖τ.toPreGNS (q*x i*q - (((τ p).re : ℂ)⁻¹*τ (p*x i*p)) • q)‖^2<δ*(τ q).re := by
  let eC := cornerPredualEquiv p hp e
  let ρ := cornerTrace p hp τ
  let y : I → Corner p hp := fun i => ⟨p*x i*p,compress_mem_corner hp (x i)⟩
  let z : I → Corner p hp := fun i => y i-(ρ (y i)) • (1 : Corner p hp)
  have ht : 0<(τ p).re := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  have hρ1 : ρ 1=1 := cornerTrace_one p hp τ hfaith hp0
  have hz : ∀ i, ρ (z i)=0 := by
    intro i
    simp only [z,map_sub,map_smul,hρ1,smul_eq_mul,mul_one,sub_self]
  obtain ⟨q,hq,hq0,hqt,hqz⟩ := exists_small_corner_of_trace_limit eC ρ
    (cornerTrace_normal p hp e τ hτ) hρ1 (cornerTrace_tracial p hp τ htr)
    (cornerTrace_faithful p hp τ hfaith hp0)
    (corner_factor p hp e τ hτ h1 htr hfaith hfactor hdiff hp0)
    (corner_no_minimal p hp hdiff) z hz hδ (div_pos hη ht)
  have hqM := corner_projection_coe p hp hq
  have hqp := corner_projection_le p hp hq
  refine ⟨q,hqM,hqp,(fun he => hq0 (Subtype.ext he)),?_,?_⟩
  · change (cornerTrace p hp τ q).re<η/(τ p).re at hqt
    rw [corner_trace_re] at hqt
    have hh := mul_lt_mul_of_pos_left hqt ht
    simpa only [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul,mul_div_cancel₀ _ ht.ne'] using hh
  · intro i
    have he : ((q*z i*q : Corner p hp):M)=
        (q:M)*x i*(q:M)-(((τ p).re : ℂ)⁻¹*τ (p*x i*p)) • (q:M) := by
      change (q:M)*(p*x i*p - (((τ p).re : ℂ)⁻¹*τ (p*x i*p)) • p)*(q:M)=_
      rw [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,q.property.2,hqM.isIdempotentElem.eq]
      congr 1
      rw [← mul_assoc,← mul_assoc,q.property.2,mul_assoc,q.property.1]
    have hh := hqz i
    change ‖(cornerTrace p hp τ).toPreGNS (q*z i*q)‖^2<δ*(cornerTrace p hp τ q).re at hh
    rw [corner_norm_sq,corner_trace_re,he] at hh
    have hh' := mul_lt_mul_of_pos_left hh ht
    have he1 : (τ p).re*((τ p).re⁻¹*‖τ.toPreGNS ((q:M)*x i*(q:M)-
        (((τ p).re : ℂ)⁻¹*τ (p*x i*p)) • (q:M))‖^2)=
        ‖τ.toPreGNS ((q:M)*x i*(q:M)-(((τ p).re : ℂ)⁻¹*τ (p*x i*p)) • (q:M))‖^2 := by
      rw [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
    rw [he1] at hh'
    have hrhs : (τ p).re*(δ*((τ p).re⁻¹*(τ (q:M)).re))=δ*(τ (q:M)).re := by
      field_simp [ht.ne']
    rw [hrhs] at hh'
    exact hh'

end HochschildQuantization

 

 

 

open scoped BigOperators ComplexConjugate InnerProductSpace
namespace HochschildRootPhase
variable {I : Type*} [Fintype I]
variable {m : ℕ} [NeZero m]

def character (v : I → ZMod m) : AddChar (I → ZMod m) ℂ where
  toFun g := ZMod.stdAddChar (∑ i,v i*g i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' g h := by
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,AddChar.map_add_eq_mul]

lemma character_apply (v g : I → ZMod m) :
    character v g=ZMod.stdAddChar (∑ i,v i*g i) := rfl

lemma character_zero (g : I → ZMod m) : character 0 g=1 := by simp [character_apply]
lemma character_add (v w g : I → ZMod m) :
    character (v+w) g=character v g*character w g := by
  simp only [character_apply,Pi.add_apply,add_mul,Finset.sum_add_distrib,AddChar.map_add_eq_mul]
lemma character_norm (v g : I → ZMod m) : ‖character v g‖=1 := by
  simp only [character_apply,ZMod.stdAddChar_apply,Circle.norm_coe]
lemma character_star (v g : I → ZMod m) : star (character v g)=character (-v) g := by
  simp only [character_apply,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib,
    AddChar.map_neg_eq_inv,ZMod.stdAddChar_apply]
  exact (Circle.coe_inv_eq_conj _).symm

lemma character_eq_one_iff (v : I → ZMod m) : character v=1 ↔ v=0 := by
  classical
  constructor
  · intro h
    ext i
    have hh := congrArg (fun χ : AddChar (I → ZMod m) ℂ => χ (Pi.single i 1)) h
    simp only [character_apply,AddChar.one_apply] at hh
    have hsum : (∑ j,v j*((Pi.single i (1:ZMod m) : I → ZMod m) j))=v i := by
      simp [Pi.single_apply]
    rw [hsum,← (ZMod.stdAddChar : AddChar (ZMod m) ℂ).map_zero_eq_one] at hh
    exact ZMod.injective_stdAddChar hh
  · rintro rfl
    ext g
    exact character_zero g

variable [DecidableEq I]

lemma sum_character (v : I → ZMod m) :
    ∑ g,character v g=if v=0 then (Fintype.card (I → ZMod m):ℂ) else 0 := by
  classical
  by_cases hv : v=0
  · subst v
    simp only [character_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,ite_true]
  · rw [ite_eq_right hv]
    exact AddChar.sum_eq_zero_of_ne_one ((character_eq_one_iff v).not.mpr hv)

lemma orthogonality (v w : I → ZMod m) :
    ∑ g,star (character v g)*character w g=
      if v=w then (Fintype.card (I → ZMod m):ℂ) else 0 := by
  classical
  simp only [character_star,← character_add,sum_character]
  congr 1
  exact propext neg_add_eq_zero

lemma character_parseval {J H : Type*} [Fintype J] [SeminormedAddCommGroup H]
    [InnerProductSpace ℂ H] (f : J → (I → ZMod m)) (hf : Function.Injective f) (v : J → H) :
    (∑ g : I → ZMod m, ‖∑ j, character (f j) g • v j‖^2)=
      (Fintype.card (I → ZMod m):ℝ)*(∑ j,‖v j‖^2) := by
  classical
  have hh : (∑ g : I → ZMod m, ⟪∑ j, character (f j) g • v j,
      ∑ j,character (f j) g • v j⟫_ℂ)=
      (Fintype.card (I → ZMod m):ℂ)*(∑ j,⟪v j,v j⟫_ℂ) := by
    simp only [sum_inner,inner_sum]
    simp only [inner_smul_left,inner_smul_right]
    calc
      _ = ∑ j,∑ k,(∑ g,star (character (f k) g)*character (f j) g)*⟪v k,v j⟫_ℂ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro g hg
        simp only [Complex.star_def]
        ring
      _ = _ := by simp only [orthogonality,hf.eq_iff]; simp [← Finset.mul_sum]
  have hr := congrArg Complex.re hh
  simp only [Complex.re_sum,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    zero_mul,sub_zero] at hr
  simpa only [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex] using hr

end HochschildRootPhase

 

 

open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open HochschildRootPhase
variable {M : Type*} [CStarAlgebra M]
variable {n m : ℕ} [NeZero m] (E : MatrixSystem M n)

def diagonalRoot (k : ZMod m) (g : Fin n → ZMod m) : M :=
  ∑ i, character (Pi.single i k) g • E.entry i i

lemma diagonalRoot_zero (g : Fin n → ZMod m) : E.diagonalRoot 0 g=1 := by
  simp only [diagonalRoot,Pi.single_zero,character_zero,one_smul,E.sum_diagonal]

lemma diagonalRoot_mul (k l : ZMod m) (g : Fin n → ZMod m) :
    E.diagonalRoot k g*E.diagonalRoot l g=E.diagonalRoot (k+l) g := by
  classical
  simp only [diagonalRoot,Finset.sum_mul,Finset.mul_sum,smul_mul_smul_comm,E.entry_mul,smul_ite,smul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Pi.single_add,character_add]

lemma diagonalRoot_star (k : ZMod m) (g : Fin n → ZMod m) :
    star (E.diagonalRoot k g)=E.diagonalRoot (-k) g := by
  simp only [diagonalRoot,star_sum,star_smul,E.star_entry,character_star,Pi.single_neg]

lemma diagonalRoot_unitary (k : ZMod m) (g : Fin n → ZMod m) : E.diagonalRoot k g ∈ unitary M := by
  constructor
  · rw [diagonalRoot_star,diagonalRoot_mul,neg_add_cancel,diagonalRoot_zero]
  · rw [diagonalRoot_star,diagonalRoot_mul,add_neg_cancel,diagonalRoot_zero]

def rootUnitary (g : Fin n → ZMod m) : unitary M := ⟨E.diagonalRoot 1 g,E.diagonalRoot_unitary 1 g⟩

def integerRootHom (g : Fin n → ZMod m) : Multiplicative ℤ →* unitary M where
  toFun k := ⟨E.diagonalRoot (k.toAdd : ZMod m) g,E.diagonalRoot_unitary _ g⟩
  map_one' := Subtype.ext (by change E.diagonalRoot ((0 : ℤ) : ZMod m) g=1; rw [Int.cast_zero,E.diagonalRoot_zero])
  map_mul' k l := Subtype.ext (by
    dsimp
    rw [Int.cast_add,E.diagonalRoot_mul])

lemma rootUnitary_zpow (g : Fin n → ZMod m) (k : ℤ) :
    ((E.rootUnitary g)^k : unitary M).val=E.diagonalRoot (k : ZMod m) g := by
  have h := (E.integerRootHom g).map_zpow (Multiplicative.ofAdd (1:ℤ)) k
  have hpow : (Multiplicative.ofAdd (1:ℤ))^k=Multiplicative.ofAdd k := by
    apply Multiplicative.toAdd.injective
    simp
  rw [hpow] at h
  have hone : (E.integerRootHom g) (Multiplicative.ofAdd (1:ℤ))=E.rootUnitary g :=
    Subtype.ext (by change E.diagonalRoot ((1:ℤ) : ZMod m) g=E.diagonalRoot 1 g; rw [Int.cast_one])
  rw [hone] at h
  exact congrArg (fun a : unitary M => (a:M)) h.symm

omit [NeZero m] in
lemma single_frequency_injective (k : ZMod m) (hk : k ≠ 0) :
    Function.Injective (fun i : Fin n => Pi.single i k) := by
  intro i j hij
  by_contra h
  have hh := congrFun hij i
  simp only [Pi.single_eq_same,Pi.single_eq_of_ne h] at hh
  exact hk hh

variable [PartialOrder M]

lemma trace_root_parseval (τ : M →ₚ[ℂ] ℂ) (a : M) (k : ZMod m) (hk : k ≠ 0) :
    (∑ g : Fin n → ZMod m, ‖τ (a*E.diagonalRoot k g)‖^2)=
      (Fintype.card (Fin n → ZMod m):ℝ)*(∑ i,‖τ (a*E.entry i i)‖^2) := by
  have hh := character_parseval (fun i : Fin n => Pi.single i k)
    (single_frequency_injective k hk) (fun i => τ (a*E.entry i i))
  simpa only [diagonalRoot,Finset.mul_sum,mul_smul_comm,map_sum,map_smul,smul_eq_mul] using hh

end MatrixSystem
end HochschildMatrixSystems

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n m : ℕ} [NeZero m] (E : MatrixSystem M n)

lemma trace_root_energy_bound (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    (a : M) (k : ZMod m) (hk : k ≠ 0) :
    (∑ g : Fin n → ZMod m, ‖τ (a*E.diagonalRoot k g)‖^2) ≤
      (Fintype.card (Fin n → ZMod m):ℝ)*(‖a‖^2/(n:ℝ)) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hdiag (i : Fin n) : (τ (E.entry i i)).re=(n:ℝ)⁻¹ := by
    have hh : τ (E.entry i i)=(n:ℂ)⁻¹ := by
      simpa [h1] using E.trace_entry_commutant τ htr hn 1 E.commutant.one_mem i i
    rw [hh,← Complex.ofReal_natCast,← Complex.ofReal_inv,Complex.ofReal_re]
  have hb (i : Fin n) : ‖τ (a*E.entry i i)‖ ≤ (n:ℝ)⁻¹*‖a‖ := by
    rw [htr]
    exact (HochschildTraceNorm.positive_weight_trace_bound τ htr (E.entry i i) a
      (E.diagonal_proj i).nonneg).trans_eq (by rw [hdiag])
  rw [E.trace_root_parseval τ a k hk]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ _i : Fin n,((n:ℝ)⁻¹*‖a‖)^2 := Finset.sum_le_sum (fun i hi =>
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (norm_nonneg _))).mpr (hb i))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

lemma exists_root_trace_energy {I : Type*} [Fintype I] (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0)
    (a : I → M) (k : I → ZMod m) (hk : ∀ i, k i ≠ 0) :
    ∃ g : Fin n → ZMod m,
      (∑ i,‖τ (a i*E.diagonalRoot (k i) g)‖^2) ≤ (∑ i,‖a i‖^2)/(n:ℝ) := by
  classical
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    E.trace_root_energy_bound τ h1 htr hn (a i) (k i) (hk i))
  rw [Finset.sum_comm,← Finset.mul_sum,← Finset.sum_div] at hh
  by_contra hg
  push Not at hg
  have hstrict : (Fintype.card (Fin n → ZMod m):ℝ)*((∑ i,‖a i‖^2)/(n:ℝ)) <
      ∑ g : Fin n → ZMod m, ∑ i,‖τ (a i*E.diagonalRoot (k i) g)‖^2 := by
    rw [← nsmul_eq_mul,← Finset.card_univ,← Finset.sum_const]
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun _ _ => hg _)
  exact (not_lt_of_ge hh) hstrict

end MatrixSystem

open BoundedHochschild HochschildRigidity HochschildSakai
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]

include e in
theorem exists_unitary_weak_powers
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (a : I → M) (k : I → ℤ) (hk : ∀ i, k i ≠ 0) {ε : ℝ} (hε : 0<ε) :
    ∃ u : unitary M, ∀ i, ‖τ (a i*(u^(k i) : unitary M) : M)‖<ε := by
  classical
  let m : ℕ := 1+ ∑ i,(k i).natAbs
  have hm : 0 < m := by dsimp [m]; omega
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hkm (i : I) : (k i : ZMod m) ≠ 0 := by
    intro hz
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (k i) m).mp hz
    have hh := Int.natAbs_le_of_dvd_ne_zero hd (hk i)
    simp only [Int.natAbs_natCast] at hh
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
      Nat.zero_le (k j).natAbs) (Finset.mem_univ i)
    dsimp [m] at hh
    omega
  let B : ℝ := ∑ i,‖a i‖^2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hε2 : 0<ε^2 := sq_pos_of_pos hε
  obtain ⟨n,hnR⟩ := exists_nat_gt (B/ε^2)
  have hn : 0<n := by exact_mod_cast (lt_of_le_of_lt (div_nonneg hB hε2.le) hnR)
  have hnRpos : (0:ℝ)<n := by exact_mod_cast hn
  obtain ⟨E⟩ := exists_matrixSystem e τ hτ htr hfaith h1 hfactor hdiff n hn
  obtain ⟨g,hg⟩ := E.exists_root_trace_energy τ h1 htr (Nat.ne_of_gt hn) a
    (fun i => (k i : ZMod m)) hkm
  refine ⟨E.rootUnitary g,fun i => ?_⟩
  have hsum : B/(n:ℝ)<ε^2 := by
    apply (div_lt_iff₀ hnRpos).mpr
    have hh := (div_lt_iff₀ hε2).mp hnR
    nlinarith
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
    sq_nonneg ‖τ (a j*E.diagonalRoot (k j : ZMod m) g)‖) (Finset.mem_univ i)
  have hh : ‖τ (a i*E.diagonalRoot (k i : ZMod m) g)‖^2<ε^2 := hi.trans_lt (hg.trans_lt hsum)
  change ‖τ (a i*((E.rootUnitary g)^(k i) : unitary M).val)‖<ε
  rw [E.rootUnitary_zpow]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hh

end HochschildMatrixSystems
end

end OAI
