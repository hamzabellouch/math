import Mathlib
import OAI.MathematicalPhysics.PEPSMove.LocalOperators
import OAI.MathematicalPhysics.PEPSMove.UnitaryCovariance

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace PolynomialPEPS.PhysicalMove.LocalMovePhysical
open Matrix QuantumSSA SupportedCurve SpectralCurve MatrixInterpolation
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
variable {L q : ℕ}

def unionJoin (A B : Finset (Vertex L)) (x : RegionConfiguration q A)
    (y : RegionConfiguration q B) : RegionConfiguration q (A∪B) :=
  fun v => if h : v.val∈A then x ⟨v,h⟩ else y ⟨v,by exact (Finset.mem_union.mp v.property).resolve_left h⟩

def unionEquiv (A B : Finset (Vertex L)) (h : Disjoint A B) :
    (RegionConfiguration q A × RegionConfiguration q B) ≃ RegionConfiguration q (A∪B) where
  toFun u := unionJoin A B u.1 u.2
  invFun z := (fun v => z ⟨v,Finset.mem_union_left B v.property⟩,
    fun v => z ⟨v,Finset.mem_union_right A v.property⟩)
  left_inv u := by
    apply Prod.ext
    · funext v; simp [unionJoin,v.property]
    · funext v
      have hv : v.val∉A := fun ha => Finset.disjoint_left.mp h ha v.property
      simp [unionJoin,hv]
  right_inv z := by
    funext v
    simp only [unionJoin]
    split_ifs <;> rfl

@[simp] theorem unionJoin_left (A B : Finset (Vertex L))
    (x : RegionConfiguration q A) (y : RegionConfiguration q B) (v : {v // v∈A}) :
    unionJoin A B x y ⟨v,Finset.mem_union_left B v.property⟩=x v := by
  simp [unionJoin,v.property]

@[simp] theorem unionJoin_right (A B : Finset (Vertex L)) (h : Disjoint A B)
    (x : RegionConfiguration q A) (y : RegionConfiguration q B) (v : {v // v∈B}) :
    unionJoin A B x y ⟨v,Finset.mem_union_right A v.property⟩=y v := by
  have hv : v.val∉A := fun ha => Finset.disjoint_left.mp h ha v.property
  simp [unionJoin,hv]

theorem liftBetween_union_right (A B : Finset (Vertex L)) (h : Disjoint A B)
    (b : Matrix (RegionConfiguration q B) (RegionConfiguration q B) ℂ) :
    reindexHom (unionEquiv A B h) (tensorRightHom b)=
      liftBetween (Finset.subset_union_right : B⊆A∪B) b := by
  classical
  ext i j
  obtain ⟨x,rfl⟩ := (unionEquiv (q:=q) A B h).surjective i
  obtain ⟨y,rfl⟩ := (unionEquiv (q:=q) A B h).surjective j
  have hx : restrictRegion (Finset.subset_union_right : B⊆A∪B)
      (unionJoin A B x.1 x.2)=x.2 := by
    funext v; exact unionJoin_right A B h _ _ v
  have hy : restrictRegion (Finset.subset_union_right : B⊆A∪B)
      (unionJoin A B y.1 y.2)=y.2 := by
    funext v; exact unionJoin_right A B h _ _ v
  have hc : (∀ v : {v // v∈A∪B}, v.val∉B →
      unionJoin A B x.1 x.2 v=unionJoin A B y.1 y.2 v) ↔ x.1=y.1 := by
    constructor
    · intro hh; funext v
      have hv : v.val∉B := fun hb => Finset.disjoint_left.mp h v.property hb
      exact (unionJoin_left A B _ _ v).symm.trans
        ((hh ⟨v,Finset.mem_union_left B v.property⟩ hv).trans (unionJoin_left A B _ _ v))
    · intro hh v hv
      have ha : v.val∈A := (Finset.mem_union.mp v.property).resolve_right hv
      simp [unionJoin,ha,hh]
  change tensorRightHom b ((unionEquiv A B h).symm ((unionEquiv A B h) x))
    ((unionEquiv A B h).symm ((unionEquiv A B h) y))=
      liftBetween Finset.subset_union_right b (unionJoin A B x.1 x.2)
        (unionJoin A B y.1 y.2)
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  change (if x.1=y.1 then (1:ℂ) else 0)*b x.2 y.2=_
  simp only [liftBetween,hc,hx,hy,ite_mul,zero_mul,one_mul]

end PolynomialPEPS.PhysicalMove.LocalMovePhysical
namespace PolynomialPEPS.PhysicalMove.LocalMovePhysical
open Matrix QuantumSSA SupportedCurve SpectralCurve MatrixInterpolation
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
variable {L q : ℕ}

theorem density_union_ptrL (Ω : State L q) (A B : Finset (Vertex L)) (h : Disjoint A B) :
    ptrL (reindexHom (unionEquiv A B h).symm (reducedDensity Ω (A∪B)))=
      reducedDensity Ω B := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro b
  rw [←ptrL_dual, Matrix.trace_mul_comm,trace_mul_reindexHom,Matrix.trace_mul_comm,
    liftBetween_union_right, Matrix.trace_mul_comm,←inner_liftLocal_trace,
    liftLocal_liftBetween,inner_liftLocal_trace,Matrix.trace_mul_comm]

theorem coefficient_gram {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Ω : State L q) (A : Finset (Vertex L))
    (e : m ≃ RegionConfiguration q A) (f : n ≃ RegionConfiguration q Aᶜ) :
    (coefficientMatrix Ω A).submatrix e f *
      ((coefficientMatrix Ω A).submatrix e f).conjTranspose=
        reindexHom e.symm (reducedDensity Ω A) := by
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  rfl

theorem coefficient_action (Ω : State L q) (A : Finset (Vertex L))
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    coefficientMatrix (asMap (liftLocal A a) Ω) A=a*coefficientMatrix Ω A := by
  ext x z
  exact asMap_liftLocal_join A a Ω x z

theorem coefficient_action_reindex {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Ω : State L q) (A : Finset (Vertex L))
    (e : m ≃ RegionConfiguration q A) (f : n ≃ RegionConfiguration q Aᶜ)
    (a : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) :
    (coefficientMatrix (asMap (liftLocal A a) Ω) A).submatrix e f=
      reindexHom e.symm a*(coefficientMatrix Ω A).submatrix e f := by
  rw [coefficient_action]
  exact (Matrix.submatrix_mul_equiv _ _ _ e _).symm

theorem coefficient_hsEnergy {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Ω : State L q) (A : Finset (Vertex L))
    (e : m ≃ RegionConfiguration q A) (f : n ≃ RegionConfiguration q Aᶜ) :
    hsEnergy ((coefficientMatrix Ω A).submatrix e f)=‖Ω‖^2 := by
  rw [EuclideanSpace.norm_sq_eq,←Equiv.sum_comp (joinEquiv A)]
  simp only [hsEnergy,Fintype.sum_prod_type]
  rw [←Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Equiv.sum_comp f]
  rfl

end PolynomialPEPS.PhysicalMove.LocalMovePhysical
namespace PolynomialPEPS.PhysicalMove.LocalMovePhysical
open Matrix QuantumSSA SupportedCurve SpectralCurve MatrixInterpolation
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
variable {L q : ℕ}

def complementJoin (A B F : Finset (Vertex L)) (hF : F=(A∪B)ᶜ)
    (x : RegionConfiguration q B) (z : RegionConfiguration q F) :
    RegionConfiguration q Aᶜ := fun v =>
  if h : v.val∈B then x ⟨v,h⟩ else z ⟨v,by
    rw [hF,Finset.mem_compl,Finset.mem_union]
    exact fun hh => hh.elim (Finset.mem_compl.mp v.property) h⟩

def complementEquiv (A B F : Finset (Vertex L)) (h : Disjoint A B) (hF : F=(A∪B)ᶜ) :
    (RegionConfiguration q B × RegionConfiguration q F) ≃ RegionConfiguration q Aᶜ where
  toFun u := complementJoin A B F hF u.1 u.2
  invFun z := (fun v => z ⟨v,Finset.mem_compl.mpr (fun ha => Finset.disjoint_left.mp h ha v.property)⟩,
    fun v => z ⟨v,by
      have hv : v.val∈(A∪B)ᶜ := hF ▸ v.property
      rw [Finset.mem_compl,Finset.mem_union] at hv
      exact Finset.mem_compl.mpr (fun ha => hv (Or.inl ha))⟩)
  left_inv u := by
    apply Prod.ext
    · funext v; simp [complementJoin,v.property]
    · funext v
      have hv : v.val∉B := by
        have hh : v.val∈(A∪B)ᶜ := hF ▸ v.property
        rw [Finset.mem_compl,Finset.mem_union] at hh
        exact fun hb => hh (Or.inr hb)
      simp [complementJoin,hv]
  right_inv z := by
    funext v
    simp only [complementJoin]
    split_ifs <;> rfl

theorem combined_compl (X Y P : Finset (Vertex L)) :
    ((X∪Y)∪P)ᶜ=((X∪P)∪Y)ᶜ := by
  congr 1
  ext v
  simp only [Finset.mem_union]
  tauto

def fourCoefficient (Ω : State L q) (X Y P : Finset (Vertex L))
    (hXY : Disjoint X Y) (hXP : Disjoint X P) (hYP : Disjoint Y P) :
    Matrix (RegionConfiguration q X ×RegionConfiguration q Y)
      (RegionConfiguration q P ×RegionConfiguration q ((X∪Y)∪P)ᶜ) ℂ :=
  (coefficientMatrix Ω (X∪Y)).submatrix (unionEquiv X Y hXY)
    (complementEquiv (X∪Y) P ((X∪Y)∪P)ᶜ (Finset.disjoint_union_left.mpr ⟨hXP,hYP⟩) rfl)

theorem fourCoefficient_reshuffle (Ω : State L q) (X Y P : Finset (Vertex L))
    (hXY : Disjoint X Y) (hXP : Disjoint X P) (hYP : Disjoint Y P) :
    reshuffle (fourCoefficient Ω X Y P hXY hXP hYP)=
      (coefficientMatrix Ω (X∪P)).submatrix (unionEquiv X P hXP)
        (complementEquiv (X∪P) Y ((X∪Y)∪P)ᶜ
          (Finset.disjoint_union_left.mpr ⟨hXY,hYP.symm⟩) (combined_compl X Y P)) := by
  ext xp yf
  change Ω (joinConfigurations (X∪Y) (unionJoin X Y xp.1 yf.1)
      (complementJoin (X∪Y) P _ rfl xp.2 yf.2))=
    Ω (joinConfigurations (X∪P) (unionJoin X P xp.1 xp.2)
      (complementJoin (X∪P) Y _ (combined_compl X Y P) yf.1 yf.2))
  apply congrArg (fun z : Configuration L q => Ω z)
  funext v
  by_cases hx : v∈X
  · simp [joinConfigurations,unionJoin,hx]
  · by_cases hy : v∈Y
    · have hp : v∉P := fun hp => Finset.disjoint_left.mp hYP hy hp
      simp [joinConfigurations,unionJoin,complementJoin,hx,hy,hp]
    · by_cases hp : v∈P <;> simp [joinConfigurations,unionJoin,complementJoin,hx,hy,hp]

theorem fourCoefficient_gram (Ω : State L q) (X Y P : Finset (Vertex L))
    (hXY : Disjoint X Y) (hXP : Disjoint X P) (hYP : Disjoint Y P) :
    fourCoefficient Ω X Y P hXY hXP hYP*(fourCoefficient Ω X Y P hXY hXP hYP).conjTranspose=
      reindexHom (unionEquiv X Y hXY).symm (reducedDensity Ω (X∪Y)) :=
  coefficient_gram _ _ _ _

end PolynomialPEPS.PhysicalMove.LocalMovePhysical
namespace PolynomialPEPS.PhysicalMove.LocalMovePhysical
open Matrix QuantumSSA SupportedCurve SpectralCurve MatrixInterpolation
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
variable {L q : ℕ}

theorem cfc_reindex {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (reindexHom e A)=reindexHom e (cfc f A) := by
  exact ((reindexHom e).map_cfc f A ((Matrix.finite_real_spectrum (A:=A)).continuousOn f)
    (reindexHom e).toAlgHom.toLinearMap.continuous_of_finiteDimensional hA
    (hA.submatrix e.symm)).symm

theorem fourCoefficient_action_XY (Ω : State L q) (X Y P : Finset (Vertex L))
    (hXY : Disjoint X Y) (hXP : Disjoint X P) (hYP : Disjoint Y P)
    (a : Matrix (RegionConfiguration q (X∪Y)) (RegionConfiguration q (X∪Y)) ℂ) :
    fourCoefficient (asMap (liftLocal (X∪Y) a) Ω) X Y P hXY hXP hYP=
      reindexHom (unionEquiv X Y hXY).symm a*fourCoefficient Ω X Y P hXY hXP hYP :=
  coefficient_action_reindex _ _ _ _ _

theorem fourCoefficient_action_Y (Ω : State L q) (X Y P : Finset (Vertex L))
    (hXY : Disjoint X Y) (hXP : Disjoint X P) (hYP : Disjoint Y P)
    (a : Matrix (RegionConfiguration q Y) (RegionConfiguration q Y) ℂ) :
    fourCoefficient (asMap (liftLocal Y a) Ω) X Y P hXY hXP hYP=
      tensorRightHom a*fourCoefficient Ω X Y P hXY hXP hYP := by
  rw [←liftLocal_liftBetween (Finset.subset_union_right : Y⊆X∪Y) a,
    fourCoefficient_action_XY,←liftBetween_union_right X Y hXY]
  rw [show reindexHom (unionEquiv X Y hXY).symm
      (reindexHom (unionEquiv X Y hXY) (tensorRightHom a))=tensorRightHom a from
    reindexHom_symm_apply (unionEquiv X Y hXY).symm _]
  rfl

theorem fourCoefficient_action_XP (Ω : State L q) (X Y P : Finset (Vertex L))
    (hXY : Disjoint X Y) (hXP : Disjoint X P) (hYP : Disjoint Y P)
    (a : Matrix (RegionConfiguration q (X∪P)) (RegionConfiguration q (X∪P)) ℂ) :
    reshuffle (fourCoefficient (asMap (liftLocal (X∪P) a) Ω) X Y P hXY hXP hYP)=
      reindexHom (unionEquiv X P hXP).symm a*reshuffle (fourCoefficient Ω X Y P hXY hXP hYP) := by
  rw [fourCoefficient_reshuffle,fourCoefficient_reshuffle]
  exact coefficient_action_reindex _ _ _ _ _

theorem fourCoefficient_action_P (Ω : State L q) (X Y P : Finset (Vertex L))
    (hXY : Disjoint X Y) (hXP : Disjoint X P) (hYP : Disjoint Y P)
    (a : Matrix (RegionConfiguration q P) (RegionConfiguration q P) ℂ) :
    reshuffle (fourCoefficient (asMap (liftLocal P a) Ω) X Y P hXY hXP hYP)=
      tensorRightHom a*reshuffle (fourCoefficient Ω X Y P hXY hXP hYP) := by
  rw [←liftLocal_liftBetween (Finset.subset_union_right : P⊆X∪P) a,
    fourCoefficient_action_XP,←liftBetween_union_right X P hXP]
  rw [show reindexHom (unionEquiv X P hXP).symm
      (reindexHom (unionEquiv X P hXP) (tensorRightHom a))=tensorRightHom a from
    reindexHom_symm_apply (unionEquiv X P hXP).symm _]
  rfl

theorem fourCoefficient_reshuffle_gram (Ω : State L q) (X Y P : Finset (Vertex L))
    (hXY : Disjoint X Y) (hXP : Disjoint X P) (hYP : Disjoint Y P) :
    reshuffle (fourCoefficient Ω X Y P hXY hXP hYP)*
      (reshuffle (fourCoefficient Ω X Y P hXY hXP hYP)).conjTranspose=
      reindexHom (unionEquiv X P hXP).symm (reducedDensity Ω (X∪P)) := by
  rw [fourCoefficient_reshuffle]
  exact coefficient_gram _ _ _ _

theorem fourCoefficient_norm (Ω : State L q) (X Y P : Finset (Vertex L))
    (hXY : Disjoint X Y) (hXP : Disjoint X P) (hYP : Disjoint Y P) :
    ‖LocalMove.flattenCLM (reshuffle (fourCoefficient Ω X Y P hXY hXP hYP))‖=‖Ω‖ := by
  have hh := coefficient_hsEnergy Ω (X∪Y) (unionEquiv X Y hXY)
    (complementEquiv (X∪Y) P ((X∪Y)∪P)ᶜ (Finset.disjoint_union_left.mpr ⟨hXP,hYP⟩) rfl)
  have hn := LocalMove.flatten_norm_sq (reshuffle (fourCoefficient Ω X Y P hXY hXP hYP))
  rw [QuantumSSA.hsEnergy_reshuffle] at hn
  change hsEnergy (fourCoefficient Ω X Y P hXY hXP hYP)=‖Ω‖^2 at hh
  nlinarith [norm_nonneg (LocalMove.flattenCLM (reshuffle (fourCoefficient Ω X Y P hXY hXP hYP))),
    norm_nonneg Ω]

end PolynomialPEPS.PhysicalMove.LocalMovePhysical

end

end OAI
