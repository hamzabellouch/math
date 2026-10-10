import Mathlib
import OAI.Analysis.FreeWords.ConcreteCornerGeometry
import OAI.Analysis.FreeWords.TraceTransferDefinitions

namespace OAI

noncomputable section

namespace KKConcreteCorner

open KKTraceTransfer

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : Submodule ℂ H) [CompleteSpace S]

omit [CompleteSpace H] in
theorem extend_mul_compress (x : S →L[ℂ] S) (y : H →L[ℂ] H)
    (hy : Commute y S.starProjection) :
    extend S (x*compress S y)=extend S x*y := by
  rw [extend_mul,extend_compress]
  simp only [← mul_assoc]
  rw [(extend_supported S x).2,mul_assoc,hy.eq,← mul_assoc,(extend_supported S x).2]

omit [CompleteSpace H] in
theorem extend_compress_mul (y : H →L[ℂ] H) (x : S →L[ℂ] S)
    (hy : Commute y S.starProjection) :
    extend S (compress S y*x)=y*extend S x := by
  rw [extend_mul,extend_compress,mul_assoc _ _ (extend S x),(extend_supported S x).1,
    ← hy.eq,mul_assoc,(extend_supported S x).1]

def centralizerVNA (s : Set (S →L[ℂ] S)) : VonNeumannAlgebra S where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ s
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (Set.centralizer (s ∪ star s))) = _
    exact Set.centralizer_centralizer_centralizer _

def cornerAlgebra (M : VonNeumannAlgebra H) : VonNeumannAlgebra S :=
  centralizerVNA S (compress S '' (M.commutant : Set (H →L[ℂ] H)))

theorem mem_cornerAlgebra_iff (M : VonNeumannAlgebra H)
    (hp : S.starProjection ∈ M) (x : S →L[ℂ] S) :
    x ∈ cornerAlgebra S M ↔ extend S x ∈ M := by
  have hc (y : H →L[ℂ] H) (hy : y∈M.commutant) : Commute y S.starProjection :=
    ((VonNeumannAlgebra.mem_commutant_iff.mp hy) _ hp).symm
  change x ∈ StarSubalgebra.centralizer ℂ _ ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro hx
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro y hy
    have hh := (hx _ ⟨y,hy,rfl⟩).1
    have he := congrArg (extend S) hh
    rw [extend_compress_mul S y x (hc y hy),extend_mul_compress S x y (hc y hy)] at he
    exact he
  · intro hx
    rintro y ⟨z,hz,rfl⟩
    have hh : ∀ (a : H →L[ℂ] H), a∈M.commutant → compress S a*x=x*compress S a := by
      intro a ha
      apply extend_injective S
      rw [extend_compress_mul S a x (hc a ha),extend_mul_compress S x a (hc a ha)]
      exact ((VonNeumannAlgebra.mem_commutant_iff.mp ha) _ hx).symm
    exact ⟨hh z hz,by rw [← compress_star]; exact hh (star z) (star_mem hz)⟩

def liftLinear (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M) :
    ConcreteAlgebra (cornerAlgebra S M) →ₗ[ℂ] ConcreteAlgebra M where
  toFun x := ⟨extend S x.val,(mem_cornerAlgebra_iff S M hp x.val).mp x.property⟩
  map_add' x y := Subtype.ext (extend_add S x.val y.val)
  map_smul' c x := Subtype.ext (extend_smul S c x.val)

@[simp] theorem lift_val (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M)
    (x : ConcreteAlgebra (cornerAlgebra S M)) :
    (liftLinear S M hp x : H →L[ℂ] H)=extend S x.val := rfl

theorem lift_injective (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M) :
    Function.Injective (liftLinear S M hp) := by
  intro x y h
  apply Subtype.ext
  exact extend_injective S (congrArg Subtype.val h)

@[simp] theorem lift_mul (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M)
    (x y : ConcreteAlgebra (cornerAlgebra S M)) :
    liftLinear S M hp (x*y)=liftLinear S M hp x*liftLinear S M hp y :=
  Subtype.ext (extend_mul S x.val y.val)

@[simp] theorem lift_star (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M)
    (x : ConcreteAlgebra (cornerAlgebra S M)) :
    liftLinear S M hp (star x)=star (liftLinear S M hp x) :=
  Subtype.ext (extend_star S x.val)

def restrict (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M)
    (x : ConcreteAlgebra M) : ConcreteAlgebra (cornerAlgebra S M) :=
  ⟨compress S x.val,(mem_cornerAlgebra_iff S M hp _).mpr (by
    rw [extend_compress]
    exact M.toStarSubalgebra.mul_mem (M.toStarSubalgebra.mul_mem hp x.property) hp)⟩

@[simp] theorem restrict_lift (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M)
    (x : ConcreteAlgebra (cornerAlgebra S M)) : restrict S M hp (liftLinear S M hp x)=x :=
  Subtype.ext (compress_extend S x.val)

end

end KKConcreteCorner

namespace KKConcreteCorner

open KKTraceTransfer

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : Submodule ℂ H) [CompleteSpace S]

variable (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M)

def projection : ConcreteAlgebra M := ⟨S.starProjection,hp⟩

@[simp] theorem lift_one : liftLinear S M hp 1=projection S M hp := Subtype.ext (extend_one S)

theorem projection_isStar' : IsStarProjection (projection S M hp) := by
  constructor
  · exact Subtype.ext (projection_isStar S).isIdempotentElem.eq
  · exact Subtype.ext (projection_isStar S).isSelfAdjoint.star_eq

@[simp] theorem lift_restrict (x : ConcreteAlgebra M) :
    liftLinear S M hp (restrict S M hp x)=projection S M hp*x*projection S M hp :=
  Subtype.ext (extend_compress S x.val)

theorem lift_supported (x : ConcreteAlgebra (cornerAlgebra S M)) :
    projection S M hp*liftLinear S M hp x=liftLinear S M hp x ∧
      liftLinear S M hp x*projection S M hp=liftLinear S M hp x :=
  ⟨Subtype.ext (extend_supported S x.val).1,Subtype.ext (extend_supported S x.val).2⟩

theorem lift_projection (q : ConcreteAlgebra (cornerAlgebra S M)) (hq : IsStarProjection q) :
    IsStarProjection (liftLinear S M hp q) := by
  constructor
  · change liftLinear S M hp q*liftLinear S M hp q=liftLinear S M hp q
    rw [← lift_mul,hq.isIdempotentElem.eq]
  · change star (liftLinear S M hp q)=liftLinear S M hp q
    rw [← lift_star,hq.isSelfAdjoint.star_eq]

end

end KKConcreteCorner
end

end OAI
