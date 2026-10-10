import OAI.Analysis.InterpolatedFactors.Absorption

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

section
namespace FreeGroupFactorMain.Amplification
variable {A : Type u_1} [CStarAlgebra A]

def subalgebraCorner (M : StarSubalgebra ℂ A) (p : A) (hp : IsStarProjection p) (hpM : p∈M) :
    StarSubalgebra ℂ (Corner p hp) where
  carrier := {x | (x:A)∈M}
  zero_mem' := zero_mem M
  one_mem' := hpM
  add_mem' {a b} ha hb := show (a:A)+(b:A)∈M from add_mem ha hb
  mul_mem' {a b} ha hb := show (a:A)*(b:A)∈M from mul_mem ha hb
  algebraMap_mem' c := by
    change c • p∈M
    exact M.smul_mem hpM c
  star_mem' {x} hx := by
    change star (x:A)∈M
    exact star_mem hx

def sandwiched (p : A) (hp : IsStarProjection p) (a b x : A)
    (ha : p*a=a) (hb : p*b=b) : Corner p hp :=
  ⟨a*x*star b,by
    constructor
    · rw [← mul_assoc,← mul_assoc,ha]
    · have hb' : star b*p=star b := by
        simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hb
      rw [mul_assoc,hb']⟩
end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification
variable {ι : Type u_2} [DecidableEq ι]

abbrev PCorner (ι : Type u_3) [DecidableEq ι] := Corner (P : Operator ι) projection_P

def pFilled (u v : ℝ) (i j : ι) : StarSubalgebra ℂ (PCorner ι) :=
  subalgebraCorner (filledEdgeAlgebra u v i j) P projection_P
    (edgeAlgebra_le_filled u v i j (P_mem_edge u v i))

def filledOfCorner {u v : ℝ} {i j : ι} (a : pFilled u v i j) : filledEdgeAlgebra u v i j :=
  ⟨a.val.val,a.property⟩

def pTrace (u v : ℝ) (i j : ι) : pFilled u v i j →ₗ[ℂ] ℂ where
  toFun a := pVacuumTrace u v a.val.val
  map_add' a b := by simp only [pVacuumTrace,vacuumTrace,AddMemClass.coe_add,add_apply,inner_add_right,mul_add]
  map_smul' c a := by
    simp only [pVacuumTrace,vacuumTrace,SetLike.val_smul,smul_apply,inner_smul_right,smul_eq_mul,RingHom.id_apply]
    ring

theorem pTrace_tracial (u v : ℝ) (hu : u≠0) (hv : v≠0) (i j : ι) (a b : pFilled u v i j) :
    pTrace u v i j (a*b)=pTrace u v i j (b*a) := by
  change (u:ℂ)⁻¹*(u:ℂ)⁻¹*vacuumTrace u v (a.val.val*b.val.val)=_
  rw [ambient_trace_mul u v hu hv
    ⟨a.val.val,filledEdgeAlgebra_le_ambient u v i j a.property⟩
    ⟨b.val.val,filledEdgeAlgebra_le_ambient u v i j b.property⟩]
  rfl

theorem P_mul_supportedLeg (u v : ℝ) (i : ι) (r : Bool) :
    P*supportedLeg u v i r=supportedLeg u v i r := by
  cases r
  · exact projection_P.isIdempotentElem.eq
  · exact edgePolar_left u v i

def pFresh (u v : ℝ) (i n : ι) (r s : Bool) : PCorner ι :=
  (u:ℂ)⁻¹ • sandwiched P projection_P (supportedLeg u v i r) (supportedLeg u v i s) (C u v n)
    (P_mul_supportedLeg u v i r) (P_mul_supportedLeg u v i s)

@[simp] theorem pFresh_val (u v : ℝ) (i n : ι) (r s : Bool) :
    (pFresh u v i n r s : Operator ι)=normalizedCreation u v i n r s := rfl

def pResidual (u v : ℝ) (i j : ι) (r s : Option Bool) : PCorner ι :=
  (u:ℂ)⁻¹ • sandwiched P projection_P (residualLeg u v i r) (residualLeg u v i s) (C u v j)
    (P_mul_residualLeg u v i r) (P_mul_residualLeg u v i s)

@[simp] theorem pResidual_val (u v : ℝ) (i j : ι) (r s : Option Bool) :
    (pResidual u v i j r s : Operator ι)=normalizedResidual u v i j r s := rfl

def pDiagonal (u v : ℝ) (i k : ι) (r : Bool) : PCorner ι :=
  ((weight u v (!r):ℂ)/(u:ℂ)) • sandwiched P projection_P
    (supportedLeg u v i r) (supportedLeg u v i r) (edgeCreation k (!r) (!r))
    (P_mul_supportedLeg u v i r) (P_mul_supportedLeg u v i r)

@[simp] theorem pDiagonal_val (u v : ℝ) (i k : ι) (r : Bool) :
    (pDiagonal u v i k r : Operator ι)=normalizedDiagonal u v i k r := rfl

theorem P_mul_legSupport (u v : ℝ) (i : ι) (r : Bool) : P*legSupport u v i r=legSupport u v i r := by
  cases r
  · exact projection_P.isIdempotentElem.eq
  · exact edgeRange_le_P u v i

theorem legSupport_projection (u v : ℝ) (i : ι) (r : Bool) : IsStarProjection (legSupport u v i r) := by
  cases r
  · exact projection_P
  · exact edgeRange_projection u v i

def pSupport (u v : ℝ) (i j : ι) (r : Bool) : pFilled u v i j :=
  ⟨⟨legSupport u v i r,P_mul_legSupport u v i r,by
    simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,(legSupport_projection u v i r).isSelfAdjoint.star_eq]
      using congrArg star (P_mul_legSupport u v i r)⟩,
    edgeAlgebra_le_filled u v i j (by
      cases r with
      | false => exact P_mem_edge u v i
      | true => exact edgeRange_mem_edge u v i)⟩

theorem pSupport_projection (u v : ℝ) (i j : ι) (r : Bool) : IsStarProjection (pSupport u v i j r) := by
  constructor
  · apply Subtype.ext;apply Subtype.ext
    exact (legSupport_projection u v i r).isIdempotentElem.eq
  · apply Subtype.ext;apply Subtype.ext
    exact (legSupport_projection u v i r).isSelfAdjoint.star_eq

theorem pSupport_false (u v : ℝ) (i j : ι) : pSupport u v i j false=1 := rfl

theorem pFresh_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j n m : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j) (hmi : m≠i) (hmj : m≠j)
    (r s r' s' : Bool) (a : pFilled u v i j) :
    star (pFresh u v i n r s)*(a : PCorner ι)*pFresh u v i m r' s'=
      if n=m ∧ r=r' ∧ s=s' then
        pTrace u v i j (a*pSupport u v i j r) • (pSupport u v i j s : PCorner ι) else 0 := by
  apply Subtype.ext
  have h := normalizedCreation_filled_covariance u v hu hv i j n m hji hni hnj hmi hmj r s r' s' (filledOfCorner a)
  split_ifs with hh
  · rw [ite_eq_left hh] at h
    exact h
  · rw [ite_eq_right hh] at h
    exact h

end FreeGroupFactorMain.WeightedFock

end

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification RectangularAbsorption
variable {ι : Type u_4} [DecidableEq ι]

theorem legSupport_mul_leg (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : ι) (r : Bool) :
    legSupport u v i r*supportedLeg u v i r=supportedLeg u v i r := by
  cases r
  · exact projection_P.isIdempotentElem.eq
  · change (edgePolar u v i*star (edgePolar u v i))*edgePolar u v i=edgePolar u v i
    rw [mul_assoc,edgePolar_initial u v hv.le hvu,edgePolar_right]

theorem pFresh_supported (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j n : ι) (r s : Bool) :
    (pSupport u v i j r : PCorner ι)*pFresh u v i n r s*(pSupport u v i j s : PCorner ι)=pFresh u v i n r s := by
  apply Subtype.ext
  change legSupport u v i r*normalizedCreation u v i n r s*legSupport u v i s=normalizedCreation u v i n r s
  have hs : star (supportedLeg u v i s)*legSupport u v i s=star (supportedLeg u v i s) := by
    simpa only [star_mul,(legSupport_projection u v i s).isSelfAdjoint.star_eq]
      using congrArg star (legSupport_mul_leg u v hv hvu i s)
  simp only [normalizedCreation,supportedCreation,mul_smul_comm,smul_mul_assoc]
  rw [← mul_assoc,← mul_assoc,legSupport_mul_leg u v hv hvu i r,mul_assoc,hs]

def freshAbsorptionData (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i j n₀ : ι) (hji : j≠i) (h₀i : n₀≠i) (h₀j : n₀≠j)
    (r s : Bool) (hrs : ¬(r=false ∧ s=false))
    (f : ℕ → ι) (hf : Function.Injective f) (hfi : ∀ n,f n≠i) (hfj : ∀ n,f n≠j) : Data (pFilled u v i j) where
  p := pSupport u v i j r
  q := pSupport u v i j s
  projection := pSupport_projection u v i j r
  projectionq := pSupport_projection u v i j s
  τ := pTrace u v i j
  tracial := pTrace_tracial u v (hv.trans hvu).ne' hv.ne' i j
  C n := pFresh u v i (f n) false false
  D := pFresh u v i n₀ r s
  D_supported := pFresh_supported u v hv hvu i j n₀ r s
  C_cov a n m := by
    have h := pFresh_covariance u v (hv.trans hvu).ne' hv.ne' i j (f n) (f m) hji
      (hfi n) (hfj n) (hfi m) (hfj m) false false false false a
    simpa only [and_true,pSupport_false,mul_one,hf.eq_iff,OneMemClass.coe_one] using h
  D_cov a := by
    simpa only [and_self,ite_true] using pFresh_covariance u v (hv.trans hvu).ne' hv.ne' i j n₀ n₀ hji
      h₀i h₀j h₀i h₀j r s r s a
  C_D a n := by
    have h := pFresh_covariance u v (hv.trans hvu).ne' hv.ne' i j (f n) n₀ hji
      (hfi n) (hfj n) h₀i h₀j false false r s a
    rw [ite_eq_right (fun h => hrs ⟨h.2.1.symm,h.2.2.symm⟩)] at h
    exact h
  D_C a n := by
    have h := pFresh_covariance u v (hv.trans hvu).ne' hv.ne' i j n₀ (f n) hji
      h₀i h₀j (hfi n) (hfj n) r s false false a
    rw [ite_eq_right (fun h => hrs ⟨h.2.1,h.2.2⟩)] at h
    exact h
end

open FreeFock Amplification RectangularAbsorption
variable {ι : Type u_5} [DecidableEq ι]

def pResidualSupport (u v : ℝ) (i j : ι) : Option Bool → pFilled u v i j
  | none => 1-pSupport u v i j true
  | some _ => pSupport u v i j true

@[simp] theorem pResidualSupport_val (u v : ℝ) (i j : ι) (r : Option Bool) :
    ((pResidualSupport u v i j r : PCorner ι):Operator ι)=residualSupport u v i r := by
  cases r <;> rfl

theorem pResidualSupport_projection (u v : ℝ) (i j : ι) (r : Option Bool) :
    IsStarProjection (pResidualSupport u v i j r) := by
  cases r with
  | none => exact (pSupport_projection u v i j true).one_sub
  | some r => exact pSupport_projection u v i j true

theorem residualSupport_projection (u v : ℝ) (i : ι) (r : Option Bool) :
    IsStarProjection (residualSupport u v i r) := by
  cases r with
  | none => exact edgeDefect_projection u v i
  | some r => exact edgeRange_projection u v i

theorem residualSupport_mul_leg (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : ι) (r : Option Bool) :
    residualSupport u v i r*residualLeg u v i r=residualLeg u v i r := by
  rcases r with _ | (_|_)
  · exact (edgeDefect_projection u v i).isIdempotentElem.eq
  · exact (edgeRange_projection u v i).isIdempotentElem.eq
  · exact legSupport_mul_leg u v hv hvu i true

theorem pResidual_supported (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι) (r s : Option Bool) :
    (pResidualSupport u v i j r : PCorner ι)*pResidual u v i j r s*
      (pResidualSupport u v i j s : PCorner ι)=pResidual u v i j r s := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul,pResidualSupport_val,pResidual_val]
  change residualSupport u v i r*normalizedResidual u v i j r s*residualSupport u v i s=normalizedResidual u v i j r s
  have hs : star (residualLeg u v i s)*residualSupport u v i s=star (residualLeg u v i s) := by
    simpa only [star_mul,(residualSupport_projection u v i s).isSelfAdjoint.star_eq]
      using congrArg star (residualSupport_mul_leg u v hv hvu i s)
  simp only [normalizedResidual,residualCreation,mul_smul_comm,smul_mul_assoc]
  rw [← mul_assoc,← mul_assoc,residualSupport_mul_leg u v hv hvu i r,mul_assoc,hs]

theorem pDiagonal_supported (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j k : ι) (r : Bool) :
    (pSupport u v i j r : PCorner ι)*pDiagonal u v i k r*(pSupport u v i j r : PCorner ι)=pDiagonal u v i k r := by
  apply Subtype.ext
  change legSupport u v i r*normalizedDiagonal u v i k r*legSupport u v i r=normalizedDiagonal u v i k r
  have hs : star (supportedLeg u v i r)*legSupport u v i r=star (supportedLeg u v i r) := by
    simpa only [star_mul,(legSupport_projection u v i r).isSelfAdjoint.star_eq]
      using congrArg star (legSupport_mul_leg u v hv hvu i r)
  simp only [normalizedDiagonal,transportedDiagonal,mul_smul_comm,smul_mul_assoc]
  rw [← mul_assoc,← mul_assoc,legSupport_mul_leg u v hv hvu i r,mul_assoc,hs]

theorem pResidual_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j : ι) (hji : j≠i) (r s r' s' : Option Bool)
    (hrs : ¬(r=none ∧ s=none)) (hrs' : ¬(r'=none ∧ s'=none)) (a : pFilled u v i j) :
    star (pResidual u v i j r s)*(a : PCorner ι)*pResidual u v i j r' s'=
      if r=r' ∧ s=s' then pTrace u v i j (a*pResidualSupport u v i j r) •
        (pResidualSupport u v i j s : PCorner ι) else 0 := by
  apply Subtype.ext
  have h := normalizedResidual_filled_covariance u v hu hv i j hji r s r' s' hrs hrs' (filledOfCorner a)
  split_ifs with hh
  · rw [ite_eq_left hh] at h
    change star (normalizedResidual u v i j r s)*a.val.val*normalizedResidual u v i j r' s'=
      pVacuumTrace u v (a.val.val*(pResidualSupport u v i j r).val.val) • (pResidualSupport u v i j s).val.val
    rw [pResidualSupport_val,pResidualSupport_val]
    exact h
  · rw [ite_eq_right hh] at h
    exact h

theorem pDiagonal_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j k l : ι) (hji : j≠i) (hjk : j≠k) (hjl : j≠l)
    (r s : Bool) (a : pFilled u v i j) :
    star (pDiagonal u v i k r)*(a : PCorner ι)*pDiagonal u v i l s=
      if k=l ∧ r=s then pTrace u v i j (a*pSupport u v i j r) •
        (pSupport u v i j r : PCorner ι) else 0 := by
  apply Subtype.ext
  have h := normalizedDiagonal_filled_covariance u v hu hv i j k l hji hjk hjl r s (filledOfCorner a)
  split_ifs with hh
  · rw [ite_eq_left hh] at h
    exact h
  · rw [ite_eq_right hh] at h
    exact h

theorem pFresh_residual (u v : ℝ) (i j n : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j)
    (r s : Bool) (a b : Option Bool) (hab : ¬(a=none ∧ b=none)) :
    Orthogonal (pFilled u v i j) (pFresh u v i n r s) (pResidual u v i j a b) := by
  intro T
  apply Subtype.ext
  exact normalized_fresh_residual u v i j n hji hni hnj r s a b hab (filledOfCorner T)

theorem pFresh_diagonal (u v : ℝ) (i j n k : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j)
    (hnk : n≠k) (hjk : j≠k) (r s t : Bool) :
    Orthogonal (pFilled u v i j) (pFresh u v i n r s) (pDiagonal u v i k t) := by
  intro T
  apply Subtype.ext
  exact normalized_fresh_diagonal u v i j n k hji hni hnj hnk hjk r s t (filledOfCorner T)

theorem pResidual_diagonal (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (a b : Option Bool) (hab : ¬(a=none ∧ b=none)) (r : Bool) :
    Orthogonal (pFilled u v i j) (pResidual u v i j a b) (pDiagonal u v i k r) := by
  intro T
  apply Subtype.ext
  exact normalized_residual_diagonal u v i j k hji hjk a b hab r (filledOfCorner T)
end FreeGroupFactorMain.WeightedFock

end

end OAI
