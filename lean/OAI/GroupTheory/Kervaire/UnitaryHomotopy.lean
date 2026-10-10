import OAI.GroupTheory.Kervaire.IncidenceTangent

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff

namespace KervaireUnitaryHomotopy
variable (B C : Type*) [CStarAlgebra B] [CStarAlgebra C]

/-- A smooth ambient representative of a smooth unitary-valued map. -/
structure UMap where
  toFun : B → C
  smooth : ContDiff ℝ ∞ toFun
  unitary : ∀ x : unitary B, toFun (x : B) ∈ unitary C

instance : CoeFun (UMap B C) (fun _ ↦ B → C) := ⟨UMap.toFun⟩

variable {B C}

/-- Elementary smooth homotopy; equalities only concern the unitary domain. -/
def Elementary (F G : UMap B C) : Prop :=
  ∃ H : ℝ × B → C, ContDiff ℝ ∞ H ∧
    (∀ t (x : unitary B), H (t,(x : B)) ∈ unitary C) ∧
    (∀ x : unitary B, H (0,(x : B)) = F x) ∧
    (∀ x : unitary B, H (1,(x : B)) = G x)

/-- Finite chains suffice, so no smooth concatenation theorem is assumed. -/
def Homotopic (F G : UMap B C) : Prop := Relation.EqvGen Elementary F G

lemma homotopic_of_elementary {F G : UMap B C} (h : Elementary F G) : Homotopic F G :=
  Relation.EqvGen.rel _ _ h

lemma homotopic_refl (F : UMap B C) : Homotopic F F := Relation.EqvGen.refl _
lemma homotopic_symm {F G : UMap B C} (h : Homotopic F G) : Homotopic G F :=
  Relation.EqvGen.symm _ _ h
lemma homotopic_trans {F G H : UMap B C} (h : Homotopic F G) (h' : Homotopic G H) :
    Homotopic F H := Relation.EqvGen.trans _ _ _ h h'

section Differential
variable {E D : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
  [StarRing E] [ContinuousStar E] [StarModule ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
local instance : NormedAlgebra ℚ E := .restrictScalars ℚ ℝ E

/-- Horizontal derivatives depend only on the restriction to the unitary group.
This is essential: homotopies cancel X X* only on that group, not on all matrices. -/
lemma fderiv_horizontal_congr {f g : ℝ × E → D}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t s : ℝ)
    (heq : ∀ x : unitary E, f (t,(x : E)) = g (s,(x : E)))
    (x : unitary E) (a : skewAdjoint.submodule ℝ E) :
    fderiv ℝ f (t,(x : E)) (0,(x : E)*(a : E)) =
      fderiv ℝ g (s,(x : E)) (0,(x : E)*(a : E)) := by
  let c : ℝ → E := fun r ↦ (x : E)*NormedSpace.exp (r • (a : E))
  have hc0 : c 0 = (x : E) := by simp [c]
  have hcd : HasDerivAt c ((x : E)*(a : E)) 0 := by
    have he : HasDerivAt (fun r : ℝ ↦ NormedSpace.exp (r • (a : E))) (a : E) 0 := by
      simpa only [zero_smul,NormedSpace.exp_zero,one_mul] using
        hasDerivAt_exp_smul_const (a : E) (0 : ℝ)
    exact he.const_mul (x : E)
  have hcu (r : ℝ) : c r ∈ unitary E := by
    apply (unitary E).mul_mem x.property
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    change star (r • (a : E)) = -(r • (a : E))
    rw [star_smul,star_trivial,a.property,smul_neg]
  have hd₀ := ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_const (0 : ℝ) t).prodMk hcd))
  have hd₁ := ((hg.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_const (0 : ℝ) s).prodMk hcd))
  have he : (fun r ↦ f (t,c r)) = fun r ↦ g (s,c r) := funext fun r ↦ heq ⟨c r,hcu r⟩
  change HasDerivAt (fun r ↦ f (t,c r)) _ 0 at hd₀
  change HasDerivAt (fun r ↦ g (s,c r)) _ 0 at hd₁
  rw [he] at hd₀
  simpa only [hc0] using hd₀.unique hd₁

end Differential

lemma invariant_of_elementary {D : Type*} (I : UMap B C → D)
    (hI : ∀ F G, Elementary F G → I F = I G)
    {F G : UMap B C} (h : Homotopic F G) : I F = I G := by
  induction h with
  | rel F G h => exact hI F G h
  | refl F => rfl
  | symm F G _ ih => exact ih.symm
  | trans F G H _ _ ih ih' => exact ih.trans ih'

end KervaireUnitaryHomotopy

namespace KervaireIncidenceCurrent

section
open MeasureTheory KervaireUnitaryHomotopy
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

omit [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))] in
lemma incidence_restrict_congr {f g : ℝ × Mat K → Mat (K ⊕ R)} (t s : ℝ)
    (h : ∀ X : unitary (Mat K), f (t,(X : Mat K)) = g (s,(X : Mat K)))
    (p : unitary (Alg K R)) : incidence f (t,(p : Alg K R)) = incidence g (s,(p : Alg K R)) := by
  unfold incidence
  rw [h ⟨p.val.1,(unitary_alg_parts p).1⟩]

omit [Fintype IK] [Fintype IR] [Fintype IZ] [IsFiniteMeasure μ] [IsMulRightInvariant μ]
  [BorelSpace (unitary (Alg K R))] in
lemma incidence_endpoint_integral {n : ℕ} (b : Fin n → Horizontal K R)
    {f g : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (t s : ℝ) (heq : ∀ X : unitary (Mat K), f (t,(X : Mat K)) = g (s,(X : Mat K)))
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin n]→L[ℝ] ℝ) :
    (∫ p : unitary (Alg K R), form (incidence f (t,(p : Alg K R)))
      (fun i ↦ fderiv ℝ (incidence f) (t,(p : Alg K R))
        (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ) =
    (∫ p : unitary (Alg K R), form (incidence g (s,(p : Alg K R)))
      (fun i ↦ fderiv ℝ (incidence g) (s,(p : Alg K R))
        (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ) := by
  apply integral_congr_ae
  filter_upwards with p
  rw [incidence_restrict_congr t s heq p]
  congr 1
  funext i
  exact fderiv_horizontal_congr (contDiff_incidence hf) (contDiff_incidence hg) t s
    (incidence_restrict_congr t s heq) p (direction (b i))

/-- An ambient representative independent of the time coordinate. -/
def timeless (F : UMap (Mat K) (Mat (K ⊕ R))) : ℝ × Mat K → Mat (K ⊕ R) :=
  fun p ↦ F p.2

omit [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))] in
lemma contDiff_timeless (F : UMap (Mat K) (Mat (K ⊕ R))) : ContDiff ℝ ∞ (timeless F) :=
  F.smooth.comp contDiff_snd

/-- The compact horizontal current evaluated on a smooth unitary map. -/
def current {n : ℕ} (b : Fin n → Horizontal K R)
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin n]→L[ℝ] ℝ)
    (F : UMap (Mat K) (Mat (K ⊕ R))) : ℝ :=
  ∫ p : unitary (Alg K R), form (incidence (timeless F) (0,(p : Alg K R)))
    (fun i ↦ fderiv ℝ (incidence (timeless F)) (0,(p : Alg K R))
      (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ

omit [Fintype IZ] in
lemma current_eq_of_elementary {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin (n+1)]→L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) (F G : UMap (Mat K) (Mat (K ⊕ R)))
    (h : Elementary F G) :
    current (μ := μ) ((horizontalBasis bK bR bZ).reindex e) form F =
      current (μ := μ) ((horizontalBasis bK bR bZ).reindex e) form G := by
  obtain ⟨H,hH,hU,h0,h1⟩ := h
  unfold current
  rw [← incidence_endpoint_integral (μ := μ) _ hH (contDiff_timeless F) 0 0 h0 form,
    ← incidence_endpoint_integral (μ := μ) _ hH (contDiff_timeless G) 1 0 h1 form]
  exact incidence_integral_constant (μ := μ) bK bR bZ e hbK hbR hH hU form hform 0 1

omit [Fintype IZ] in
lemma current_eq_of_homotopic {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin (n+1)]→L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) {F G : UMap (Mat K) (Mat (K ⊕ R))}
    (h : Homotopic F G) :
    current (μ := μ) ((horizontalBasis bK bR bZ).reindex e) form F =
      current (μ := μ) ((horizontalBasis bK bR bZ).reindex e) form G :=
  invariant_of_elementary (current (μ := μ) ((horizontalBasis bK bR bZ).reindex e) form)
    (current_eq_of_elementary bK bR bZ e hbK hbR form hform) h

end

variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

def model : ℝ × Mat K → Mat (K ⊕ R) := fun p ↦ diag p.2 (-1)

lemma contDiff_model : ContDiff ℝ ∞ (model (K := K) (R := R)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × Mat K ↦ diag p.2 (-1))
  simp only [diag_eq_corner]
  exact ((in11 (K := K) (R := R)).contDiff.comp contDiff_snd).add contDiff_const

lemma fderiv_model (p v : ℝ × Mat K) :
    fderiv ℝ (model (K := K) (R := R)) p v = in11 v.2 := by
  have hd := (((in11 (K := K) (R := R)).hasFDerivAt).comp p
    hasFDerivAt_snd).add (hasFDerivAt_const (in22 (K := K) (R := R) (-1)) p)
  have he : (fun x : ℝ × Mat K ↦ in11 (K := K) (R := R) x.2 + in22 (-1)) = model := by
    funext x
    exact (diag_eq_corner _ _).symm
  change HasFDerivAt (fun x : ℝ × Mat K ↦ in11 (K := K) (R := R) x.2 + in22 (-1)) _ p at hd
  rw [he] at hd
  rw [hd.fderiv]
  simp

/-- Conjugation is a real linear automorphism of the skew-Hermitian space. -/
def skewConj (U : unitary (Mat K)) :
    skewAdjoint.submodule ℝ (Mat K) ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Mat K) where
  toFun A := ⟨star (U : Mat K)*(A : Mat K)*U, by
    change star (star (U : Mat K)*(A : Mat K)*U) = -_
    rw [star_mul,star_mul,star_star,A.property]
    simp [mul_assoc]⟩
  invFun A := ⟨(U : Mat K)*(A : Mat K)*star (U : Mat K), by
    change star ((U : Mat K)*(A : Mat K)*star (U : Mat K)) = -_
    rw [star_mul,star_mul,star_star,A.property]
    simp [mul_assoc]⟩
  left_inv A := by
    apply Subtype.ext
    change (U : Mat K)*(star (U : Mat K)*(A : Mat K)*U)*star (U : Mat K) = A
    simp only [mul_assoc, U.property.2, mul_one]
    rw [← mul_assoc,U.property.2,one_mul]
  right_inv A := by
    apply Subtype.ext
    change star (U : Mat K)*((U : Mat K)*(A : Mat K)*star (U : Mat K))*U = A
    simp only [mul_assoc,U.property.1,mul_one]
    rw [← mul_assoc,U.property.1,one_mul]
  map_add' A B := by apply Subtype.ext; simp [mul_add,add_mul]
  map_smul' c A := by apply Subtype.ext; simp

def gaugeFrame (U : unitary (Mat K)) (V : unitary (Mat R)) : unitary (Mat (K ⊕ R)) :=
  ⟨diag (U : Mat K) (V : Mat R),diag_unitary U.property V.property⟩

def gaugePoint (U : unitary (Mat K)) (V : unitary (Mat R)) : unitary (Alg K R) :=
  ⟨(1,(gaugeFrame U V : Mat (K ⊕ R)),-1), by
    constructor <;> apply Prod.ext
    · simp
    · exact Prod.ext (gaugeFrame U V).property.1 (by simp)
    · simp
    · exact Prod.ext (gaugeFrame U V).property.2 (by simp)⟩

lemma model_incidence_gauge (t : ℝ) (U : unitary (Mat K)) (V : unitary (Mat R)) :
    incidence model (t,(gaugePoint U V : Alg K R)) = 1 := by
  change diag 1 (-1) * diag (U : Mat K) (V : Mat R) * diag 1 (star (-1 : Mat R)) *
    star (diag (U : Mat K) (V : Mat R)) = 1
  simp only [diag_star,diag_mul,star_neg,star_one,one_mul,neg_mul,mul_one,mul_neg,neg_neg,
    U.property.2,V.property.2,diag_one]

def modelHorizontalEquiv (U : unitary (Mat K)) (V : unitary (Mat R)) :
    Horizontal K R ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Mat (K ⊕ R)) :=
  ((skewConj U).prodCongr (LinearEquiv.refl ℝ _)) |>.trans
    ((KervaireFixedSpace.degreeDerivativeEquiv (K := K) (R := R) 1 one_ne_zero).trans
      (skewConj (star (gaugeFrame U V))))

lemma fderiv_model_gauge (t : ℝ) (U : unitary (Mat K)) (V : unitary (Mat R))
    (h : Horizontal K R) :
    fderiv ℝ (incidence model) (t,(gaugePoint U V : Alg K R))
      (0,(gaugePoint U V : Alg K R)*(direction h : Alg K R)) =
      (modelHorizontalEquiv U V h : Mat (K ⊕ R)) := by
  rw [fderiv_incidence contDiff_model, fderiv_model]
  change in11 (1*(h.1 : Mat K)) * diag (U : Mat K) (V : Mat R) * diag 1 (star (-1 : Mat R)) *
    star (diag (U : Mat K) (V : Mat R)) +
    diag 1 (-1) * (diag (U : Mat K) (V : Mat R)*off h.2.2) * diag 1 (star (-1 : Mat R)) *
    star (diag (U : Mat K) (V : Mat R)) +
    diag 1 (-1) * diag (U : Mat K) (V : Mat R) * in22 (star ((-1 : Mat R)*(h.2.1 : Mat R))) *
    star (diag (U : Mat K) (V : Mat R)) +
    diag 1 (-1) * diag (U : Mat K) (V : Mat R) * diag 1 (star (-1 : Mat R)) *
    star (diag (U : Mat K) (V : Mat R)*off h.2.2) = _
  have hb : star (h.2.1 : Mat R) = -(h.2.1 : Mat R) := h.2.1.property
  simp only [star_mul,star_neg,star_one,diag_star,off_skew,one_mul,neg_one_mul,hb,neg_neg]
  change _ = star (star (diag (U : Mat K) (V : Mat R))) *
    KervaireFixedSpace.derivativeMatrix 1 (skewConj U h.1) h.2.1 h.2.2 *
      star (diag (U : Mat K) (V : Mat R))
  rw [star_star,diag_star]
  have hi11 (A : Mat K) : in11 (R := R) A = fromBlocks A 0 0 0 := rfl
  have hi22 (B : Mat R) : in22 (K := K) B = fromBlocks 0 0 0 B := rfl
  simp only [hi11,hi22,diag,off,KervaireFixedSpace.derivativeMatrix,one_smul,
    skewConj,fromBlocks_multiply,fromBlocks_neg,
    Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,Matrix.one_mul,Matrix.mul_one]
  have hu : (U : Mat K)*(star (U : Mat K)*(h.1 : Mat K)) = h.1 := by
    rw [← mul_assoc,U.property.2,one_mul]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks,Matrix.mul_assoc,U.property.2,hu,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_neg,Matrix.neg_mul,two_smul]

end KervaireIncidenceCurrent

end

end OAI
