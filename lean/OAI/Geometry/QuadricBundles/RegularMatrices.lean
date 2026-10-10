import OAI.Geometry.QuadricBundles.TriangularSections

namespace OAI

universe u1

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix
open scoped BigOperators
noncomputable section

def regularFunctionRing (U : Set BaseCoordinates) : Subring (BaseCoordinates → ℂ) where
  carrier := {f | UniformlyRegularOn U f}
  zero_mem' := uniformlyRegular_const U 0
  one_mem' := uniformlyRegular_const U 1
  add_mem' := UniformlyRegularOn.add
  mul_mem' := UniformlyRegularOn.mul
  neg_mem' := UniformlyRegularOn.neg

def regularEval (U : Set BaseCoordinates) (z : BaseCoordinates) : regularFunctionRing U →+* ℂ where
  toFun f := f.val z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

lemma UniformlyRegularOn.matrix_det {r : ℕ} {U : Set BaseCoordinates}
    {A : BaseCoordinates → Matrix (Fin r) (Fin r) ℂ}
    (h : ∀ a b,UniformlyRegularOn U (fun z ↦ A z a b)) :
    UniformlyRegularOn U (fun z ↦ (A z).det) := by
  let B : Matrix (Fin r) (Fin r) (regularFunctionRing U) := fun a b ↦ ⟨fun z ↦ A z a b,h a b⟩
  have hb := B.det.property
  apply hb.congr
  intro z _
  exact (regularEval U z).map_det B
lemma UniformlyRegularOn.matrix_adjugate {r : ℕ} {U : Set BaseCoordinates}
    {A : BaseCoordinates → Matrix (Fin r) (Fin r) ℂ}
    (h : ∀ a b,UniformlyRegularOn U (fun z ↦ A z a b)) (a b : Fin r) :
    UniformlyRegularOn U (fun z ↦ (A z).adjugate a b) := by
  let B : Matrix (Fin r) (Fin r) (regularFunctionRing U) := fun a b ↦ ⟨fun z ↦ A z a b,h a b⟩
  have hb := (B.adjugate a b).property
  apply hb.congr
  intro z _
  exact congrFun (congrFun ((regularEval U z).map_adjugate B) a) b
lemma UniformlyRegularOn.matrix_inv {r : ℕ} {U : Set BaseCoordinates}
    {A : BaseCoordinates → Matrix (Fin r) (Fin r) ℂ}
    (h : ∀ a b,UniformlyRegularOn U (fun z ↦ A z a b))
    (hu : ∀ z∈U,IsUnit (A z).det) (a b : Fin r) :
    UniformlyRegularOn U (fun z ↦ (A z)⁻¹ a b) := by
  apply (((UniformlyRegularOn.matrix_det h).inv (fun z hz ↦ (hu z hz).ne_zero)).mul (UniformlyRegularOn.matrix_adjugate h a b)).congr
  intro z _
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
lemma UniformlyRegularOn.matrix_mul {r : ℕ} {U : Set BaseCoordinates}
    {A B : BaseCoordinates → Matrix (Fin r) (Fin r) ℂ}
    (hA : ∀ a b,UniformlyRegularOn U (fun z ↦ A z a b))
    (hB : ∀ a b,UniformlyRegularOn U (fun z ↦ B z a b)) (a b : Fin r) :
    UniformlyRegularOn U (fun z ↦ (A z*B z) a b) := by
  exact UniformlyRegularOn.fintype_sum (fun c ↦ (hA a c).mul (hB c b))

namespace BinaryForms

def RegularFamily (U : Set BaseCoordinates) (p : BaseCoordinates → Poly (R := ℂ)) : Prop :=
  ∀ a,UniformlyRegularOn U (fun z ↦ (p z).coeff a)
lemma RegularFamily.const (U : Set BaseCoordinates) (p : Poly (R := ℂ)) : RegularFamily U (fun _ ↦ p) :=
  fun _ ↦ uniformlyRegular_const U _
lemma RegularFamily.C {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) : RegularFamily U (fun z ↦ C (f z)) := by
  intro a
  by_cases ha : 0=a
  · simpa only [coeff_C,ite_eq_left ha] using hf
  · simpa only [coeff_C,ite_eq_right ha] using uniformlyRegular_const U 0
lemma RegularFamily.add {U : Set BaseCoordinates} {p q : BaseCoordinates → Poly (R := ℂ)}
    (hp : RegularFamily U p) (hq : RegularFamily U q) : RegularFamily U (fun z ↦ p z+q z) := by
  intro a
  exact (hp a).add (hq a)
lemma RegularFamily.sub {U : Set BaseCoordinates} {p q : BaseCoordinates → Poly (R := ℂ)}
    (hp : RegularFamily U p) (hq : RegularFamily U q) : RegularFamily U (fun z ↦ p z-q z) := by
  intro a
  simpa only [coeff_sub] using (hp a).sub (hq a)
lemma RegularFamily.mul {U : Set BaseCoordinates} {p q : BaseCoordinates → Poly (R := ℂ)}
    (hp : RegularFamily U p) (hq : RegularFamily U q) : RegularFamily U (fun z ↦ p z*q z) := by
  intro a
  simp only [coeff_mul]
  exact UniformlyRegularOn.finset_sum _ (fun b _ ↦ (hp b.1).mul (hq b.2))
lemma RegularFamily.pow {U : Set BaseCoordinates} {p : BaseCoordinates → Poly (R := ℂ)}
    (hp : RegularFamily U p) (n : ℕ) : RegularFamily U (fun z ↦ p z^n) := by
  induction n with
  | zero => simpa only [pow_zero] using RegularFamily.const U 1
  | succ n ih => simpa only [pow_succ] using ih.mul hp
lemma RegularFamily.fintype_sum {ι : Type u1} [Fintype ι] {U : Set BaseCoordinates}
    {p : ι → BaseCoordinates → Poly (R := ℂ)} (hp : ∀ i,RegularFamily U (p i)) :
    RegularFamily U (fun z ↦ ∑ i,p i z) := by
  intro a
  simpa only [coeff_sum] using UniformlyRegularOn.fintype_sum (fun i ↦ hp i a)
lemma substitute_regular {U : Set BaseCoordinates} {T : BaseCoordinates → Matrix (Fin 2) (Fin 2) ℂ}
    (hT : ∀ a b,UniformlyRegularOn U (fun z ↦ T z a b)) (p : Poly (R := ℂ)) :
    RegularFamily U (fun z ↦ substitute (T z) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [substitute_C] using RegularFamily.const U (C c)
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p b hp =>
    simp only [map_mul,substitute_X]
    exact hp.mul (RegularFamily.fintype_sum (fun a ↦ (RegularFamily.C (hT a b)).mul (RegularFamily.const U (X a))))
lemma symmetricMatrix_regular {U : Set BaseCoordinates} {T : BaseCoordinates → Matrix (Fin 2) (Fin 2) ℂ}
    (hT : ∀ a b,UniformlyRegularOn U (fun z ↦ T z a b)) (n : ℕ) (a b : Fin (n+1)) :
    UniformlyRegularOn U (fun z ↦ symmetricMatrix n (T z) a b) :=
  substitute_regular hT _ _
lemma adaptedPolynomials_regular {U : Set BaseCoordinates} {h d u v : BaseCoordinates → ℂ}
    (hh : UniformlyRegularOn U h) (hd : UniformlyRegularOn U d)
    (hu : UniformlyRegularOn U u) (hv : UniformlyRegularOn U v) (t : ℕ) (k : Fin (2*t+1)) :
    RegularFamily U (fun z ↦ adaptedPolynomials (h z) (d z) (u z) (v z) t k) := by
  have hk : RegularFamily U (fun z ↦ kernelForm (h z) (d z)) :=
    ((RegularFamily.C hd).mul (RegularFamily.const U (X 0))).sub ((RegularFamily.C hh).mul (RegularFamily.const U (X 1)))
  have hl : RegularFamily U (fun z ↦ liftForm (u z) (v z)) :=
    ((RegularFamily.C hu).mul (RegularFamily.const U (X 0))).add ((RegularFamily.C hv).mul (RegularFamily.const U (X 1)))
  induction t with
  | zero => exact RegularFamily.const U 1
  | succ t ih =>
    refine Fin.lastCases (n:=2*t+2) ?_ (fun k ↦ ?_) k
    · simpa only [adaptedPolynomials,Fin.snoc_last] using hl.pow (2*(t+1))
    · refine Fin.lastCases (n:=2*t+1) ?_ (fun k ↦ ?_) k
      · simpa only [adaptedPolynomials,Fin.snoc_castSucc,Fin.snoc_last] using
          hk.mul (RegularFamily.const U (X 0^(2*t+1)))
      · simpa only [adaptedPolynomials,Fin.snoc_castSucc] using
          (hk.mul (RegularFamily.const U (X 1))).mul (ih k)
lemma adaptedMatrix_regular {U : Set BaseCoordinates} {h d u v : BaseCoordinates → ℂ}
    (hh : UniformlyRegularOn U h) (hd : UniformlyRegularOn U d)
    (hu : UniformlyRegularOn U u) (hv : UniformlyRegularOn U v) (t : ℕ) (a b : Fin (2*t+1)) :
    UniformlyRegularOn U (fun z ↦ adaptedMatrix (h z) (d z) (u z) (v z) t a b) :=
  adaptedPolynomials_regular hh hd hu hv t b _
end BinaryForms
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial
noncomputable section
lemma polynomial_bezout (h d : BasePolynomial)
    (hu : ∀ z : BaseCoordinates,baseEval d z=0 → baseEval h z≠0) :
    ∃ u v : BasePolynomial,u*h+v*d=1 := by
  let J : Ideal BasePolynomial := Ideal.span {h,d}
  have hv : (1 : BasePolynomial)∈MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ J) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    rw [MvPolynomial.zeroLocus_span] at hz
    have hh := hz h (Set.mem_insert h {d})
    have hd := hz d (Set.mem_insert_of_mem h (Set.mem_singleton d))
    have he : z=![z 0,z 1] := by ext k; fin_cases k <;> rfl
    have hdz : baseEval d (z 0,z 1)=0 := by simpa only [baseEval,← he,aeval_eq_eval] using hd
    exact False.elim (hu (z 0,z 1) hdz (by simpa only [baseEval,← he,aeval_eq_eval] using hh))
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hv
  obtain ⟨n,hn⟩ := hv
  apply Ideal.mem_span_pair.mp
  simpa only [one_pow] using hn

namespace EqualizerData
variable (D : EqualizerData)
def bezoutU (i : StandardChart) : BasePolynomial := (polynomial_bezout (D.lift i) (D.divisor i) (D.lift_unit i)).choose
def bezoutV (i : StandardChart) : BasePolynomial :=
  (polynomial_bezout (D.lift i) (D.divisor i) (D.lift_unit i)).choose_spec.choose
lemma bezout_spec (i : StandardChart) : D.bezoutU i*D.lift i+D.bezoutV i*D.divisor i=1 :=
  (polynomial_bezout (D.lift i) (D.divisor i) (D.lift_unit i)).choose_spec.choose_spec
lemma bezout_eval (i : StandardChart) (z : BaseCoordinates) :
    baseEval (D.bezoutU i) z*baseEval (D.lift i) z+
      baseEval (D.bezoutV i) z*baseEval (D.divisor i) z=1 := by
  have h := congrArg (fun p ↦ baseEval p z) (D.bezout_spec i)
  simpa using h
end EqualizerData
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix
open BinaryForms
noncomputable section
namespace EqualizerData
variable (D : EqualizerData)
def kernelFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ :=
  firstFactor i j z^21*(secondFactor i j z)⁻¹^3
lemma kernelFactor_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (kernelFactor i j) :=
  ((firstFactor_regular i j _).pow 21).mul
    (((secondFactor_regular i j _).inv (fun _ hz ↦ secondFactor_ne_zero hz)).pow 3)
lemma kernelFactor_divisor (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    kernelFactor i j z*(firstFactor i j z*secondFactor i j z)^3=topFactor i j z := by
  have hs := secondFactor_ne_zero hz
  unfold kernelFactor topFactor
  field_simp
lemma bottomFactor_divisor (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    bottomFactor i j z*(firstFactor i j z*secondFactor i j z)^3=quotientFactor i j z := by
  have hf := firstFactor_ne_zero hz
  unfold bottomFactor quotientFactor
  field_simp
lemma kernelFactor_bottomFactor (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    kernelFactor i j z*bottomFactor i j z=(firstFactor i j z*secondFactor i j z)^18 := by
  have hf := firstFactor_ne_zero hz
  have hs := secondFactor_ne_zero hz
  unfold kernelFactor bottomFactor
  field_simp
lemma kernel_coordinates (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    baseEval (D.divisor j) (coordinateChange i j z)*topFactor i j z=
      kernelFactor i j z*baseEval (D.divisor i) z ∧
    baseEval (D.divisor j) (coordinateChange i j z)*D.low i j z-
      baseEval (D.lift j) (coordinateChange i j z)*bottomFactor i j z=
        -kernelFactor i j z*baseEval (D.lift i) z := by
  let δ := (firstFactor i j z*secondFactor i j z)^3
  have hδ : δ≠0 := pow_ne_zero _ (mul_ne_zero (firstFactor_ne_zero hz) (secondFactor_ne_zero hz))
  have hk := kernelFactor_divisor i j hz
  have hb := bottomFactor_divisor i j hz
  have hd := D.divisor_change i j z hz
  have hl := D.low_spec i j hz
  change baseEval (D.divisor i) z=δ*baseEval (D.divisor j) (coordinateChange i j z) at hd
  change kernelFactor i j z*δ=topFactor i j z at hk
  change bottomFactor i j z*δ=quotientFactor i j z at hb
  unfold numerator at hl
  constructor
  · rw [hd,← hk]; ring
  · apply mul_left_cancel₀ hδ
    linear_combination hl-(D.low i j z)*hd-
      (baseEval (D.lift j) (coordinateChange i j z))*hb+(baseEval (D.lift i) z)*hk

lemma substitute_kernel (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    substitute (D.coordinateTransition i j z)
      (kernelForm (baseEval (D.lift j) (coordinateChange i j z))
        (baseEval (D.divisor j) (coordinateChange i j z)))=
      C (kernelFactor i j z)*kernelForm (baseEval (D.lift i) z) (baseEval (D.divisor i) z) := by
  obtain ⟨h0,h1⟩ := D.kernel_coordinates i j hz
  apply MvPolynomial.funext
  intro x
  rw [eval_substitute]
  simp only [eval_kernelForm,map_mul,eval_C]
  simp only [coordinateTransition,Matrix.transpose_apply,Matrix.mulVec, dotProduct,Fin.sum_univ_two,
    Matrix.of_apply,cons_val_zero,cons_val_one,cons_val_fin_one,zero_mul]
  linear_combination (x 0)*h0+(x 1)*h1
lemma substitute_f (i j : StandardChart) (z : BaseCoordinates) :
    substitute (D.coordinateTransition i j z) (X 1)=C (bottomFactor i j z)*X 1 := by
  rw [substitute_X]
  simp [coordinateTransition,Fin.sum_univ_two]
lemma substitute_e_projection (i j : StandardChart) (z : BaseCoordinates) :
    MvPolynomial.eval ![1,0] (substitute (D.coordinateTransition i j z) (X 0))=topFactor i j z := by
  rw [substitute_X]
  simp [coordinateTransition,Fin.sum_univ_two]
lemma quotient_covector (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) (x : Fin 2 → ℂ) :
    baseEval (D.lift i) z*((D.coordinateTransition i j z).mulVec x 0)+
      baseEval (D.divisor i) z*((D.coordinateTransition i j z).mulVec x 1)=
    quotientFactor i j z*(baseEval (D.lift j) (coordinateChange i j z)*x 0+
      baseEval (D.divisor j) (coordinateChange i j z)*x 1) := by
  have hl := D.low_spec i j hz
  have hd := D.divisor_factor i j hz
  unfold numerator at hl
  simp only [coordinateTransition,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
    cons_val_zero,cons_val_one,cons_val_fin_one,zero_mul]
  linear_combination (x 0)*hl+(x 1)*hd
lemma substitute_lift_quotient (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    MvPolynomial.eval ![baseEval (D.lift i) z,baseEval (D.divisor i) z]
      (substitute (D.coordinateTransition i j z)
        (liftForm (baseEval (D.bezoutU j) (coordinateChange i j z))
          (baseEval (D.bezoutV j) (coordinateChange i j z))))=quotientFactor i j z := by
  rw [eval_substitute,eval_liftForm]
  have h := D.quotient_covector i j hz
    ![baseEval (D.bezoutU j) (coordinateChange i j z),baseEval (D.bezoutV j) (coordinateChange i j z)]
  simp only [coordinateTransition,Matrix.transpose_apply,Matrix.mulVec, dotProduct,Fin.sum_univ_two,
    Matrix.of_apply,cons_val_zero,cons_val_one,cons_val_fin_one,zero_mul] at h ⊢
  have hu := D.bezout_eval j (coordinateChange i j z)
  linear_combination h+(quotientFactor i j z)*hu
end EqualizerData
end
end QuadricCounterexample

end

end OAI
