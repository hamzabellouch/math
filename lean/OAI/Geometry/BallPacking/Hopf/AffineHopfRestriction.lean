import Mathlib
import OAI.Geometry.BallPacking.Hopf.SixLargeQuadricPacking

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
section
variable {ι : Type*} [Fintype ι]

def complexAffineTangent : (ι → ℂ) →L[ℝ] (Option ι → ℂ) :=
  ContinuousLinearMap.pi fun i => match i with
  | none => 0
  | some i => ContinuousLinearMap.proj i

omit [Fintype ι] in
@[simp] theorem complexAffineTangent_none (z : ι → ℂ) : complexAffineTangent z none=0 := rfl
omit [Fintype ι] in
@[simp] theorem complexAffineTangent_some (z : ι → ℂ) (i : ι) : complexAffineTangent z (some i)=z i := rfl

theorem complexAffineLift_hasFDerivAt (z : ι → ℂ) :
    HasFDerivAt complexAffineLift complexAffineTangent z := by
  have he : complexAffineLift (ι := ι)=fun z => complexAffineLift 0+complexAffineTangent z := by
    ext z i
    cases i <;> simp
  rw [he]
  convert! (show HasFDerivAt
    ((fun _ : ι → ℂ => complexAffineLift (0 : ι → ℂ)) + ⇑(complexAffineTangent (ι := ι)))
    complexAffineTangent z from by
    simpa only [zero_add] using
    (hasFDerivAt_const (complexAffineLift (0 : ι → ℂ)) z).add
      (complexAffineTangent (ι := ι)).hasFDerivAt) using 1

@[simp] theorem complexAffineLift_fderiv (z : ι → ℂ) :
    fderiv ℝ complexAffineLift z=complexAffineTangent := (complexAffineLift_hasFDerivAt z).fderiv

theorem complexPairing_affine_tangent (z v : ι → ℂ) :
    complexPairing (complexAffineLift z) (complexAffineTangent v)=complexPairing z v := by
  simp [complexPairing,Fintype.sum_option]

theorem complexPairing_tangent_tangent (z v : ι → ℂ) :
    complexPairing (complexAffineTangent z) (complexAffineTangent v)=complexPairing z v := by
  simp [complexPairing,Fintype.sum_option]

theorem hopfForm_affine_restriction (c : ℝ) (z v w : ι → ℂ) :
    hopfForm c (complexCartesian (complexAffineLift z))
      (complexCartesian (complexAffineTangent v)) (complexCartesian (complexAffineTangent w))=
      affineFSForm c (complexCartesian z) (complexCartesian v) (complexCartesian w) := by
  have hn : complexCartesian (complexAffineLift z)≠0 := by
    intro he
    have hh := congrFun (complexCartesian.injective (he.trans (map_zero _).symm)) none
    exact one_ne_zero (by simpa only [complexAffineLift_none,Pi.zero_apply] using hh)
  have hd (u : ι → ℂ) :
      phaseDot (complexCartesian (complexAffineLift z)) (complexCartesian (complexAffineTangent u))=
        phaseDot (complexCartesian z) (complexCartesian u) := by
    rw [←complexPairing_re,complexPairing_affine_tangent,complexPairing_re]
  have ha (u : ι → ℂ) :
      phaseArea (complexCartesian (complexAffineLift z)) (complexCartesian (complexAffineTangent u))=
        phaseArea (complexCartesian z) (complexCartesian u) := by
    rw [←complexPairing_im,complexPairing_affine_tangent,complexPairing_im]
  have ht : phaseArea (complexCartesian (complexAffineTangent v)) (complexCartesian (complexAffineTangent w))=
      phaseArea (complexCartesian v) (complexCartesian w) := by
    rw [←complexPairing_im,complexPairing_tangent_tangent,complexPairing_im]
  rw [hopfForm_apply c hn,affineFSForm_apply,complexAffineLift_sq,hd,ha,hd,ha,ht]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hopfForm_affine_pullback {Z : E → (ι → ℂ)} {x : E}
    (hZ : DifferentiableAt ℝ Z x) (c : ℝ) (v w : E) :
    hopfForm c (complexCartesian (complexAffineLift (Z x)))
      (fderiv ℝ (fun y => complexCartesian (complexAffineLift (Z y))) x v)
      (fderiv ℝ (fun y => complexCartesian (complexAffineLift (Z y))) x w)=
    affineFSForm c (complexCartesian (Z x))
      (fderiv ℝ (fun y => complexCartesian (Z y)) x v)
      (fderiv ℝ (fun y => complexCartesian (Z y)) x w) := by
  have hd := complexCartesian.hasFDerivAt.comp x
    ((complexAffineLift_hasFDerivAt (Z x)).comp x hZ.hasFDerivAt)
  have hdz := complexCartesian.hasFDerivAt.comp x hZ.hasFDerivAt
  rw [show fderiv ℝ (fun y => complexCartesian (complexAffineLift (Z y))) x=_ from hd.fderiv,
    show fderiv ℝ (fun y => complexCartesian (Z y)) x=_ from hdz.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  exact hopfForm_affine_restriction c (Z x) _ _

end

variable {ι : Type} [Fintype ι]

 def bubbleCoordinates (ε : ℂ) (x : Option ι → ℂ) : Option ι → ℂ
  | none => ε*x none
  | some i => x (some i)

 def homogeneousBubble (L m p : ℕ) (ε : ℂ) (x : Option ι → ℂ) : (Fin m → Option ι) → ℂ :=
  fun j => ε^(p-m)*x none^(L-m)*homogeneousVeronese m (bubbleCoordinates ε x) j

 theorem bubbleCoordinates_smooth :
    ContDiff ℂ ∞ (fun a : ℂ×(Option ι → ℂ) => bubbleCoordinates a.1 a.2) := by
  apply contDiff_pi.mpr
  rintro (_|i)
  · exact contDiff_fst.mul ((contDiff_apply ℂ ℂ none).comp contDiff_snd)
  · exact (contDiff_apply ℂ ℂ (some i)).comp contDiff_snd

 theorem homogeneousBubble_joint_smooth (L m p : ℕ) :
    ContDiff ℂ ∞ (fun a : ℂ×(Option ι → ℂ) => homogeneousBubble L m p a.1 a.2) := by
  apply contDiff_pi.mpr
  intro j
  exact ((contDiff_fst.pow _).mul (((contDiff_apply ℂ ℂ none).comp contDiff_snd).pow _)).mul
    ((contDiff_apply ℂ ℂ j).comp ((homogeneousVeronese_smooth m).comp bubbleCoordinates_smooth))

omit [Fintype ι] in
 theorem bubbleCoordinates_smul (ε ζ : ℂ) (x : Option ι → ℂ) :
    bubbleCoordinates ε (ζ•x)=ζ•bubbleCoordinates ε x := by
  ext i
  cases i <;> simp [bubbleCoordinates,Pi.smul_apply,smul_eq_mul,mul_left_comm]

omit [Fintype ι] in
 theorem homogeneousBubble_homogeneous {L m : ℕ} (hm : m≤L) (p : ℕ)
    (ε ζ : ℂ) (x : Option ι → ℂ) :
    homogeneousBubble L m p ε (ζ•x)=ζ^L•homogeneousBubble L m p ε x := by
  ext j
  simp only [homogeneousBubble,Pi.smul_apply,smul_eq_mul,mul_pow,bubbleCoordinates_smul,
    homogeneousVeronese_homogeneous]
  rw [show ζ^L=ζ^(L-m)*ζ^m by rw [←pow_add,Nat.sub_add_cancel hm]]
  ring

omit [Fintype ι] in
 theorem bubbleCoordinates_affine (ε : ℂ) (z : ι → ℂ) :
    bubbleCoordinates ε (complexAffineLift (ε•z))=ε•complexAffineLift z := by
  ext i
  cases i <;> simp [bubbleCoordinates,complexAffineLift,Pi.smul_apply,smul_eq_mul]

omit [Fintype ι] in
 theorem homogeneousBubble_scaled {m p : ℕ} (hp : m≤p) (L : ℕ) (ε : ℂ) (z : ι → ℂ) :
    homogeneousBubble L m p ε (complexAffineLift (ε•z))=ε^p•homogeneousVeronese m (complexAffineLift z) := by
  ext j
  simp only [homogeneousBubble,complexAffineLift_none,one_pow,mul_one,bubbleCoordinates_affine,
    homogeneousVeronese_homogeneous,Pi.smul_apply,smul_eq_mul]
  rw [←mul_assoc,←pow_add,Nat.sub_add_cancel hp]

omit [Fintype ι] in
 theorem homogeneousBubble_zero {m p : ℕ} (hp : m<p) (L : ℕ) (x : Option ι → ℂ) :
    homogeneousBubble L m p 0 x=0 := by
  ext j
  simp [homogeneousBubble,zero_pow (show p-m≠0 by omega)]

variable {κ : Type} [Fintype κ]
 def bubblePolynomial (L m p N : ℕ) (P : (Option ι → ℂ) → (κ → ℂ))
    (ε : ℂ) (x : Option ι → ℂ) : (κ ⊕ ((Fin m → Option ι) ⊕ (Fin L → Option ι))) → ℂ :=
  Sum.elim (P x) (Sum.elim (homogeneousBubble L m p ε x) (fun j => ε^N*homogeneousVeronese L x j))

 theorem bubblePolynomial_joint_smooth (L m p N : ℕ) {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℂ ∞ P) :
    ContDiff ℂ ∞ (fun a : ℂ×(Option ι → ℂ) => bubblePolynomial L m p N P a.1 a.2) := by
  apply contDiff_pi.mpr
  rintro (i|(j|k))
  · exact (contDiff_apply ℂ ℂ i).comp (hP.comp contDiff_snd)
  · exact (contDiff_apply ℂ ℂ j).comp (homogeneousBubble_joint_smooth L m p)
  · exact (contDiff_fst.pow N).mul ((contDiff_apply ℂ ℂ k).comp ((homogeneousVeronese_smooth L).comp contDiff_snd))

omit [Fintype ι] [Fintype κ] in
 theorem bubblePolynomial_homogeneous {L m : ℕ} (hm : m≤L) (p N : ℕ)
    {P : (Option ι → ℂ) → (κ → ℂ)} (hP : ∀ (ζ : ℂ) x,P (ζ•x)=ζ^L•P x)
    (ε ζ : ℂ) (x : Option ι → ℂ) :
    bubblePolynomial L m p N P ε (ζ•x)=ζ^L•bubblePolynomial L m p N P ε x := by
  ext i
  rcases i with (i|(j|k))
  · exact congrFun (hP ζ x) i
  · exact congrFun (homogeneousBubble_homogeneous hm p ε ζ x) j
  · simp only [bubblePolynomial,Sum.elim_inr,homogeneousVeronese_homogeneous,Pi.smul_apply,smul_eq_mul]
    ring

omit [Fintype ι] [Fintype κ] in
 theorem bubblePolynomial_nonzero (L m p N : ℕ) (P : (Option ι → ℂ) → (κ → ℂ))
    {ε : ℂ} (hε : ε≠0) {x : Option ι → ℂ} (hx : x≠0) :
    bubblePolynomial L m p N P ε x≠0 := by
  intro h
  apply homogeneousVeronese_nonzero L hx
  funext j
  have hh := congrFun h (Sum.inr (Sum.inr j))
  change ε^N*homogeneousVeronese L x j=0 at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero N hε)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def distinguishedChart (ε : ℂ) (z : Fin 3 → ℂ) : Fin 4 → ℂ :=
  ![1,ε*z 0,ε*z 1,ε*z 2]

 def distinguishedResidualTerm (p n k J K : ℕ) (ε : ℂ) (z : Fin 3 → ℂ) : ℂ :=
  ε^(k+liftBeta n J K+liftGamma n J K+liftDelta n J K-p)*
    (z 0-ε*z 1*z 2)^k*z 0^liftBeta n J K*z 1^liftGamma n J K*z 2^liftDelta n J K

 theorem distinguishedResidualTerm_smooth (p n k J K : ℕ) :
    ContDiff ℂ ∞ (fun a : ℂ×(Fin 3 → ℂ) => distinguishedResidualTerm p n k J K a.1 a.2) := by
  unfold distinguishedResidualTerm
  fun_prop

 theorem distinguishedResidualTerm_factor {p n k J K : ℕ}
    (hp : p≤k+liftBeta n J K+liftGamma n J K+liftDelta n J K)
    (ε : ℂ) (z : Fin 3 → ℂ) :
    firstQuadric (distinguishedChart ε z)^k * quadricLiftMonomial n J K (distinguishedChart ε z)=
      ε^p*distinguishedResidualTerm p n k J K ε z := by
  have he : firstQuadric (distinguishedChart ε z)=ε*(z 0-ε*z 1*z 2) := by
    simp only [firstQuadric,distinguishedChart,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    ring
  rw [he]
  simp only [quadricLiftMonomial,distinguishedChart,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,one_pow,one_mul,mul_pow,distinguishedResidualTerm]
  have hpw : ε^p*ε^(k+liftBeta n J K+liftGamma n J K+liftDelta n J K-p)=
      ε^k*ε^liftBeta n J K*ε^liftGamma n J K*ε^liftDelta n J K := by
    rw [←pow_add,Nat.add_sub_of_le hp]
    simp only [pow_add]
  calc
    _=(ε^k*ε^liftBeta n J K*ε^liftGamma n J K*ε^liftDelta n J K)*
      ((z 0-ε*z 1*z 2)^k*z 0^liftBeta n J K*z 1^liftGamma n J K*z 2^liftDelta n J K) := by ring
    _=_ := by rw [←hpw]; ring

 def distinguishedResidualPolynomial {A B : ℕ} (p L S : ℕ) (t δ : ℝ)
    (ε : ℂ) (z : Fin 3 → ℂ) : TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ :=
  fun ki => (δ:ℂ)⁻¹^(latticeIndex ki.1).1*(t:ℂ)⁻¹^(latticeIndex ki.1).2 *
    ∑ d∈(cubicNormalSection (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) (latticeIndex ki.1).2 ki.2).support,
      (cubicNormalSection (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) (latticeIndex ki.1).2 ki.2).coeff d *
        distinguishedResidualTerm p (L-2*(latticeIndex ki.1).1) (latticeIndex ki.1).1 (d 0) (d 1) ε z

 theorem distinguishedResidualPolynomial_smooth {A B : ℕ} (p L S : ℕ) (t δ : ℝ) :
    ContDiff ℂ ∞ (fun a : ℂ×(Fin 3 → ℂ) => distinguishedResidualPolynomial (A := A) (B := B) p L S t δ a.1 a.2) := by
  apply contDiff_pi.mpr
  intro ki
  exact contDiff_const.mul (ContDiff.sum (fun _ _ => contDiff_const.mul (distinguishedResidualTerm_smooth _ _ _ _ _)))

 theorem outerPolynomial_distinguished_factor {L S A B p : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (hp : p≤L-S) (t δ : ℝ) (ε : ℂ) (z : Fin 3 → ℂ) :
    outerPolynomial (A := A) (B := B) L S t δ (distinguishedChart ε z)=
      ε^p•distinguishedResidualPolynomial p L S t δ ε z := by
  classical
  ext ki
  unfold outerPolynomial liftedSection quadricLiftPolynomial distinguishedResidualPolynomial
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hh := distinguishedResidualTerm_factor
    (hp.trans (liftedSection_origin_orders hAS hS hB ki.1 ki.2 d hd)) ε z
  calc
    _=((δ:ℂ)⁻¹^(latticeIndex ki.1).1*(t:ℂ)⁻¹^(latticeIndex ki.1).2)*
      (cubicNormalSection (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) (latticeIndex ki.1).2 ki.2).coeff d *
      (firstQuadric (distinguishedChart ε z)^(latticeIndex ki.1).1*
        quadricLiftMonomial (L-2*(latticeIndex ki.1).1) (d 0) (d 1) (distinguishedChart ε z)) := by ring
    _=_ := by rw [hh]; ring

 theorem distinguishedResidualPolynomial_zero {L S A B p : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (hp : p<L-S) (t δ : ℝ) (z : Fin 3 → ℂ) :
    distinguishedResidualPolynomial (A := A) (B := B) p L S t δ 0 z=0 := by
  classical
  ext ki
  unfold distinguishedResidualPolynomial
  rw [Finset.sum_eq_zero]
  · simp
  · intro d hd
    have hh := liftedSection_origin_orders hAS hS hB ki.1 ki.2 d hd
    have he : (latticeIndex ki.1).1+liftBeta (L-2*(latticeIndex ki.1).1) (d 0) (d 1)+
      liftGamma (L-2*(latticeIndex ki.1).1) (d 0) (d 1)+liftDelta (L-2*(latticeIndex ki.1).1) (d 0) (d 1)-p≠0 := by omega
    simp [distinguishedResidualTerm,zero_pow he]

 def distinguishedHomogeneousCoordinates (x : Option (Fin 3) → ℂ) : Fin 4 → ℂ :=
   ![x none,x (some 0),x (some 1),x (some 2)]

 theorem distinguishedHomogeneousCoordinates_smooth :
     ContDiff ℂ ∞ distinguishedHomogeneousCoordinates := by
   apply contDiff_pi.mpr
   intro i
   fin_cases i <;> exact contDiff_apply ℂ ℂ _

 theorem distinguishedHomogeneousCoordinates_smul (ζ : ℂ) (x : Option (Fin 3) → ℂ) :
     distinguishedHomogeneousCoordinates (ζ•x)=ζ•distinguishedHomogeneousCoordinates x := by
   ext i
   fin_cases i <;> rfl

 theorem distinguishedHomogeneousCoordinates_chart (ε : ℂ) (z : Fin 3 → ℂ) :
     distinguishedHomogeneousCoordinates (complexAffineLift (ε•z))=distinguishedChart ε z := by
   ext i
   fin_cases i <;> rfl

 theorem complexAffineLift_complex_smooth :
     ContDiff ℂ ∞ (complexAffineLift (ι := Fin 3)) := by
   apply contDiff_pi.mpr
   rintro (_|i)
   · exact contDiff_const
   · exact contDiff_apply ℂ ℂ i

 def cubicBubblePolynomial {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ) (ε : ℂ) :=
   bubblePolynomial L m p N
     (outerPolynomial (A := A) (B := B) L S t δ ∘ distinguishedHomogeneousCoordinates) ε

 def cubicBubbleResidual {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ)
     (ε : ℂ) (z : Fin 3 → ℂ) :
     ((TrapezoidWeight A B × WeightedHomogeneousIndex) ⊕
       ((Fin m → Option (Fin 3)) ⊕ (Fin L → Option (Fin 3)))) → ℂ :=
   Sum.elim (distinguishedResidualPolynomial p L S t δ ε z)
     (Sum.elim (homogeneousVeronese m (complexAffineLift z))
       (fun j => ε^(N-p)*homogeneousVeronese L (complexAffineLift (ε•z)) j))

 theorem cubicBubblePolynomial_joint_smooth {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ) :
     ContDiff ℂ ∞ (fun a : ℂ×(Option (Fin 3) → ℂ) =>
       cubicBubblePolynomial (A := A) (B := B) L S m p N t δ a.1 a.2) := by
   exact bubblePolynomial_joint_smooth L m p N
     ((outerPolynomial_smooth L S t δ).comp distinguishedHomogeneousCoordinates_smooth)

 theorem cubicBubbleResidual_joint_smooth {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ) :
     ContDiff ℂ ∞ (fun a : ℂ×(Fin 3 → ℂ) =>
       cubicBubbleResidual (A := A) (B := B) L S m p N t δ a.1 a.2) := by
   apply contDiff_pi.mpr
   rintro (i|(j|k))
   · exact (contDiff_apply ℂ ℂ i).comp (distinguishedResidualPolynomial_smooth p L S t δ)
   · exact (contDiff_apply ℂ ℂ j).comp ((homogeneousVeronese_smooth m).comp
       (complexAffineLift_complex_smooth.comp contDiff_snd))
   · exact (contDiff_fst.pow _).mul ((contDiff_apply ℂ ℂ k).comp
       ((homogeneousVeronese_smooth L).comp (complexAffineLift_complex_smooth.comp
         (contDiff_fst.smul contDiff_snd))))

 theorem cubicBubblePolynomial_homogeneous {L S A B m : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hm : m≤L)
     (p N : ℕ) (t δ : ℝ) (ε ζ : ℂ) (x : Option (Fin 3) → ℂ) :
     cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε (ζ•x)=
       ζ^L•cubicBubblePolynomial L S m p N t δ ε x := by
   apply bubblePolynomial_homogeneous hm
   intro ζ x
   simp only [Function.comp_def,distinguishedHomogeneousCoordinates_smul]
   ext ki
   simp only [outerPolynomial,Pi.smul_apply,smul_eq_mul,
     liftedSection_homogeneous hAS hS hB]
   ring

 theorem cubicBubblePolynomial_nonzero {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ)
     {ε : ℂ} (hε : ε≠0) {x : Option (Fin 3) → ℂ} (hx : x≠0) :
     cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε x≠0 := by
   exact bubblePolynomial_nonzero L m p N _ hε hx

 theorem cubicBubblePolynomial_scaled {L S A B m p N : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p≤L-S)
     (hm : m≤p) (hN : p≤N) (t δ : ℝ) (ε : ℂ) (z : Fin 3 → ℂ) :
     cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε (complexAffineLift (ε•z))=
       ε^p•cubicBubbleResidual L S m p N t δ ε z := by
   ext i
   rcases i with (i|(j|k))
   · exact congrFun (outerPolynomial_distinguished_factor hAS hS hB hp t δ ε z) i
   · exact congrFun (homogeneousBubble_scaled hm L ε z) j
   · change ε^N*_=ε^p*(ε^(N-p)*_)
     rw [←mul_assoc,←pow_add,Nat.add_sub_of_le hN]

 theorem cubicBubbleResidual_nonzero {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ)
     (ε : ℂ) (z : Fin 3 → ℂ) :
     cubicBubbleResidual (A := A) (B := B) L S m p N t δ ε z≠0 := by
   intro h
   have hh := congrFun h (Sum.inr (Sum.inl (fun _ => none)))
   change homogeneousVeronese m (complexAffineLift z) (fun _ => none)=0 at hh
   simp [homogeneousVeronese] at hh

 theorem cubicBubbleResidual_zero {L S A B m p N : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (t δ : ℝ) (z : Fin 3 → ℂ) :
     cubicBubbleResidual (A := A) (B := B) L S m p N t δ 0 z=
       Sum.elim (0 : TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ)
         (Sum.elim (homogeneousVeronese m (complexAffineLift z))
           (0 : (Fin L → Option (Fin 3)) → ℂ)) := by
   ext i
   rcases i with (i|(j|k))
   · exact congrFun (distinguishedResidualPolynomial_zero hAS hS hB hp t δ z) i
   · rfl
   · simp [cubicBubbleResidual,zero_pow (show N-p≠0 by omega)]

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open scoped BigOperators
section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem phasePowerMap_dot {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    {m : ℕ} (hs : ∀ z,phaseSq (F z)=(phaseSq z)^m) (z v : PlanePhase ι) :
    phaseDot (F z) (fderiv ℝ F z v)=(m:ℝ)*(phaseSq z)^(m-1)*phaseDot z v := by
  have h₁ := (phaseSq_hasFDerivAt (F z)).comp z (hF.differentiable (by simp) z).hasFDerivAt
  have h₂ := (phaseSq_hasFDerivAt z).pow m
  have he : (fun z => phaseSq (F z))=(fun z => (phaseSq z)^m) := funext hs
  change HasFDerivAt (fun x => phaseSq (F x)) _ z at h₁
  rw [he] at h₁
  have hh := congrArg (fun L => L v) (h₁.unique h₂)
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,nsmul_eq_mul] at hh
  nlinarith only [hh]

 theorem phasePowerMap_area {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    {m : ℕ} (hs : ∀ z,phaseSq (F z)=(phaseSq z)^m)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v)) (z v : PlanePhase ι) :
    phaseArea (F z) (fderiv ℝ F z v)=(m:ℝ)*(phaseSq z)^(m-1)*phaseArea z v := by
  have hh := phasePowerMap_dot hF hs z (phaseJ v)
  rw [hJ,phaseDot_J_right,phaseDot_J_right] at hh
  linarith

 theorem homogeneousVeronese_hopf (m : ℕ) (c : ℝ) {z : ι → ℂ} (hz : z≠0) (v : ι → ℂ) :
    hopfPrimitive c (complexCartesian (homogeneousVeronese (m+1) z))
      (fderiv ℝ (fun y => complexCartesian (homogeneousVeronese (m+1) y)) z v)=
      hopfPrimitive ((m+1:ℕ)*c) (complexCartesian z) (complexCartesian v) := by
  let F := cartesianConjugate (homogeneousVeronese (ι := ι) (m+1))
  have hV := homogeneousVeronese_smooth (ι := ι) (m+1)
  have hF : ContDiff ℝ ∞ F := cartesianConjugate_smooth (hV.restrict_scalars ℝ)
  have hs (x : PlanePhase ι) : phaseSq (F x)=(phaseSq x)^(m+1) := by
    change phaseSq (complexCartesian (homogeneousVeronese (m+1) (complexCartesian.symm x)))=_
    rw [homogeneousVeronese_sq,ContinuousLinearEquiv.apply_symm_apply]
  have hJ := cartesianConjugate_J hV
  have ha := phasePowerMap_area hF hs hJ (complexCartesian z) (complexCartesian v)
  have hD : fderiv ℝ F (complexCartesian z) (complexCartesian v)=
      fderiv ℝ (fun y => complexCartesian (homogeneousVeronese (m+1) y)) z v := by
    change fderiv ℝ (fun x : PlanePhase ι => complexCartesian (homogeneousVeronese (m+1) (complexCartesian.symm x))) (complexCartesian z) (complexCartesian v)=_
    have hh := ((complexCartesian.contDiff.comp (hV.restrict_scalars ℝ)).differentiable (by simp) z).hasFDerivAt.comp
      (complexCartesian z) complexCartesian.symm.hasFDerivAt
    simpa only [F,cartesianConjugate,Function.comp_def,ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using congrArg (fun L => L (complexCartesian v)) hh.fderiv
  change phaseArea (complexCartesian (homogeneousVeronese (m+1) z))
    (fderiv ℝ F (complexCartesian z) (complexCartesian v))=_ at ha
  rw [hD] at ha
  have hsz : phaseSq (complexCartesian z)≠0 := (phaseSq_pos (by
    intro h; exact hz (complexCartesian.injective (h.trans (map_zero _).symm)))).ne'
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,homogeneousVeronese_sq,ha,Nat.add_sub_cancel,
    Nat.cast_add,Nat.cast_one]
  rw [pow_succ]
  field_simp [hsz]

end
section

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

 def complexMiddleBlock (z : κ → ℂ) : (ι ⊕ (κ ⊕ ν)) → ℂ :=
   Sum.elim 0 (Sum.elim z 0)

 def complexMiddleBlockCLM : (κ → ℂ) →L[ℝ] ((ι ⊕ (κ ⊕ ν)) → ℂ) :=
   ContinuousLinearMap.pi fun i => match i with
     | Sum.inl _ => 0
     | Sum.inr (Sum.inl k) => ContinuousLinearMap.proj k
     | Sum.inr (Sum.inr _) => 0

omit [Fintype ι] [Fintype κ] [Fintype ν] in
 theorem complexMiddleBlockCLM_apply (z : κ → ℂ) :
     complexMiddleBlockCLM (ι := ι) (ν := ν) z=complexMiddleBlock z := by
   ext i
   rcases i with (i|(k|j)) <;> rfl

 theorem complexMiddleBlock_sq (z : κ → ℂ) :
     phaseSq (complexCartesian (complexMiddleBlock (ι := ι) (ν := ν) z))=
       phaseSq (complexCartesian z) := by
   simp [complexCartesian_sq,complexMiddleBlock,Fintype.sum_sum_type]

 theorem complexMiddleBlock_pairing (z v : κ → ℂ) :
     complexPairing (complexMiddleBlock (ι := ι) (ν := ν) z) (complexMiddleBlock v)=
       complexPairing z v := by
   simp [complexPairing,complexMiddleBlock,Fintype.sum_sum_type]

 theorem complexMiddleBlock_hopf (c : ℝ) (z v : κ → ℂ) :
     hopfPrimitive c (complexCartesian (complexMiddleBlock (ι := ι) (ν := ν) z))
       (complexCartesian (complexMiddleBlock v))=
     hopfPrimitive c (complexCartesian z) (complexCartesian v) := by
   simp only [hopfPrimitive,smul_apply,smul_eq_mul,complexMiddleBlock_sq,
     ←complexPairing_im,complexMiddleBlock_pairing]

 theorem complexMiddleBlock_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
     {F : E → (κ → ℂ)} (hF : ContDiff ℝ ∞ F) (c : ℝ) :
     primitivePullback (hopfPrimitive c)
       (fun z => complexCartesian (complexMiddleBlock (ι := ι) (ν := ν) (F z)))=
     primitivePullback (hopfPrimitive c) (fun z => complexCartesian (F z)) := by
   ext z v
   have hD := complexCartesian.hasFDerivAt.comp z
     ((complexMiddleBlockCLM (ι := ι) (ν := ν)).hasFDerivAt.comp z
       (hF.differentiable (by simp) z).hasFDerivAt)
   have hD' := complexCartesian.hasFDerivAt.comp z (hF.differentiable (by simp) z).hasFDerivAt
   change hopfPrimitive c _ (fderiv ℝ _ z v)=hopfPrimitive c _ (fderiv ℝ _ z v)
   rw [show fderiv ℝ (fun z => complexCartesian (complexMiddleBlock (ι := ι) (ν := ν) (F z))) z=_ from by simpa only [Function.comp_def,complexMiddleBlockCLM_apply] using hD.fderiv,
     show fderiv ℝ (fun z => complexCartesian (F z)) z=_ from hD'.fderiv]
   simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
     complexMiddleBlockCLM_apply] using complexMiddleBlock_hopf (ι := ι) (ν := ν) c (F z) (fderiv ℝ F z v)

 theorem homogeneousVeronese_affinePrimitive (m : ℕ) (c : ℝ) :
     primitivePullback (hopfPrimitive c)
       (fun z : ι → ℂ => complexCartesian (homogeneousVeronese (m+1) (complexAffineLift z)))=
     primitivePullback (affineFSPrimitive ((m+1:ℕ)*c)) complexCartesian := by
   ext z v
   have hV := ((complexCartesian (ι := Fin (m+1) → Option ι)).contDiff.comp
     ((homogeneousVeronese_smooth (m+1)).restrict_scalars ℝ)).differentiable (by simp) (complexAffineLift z)
   have hD := hV.hasFDerivAt.comp z (complexAffineLift_hasFDerivAt z)
   have hz : complexAffineLift z≠0 := by
     intro h
     exact one_ne_zero (congrFun h none)
   change hopfPrimitive c _ (fderiv ℝ _ z v)=_
   rw [show fderiv ℝ (fun z => complexCartesian (homogeneousVeronese (m+1) (complexAffineLift z))) z=_ from hD.fderiv]
   simp only [ContinuousLinearMap.comp_apply]
   change hopfPrimitive c _ (fderiv ℝ (fun y => complexCartesian (homogeneousVeronese (m+1) y))
     (complexAffineLift z) (complexAffineTangent v))=_
   rw [homogeneousVeronese_hopf m c hz]
   rw [←complexAffineLift_fderiv z,affineFSPrimitive_hopf]
   simp only [primitivePullback,ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,
     ContinuousLinearEquiv.coe_coe]

end

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem fibrePrimitivePullback_smooth {α : F → F →L[ℝ] ℝ} {G : ℝ×E → F}
     (hG : ContDiff ℝ ∞ G) (hα : ∀ p,ContDiffAt ℝ ∞ α (G p)) :
     ContDiff ℝ ∞ (fun p : ℝ×E => primitivePullback α (fun x => G (p.1,x)) p.2) := by
   have hβ : ContDiff ℝ ∞ (primitivePullback α G) :=
     contDiff_iff_contDiffAt.mpr (fun p => primitivePullback_smoothAt (hα p) hG.contDiffAt)
   have he (p : ℝ×E) : primitivePullback α (fun x => G (p.1,x)) p.2=
       (primitivePullback α G p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
     have hi : HasFDerivAt (fun x : E => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
       convert! (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1
     have hd := (hG.differentiable (by simp) p).hasFDerivAt.comp p.2 hi
     unfold primitivePullback
     rw [show fderiv ℝ (fun x => G (p.1,x)) p.2=_ from hd.fderiv]
     rfl
   simp_rw [he]
   exact hβ.clm_comp contDiff_const

end PackingSufficiencySupport.Hamiltonian
end

end OAI
