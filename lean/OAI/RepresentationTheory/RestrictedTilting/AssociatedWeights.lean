import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.AssociatedLattices
import OAI.RepresentationTheory.RestrictedTilting.TiltingBounds

namespace OAI

/-! Character transfer, numerator weights and associated-origin tilting. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
universe u v w
variable {k : Type u} [Field k] {G : Type v} [Monoid G]
variable {M : Type w} [AddCommGroup M] [Module k M]

noncomputable def characterFiniteSubmodule (ρ : Representation k G M) : Submodule k M where
  carrier := {v | ∃ c : (G →* k) →₀ M, ∀ g, ρ g v = characterEvaluation g c}
  zero_mem' := ⟨0, by intro g; simp⟩
  add_mem' := by
    rintro v w ⟨c,hc⟩ ⟨d,hd⟩
    exact ⟨c+d, fun g => by rw [map_add, hc, hd, map_add]⟩
  smul_mem' := by
    rintro a v ⟨c,hc⟩
    exact ⟨a • c, fun g => by rw [map_smul, hc, map_smul]⟩

lemma characterFinite_eigen (ρ : Representation k G M) (χ : G →* k) (v : M)
    (hv : ∀ g, ρ g v = χ g • v) : v ∈ characterFiniteSubmodule ρ := by
  classical
  refine ⟨Finsupp.single χ v, fun g => ?_⟩
  simpa [characterEvaluation_apply] using hv g

lemma characterFinite_map {N : Type*} [AddCommGroup N] [Module k N]
    (ρ : Representation k G M) (σ : Representation k G N) (f : M →ₗ[k] N)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) {v : M}
    (hv : v ∈ characterFiniteSubmodule ρ) : f v ∈ characterFiniteSubmodule σ := by
  classical
  obtain ⟨c,hc⟩ := hv
  refine ⟨c.mapRange f f.map_zero, fun g => ?_⟩
  rw [characterEvaluation_apply, Finsupp.sum_mapRange_index (fun _ => smul_zero _)]
  rw [← hf, hc, characterEvaluation_apply]
  simp only [Finsupp.sum, map_sum, map_smul]

lemma HasCharacterExpansions.of_surjective {N : Type*} [AddCommGroup N] [Module k N]
    (ρ : Representation k G M) (σ : Representation k G N) (f : M →ₗ[k] N)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (hs : Function.Surjective f)
    (hρ : HasCharacterExpansions ρ) : HasCharacterExpansions σ := by
  intro w
  obtain ⟨v,rfl⟩ := hs w
  exact characterFinite_map ρ σ f hf (hρ v)

lemma HasCharacterExpansions.of_injective {N : Type*} [AddCommGroup N] [Module k N]
    (ρ : Representation k G M) (σ : Representation k G N) (f : M →ₗ[k] N)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (hi : Function.Injective f)
    (hσ : HasCharacterExpansions σ) : HasCharacterExpansions ρ := by
  classical
  obtain ⟨s,hs⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  have hsf (v : M) : s (f v) = v := LinearMap.congr_fun hs v
  intro v
  obtain ⟨c,hc⟩ := hσ (f v)
  refine ⟨c.mapRange s s.map_zero, fun g => ?_⟩
  rw [Finsupp.sum_mapRange_index (fun _ => smul_zero _)]
  calc
    ρ g v = s (σ g (f v)) := by rw [← hf, hsf]
    _ = c.sum (fun χ x => χ g • s x) := by
      rw [hc]
      simp only [Finsupp.sum, map_sum, map_smul]

end

section
open scoped BigOperators
universe u
variable (k : Type u) [Field k]
noncomputable def diagonalPolynomialScale {σ : Type*} (c : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (c i) * MvPolynomial.X i)

lemma diagonalPolynomialScale_monomial {σ : Type*} [Fintype σ]
    (c : σ → k) (d : σ →₀ ℕ) (r : k) :
    diagonalPolynomialScale k c (MvPolynomial.monomial d r) =
      MvPolynomial.monomial d (r * ∏ i, c i ^ d i) := by
  classical
  change MvPolynomial.eval₂ MvPolynomial.C
    (fun i => MvPolynomial.C (c i) * MvPolynomial.X i) (MvPolynomial.monomial d r) = _
  rw [MvPolynomial.eval₂_monomial, Finsupp.prod_fintype]
  · simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    · simp only [map_mul, mul_assoc]
    · intro i; simp
  · intro i
    simp

lemma diagonalPolynomialScale_coeff {σ : Type*} [Fintype σ]
    (c : σ → k) (P : MvPolynomial σ k) (d : σ →₀ ℕ) :
    (diagonalPolynomialScale k c P).coeff d = P.coeff d * ∏ i, c i ^ d i := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e r =>
    rw [diagonalPolynomialScale_monomial]
    simp only [MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst e
      rfl
    · simp
  | add P Q hP hQ =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ, add_mul]

noncomputable def planeTorusPolynomial (a : kˣ) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  diagonalPolynomialScale k ![(a⁻¹ : kˣ).val, a.val]

lemma planeTorusPolynomial_coeff (a : kˣ) (P : MvPolynomial (Fin 2) k)
    (d : Fin 2 →₀ ℕ) :
    (planeTorusPolynomial k a P).coeff d =
      P.coeff d * integerCharacter k ((d 1 : ℤ) - d 0) a := by
  rw [planeTorusPolynomial, diagonalPolynomialScale_coeff]
  congr 1
  simp [Fin.prod_univ_two, integerCharacter, zpow_sub, mul_comm]

 
lemma positive_plane_weight_dvd [Infinite k] (P : MvPolynomial (Fin 2) k)
    (h : ℤ) (hh : 0 < h)
    (hP : ∀ a : kˣ, planeTorusPolynomial k a P = integerCharacter k h a • P) :
    MvPolynomial.X 1 ∣ P := by
  classical
  conv_rhs => rw [MvPolynomial.as_sum P]
  apply Finset.dvd_sum
  intro d hd
  rw [MvPolynomial.X_dvd_monomial]
  right
  intro hd1
  have hc : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have he : (d 1 : ℤ) - d 0 = h := by
    apply integerCharacter_injective k
    ext a
    have ha := congrArg (fun polynomial : MvPolynomial (Fin 2) k => polynomial.coeff d) (hP a)
    rw [planeTorusPolynomial_coeff, MvPolynomial.coeff_smul, smul_eq_mul] at ha
    exact mul_left_cancel₀ hc (ha.trans (mul_comm _ _))
  rw [hd1] at he
  omega

end

section
open scoped BigOperators Matrix Kronecker
universe u
variable (k : Type u) [Field k]

def coordinateCharacter (ij : Fin 2 × Fin 2) : kˣ →* k :=
  if ij.1 = 0 then inverseUnitCharacter k else Units.coeHom k

lemma linearChange_diagonal {σ : Type*} [Fintype σ] [DecidableEq σ] (c : σ → k) :
    linearChange (Matrix.diagonal c) = diagonalPolynomialScale k c := by
  ext i : 1
  simp [linearChange, diagonalPolynomialScale, Matrix.diagonal_apply, apply_ite]

lemma leftCoordinateMatrix_diagonal (a : kˣ) :
    leftCoordinateMatrix k (diagonalTorus k a) =
      Matrix.diagonal (fun ij => coordinateCharacter k ij a) := by
  ext ⟨i,j⟩ ⟨l,m⟩
  change (diagonalTorus k a)⁻¹ l i * (1 : Matrix (Fin 2) (Fin 2) k) j m = _
  rw [← map_inv]
  change !![((↑a⁻¹ : k)), 0; 0, ((↑(a⁻¹)⁻¹ : k))] l i *
    (1 : Matrix (Fin 2) (Fin 2) k) j m = _
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
    simp [coordinateCharacter, inverseUnitCharacter]

lemma coordinatePolynomial_torus_scale (a : kˣ) (P : MvPolynomial (Fin 2 × Fin 2) k) :
    coordinatePolynomialRepresentation k (diagonalTorus k a) P =
      diagonalPolynomialScale k (fun ij => coordinateCharacter k ij a) P := by
  change linearChange (leftCoordinateMatrix k (diagonalTorus k a)) P = _
  rw [leftCoordinateMatrix_diagonal, linearChange_diagonal]

lemma coordinatePolynomial_characters : HasCharacterExpansions
    ((coordinatePolynomialRepresentation k).comp (diagonalTorus k)) := by
  intro P
  change P ∈ characterFiniteSubmodule _
  induction P using MvPolynomial.induction_on' with
  | monomial d r =>
    apply characterFinite_eigen _ (∏ ij, coordinateCharacter k ij ^ d ij)
    intro a
    change coordinatePolynomialRepresentation k (diagonalTorus k a)
      (MvPolynomial.monomial d r) = _
    rw [coordinatePolynomial_torus_scale, diagonalPolynomialScale_monomial]
    simp only [MonoidHom.finsetProd_apply, MonoidHom.pow_apply, MvPolynomial.smul_monomial,
      smul_eq_mul, mul_comm]
  | add P Q hP hQ => exact (characterFiniteSubmodule _).add_mem hP hQ

lemma regularSL2_characters : HasCharacterExpansions
    ((regularSL2Representation k).comp (diagonalTorus k)) := by
  apply HasCharacterExpansions.of_surjective
    ((coordinatePolynomialRepresentation k).comp (diagonalTorus k))
    ((regularSL2Representation k).comp (diagonalTorus k))
    (coordinateToRegular k) _ (coordinateToRegular_surjective k)
    (coordinatePolynomial_characters k)
  intro a P
  apply Subtype.ext
  funext h
  exact coordinatePolynomial_evaluation k (diagonalTorus k a) h P

lemma regularVector_characters (ι : Type u) [Fintype ι] [DecidableEq ι] :
    HasCharacterExpansions ((regularVectorRepresentation k ι).comp (diagonalTorus k)) := by
  intro f
  let ei (i : ι) : regularSL2Functions k →ₗ[k] (ι → regularSL2Functions k) :=
    LinearMap.single k (fun _ : ι => regularSL2Functions k) i
  have hsum : ∑ i, ei i (f i) = f := by ext i; simp [ei]
  change f ∈ characterFiniteSubmodule _
  rw [← hsum]
  apply Submodule.sum_mem
  intro j _
  apply characterFinite_map ((regularSL2Representation k).comp (diagonalTorus k))
    _ (ei j) _ (regularSL2_characters k (f j))
  intro a v
  funext i
  change (ei j (regularSL2Representation k (diagonalTorus k a) v)) i =
    regularSL2Representation k (diagonalTorus k a) (ei j v i)
  simp only [ei, LinearMap.single_apply, Pi.single_apply]
  split_ifs <;> simp_all

 

lemma associatedSections_characters (ι : Type u) [Fintype ι] [DecidableEq ι]
    (ρ : Representation k (Multiplicative k) (ι → k)) :
    HasCharacterExpansions (k := k) (M := associatedSectionsSubmodule k ι ρ)
      ((associatedSectionsRepresentation k ι ρ).comp (diagonalTorus k)) := by
  exact HasCharacterExpansions.of_injective _ _ (associatedSectionsSubmodule k ι ρ).subtype
    (fun _ _ => rfl) (associatedSectionsSubmodule k ι ρ).injective_subtype
    (regularVector_characters k ι)

end

section
universe u
variable (k : Type u) [Field k] [Infinite k]

noncomputable def planeTorusScale (a : kˣ) (x : planeTorusPoints k) : planeTorusPoints k :=
  ⟨![(↑a⁻¹ : k) * x.val 0, (a : k) * x.val 1], by
    intro i
    fin_cases i
    · exact mul_ne_zero (Units.ne_zero a⁻¹) (x.property 0)
    · exact mul_ne_zero (Units.ne_zero a) (x.property 1)⟩

omit [Infinite k] in
lemma planeTorusScale_coordinate (a : kˣ) (x : planeTorusPoints k) (i : Fin 2) :
    (planeTorusScale k a x).val i = ![(↑a⁻¹ : k), (a : k)] i * x.val i := by
  fin_cases i <;> rfl

omit [Infinite k] in
lemma diagonalPolynomialScale_eval {σ : Type*} (c x : σ → k) (P : MvPolynomial σ k) :
    MvPolynomial.eval x (diagonalPolynomialScale k c P) =
      MvPolynomial.eval (fun i => c i * x i) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [diagonalPolynomialScale]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul]
    rw [hP]
    congr 1
    simp [diagonalPolynomialScale]

omit [Infinite k] in
lemma planeTorusPolynomial_eval (a : kˣ) (x : planeTorusPoints k)
    (P : MvPolynomial (Fin 2) k) :
    MvPolynomial.eval x.val (planeTorusPolynomial k a P) =
      MvPolynomial.eval (planeTorusScale k a x).val P := by
  rw [planeTorusPolynomial, diagonalPolynomialScale_eval]
  have hx : (fun i => ![(↑a⁻¹ : k), (a : k)] i * x.val i) =
      (planeTorusScale k a x).val := by
    funext i
    exact (planeTorusScale_coordinate k a x i).symm
  rw [hx]

omit [Infinite k] in
lemma planeXSection_torus (a : kˣ) (x : planeTorusPoints k) :
    (diagonalTorus k a)⁻¹ * planeXSection k x = planeXSection k (planeTorusScale k a x) := by
  rw [← map_inv]
  apply Subtype.ext
  change !![(↑a⁻¹ : k), 0; 0, (↑(a⁻¹)⁻¹ : k)] *
    !![x.val 0, 0; x.val 1, (x.val 0)⁻¹] =
      !![(↑a⁻¹ : k) * x.val 0, 0; (a : k) * x.val 1, ((↑a⁻¹ : k) * x.val 0)⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))

omit [Fintype ι] [DecidableEq ι] in
lemma associatedXChart_torus_evaluation (a : kˣ) (f : associatedSectionsSubmodule k ι ρ)
    (x : planeTorusPoints k) :
    (fun i => planeChartEvaluation k 0
      (associatedXChart k ι ρ (associatedSectionsRepresentation k ι ρ (diagonalTorus k a) f) i) x) =
    (fun i => planeChartEvaluation k 0 (associatedXChart k ι ρ f i) (planeTorusScale k a x)) := by
  rw [associatedXChart_evaluation, associatedXChart_evaluation]
  change regularVectorEvaluation k ι ((diagonalTorus k a)⁻¹ * planeXSection k x) f.val = _
  rw [planeXSection_torus]

omit [Fintype ι] [DecidableEq ι] in
lemma associatedNumerator_weight (d : ℕ) (f : associatedSectionsSubmodule k ι ρ)
    (F : ι → MvPolynomial (Fin 2) k)
    (hF : ∀ i, algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k 0) (F i) =
      planeChartCoordinate k 0 0 ^ d * associatedXChart k ι ρ f i)
    (h : ℤ) (hf : ∀ a : kˣ, associatedSectionsRepresentation k ι ρ (diagonalTorus k a) f =
      integerCharacter k h a • f) (i : ι) (a : kˣ) :
    planeTorusPolynomial k a (F i) = integerCharacter k (h-d) a • F i := by
  apply planeTorusEvaluation_injective k
  funext x
  simp only [planeTorusEvaluation_apply]
  rw [planeTorusPolynomial_eval, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
    associatedNumerator_evaluation k ι ρ d f F hF,
    associatedNumerator_evaluation k ι ρ d f F hF]
  have hx := congrFun (associatedXChart_torus_evaluation k ι ρ a f x) i
  rw [hf, map_smul] at hx
  simp only [Pi.smul_apply, map_smul] at hx
  change integerCharacter k h a * planeChartEvaluation k 0 (associatedXChart k ι ρ f i) x =
    planeChartEvaluation k 0 (associatedXChart k ι ρ f i) (planeTorusScale k a x) at hx
  rw [← hx]
  change ((↑a⁻¹ : k) * x.val 0)^d *
    (integerCharacter k h a * planeChartEvaluation k 0 (associatedXChart k ι ρ f i) x) = _
  simp only [integerCharacter, MonoidHom.comp_apply, zpowGroupHom_apply,
    Units.coeHom_apply, zpow_sub, zpow_natCast, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, mul_pow, inv_pow]
  ring

end

section GenericDivision
variable {R K ι : Type*} [CommRing R] [Field K] [Algebra R K]

lemma gluedLattice_div_y (x y : R) (T : (ι → K) ≃ₗ[K] (ι → K))
    (hy : algebraMap R K y ≠ 0) {z : ι → K} (hz : z ∈ gluedLattice x y T)
    (hx : (algebraMap R K y)⁻¹ • z ∈ powerLocalization x (coordinateLattice (R := R) (K := K) (ι := ι))) :
    (algebraMap R K y)⁻¹ • z ∈ gluedLattice x y T := by
  refine ⟨hx, ?_⟩
  change z ∈ powerLocalization x (coordinateLattice (R := R)) ∧
    z ∈ (powerLocalization y (coordinateLattice (R := R))).map (T.toLinearMap.restrictScalars R) at hz
  obtain ⟨w,hw,he⟩ := hz.2
  refine ⟨(algebraMap R K y)⁻¹ • w,
    powerLocalization_div (K := K) y (coordinateLattice (R := R) (K := K) (ι := ι)) hy hw, ?_⟩
  change T ((algebraMap R K y)⁻¹ • w) = (algebraMap R K y)⁻¹ • z
  change T w = z at he
  rw [map_smul, he]

end GenericDivision

section
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))

include hP in
lemma associated_y_divisible (d : ℕ) (f : associatedSectionsSubmodule k ι ρ)
    (F : ι → MvPolynomial (Fin 2) k)
    (hF : ∀ i, algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k 0) (F i) =
      planeChartCoordinate k 0 0 ^ d * associatedXChart k ι ρ f i)
    (hdiv : ∀ i, MvPolynomial.X 1 ∣ F i) :
    ∃ f' : associatedSectionsSubmodule k ι ρ, f = (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • f' := by
  let y : planeFractionField k :=
    algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) (MvPolynomial.X 1)
  have hy : y ≠ 0 := planeFractionCoordinate_ne_zero k 1
  have hx : y⁻¹ • associatedFractionChart k ι ρ f ∈
      powerLocalization (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) coordinateLattice := by
    refine ⟨d, (mem_coordinateLattice _).mpr fun i => ?_⟩
    obtain ⟨Q,hQ⟩ := hdiv i
    refine ⟨Q, ?_⟩
    have hi := congrArg (planeChartToFraction k 0) (hF i)
    rw [planeChartToFraction_algebraMap, hQ, map_mul, map_mul, map_pow,
      planeChartCoordinate, planeChartToFraction_algebraMap] at hi
    change y * algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) Q =
      algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) (MvPolynomial.X 0)^d *
        associatedFractionChart k ι ρ f i at hi
    simp only [Pi.smul_apply, Algebra.smul_def, map_pow]
    change algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) Q =
      algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) (MvPolynomial.X 0)^d *
        (y⁻¹ * associatedFractionChart k ι ρ f i)
    calc
      _ = y⁻¹ * (y * algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) Q) := by
        rw [← mul_assoc, inv_mul_cancel₀ hy, one_mul]
      _ = _ := by rw [hi]; ring
  have hz := gluedLattice_div_y (MvPolynomial.X 0 : MvPolynomial (Fin 2) k)
    (MvPolynomial.X 1) (planeGlobalTransition k P (associatedPolynomial_zero k ι ρ P hP)
      (associatedPolynomial_add k ι ρ P hP)) hy
    (associatedFractionChart_mem k ι ρ P hP f) hx
  obtain ⟨f',hf'⟩ := associatedLatticeMap_surjective k ι ρ P hP ⟨_,hz⟩
  have he : associatedFractionChart k ι ρ f' = y⁻¹ • associatedFractionChart k ι ρ f :=
    congrArg Subtype.val hf'
  refine ⟨f', associatedFractionChart_injective k ι ρ ?_⟩
  rw [map_smul, he]
  rw [← algebraMap_smul (planeFractionField k) (MvPolynomial.X 1)]
  change associatedFractionChart k ι ρ f = y • (y⁻¹ • associatedFractionChart k ι ρ f)
  rw [smul_inv_smul₀ hy]


include hP in
lemma associatedOrigin_weight_upper (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
    (n : ℤ) (hn : (d : ℤ) < n) (v : (associatedOriginRep k ι ρ).V)
    (hv : ∀ a : kˣ, (associatedOriginRep k ι ρ).ρ (diagonalTorus k a) v =
      integerCharacter k n a • v) : v = 0 := by
  let Q : (associatedSectionsSubmodule k ι ρ) →ₗ[k] (associatedOriginRep k ι ρ).V :=
    (associatedOriginRelations k ι ρ).mkQ
  obtain ⟨f,hfv,hf⟩ := eigenvector_lift
    ((associatedSectionsRepresentation k ι ρ).comp (diagonalTorus k))
    ((associatedOriginRep k ι ρ).ρ.comp (diagonalTorus k))
    (associatedSections_characters k ι ρ) Q (fun _ _ => rfl)
    (associatedOriginRelations k ι ρ).mkQ_surjective (integerCharacter k n) v hv
  obtain ⟨F,hF⟩ := associatedNumerator_exists k ι ρ P hP d hd f
  have hdiv (i : ι) : MvPolynomial.X 1 ∣ F i := by
    apply positive_plane_weight_dvd k (F i) (n-d) (by omega)
    exact associatedNumerator_weight k ι ρ d f F hF n hf i
  obtain ⟨f',hff'⟩ := associated_y_divisible k ι ρ P hP d f F hF hdiv
  have hmem : f ∈ associatedOriginRelations k ι ρ := by
    rw [hff']
    exact associatedOrigin_coordinate_mem k ι ρ 1 f'
  rw [← hfv]
  exact (Submodule.Quotient.mk_eq_zero (associatedOriginRelations k ι ρ)).mpr hmem

end

section
universe u
variable (k : Type u) [Field k]

variable [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))

 

theorem associatedOrigin_weights
    (P : Matrix ι ι (Polynomial k))
    (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
    (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    HasWeightsBetween (associatedOriginRep k ι ρ).ρ (-(d : ℤ)) d :=
  weights_between_of_upper k _ d (associatedOrigin_weight_upper k ι ρ P hP d hd)

end

universe u
variable (k : Type u) [Field k] [Infinite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)

noncomputable def associatedOriginFD : FDRep k (SL2 k) := by
  let : Module.Finite k (associatedOriginRep k ι ρ).V := associatedOrigin_finite k ι ρ P hP d hd
  exact FDRep.of (associatedOriginRep k ι ρ).ρ

 

theorem associatedOrigin_tilting (m : ℕ) (hm : d < p^(m+1)) :
    IsTilting k (steinberg k p m ⊗ associatedOriginFD k ι ρ P hP d hd) := by
  apply bounded_weights_tilting k p m d hm
  · exact associatedOrigin_rational k ι ρ
  · exact associatedOrigin_weights k ι ρ P hP d hd
end FiberFunctorProof
end

end OAI
