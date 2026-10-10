import Mathlib.Algebra.Polynomial.Eval.Coeff
import OAI.AlgebraicGeometry.PlaneCurves.DividedFamilies
import OAI.AlgebraicGeometry.PlaneCurves.RelationIdeals

namespace OAI

/-!
# Normal frame identities, restricted polynomials, and automorphy
-/

section

/-! Genuine homogeneous coefficient evaluation on actual automorphic coordinate
sections. This is a restriction bridge, not an assertion that the coordinates
embed a plane cubic or that nonzero residue classes remain nonzero. -/
noncomputable section
namespace Nagata.Workers.W17

/-- Evaluating an actual multivariate polynomial in holomorphic coordinate
functions gives a holomorphic function on their common genuine domain. -/
theorem differentiableAt_mvPolynomial_section_eval
    {σ : Type*} {τ L : ℂ} {N : ℤ}
    (X : σ → Nagata.W08.automorphicSections τ N L)
    (T : MvPolynomial σ ℂ) (z : ℂ) (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w => MvPolynomial.eval (fun i => (X i).val w) T) z := by
  induction T using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
      simp only [map_add]
      exact hP.add hQ
  | mul_X P i hP =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact hP.mul ((X i).property.2.1 z hz)

/-- Homogeneous evaluation has the exact multiplied degree and multiplier. -/
theorem homogeneous_section_eval_automorphy
    {σ : Type*} {τ L : ℂ} {N : ℤ}
    (X : σ → Nagata.W08.automorphicSections τ N L)
    (T : MvPolynomial σ ℂ) (n : ℕ) (hT : T.IsHomogeneous n)
    (z : ℂ) (hz : z ≠ 0) :
    MvPolynomial.eval (fun i => (X i).val (τ*z)) T =
      L^n * z^(-(N*(n:ℤ))) * MvPolynomial.eval (fun i => (X i).val z) T := by
  have hcoord : (fun i => (X i).val (τ*z)) =
      fun i => (L*z^(-N)) * (X i).val z := by
    funext i
    exact (X i).property.2.2 z hz
  rw [hcoord, Nagata.W16.homogeneous_eval_scale hT, mul_pow]
  have hp : (z^(-N))^n = z^(-(N*(n:ℤ))) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hp]

/-- The forced-zero extension is an actual section with the precise degree.
The punctured-domain convention is preserved even for constant polynomials. -/
theorem homogeneous_eval_mem_automorphicSections
    {σ : Type*} {τ L : ℂ} {N : ℤ} (hτ : τ ≠ 0)
    (X : σ → Nagata.W08.automorphicSections τ N L)
    (T : MvPolynomial σ ℂ) (n : ℕ) (hT : T.IsHomogeneous n) :
    Nagata.W08.normalizeAtZero (fun z => MvPolynomial.eval (fun i => (X i).val z) T) ∈
      Nagata.W08.automorphicSections τ (N*(n:ℤ)) (L^n) := by
  apply Nagata.W08.normalizeAtZero_mem_automorphicSections hτ
  · intro z hz
    exact differentiableAt_mvPolynomial_section_eval X T z hz
  · intro z hz
    exact homogeneous_section_eval_automorphy X T n hT z hz

end Nagata.Workers.W17

end
end

section

/-! Coefficientwise restriction of an actual ambient normal polynomial.
Zero-extension at the removed origin is additive, not unital; `mapRange`
therefore retains the correct punctured-plane representation for constants. -/
noncomputable section
namespace Nagata.Workers.W17

variable {σ : Type*}

def restrictedCoefficient (X : σ → ℂ → ℂ) (T : MvPolynomial σ ℂ) : ℂ → ℂ :=
  Nagata.W08.normalizeAtZero (fun z => MvPolynomial.eval (fun i => X i z) T)

@[simp] theorem restrictedCoefficient_zero (X : σ → ℂ → ℂ) :
    restrictedCoefficient X 0 = 0 := by
  funext z
  simp [restrictedCoefficient, Nagata.W08.normalizeAtZero]

def restrictedNormalPolynomial (X : σ → ℂ → ℂ)
    (F : Polynomial (MvPolynomial σ ℂ)) : Polynomial (ℂ → ℂ) :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (F.toFinsupp.coeff.mapRange (restrictedCoefficient X) (restrictedCoefficient_zero X)))

@[simp] theorem restrictedNormalPolynomial_coeff
    (X : σ → ℂ → ℂ) (F : Polynomial (MvPolynomial σ ℂ)) (j : ℕ) :
    (restrictedNormalPolynomial X F).coeff j = restrictedCoefficient X (F.coeff j) := rfl

/-- The finite degree bound survives restriction, including at the forced-zero origin. -/
theorem restrictedNormalPolynomial_bound
    (X : σ → ℂ → ℂ) (F : Polynomial (MvPolynomial σ ℂ)) (N : ℕ)
    (hF : ∀ j, N < j → F.coeff j = 0) :
    ∀ j, N < j → (restrictedNormalPolynomial X F).coeff j = 0 := by
  intro j hj
  simp only [restrictedNormalPolynomial_coeff, hF j hj, restrictedCoefficient_zero]

/-- A genuine coefficient evaluation witness proves the restricted polynomial nonzero. -/
theorem restrictedNormalPolynomial_ne_zero
    (X : σ → ℂ → ℂ) (F : Polynomial (MvPolynomial σ ℂ))
    (hw : ∃ j z, z ≠ 0 ∧ MvPolynomial.eval (fun i => X i z) (F.coeff j) ≠ 0) :
    restrictedNormalPolynomial X F ≠ 0 := by
  obtain ⟨j,z,hz,hw⟩ := hw
  intro he
  have hc := congrArg (fun P : Polynomial (ℂ → ℂ) => P.coeff j z) he
  simp only [restrictedNormalPolynomial_coeff, restrictedCoefficient,
    Nagata.W08.normalizeAtZero_of_ne _ hz, Polynomial.coeff_zero, Pi.zero_apply] at hc
  exact hw hc

/-- Evaluation at a genuine punctured-plane point is a unital ring map. -/
def functionEvaluation (z : ℂ) : (ℂ → ℂ) →+* ℂ where
  toFun f := f z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Coefficient restriction commutes with every genuine point evaluation. -/
theorem restrictedNormalPolynomial_map_evaluation
    (X : σ → ℂ → ℂ) (F : Polynomial (MvPolynomial σ ℂ)) (z : ℂ) (hz : z ≠ 0) :
    (restrictedNormalPolynomial X F).map (functionEvaluation z) =
      F.map (MvPolynomial.eval (fun i => X i z)) := by
  ext j
  simp only [Polynomial.coeff_map, restrictedNormalPolynomial_coeff]
  change Nagata.W08.normalizeAtZero (fun z => MvPolynomial.eval (fun i => X i z) (F.coeff j)) z = _
  exact Nagata.W08.normalizeAtZero_of_ne _ hz

/-- Exact scalar expression in the covering frame, needed for the local normal jets. -/
theorem restrictedNormalPolynomial_scalarExpression
    (X : σ → ℂ → ℂ) (F : Polynomial (MvPolynomial σ ℂ))
    (z w : ℂ) (hz : z ≠ 0) :
    Nagata.CoefficientSpaces.scalarExpression (restrictedNormalPolynomial X F) z w =
      (F.map (MvPolynomial.eval (fun i => X i z))).eval w := by
  have he : Nagata.CoefficientSpaces.scalarExpression (restrictedNormalPolynomial X F) z w =
      Polynomial.eval₂ (functionEvaluation z) w (restrictedNormalPolynomial X F) := by
    rw [Polynomial.eval₂_eq_sum]
    rfl
  rw [he, Polynomial.eval₂_eq_eval_map, restrictedNormalPolynomial_map_evaluation X F z hz]

theorem restrictedNormalPolynomial_source_sections
    {τ L : ℂ} (hτ : τ ≠ 0)
    (X : σ → Nagata.W08.automorphicSections τ 3 L)
    (F : Polynomial (MvPolynomial σ ℂ)) (d : ℕ)
    (hhom : ∀ j, (F.coeff j).IsHomogeneous (d-3*j))
    (hbound : ∀ j, d/3 < j → F.coeff j = 0) :
    ∀ j : ℕ, (restrictedNormalPolynomial (fun i => (X i).val) F).coeff j ∈
      Nagata.W08.automorphicSections τ (3*((d:ℤ)-3*(j:ℤ))) (L^((d:ℤ)-3*(j:ℤ))) := by
  intro j
  by_cases hj : j ≤ d/3
  · have hle : 3*j ≤ d := by omega
    have he : ((d-3*j:ℕ):ℤ) = (d:ℤ)-3*(j:ℤ) := by omega
    rw [restrictedNormalPolynomial_coeff, ← he, zpow_natCast]
    exact homogeneous_eval_mem_automorphicSections hτ X (F.coeff j) (d-3*j) (hhom j)
  · rw [restrictedNormalPolynomial_coeff, hbound j (Nat.lt_of_not_ge hj), restrictedCoefficient_zero]
    exact Submodule.zero_mem _

end Nagata.Workers.W17

end
end

section

/-! Exact homogeneous-frame transformation for the actual normal polynomial.
This identity is algebraic and holds in every projective affine chart. -/
noncomputable section
namespace Nagata.Workers.W17
open scoped BigOperators

/-- Evaluation commutes with the actual two-variable projective chart map. -/
theorem eval_directChartHom (c : Fin 3) (T : MvPolynomial (Fin 3) ℂ)
    (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (Nagata.W27.directChartHom c T) =
      MvPolynomial.eval (Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 v) T := by
  have he : (MvPolynomial.eval v).comp (Nagata.W27.directChartHom c) =
      MvPolynomial.eval (Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Nagata.W27.directChartHom]
    · intro a
      by_cases ha : a = c
      · subst a
        simp [Nagata.W27.directChartHom]
      · obtain ⟨b,rfl⟩ := Fin.exists_succAbove_eq ha
        simp [Nagata.W27.directChartHom]
  exact RingHom.congr_fun he T

/-- Normalizing a nonzero chart coordinate reconstructs the genuine cone vector. -/
theorem scaled_chart_vector (c : Fin 3) (x : Fin 3 → ℂ) (hx : x c ≠ 0) :
    (x c) • Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 (fun b => x (c.succAbove b) / x c) = x := by
  funext a
  by_cases ha : a = c
  · subst a
    simp
  · obtain ⟨b,rfl⟩ := Fin.exists_succAbove_eq ha
    simp [smul_eq_mul, mul_div_cancel₀ _ hx]

/-- The homogeneous normal polynomial transforms by weight d, and its fiber
coordinate by weight k. This supplies the exact covering-frame scalar identity. -/
theorem normal_polynomial_frame_identity
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (c : Fin 3) (x : Fin 3 → ℂ) (hx : x c ≠ 0) (w : ℂ) :
    (∑ α ∈ I, w^j α * MvPolynomial.eval x (T α)) =
      (x c)^d * ∑ α ∈ I, (w/(x c)^k)^j α *
        MvPolynomial.eval (fun b => x (c.succAbove b)/x c)
          (Nagata.W27.directChartHom c (T α)) := by
  have he := Nagata.W16.AssociatedBundle.weightedEval_scale I T j d k hhom hbound
    (Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 (fun b => x (c.succAbove b)/x c)) (w/(x c)^k) (x c)
  rw [scaled_chart_vector c x hx, mul_div_cancel₀ w (pow_ne_zero k hx)] at he
  simpa only [Nagata.W16.AssociatedBundle.weightedEval, eval_directChartHom,
    mul_comm] using he

end Nagata.Workers.W17

end
end

section

namespace Nagata.Workers.W17

/-- The actual restriction of a polynomial with nonzero residue remains nonzero
once the actual ideal of coordinate relations is identified with the equation. -/
theorem restrictedNormalPolynomial_ne_zero_of_principal_relations
    (X : Fin 3 → ℂ → ℂ) (G : MvPolynomial (Fin 3) ℂ)
    (hrelations : Nagata.Workers.W25.polynomialRelationIdeal X = Ideal.span ({G} : Set _))
    (F : Polynomial (MvPolynomial (Fin 3) ℂ))
    (hF : F.map (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))) ≠ 0) :
    restrictedNormalPolynomial X F ≠ 0 := by
  intro hz
  apply hF
  ext j
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← hrelations, Nagata.Workers.W25.mem_polynomialRelationIdeal]
  intro z hz0
  have hc := congrArg (fun P : Polynomial (ℂ → ℂ) => P.coeff j z) hz
  simpa only [restrictedNormalPolynomial_coeff, restrictedCoefficient,
    Nagata.W08.normalizeAtZero_of_ne _ hz0, Polynomial.coeff_zero, Pi.zero_apply] using hc

end Nagata.Workers.W17

end

section

/-! Actual affine-coordinate swap for the alternative smooth normal direction.
This is the algebraic transport needed when the nonzero normal partial is X0
rather than X1 in the fixed ordered projective chart. -/
noncomputable section
namespace Nagata.Workers.W17
open Nagata.Workers.W28

/-- The genuine polynomial-ring equivalence exchanging the two affine variables. -/
def affineSwap : MvPolynomial (Fin 2) ℂ ≃+* MvPolynomial (Fin 2) ℂ :=
  (MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 2) 1)).toRingEquiv

theorem eval_affineSwap (P : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    planePolynomialEval (affineSwap P) p = planePolynomialEval P p.swap := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then p.1 else p.2)
    (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P) = _
  rw [MvPolynomial.eval_rename]
  apply congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval v P)
  funext i
  fin_cases i <;> simp

/-- Every actual ordinary multiplicity condition survives the coordinate swap. -/
theorem order_affineSwap_iff (P : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) (m : ℕ) :
    Nagata.AffineMultiplicity.orderAtLeast
      (fun i : Fin 2 => if i = 0 then p.2 else p.1) m (affineSwap P) ↔
    Nagata.AffineMultiplicity.orderAtLeast
      (fun i : Fin 2 => if i = 0 then p.1 else p.2) m P := by
  apply Nagata.AffineMultiplicity.orderAtLeast_equiv_iff _ _ affineSwap
  intro Q
  exact eval_affineSwap Q p.swap

/-- Swapping the actual variables commutes with the finite G-adic family. -/
theorem affineSwap_factoredPlaneFamily
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (G : MvPolynomial (Fin 2) ℂ) (s : ℂ) :
    affineSwap (factoredPlaneFamily I j R G s) =
      factoredPlaneFamily I j (fun α => affineSwap (R α)) (affineSwap G) s := by
  simp [factoredPlaneFamily, affineSwap, map_sum, map_mul, map_pow]

/-- The alternative normal partial becomes the standard one after swapping. -/
theorem partialY_affineSwap (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    planePolynomialEval (MvPolynomial.pderiv 1 (affineSwap G)) p.swap =
      planePolynomialEval (MvPolynomial.pderiv 0 G) p := by
  have hd := MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2) G
  have hd' : MvPolynomial.pderiv 1 (affineSwap G) = affineSwap (MvPolynomial.pderiv 0 G) := by
    simpa [affineSwap] using hd
  rw [hd', eval_affineSwap]
  rfl

/-- The other derivative coordinate is exchanged at the same actual point. -/
theorem partialX_affineSwap (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    planePolynomialEval (MvPolynomial.pderiv 0 (affineSwap G)) p.swap =
      planePolynomialEval (MvPolynomial.pderiv 1 G) p := by
  have hd := MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective (1 : Fin 2) G
  have hd' : MvPolynomial.pderiv 0 (affineSwap G) = affineSwap (MvPolynomial.pderiv 1 G) := by
    simpa [affineSwap] using hd
  rw [hd', eval_affineSwap]
  rfl

/-- The actual normal displacement is unchanged when both variables and
velocity coordinates are swapped. -/
theorem polynomialGradient_affineSwap (G : MvPolynomial (Fin 2) ℂ) (p V : ComplexPlane) :
    polynomialGradient (affineSwap G) p.swap V.swap = polynomialGradient G p V := by
  change planePolynomialEval (MvPolynomial.pderiv 0 (affineSwap G)) p.swap * V.2 +
      planePolynomialEval (MvPolynomial.pderiv 1 (affineSwap G)) p.swap * V.1 =
    planePolynomialEval (MvPolynomial.pderiv 0 G) p * V.1 +
      planePolynomialEval (MvPolynomial.pderiv 1 G) p * V.2
  rw [partialX_affineSwap, partialY_affineSwap, add_comm]

/-- Swapping commutes with the actual affine-linear moving point. -/
theorem swap_affine_motion (p V : ComplexPlane) (s : ℂ) :
    (p+s • V).swap = p.swap+s • V.swap := rfl

end Nagata.Workers.W17

end
end

end OAI
