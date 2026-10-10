import OAI.Algebra.Determinantal.DeterminantFields

namespace OAI

namespace PermanentBorder.DeterminantFiberScheme
open Polynomial
universe u
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

noncomputable def pencil (θ : Fin n → R) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R[X][X] :=
  (X : R[X][X]) • 1 +
    (((X : R[X]) • (Matrix.diagonal θ).map C + A.map C).map C)

theorem map_pencil (f : R →+* S) (θ : Fin n → R)
    (A : Matrix (Fin n) (Fin n) R) :
    (pencil θ A).map (Bivariate.map f) = pencil (f ∘ θ) (A.map f) := by
  classical
  ext i j
  dsimp [pencil, Bivariate.map, Matrix.map, Matrix.smul_apply, Matrix.add_apply]
  by_cases h : i = j
  · subst j
    simp [Polynomial.coe_mapRingHom]
  · simp [h, Polynomial.coe_mapRingHom]

theorem map_determinant (f : R →+* S) (θ : Fin n → R)
    (A : Matrix (Fin n) (Fin n) R) :
    Bivariate.map f (pencil θ A).det = (pencil (f ∘ θ) (A.map f)).det := by
  rw [RingHom.map_det]
  change ((pencil θ A).map (Bivariate.map f)).det = _
  rw [map_pencil]

theorem determinant_ne_zero [Nontrivial R] (θ : Fin n → R)
    (A : Matrix (Fin n) (Fin n) R) : (pencil θ A).det ≠ 0 := by
  have hc : (pencil θ A).det.coeff n = 1 := by
    have hm : (1 : Matrix (Fin n) (Fin n) R[X]).map C = 1 := C.mapMatrix.map_one
    simpa only [pencil, hm, Fintype.card_fin, Matrix.det_one] using
      coeff_det_X_add_C_card (1 : Matrix (Fin n) (Fin n) R[X])
        ((X : R[X]) • (Matrix.diagonal θ).map C + A.map C)
  intro hz
  rw [hz, coeff_zero] at hc
  exact zero_ne_one hc

variable (K : Type u) [Field K]
abbrev PolynomialRing (n : ℕ) := MvPolynomial (Fin n × Fin n) K
noncomputable def universalMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (PolynomialRing K n) :=
  fun i j => MvPolynomial.X (i,j)

noncomputable def fiberIdeal {n : ℕ} (θ : Fin n → K) (p : K[X][X]) :
    Ideal (PolynomialRing K n) :=
  Ideal.span (Set.range (fun ab : ℕ × ℕ =>
    (((pencil (MvPolynomial.C ∘ θ) (universalMatrix K n)).det -
      Bivariate.map MvPolynomial.C p).coeff ab.1).coeff ab.2))

abbrev CoordinateRing {n : ℕ} (θ : Fin n → K) (p : K[X][X]) :=
  PolynomialRing K n ⧸ fiberIdeal K θ p

variable {K}

theorem field_point_equation {n : ℕ} (θ : Fin n → K) (p : K[X][X])
    {L : Type u} [Field L] [Algebra K L]
    (f : CoordinateRing K θ p →ₐ[K] L) :
    let g := f.comp (Ideal.Quotient.mkₐ K (fiberIdeal K θ p))
    (pencil (algebraMap K L ∘ θ) ((universalMatrix K n).map g)).det =
      Bivariate.map (algebraMap K L) p := by
  classical
  intro g
  have hz (a b : ℕ) : g
      ((((pencil (MvPolynomial.C ∘ θ) (universalMatrix K n)).det -
        Bivariate.map MvPolynomial.C p).coeff a).coeff b) = 0 := by
    change f (Ideal.Quotient.mk _ _) = 0
    have hm : ((((pencil (MvPolynomial.C ∘ θ) (universalMatrix K n)).det -
        Bivariate.map MvPolynomial.C p).coeff a).coeff b) ∈ fiberIdeal K θ p :=
      Ideal.subset_span (Set.mem_range_self (a,b))
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, _root_.map_zero]
  have hmap : Bivariate.map g.toRingHom
      ((pencil (MvPolynomial.C ∘ θ) (universalMatrix K n)).det -
        Bivariate.map MvPolynomial.C p) = 0 := by
    ext a b
    simp only [Bivariate.map, Polynomial.coe_mapRingHom,
      Polynomial.coeff_map, Polynomial.coeff_zero]
    exact hz a b
  have heq := sub_eq_zero.mp ((RingHom.map_sub (Bivariate.map g.toRingHom)
    (pencil (MvPolynomial.C ∘ θ) (universalMatrix K n)).det
    (Bivariate.map MvPolynomial.C p)).symm.trans hmap)
  have hθ : g.toRingHom ∘ (MvPolynomial.C ∘ θ) = algebraMap K L ∘ θ := by
    ext i
    exact g.commutes (θ i)
  have hp : Bivariate.map g.toRingHom (Bivariate.map MvPolynomial.C p) =
      Bivariate.map (algebraMap K L) p := by
    ext a b
    simp only [Bivariate.map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    exact g.commutes _
  rw [map_determinant,hθ,hp] at heq
  exact heq

theorem range_le_of_variables_mem {σ : Type*} {L : Type u} [Field L] [Algebra K L]
    (f : MvPolynomial σ K →ₐ[K] L) (F : IntermediateField K L)
    (h : ∀ i, f (MvPolynomial.X i) ∈ F) : f.range ≤ F.toSubalgebra := by
  rintro y ⟨p, rfl⟩
  change f p ∈ F
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.algHom_C] using F.algebraMap_mem c
  | add p q hp hq => simpa only [map_add] using F.add_mem hp hq
  | mul_X p i hp => simpa only [map_mul] using F.mul_mem hp (h i)

theorem field_image_trdeg_le [Infinite K] {k : ℕ} (hk : 0 < k)
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ) (p : K[X][X])
    (L : Type u) [Field L] [Algebra K L]
    (f : CoordinateRing K θ p →ₐ[K] L) :
    Algebra.trdeg K f.range ≤ ((k+1).choose 2 : Cardinal) := by
  classical
  let Ω := AlgebraicClosure L
  let ι : L →ₐ[K] Ω := IsScalarTower.toAlgHom K L Ω
  let f' := ι.comp f
  let g := f'.comp (Ideal.Quotient.mkₐ K (fiberIdeal K θ p))
  let A := (universalMatrix K (k+1)).map g
  have he : (pencil (algebraMap K Ω ∘ θ) A).det =
      Bivariate.map (algebraMap K Ω) p := field_point_equation θ p f'
  have hp : p ≠ 0 := by
    intro hp
    rw [hp, _root_.map_zero] at he
    exact determinant_ne_zero _ _ he
  obtain ⟨F,hF,hAF⟩ := DeterminantFibers.matrix_field_bound θ hθ A hk p hp he
  have hg : g.range ≤ F.toSubalgebra := by
    apply range_le_of_variables_mem
    rintro ⟨i,j⟩
    exact hAF i j
  let h : f.range →ₐ[K] Ω := ι.comp f.range.val
  have hmem : ∀ z, h z ∈ F.toSubalgebra := by
    rintro ⟨z,x,hx⟩
    obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective x
    apply hg
    exact ⟨q, by exact congrArg ι hx⟩
  let hFmap := h.codRestrict F.toSubalgebra hmem
  have hinj : Function.Injective hFmap := by
    intro x y heq
    apply Subtype.ext
    exact (FaithfulSMul.algebraMap_injective L Ω) (congrArg Subtype.val heq)
  exact (trdeg_le_of_injective hFmap hinj).trans hF

theorem coordinate_ring_dimension_le [Infinite K] {k : ℕ} (hk : 0 < k)
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ) (p : K[X][X]) :
    ringKrullDim (CoordinateRing K θ p) ≤ (k+1).choose 2 := by
  apply AlgebraicDimension.krullDim_le_of_field_images (K := K) ((k+1).choose 2)
  intro L _ _ f
  exact field_image_trdeg_le hk θ hθ p L f

end PermanentBorder.DeterminantFiberScheme

namespace PermanentBorder.DeterminantFibers
open Polynomial AdjugateAlgebra
universe u
variable {K L : Type u} [Field K] [Infinite K] [Field L] [Algebra K L]
  [IsAlgClosed L] {k : ℕ}

noncomputable def curveCoefficientField (P : L[X][X]) : IntermediateField K L :=
  IntermediateField.adjoin K (Set.range (fun ab : ℕ × ℕ => (P.coeff ab.1).coeff ab.2))

omit [Infinite K] [IsAlgClosed L] in
lemma coefficient_mem_curveCoefficientField (P : L[X][X]) (a b : ℕ) :
    (P.coeff a).coeff b ∈ curveCoefficientField (K := K) P :=
  IntermediateField.subset_adjoin K _ (Set.mem_range_self (a,b))

theorem matrix_field_bound_over_curve (θ : Fin (k+1) → K)
    (hθ : Function.Injective θ) (A : Matrix (Fin (k+1)) (Fin (k+1)) L)
    (hk : 0 < k) (B : ℕ)
    (hB : Algebra.trdeg K (curveCoefficientField (K := K)
      (pencilMatrix (pencilBase (fun i => algebraMap K L (θ i)) A)).det) ≤ (B : Cardinal)) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (B + (k+1).choose 2 : ℕ) ∧ ∀ i j, A i j ∈ F := by
  classical
  let P := (pencilMatrix (pencilBase (fun i => algebraMap K L (θ i)) A)).det
  let E := curveCoefficientField (K := K) P
  let : Infinite E := Infinite.of_injective (algebraMap K E) (algebraMap K E).injective
  obtain ⟨p,hp⟩ := (Bivariate.inField_iff_lifts E P).mp
    (coefficient_mem_curveCoefficientField P)
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hp
    exact DeterminantFiberScheme.determinant_ne_zero _ _ hp.symm
  let θE : Fin (k+1) → E := fun i => algebraMap K E (θ i)
  have hθE : Function.Injective θE := (algebraMap K E).injective.comp hθ
  have hdet : (pencilMatrix (pencilBase (fun i => algebraMap E L (θE i)) A)).det =
      Bivariate.map (algebraMap E L) p := by
    exact hp.symm
  obtain ⟨F,hF,hAF⟩ := matrix_field_bound θE hθE A hk p hp0 hdet
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : FaithfulSMul E F := (faithfulSMul_iff_algebraMap_injective E F).mpr
    (algebraMap E F).injective
  refine ⟨F.restrictScalars K, ?_, hAF⟩
  change Algebra.trdeg K F ≤ _
  rw [← trdeg_add_eq K E]
  exact (add_le_add hB hF).trans_eq (by simp)

end PermanentBorder.DeterminantFibers

namespace PermanentBorder.SpectralDimension
open MvPolynomial Polynomial Matrix
open Conductor AdjugateAlgebra DeterminantFibers
universe u

noncomputable def normalizationDefect {L : Type u} [Field L] {k : ℕ}
    (θ : Fin (k+1) → L) (A : Matrix (Fin (k+1)) (Fin (k+1)) L) : ℕ∞ :=
  let T := -(pencilBase θ A)
  let Q := FractionRing L[X]
  let R := integralClosure L[X] (AdjoinRoot (T.charpoly.map (algebraMap L[X] Q)))
  Module.length L (R ⧸ LinearMap.range
    (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toLinearMap)

variable (K : Type u) [Field K]

noncomputable def gradientIdeal {k : ℕ} (θ : Fin (k+1) → K) (q : ℕ) :
    Ideal (MvPolynomial (Fin (k+1) × Fin (k+1)) K) :=
  Ideal.span (Set.range (fun ij => pderiv ij (Selector.diagonalCoefficient
    (Matrix.of fun a b => (MvPolynomial.X (a,b) :
      MvPolynomial (Fin (k+1) × Fin (k+1)) K)) (fun i => MvPolynomial.C (θ i)) q)))

variable {K}

theorem field_point_critical {L : Type u} [Field L] [Algebra K L] {k q : ℕ}
    (θ : Fin (k+1) → K)
    (f : (MvPolynomial (Fin (k+1) × Fin (k+1)) K ⧸ gradientIdeal K θ q) →ₐ[K] L) :
    let g := f.comp (Ideal.Quotient.mkₐ K (gradientIdeal K θ q))
    ∀ ij, MvPolynomial.eval (fun ab => g (MvPolynomial.X (ab.1,ab.2)))
      (pderiv ij (Selector.diagonalCoefficient
        (Matrix.of fun a b => (MvPolynomial.X (a,b) :
          MvPolynomial (Fin (k+1) × Fin (k+1)) L))
        (fun i => MvPolynomial.C (algebraMap K L (θ i))) q)) = 0 := by
  classical
  intro g ij
  let P := Selector.diagonalCoefficient
    (Matrix.of fun a b => (MvPolynomial.X (a,b) :
      MvPolynomial (Fin (k+1) × Fin (k+1)) K)) (fun i => MvPolynomial.C (θ i)) q
  have hP : MvPolynomial.map (algebraMap K L) P = Selector.diagonalCoefficient
      (Matrix.of fun a b => (MvPolynomial.X (a,b) :
        MvPolynomial (Fin (k+1) × Fin (k+1)) L))
      (fun i => MvPolynomial.C (algebraMap K L (θ i))) q := by
    dsimp [P]
    rw [Selector.diagonalCoefficient_map]
    simp only [Matrix.of_apply, MvPolynomial.map_X, MvPolynomial.map_C]
    rfl
  rw [← hP, MvPolynomial.pderiv_map, MvPolynomial.eval_map]
  have hg : MvPolynomial.aeval (fun ab => g (MvPolynomial.X (ab.1,ab.2))) = g := by
    ext ab
    simp only [MvPolynomial.aeval_X, Prod.mk.eta]
  change MvPolynomial.aeval _ (pderiv ij P) = 0
  rw [hg]
  change f (Ideal.Quotient.mk _ (pderiv ij P)) = 0
  have hm : pderiv ij P ∈ gradientIdeal K θ q :=
    Ideal.subset_span (Set.mem_range_self ij)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]

end PermanentBorder.SpectralDimension

end OAI
