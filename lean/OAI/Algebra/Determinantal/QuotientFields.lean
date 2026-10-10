import OAI.Algebra.Determinantal.CurveParameters

namespace OAI
namespace PermanentBorder.FinitePlaneFrames
open Module Matrix MvPolynomial
variable {K L S : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing S] [Algebra L S]

theorem monomial_coordinates_mem {n : ℕ} (F : IntermediateField K L)
    (q : MvPolynomial (Fin 2) L →ₐ[L] S) (b : Basis (Fin n) L S)
    (hA : ∀ i j, representation b (q (X 0)) i j ∈ F)
    (hB : ∀ i j, representation b (q (X 1)) i j ∈ F)
    (hv : ∀ i, unitVector b i ∈ F) (r s : ℕ) :
    ∀ i, b.repr (q (X 0 ^ r * X 1 ^ s)) i ∈ F := by
  have h := MatrixSubfield.mulVec_mem F
    ((representation b (q (X 0))) ^ r * (representation b (q (X 1))) ^ s)
    (unitVector b)
    (MatrixSubfield.mul_mem F _ _ (MatrixSubfield.pow_mem F _ hA r)
      (MatrixSubfield.pow_mem F _ hB s)) hv
  have he : (representation b (q (X 0))) ^ r * (representation b (q (X 1))) ^ s =
      representation b (q (X 0 ^ r * X 1 ^ s)) := by simp only [map_mul,map_pow]
  simpa only [he, action_on_unit, Basis.equivFun_apply] using h

theorem unshifted_representation_mem {n : ℕ} (F : IntermediateField K L)
    (b : Basis (Fin n) L S) (x : S) (a : L) (ha : a ∈ F)
    (h : ∀ i j, representation b (x - algebraMap L S a) i j ∈ F) :
    ∀ i j, representation b x i j ∈ F := by
  have he : representation b x = representation b (x - algebraMap L S a) +
      algebraMap L (Matrix (Fin n) (Fin n) L) a := by
    rw [map_sub, AlgHom.commutes, sub_add_cancel]
  intro i j
  rw [he, Matrix.add_apply]
  refine F.add_mem (h i j) ?_
  change (Matrix.scalar (Fin n) a) i j ∈ F
  by_cases hij : i = j
  · subst j; simpa using ha
  · simp [Matrix.scalar, Matrix.diagonal, hij]

end PermanentBorder.FinitePlaneFrames
namespace PermanentBorder.FiniteAlgebras
open Module MvPolynomial Matrix FinitePlaneFrames CurveParameters
universe u
variable {K L : Type u} {R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R] [Module.Finite L R] [IsAlgClosed L]

noncomputable def localChart (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (p : MvPolynomial (Fin 2) K) (hpq : q (p.map (algebraMap K L)) = 0)
    (m : MaximalSpectrum R) (e : ℕ) (he : 0 < e)
    (b : Basis (Fin (finrank L (R ⧸ m.asIdeal ^ e))) L (R ⧸ m.asIdeal ^ e))
    (r s : Fin (finrank L (R ⧸ m.asIdeal ^ e)) → ℕ)
    (hb : CyclicFrames.MonomialBasis r s
      (representation b (shiftedLocalHom L R q m e (X 0)))
      (representation b (shiftedLocalHom L R q m e (X 1))) (unitVector b)) :
    LocalChart (L := L) p where
  length := finrank L (R ⧸ m.asIdeal ^ e)
  positive := local_length_pos L R m he
  support := supportPoint L R q m
  on_curve := by
    have h := supportPoint_on_curve L R q m (p.map (algebraMap K L)) hpq
    simpa only [aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp] using h
  r := r
  s := s
  A := representation b (shiftedLocalHom L R q m e (X 0))
  B := representation b (shiftedLocalHom L R q m e (X 1))
  v := unitVector b
  nilA := (shiftedLocalHom_X_nilpotent L R q m e 0).map (representation b)
  nilB := (shiftedLocalHom_X_nilpotent L R q m e 1).map (representation b)
  commutes := by
    have h := congrArg (representation b) (mul_comm
      (shiftedLocalHom L R q m e (X 0)) (shiftedLocalHom L R q m e (X 1)))
    simpa only [map_mul] using h
  basis_eq := hb

theorem local_monomial_coordinates_mem (F : IntermediateField K L)
    (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (p : MvPolynomial (Fin 2) K) (hpq : q (p.map (algebraMap K L)) = 0)
    (m : MaximalSpectrum R) (e : ℕ) (he : 0 < e)
    (b : Basis (Fin (finrank L (R ⧸ m.asIdeal ^ e))) L (R ⧸ m.asIdeal ^ e))
    (r s : Fin (finrank L (R ⧸ m.asIdeal ^ e)) → ℕ)
    (hb : CyclicFrames.MonomialBasis r s
      (representation b (shiftedLocalHom L R q m e (X 0)))
      (representation b (shiftedLocalHom L R q m e (X 1))) (unitVector b))
    (hF : (localChart q p hpq m e he b r s hb).InField F) (r' s' : ℕ) :
    ∀ i, b.repr (localHom L R q m e (X 0 ^ r' * X 1 ^ s')) i ∈ F := by
  apply monomial_coordinates_mem F (localHom L R q m e) b _ _ hF.2.2.2 r' s'
  · apply unshifted_representation_mem F b _ (supportPoint L R q m 0) (hF.1 0)
    have h : ∀ i j, representation b (shiftedLocalHom L R q m e (X 0)) i j ∈ F := hF.2.1
    simpa only [shiftedLocalHom_X] using h
  · apply unshifted_representation_mem F b _ (supportPoint L R q m 1) (hF.1 1)
    have h : ∀ i j, representation b (shiftedLocalHom L R q m e (X 1)) i j ∈ F := hF.2.2.1
    simpa only [shiftedLocalHom_X] using h

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.CurveQuotientParameters
open Module Matrix MvPolynomial FiniteAlgebras FinitePlaneFrames CurveParameters
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [Infinite K] [IsAlgClosed L] [CommRing R] [Algebra L R] [Module.Finite L R]

theorem chart_field_bound (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0)
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (hq : Function.Surjective q)
    (hpq : q (p.map (algebraMap K L)) = 0)
    {n : ℕ} (b₀ : Basis (Fin n) L R) (r₀ s₀ : Fin n → ℕ)
    (hb₀ : ∀ i, b₀ i = q (X 0 ^ r₀ i * X 1 ^ s₀ i)) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (finrank L R : Cardinal) ∧
      (∀ i j, representation b₀ (q (X 0)) i j ∈ F) ∧
      (∀ i j, representation b₀ (q (X 1)) i j ∈ F) ∧
      (∀ i, unitVector b₀ i ∈ F) := by
  classical
  have : IsArtinianRing R := artinian L R
  let _ : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  obtain ⟨e, he, E, hE⟩ := exists_canonical_local_power_decomposition L R
  choose b r s hb using fun m => local_monomial_chart L R q hq m e
  let D : MaximalSpectrum R → LocalChart (L := L) p := fun m =>
    localChart q p hpq m e he (b m) (r m) (s m) (hb m)
  have hbot : Algebra.trdeg K (⊥ : IntermediateField K L) ≤ (0 : Cardinal) := by
    rw [trdeg_eq_zero]
  obtain ⟨F, _, hF, hDF⟩ := extend_by_finite_family hp D Finset.univ
    (⊥ : IntermediateField K L) hbot
  have hdF : ∀ m, (D m).InField F := fun m => hDF m (Finset.mem_univ m)
  have hlen : finrank L R = ∑ m : MaximalSpectrum R, finrank L (R ⧸ m.asIdeal ^ e) := by
    rw [E.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  have hdeg : Algebra.trdeg K F ≤ (finrank L R : Cardinal) := by
    rw [hlen]
    simpa only [D, localChart, Nat.zero_add] using hF
  let w : R ≃ₗ[L] ((m : MaximalSpectrum R) × Fin (finrank L (R ⧸ m.asIdeal ^ e))) → L :=
    E.toLinearEquiv.trans ((LinearEquiv.piCongrRight fun m => (b m).equivFun).trans
      (LinearEquiv.piCurry L (fun (m : MaximalSpectrum R) (_ : Fin (finrank L (R ⧸ m.asIdeal ^ e))) => L)).symm)
  let c := Basis.ofEquivFun w
  have hmon (a d : ℕ) : ∀ i, c.repr (q (X 0 ^ a * X 1 ^ d)) i ∈ F := by
    intro i
    change (b i.1).repr (E (q (X 0 ^ a * X 1 ^ d)) i.1) i.2 ∈ F
    rw [hE]
    exact local_monomial_coordinates_mem F q p hpq i.1 e he
      (b i.1) (r i.1) (s i.1) (hb i.1) (hdF i.1) a d i.2
  have hbc : ∀ i j, c.repr (b₀ j) i ∈ F := by
    intro i j
    rw [hb₀]
    exact hmon (r₀ j) (s₀ j) i
  have hmon₀ (a d : ℕ) : ∀ i, b₀.repr (q (X 0 ^ a * X 1 ^ d)) i ∈ F :=
    BasisFieldRecovery.repr_mem F b₀ c hbc _ (hmon a d)
  refine ⟨F,hdeg,?_,?_,?_⟩
  · intro i j
    rw [show representation b₀ (q (X 0)) i j = b₀.repr (q (X 0) * b₀ j) i from
      LinearMap.toMatrixAlgEquiv_apply b₀ (Algebra.lmul L R (q (X 0))) i j]
    have h : q (X 0) * b₀ j = q (X 0 ^ (r₀ j + 1) * X 1 ^ s₀ j) := by
      rw [hb₀, ← map_mul]
      congr 1
      ring
    rw [h]
    exact hmon₀ (r₀ j+1) (s₀ j) i
  · intro i j
    rw [show representation b₀ (q (X 1)) i j = b₀.repr (q (X 1) * b₀ j) i from
      LinearMap.toMatrixAlgEquiv_apply b₀ (Algebra.lmul L R (q (X 1))) i j]
    have h : q (X 1) * b₀ j = q (X 0 ^ r₀ j * X 1 ^ (s₀ j+1)) := by
      rw [hb₀, ← map_mul]
      congr 1
      ring
    rw [h]
    exact hmon₀ (r₀ j) (s₀ j+1) i
  · intro i
    simpa only [pow_zero, one_mul, map_one, unitVector, Basis.equivFun_apply] using hmon₀ 0 0 i

end PermanentBorder.CurveQuotientParameters

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Matrix Module
variable {K : Type*} [Field K] {k : ℕ}

@[simp] theorem planeMap_single (d : ℕ) (i : PlaneIndex d) :
    planeMap d (Pi.single i (1 : K)) =
      monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1) := by
  classical
  simp only [planeMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

noncomputable def rowCoordinateMap (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    (PlaneIndex (k-1) → K) →ₗ[K] (K[X][X] ⧸ rowIdeal (pencilBase θ A)) :=
  (Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A))).toLinearMap.comp (planeMap (k-1))

theorem rowCoordinateMap_bijective (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Function.Bijective (rowCoordinateMap θ A) := by
  classical
  have hinj : Function.Injective (rowCoordinateMap θ A) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hmem : planeMap (k-1) v ∈ rowIdeal (pencilBase θ A) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hv
    have hz := rowIdeal_low_degree_zero θ hθ A hk hmem (totalDegreeLE_planeMap (k-1) v)
    funext i
    have hc := congrArg (fun p : K[X][X] => (p.coeff i.val.1.val).coeff
      (i.val.2.val-i.val.1.val-1)) hz
    simpa only [coeff_planeMap, coeff_zero, Pi.zero_apply] using hc
  refine ⟨hinj, LinearMap.range_eq_top.mp ?_⟩
  apply top_unique
  rw [← row_quotient_spanned θ hθ A hk]
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  refine ⟨Pi.single i 1, ?_⟩
  simp [rowCoordinateMap]

noncomputable def rowCoordinates (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    (PlaneIndex (k-1) → K) ≃ₗ[K] (K[X][X] ⧸ rowIdeal (pencilBase θ A)) :=
  LinearEquiv.ofBijective (rowCoordinateMap θ A) (rowCoordinateMap_bijective θ hθ A hk)

noncomputable def rowBasis (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Basis (PlaneIndex (k-1)) K (K[X][X] ⧸ rowIdeal (pencilBase θ A)) :=
  Basis.ofEquivFun (rowCoordinates θ hθ A hk).symm

@[simp] theorem rowBasis_apply (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) (i : PlaneIndex (k-1)) :
    rowBasis θ hθ A hk i = (Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A)))
      (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1)) := by
  classical
  rw [rowBasis, Basis.coe_ofEquivFun]
  change rowCoordinateMap θ A (Pi.single i 1) = _
  simp [rowCoordinateMap]

theorem rowBasis_repr (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k)
    (P : K[X][X]) (hP : TotalDegreeLE P (k-1)) (i : PlaneIndex (k-1)) :
    (rowBasis θ hθ A hk).repr ((Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A))) P) i =
      (P.coeff i.val.1.val).coeff (i.val.2.val-i.val.1.val-1) := by
  let E := rowCoordinates θ hθ A hk
  let q := Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A))
  let v := E.symm (q P)
  have he : q (planeMap (k-1) v) = q P := E.apply_symm_apply (q P)
  have hm : planeMap (k-1) v - P ∈ rowIdeal (pencilBase θ A) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (planeMap (k-1) v - P) = 0
    rw [map_sub, he, sub_self]
  have hz := rowIdeal_low_degree_zero θ hθ A hk hm
    ((totalDegreeLE_planeMap (k-1) v).sub hP)
  have hh := congrArg (fun p : K[X][X] => (p.coeff i.val.1.val).coeff
    (i.val.2.val-i.val.1.val-1)) (sub_eq_zero.mp hz)
  change v i = _
  simpa only [coeff_planeMap] using hh

end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.Bivariate
open Polynomial
variable (K : Type*) [CommSemiring K]

noncomputable def equivalence : MvPolynomial (Fin 2) K ≃ₐ[K] K[X][X] :=
  (MvPolynomial.finSuccEquiv K 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)))

@[simp] theorem equivalence_X_zero :
    equivalence K (MvPolynomial.X 0) = (X : K[X][X]) := by
  simp [equivalence, MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem equivalence_X_one :
    equivalence K (MvPolynomial.X 1) = C (X : K[X]) := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X (Fin.succ 0))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp] theorem equivalence_C (c : K) :
    equivalence K (MvPolynomial.C c) = C (C c) := (equivalence K).commutes c

variable {K} {L : Type*} [CommSemiring L]

noncomputable def map (f : K →+* L) : K[X][X] →+* L[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom f)

theorem equivalence_map (f : K →+* L) (p : MvPolynomial (Fin 2) K) :
    equivalence L (MvPolynomial.map f p) = map f (equivalence K p) := by
  have h : (equivalence L).toRingHom.comp (MvPolynomial.map f) =
      (map f).comp (equivalence K).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [map]
    · intro i
      fin_cases i <;> simp [map]
  exact RingHom.congr_fun h p

@[simp] theorem equivalence_monomial (a b : ℕ) :
    equivalence K (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      monomial a (monomial b (1 : K)) := by
  simp only [map_mul, map_pow, equivalence_X_zero, equivalence_X_one]
  rw [← Polynomial.C_pow]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_one, one_mul]
  exact mul_comm _ _

end PermanentBorder.Bivariate

namespace PermanentBorder.Bivariate
open Polynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def InField (F : IntermediateField K L) (P : L[X][X]) : Prop :=
  ∀ a b, (P.coeff a).coeff b ∈ F

theorem inField_iff_lifts (F : IntermediateField K L) (P : L[X][X]) :
    InField F P ↔ ∃ Q : F[X][X], map F.val.toRingHom Q = P := by
  change (∀ a b, (P.coeff a).coeff b ∈ F) ↔
    ∃ Q : F[X][X], Polynomial.map (Polynomial.mapRingHom F.val.toRingHom) Q = P
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h a
    have hp : P.coeff a ∈ Polynomial.lifts F.val.toRingHom := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro b
      exact ⟨⟨_,h a b⟩,rfl⟩
    exact (Polynomial.mem_lifts _).mp hp
  · intro h a b
    obtain ⟨Q,hQ⟩ := h a
    rw [← hQ]
    change (Polynomial.map F.val.toRingHom Q).coeff b ∈ F
    rw [Polynomial.coeff_map]
    exact (Q.coeff b).property

theorem InField.add {F : IntermediateField K L} {P Q : L[X][X]}
    (hP : InField F P) (hQ : InField F Q) : InField F (P+Q) := by
  intro a b
  simp only [coeff_add]
  exact F.add_mem (hP a b) (hQ a b)

theorem InField.sub {F : IntermediateField K L} {P Q : L[X][X]}
    (hP : InField F P) (hQ : InField F Q) : InField F (P-Q) := by
  intro a b
  simp only [coeff_sub]
  exact F.sub_mem (hP a b) (hQ a b)

theorem InField.mul {F : IntermediateField K L} {P Q : L[X][X]}
    (hP : InField F P) (hQ : InField F Q) : InField F (P*Q) := by
  obtain ⟨P',rfl⟩ := (inField_iff_lifts F P).mp hP
  obtain ⟨Q',rfl⟩ := (inField_iff_lifts F Q).mp hQ
  exact (inField_iff_lifts F _).mpr ⟨P'*Q', map_mul _ _ _⟩

theorem inField_map (F : IntermediateField K L) (P : K[X][X]) :
    InField F (map (algebraMap K L) P) := by
  intro a b
  simp only [map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  exact F.algebraMap_mem _

theorem inField_C_C (F : IntermediateField K L) (a : L) (ha : a ∈ F) :
    InField F (C (C a)) := by
  apply (inField_iff_lifts F _).mpr
  exact ⟨C (C ⟨a,ha⟩), by simp [map]⟩

theorem inField_X (F : IntermediateField K L) : InField F (X : L[X][X]) := by
  exact (inField_iff_lifts F _).mpr ⟨X, by simp [map]⟩

theorem inField_C_X (F : IntermediateField K L) : InField F (C (X : L[X])) := by
  exact (inField_iff_lifts F _).mpr ⟨C X, by simp [map]⟩

theorem eval_mem (F : IntermediateField K L) (P : L[X])
    (hP : ∀ a, P.coeff a ∈ F) (t : L) (ht : t ∈ F) : P.eval t ∈ F := by
  rw [Polynomial.eval_eq_sum_range]
  exact F.sum_mem fun a _ => F.mul_mem (hP a) (pow_mem ht a)

end PermanentBorder.Bivariate

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Module
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem coordinates_mem {R ι : Type*} [AddCommGroup R] [Module L R]
    (F : IntermediateField K L) (f : L[X][X] →ₗ[L] R) (b : Basis ι L R)
    (hmon : ∀ a d i, b.repr (f (monomial a (monomial d 1))) i ∈ F)
    (P : L[X][X]) (hP : Bivariate.InField F P) (i : ι) :
    b.repr (f P) i ∈ F := by
  rw [eq_sum_bivariate P, map_sum, map_sum, Finsupp.finsetSum_apply]
  apply F.sum_mem
  intro a _
  rw [map_sum, map_sum, Finsupp.finsetSum_apply]
  apply F.sum_mem
  intro d _
  have he : monomial a (monomial d ((P.coeff a).coeff d)) =
      ((P.coeff a).coeff d) • monomial a (monomial d (1 : L)) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact F.mul_mem (hP a d) (hmon a d i)

variable {k : ℕ}

theorem scaled_coeff_mem (F : IntermediateField K L) (P : L[X][X])
    (hP : Bivariate.InField F P) (a d : ℕ) :
    ((scaleHom P).coeff a).coeff d ∈ F := by
  rw [coeff_scaleHom]
  split_ifs
  · exact hP _ _
  · exact F.zero_mem

omit [Algebra K L] in

theorem map_rowEntry (f : K →+* L) (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (i : Fin (k+1)) :
    Bivariate.map f (rowEntry (pencilBase θ A) i) =
      rowEntry (pencilBase (fun j => f (θ j)) (A.map f)) i := by
  have hp : (pencilMatrix (pencilBase θ A)).map (Bivariate.map f) =
      pencilMatrix (pencilBase (fun j => f (θ j)) (A.map f)) := by
    apply Matrix.ext
    intro j l
    by_cases hjl : j=l <;> simp [pencilMatrix, pencilBase, Bivariate.map,
      hjl]
  have ha := (Bivariate.map f).map_adjugate (pencilMatrix (pencilBase θ A))
  change (pencilMatrix (pencilBase θ A)).adjugate.map (Bivariate.map f) =
    ((pencilMatrix (pencilBase θ A)).map (Bivariate.map f)).adjugate at ha
  rw [hp] at ha
  simp only [rowEntry, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (congrFun ha j) i

end PermanentBorder.AdjugateAlgebra

end OAI
