import OAI.Algebra.Determinantal.PunctualCharts

namespace OAI
namespace PermanentBorder.CurveParameters
open Matrix Algebra MvPolynomial CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

omit [Infinite K] in

theorem support_field_bound (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0)
    (x : Fin 2 → L) (hx : aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤ (1 : Cardinal) := by
  have h := ParameterBounds.field_adjoin_trdeg_lt_of_relation x p hp hx
  apply Cardinal.lt_natCast_add_one_iff.mp
  convert h using 1
  norm_num

theorem extend_by_chart {p₀ n : ℕ} (F : IntermediateField K L)
    (hF : Algebra.trdeg K F ≤ (p₀ : Cardinal))
    (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0)
    (x : Fin 2 → L) (hx : aeval x p = 0) (hn : 0 < n)
    (r s : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hAB : A * B = B * A)
    (hb : MonomialBasis r s A B v) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (p₀+n : ℕ) ∧
      (∀ i, x i ∈ E) ∧ (∀ i j, A i j ∈ E) ∧
      (∀ i j, B i j ∈ E) ∧ (∀ i, v i ∈ E) := by
  have : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  let pF := MvPolynomial.map (algebraMap K F) p
  have hpF : pF ≠ 0 := by
    exact fun h => hp ((MvPolynomial.map_injective _ (algebraMap K F).injective)
      (by simpa only [map_zero] using h))
  have hxF : aeval (R := F) x pF = 0 := by
    change eval₂ (algebraMap F L) x (MvPolynomial.map (algebraMap K F) p) = 0
    rw [MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq K F L]
    exact hx
  let T := IntermediateField.adjoin F (Set.range x)
  have : IsScalarTower K T L := IsScalarTower.of_algebraMap_eq' (by ext z; rfl)
  have : Infinite T := Infinite.of_injective (algebraMap K T) (algebraMap K T).injective
  have hT : Algebra.trdeg F T ≤ (1 : Cardinal) := support_field_bound pF hpF x hxF
  obtain ⟨U,hU,hAU,hBU,hvU⟩ := PunctualCharts.chart_field_bound (K := T)
    hn r s A B v hA hB hAB hb
  have : FaithfulSMul T U := (faithfulSMul_iff_algebraMap_injective T U).mpr
    (algebraMap T U).injective
  let E := U.restrictScalars K
  have : FaithfulSMul K F := (faithfulSMul_iff_algebraMap_injective K F).mpr
    (algebraMap K F).injective
  have : FaithfulSMul F T := (faithfulSMul_iff_algebraMap_injective F T).mpr
    (algebraMap F T).injective
  have : FaithfulSMul K T := (faithfulSMul_iff_algebraMap_injective K T).mpr
    (algebraMap K T).injective
  have hFE : F ≤ E := by
    intro z hz
    exact U.algebraMap_mem (algebraMap F T ⟨z,hz⟩)
  have hxE : ∀ i, x i ∈ E := fun i =>
    U.algebraMap_mem ⟨x i, IntermediateField.subset_adjoin F _ (Set.mem_range_self i)⟩
  refine ⟨E,hFE,?_,hxE,hAU,hBU,hvU⟩
  calc
    Algebra.trdeg K E = Algebra.trdeg K T + Algebra.trdeg T U :=
      (trdeg_add_eq K T (A := U)).symm
    _ = (Algebra.trdeg K F + Algebra.trdeg F T) + Algebra.trdeg T U := by
      rw [trdeg_add_eq K F (A := T)]
    _ ≤ ((p₀ : Cardinal) + 1) + (n-1 : ℕ) := add_le_add (add_le_add hF hT) hU
    _ = (p₀+n : ℕ) := by
      rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hn, ← Nat.cast_add]

end PermanentBorder.CurveParameters
namespace PermanentBorder.CurveParameters
open Matrix Algebra MvPolynomial CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

structure LocalChart (p : MvPolynomial (Fin 2) K) where
  length : ℕ
  positive : 0 < length
  support : Fin 2 → L
  on_curve : aeval support p = 0
  r : Fin length → ℕ
  s : Fin length → ℕ
  A : Matrix (Fin length) (Fin length) L
  B : Matrix (Fin length) (Fin length) L
  v : Fin length → L
  nilA : IsNilpotent A
  nilB : IsNilpotent B
  commutes : A * B = B * A
  basis_eq : MonomialBasis r s A B v

namespace LocalChart
variable {p : MvPolynomial (Fin 2) K}

def InField (D : LocalChart (L := L) p) (F : IntermediateField K L) : Prop :=
  (∀ i, D.support i ∈ F) ∧ (∀ i j, D.A i j ∈ F) ∧
  (∀ i j, D.B i j ∈ F) ∧ (∀ i, D.v i ∈ F)

theorem InField.mono {D : LocalChart (L := L) p} {F E : IntermediateField K L}
    (h : D.InField F) (hFE : F ≤ E) : D.InField E :=
  ⟨fun i => hFE (h.1 i),fun i j => hFE (h.2.1 i j),
    fun i j => hFE (h.2.2.1 i j),fun i => hFE (h.2.2.2 i)⟩

theorem extend [Infinite K] (D : LocalChart (L := L) p) (hp : p ≠ 0)
    {b : ℕ} (F : IntermediateField K L) (hF : Algebra.trdeg K F ≤ (b : Cardinal)) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (b + D.length : ℕ) ∧ D.InField E :=
  extend_by_chart F hF p hp D.support D.on_curve D.positive D.r D.s D.A D.B D.v
    D.nilA D.nilB D.commutes D.basis_eq

end LocalChart

theorem extend_by_finite_family [Infinite K] {κ : Type*}
    {p : MvPolynomial (Fin 2) K} (hp : p ≠ 0)
    (D : κ → LocalChart (L := L) p) (t : Finset κ)
    {b : ℕ} (F : IntermediateField K L) (hF : Algebra.trdeg K F ≤ (b : Cardinal)) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (b + ∑ i ∈ t, (D i).length : ℕ) ∧
      ∀ i ∈ t, (D i).InField E := by
  classical
  induction t using Finset.induction_on generalizing b F with
  | empty =>
    exact ⟨F,le_rfl,by simpa using hF,by simp⟩
  | @insert i t hi ih =>
    obtain ⟨T,hFT,hT,hDT⟩ := (D i).extend hp F hF
    obtain ⟨E,hTE,hE,hDE⟩ := ih T hT
    refine ⟨E,hFT.trans hTE,?_,?_⟩
    · simpa only [Finset.sum_insert hi, Nat.add_assoc] using hE
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjt
      · subst j
        exact hDT.mono hTE
      · exact hDE j hjt

end PermanentBorder.CurveParameters

namespace PermanentBorder.FiniteAlgebras
open Module
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R] [Module.Finite L R]

include L in

theorem artinian : IsArtinianRing R := isArtinian_of_tower L inferInstance

theorem exists_local_power_decomposition :
    ∃ e : ℕ, 0 < e ∧
      Nonempty (R ≃ₐ[L] ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal ^ e) := by
  have : IsArtinianRing R := artinian L R
  obtain ⟨e,he⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
  have he' : nilradical R ^ (e+1) = ⊥ := by rw [pow_succ, he]; simp
  refine ⟨e+1, Nat.zero_lt_succ e, ⟨?_⟩⟩
  exact ((AlgEquiv.quotientBot R R).symm.trans
    ((Ideal.quotientEquivAlgOfEq R he'.symm).trans
      (IsArtinianRing.quotNilradicalPowEquivPi R (e+1)))).restrictScalars L

theorem maximal_power_ne_top (m : MaximalSpectrum R) {e : ℕ} (he : 0 < e) :
    m.asIdeal ^ e ≠ ⊤ := by
  intro h
  exact m.isMaximal.ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self he.ne'))

theorem scalar_residue [IsAlgClosed L] (m : MaximalSpectrum R) (x : R) :
    ∃ a : L, x - algebraMap L R a ∈ m.asIdeal := by
  have : m.asIdeal.IsMaximal := m.isMaximal
  let _ : Field (R ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  obtain ⟨a,ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := L) (K := R ⧸ m.asIdeal)).2 (Ideal.Quotient.mk m.asIdeal x)
  refine ⟨a, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  rw [map_sub, ← ha]
  exact sub_self _

theorem translated_coordinate_nilpotent [IsAlgClosed L]
    (m : MaximalSpectrum R) (e : ℕ) (x : R) :
    ∃ a : L, IsNilpotent
      (Ideal.Quotient.mk (m.asIdeal ^ e) x - algebraMap L (R ⧸ m.asIdeal ^ e) a) := by
  obtain ⟨a,ha⟩ := scalar_residue L R m x
  refine ⟨a,e,?_⟩
  change (Ideal.Quotient.mk (m.asIdeal ^ e) (x - algebraMap L R a)) ^ e = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow ha e

theorem finrank_sum_of_equiv {e : ℕ}
    (E : R ≃ₐ[L] ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal ^ e) :
    ∃ _ : Fintype (MaximalSpectrum R),
      finrank L R = ∑ m : MaximalSpectrum R, finrank L (R ⧸ m.asIdeal ^ e) := by
  have : IsArtinianRing R := artinian L R
  let _ : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  refine ⟨inferInstance, ?_⟩
  rw [E.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.FiniteAlgebras
open Module MvPolynomial
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R]
  [Module.Finite L R] [IsAlgClosed L]

noncomputable def residueEquiv (m : MaximalSpectrum R) :
    L ≃ₐ[L] R ⧸ m.asIdeal := by
  have : m.asIdeal.IsMaximal := m.isMaximal
  let _ : Field (R ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact AlgEquiv.ofBijective (Algebra.ofId L (R ⧸ m.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

noncomputable def residue (m : MaximalSpectrum R) : R →ₐ[L] L :=
  (residueEquiv L R m).symm.toAlgHom.comp (Ideal.Quotient.mkₐ L m.asIdeal)

theorem sub_residue_mem (m : MaximalSpectrum R) (x : R) :
    x - algebraMap L R (residue L R m x) ∈ m.asIdeal := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub]
  change Ideal.Quotient.mk m.asIdeal x - residueEquiv L R m
    ((residueEquiv L R m).symm (Ideal.Quotient.mk m.asIdeal x)) = 0
  rw [AlgEquiv.apply_symm_apply, sub_self]

theorem residue_nilpotent (m : MaximalSpectrum R) (e : ℕ) (x : R) :
    IsNilpotent (Ideal.Quotient.mk (m.asIdeal ^ e) x -
      algebraMap L (R ⧸ m.asIdeal ^ e) (residue L R m x)) := by
  refine ⟨e,?_⟩
  change (Ideal.Quotient.mk (m.asIdeal ^ e)
    (x - algebraMap L R (residue L R m x))) ^ e = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (sub_residue_mem L R m x) e

noncomputable def supportPoint (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) : Fin 2 → L := fun i => residue L R m (q (X i))

theorem supportPoint_on_curve (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) (p : MvPolynomial (Fin 2) L) (hp : q p = 0) :
    aeval (supportPoint L R q m) p = 0 := by
  have h : (residue L R m).comp q = aeval (supportPoint L R q m) := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X, supportPoint]
  rw [← h, AlgHom.comp_apply, hp, map_zero]

end PermanentBorder.FiniteAlgebras

namespace PermanentBorder.PlaneTranslations
open MvPolynomial
variable {L : Type*} [CommRing L]

noncomputable def translate (a : Fin 2 → L) :
    MvPolynomial (Fin 2) L →ₐ[L] MvPolynomial (Fin 2) L :=
  aeval fun i => X i + C (a i)

@[simp] theorem translate_X (a : Fin 2 → L) (i : Fin 2) :
    translate a (X i) = X i + C (a i) := aeval_X _ _

@[simp] theorem translate_C (a : Fin 2 → L) (c : L) :
    translate a (C c) = C c := by exact (translate a).commutes c

theorem translate_comp (a b : Fin 2 → L) :
    (translate a).comp (translate b) = translate (a+b) := by
  ext i
  simp only [AlgHom.comp_apply, translate_X, map_add, translate_C, Pi.add_apply, map_add]
  simp only [add_assoc]

noncomputable def equivalence (a : Fin 2 → L) :
    MvPolynomial (Fin 2) L ≃ₐ[L] MvPolynomial (Fin 2) L :=
  AlgEquiv.ofAlgHom (translate a) (translate (-a))
    (by rw [translate_comp]; ext i; simp)
    (by rw [translate_comp]; ext i; simp)

@[simp] theorem equivalence_X (a : Fin 2 → L) (i : Fin 2) :
    equivalence a (X i) = X i + C (a i) := by
  exact translate_X a i

end PermanentBorder.PlaneTranslations

namespace PermanentBorder.FinitePlaneFrames
open MvPolynomial Module Matrix
variable {L S : Type*} [Field L] [CommRing S] [Algebra L S]

noncomputable def representation {n : ℕ} (b : Basis (Fin n) L S) :
    S →ₐ[L] Matrix (Fin n) (Fin n) L :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul L S)

noncomputable def unitVector {n : ℕ} (b : Basis (Fin n) L S) : Fin n → L := b.equivFun 1

theorem action_on_unit {n : ℕ} (b : Basis (Fin n) L S) (x : S) :
    (representation b x).mulVec (unitVector b) = b.equivFun x := by
  change ((LinearMap.toMatrix b b) (Algebra.lmul L S x)).mulVec
    (fun i => b.repr 1 i) = _
  rw [LinearMap.toMatrix_mulVec_repr]
  simp only [Module.Basis.equivFun_apply]
  change (fun i => b.repr (x * 1) i) = _
  rw [mul_one]

theorem exists_monomial_basis [Module.Finite L S]
    (q : MvPolynomial (Fin 2) L →ₐ[L] S) (hq : Function.Surjective q) :
    ∃ (b : Basis (Fin (finrank L S)) L S) (r s : Fin (finrank L S) → ℕ),
      ∀ i, b i = q (X 0 ^ r i * X 1 ^ s i) := by
  classical
  let μ := q.toLinearMap ∘ (MvPolynomial.basisMonomials (Fin 2) L)
  have hsp : Submodule.span L (Set.range μ) = ⊤ := by
    rw [show Set.range μ = q.toLinearMap '' Set.range (MvPolynomial.basisMonomials (Fin 2) L) from
      Set.range_comp _ _]
    rw [← Submodule.map_span, (MvPolynomial.basisMonomials (Fin 2) L).span_eq,
      Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hq
  have hdim : finrank L (Submodule.span L (Set.range μ)) = finrank L S := by
    rw [hsp, finrank_top]
  obtain ⟨f,hmem,hspan,hind⟩ : ∃ f : Fin (finrank L S) → S,
      (∀ i, f i ∈ Set.range μ) ∧ Submodule.span L (Set.range f) = ⊤ ∧
        LinearIndependent L f := by
    have he := Submodule.exists_fun_fin_finrank_span_eq L (Set.range μ)
    rw [hdim] at he
    simpa only [hsp] using he
  choose e he using hmem
  let b := Basis.mk hind (le_of_eq hspan.symm)
  refine ⟨b,fun i => e i 0,fun i => e i 1,?_⟩
  intro i
  rw [show b i = f i from Basis.mk_apply hind (le_of_eq hspan.symm) i, ← he i]
  change q (monomial (e i) 1) = _
  congr 1
  rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_two]
  · simp

end PermanentBorder.FinitePlaneFrames
namespace PermanentBorder.FiniteAlgebras
open Module MvPolynomial Matrix FinitePlaneFrames
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R]
  [Module.Finite L R] [IsAlgClosed L]

noncomputable def localHom (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) (e : ℕ) :
    MvPolynomial (Fin 2) L →ₐ[L] R ⧸ m.asIdeal ^ e :=
  (Ideal.Quotient.mkₐ L (m.asIdeal ^ e)).comp q

noncomputable def shiftedLocalHom (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) (e : ℕ) :
    MvPolynomial (Fin 2) L →ₐ[L] R ⧸ m.asIdeal ^ e :=
  (localHom L R q m e).comp (PlaneTranslations.translate (-supportPoint L R q m))

theorem shiftedLocalHom_X (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) (e : ℕ) (i : Fin 2) :
    shiftedLocalHom L R q m e (X i) = localHom L R q m e (X i) -
      algebraMap L (R ⧸ m.asIdeal ^ e) (supportPoint L R q m i) := by
  simp only [shiftedLocalHom, AlgHom.comp_apply, PlaneTranslations.translate_X,
    map_add, Pi.neg_apply, map_neg]
  rw [show (localHom L R q m e) (C (supportPoint L R q m i)) =
    algebraMap L (R ⧸ m.asIdeal ^ e) (supportPoint L R q m i) from
      (localHom L R q m e).commutes _]
  exact (sub_eq_add_neg _ _).symm

theorem shiftedLocalHom_surjective (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (hq : Function.Surjective q) (m : MaximalSpectrum R) (e : ℕ) :
    Function.Surjective (shiftedLocalHom L R q m e) :=
  Ideal.Quotient.mk_surjective.comp (hq.comp
    (PlaneTranslations.equivalence (-supportPoint L R q m)).surjective)

theorem shiftedLocalHom_X_nilpotent (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) (e : ℕ) (i : Fin 2) :
    IsNilpotent (shiftedLocalHom L R q m e (X i)) := by
  rw [shiftedLocalHom_X]
  exact residue_nilpotent L R m e (q (X i))

omit [IsAlgClosed L] in

theorem local_length_pos (m : MaximalSpectrum R) {e : ℕ} (he : 0 < e) :
    0 < finrank L (R ⧸ m.asIdeal ^ e) := by
  have : Nontrivial (R ⧸ m.asIdeal ^ e) :=
    Ideal.Quotient.nontrivial_iff.mpr (maximal_power_ne_top R m he)
  exact finrank_pos

theorem local_monomial_chart (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (hq : Function.Surjective q) (m : MaximalSpectrum R) (e : ℕ) :
    ∃ (b : Basis (Fin (finrank L (R ⧸ m.asIdeal ^ e))) L (R ⧸ m.asIdeal ^ e))
      (r s : Fin (finrank L (R ⧸ m.asIdeal ^ e)) → ℕ),
      CyclicFrames.MonomialBasis r s
        (representation b (shiftedLocalHom L R q m e (X 0)))
        (representation b (shiftedLocalHom L R q m e (X 1))) (unitVector b) := by
  obtain ⟨b,r,s,hb⟩ := FinitePlaneFrames.exists_monomial_basis
    (shiftedLocalHom L R q m e) (shiftedLocalHom_surjective L R q hq m e)
  refine ⟨b,r,s,?_⟩
  intro i
  have h : (representation b (shiftedLocalHom L R q m e (X 0))) ^ r i *
      (representation b (shiftedLocalHom L R q m e (X 1))) ^ s i =
      representation b (shiftedLocalHom L R q m e (X 0 ^ r i * X 1 ^ s i)) := by
    simp only [map_mul, map_pow]
  rw [h, action_on_unit, ← hb i]
  ext j
  simpa only [Pi.single_apply, eq_comm] using b.equivFun_self i j

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.FiniteAlgebras
open Module
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R] [Module.Finite L R]

theorem exists_canonical_local_power_decomposition :
    ∃ e : ℕ, 0 < e ∧ ∃ E : R ≃ₐ[L] ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal ^ e,
      ∀ x m, E x m = Ideal.Quotient.mk (m.asIdeal ^ e) x := by
  have : IsArtinianRing R := artinian L R
  obtain ⟨e,he⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
  have he' : nilradical R ^ (e+1) = ⊥ := by rw [pow_succ, he]; simp
  let E := ((AlgEquiv.quotientBot R R).symm.trans
    ((Ideal.quotientEquivAlgOfEq R he'.symm).trans
      (IsArtinianRing.quotNilradicalPowEquivPi R (e+1)))).restrictScalars L
  exact ⟨e+1, Nat.zero_lt_succ e, E, fun _ _ => rfl⟩

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.BasisFieldRecovery
open Module Matrix
variable {K L S ι κ : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup S] [Module L S] [Fintype ι] [Fintype κ]

omit [Fintype ι] in

theorem repr_mem (F : IntermediateField K L) (b : Basis ι L S) (c : Basis κ L S)
    (hbc : ∀ i j, c.repr (b j) i ∈ F) (x : S) (hx : ∀ i, c.repr x i ∈ F) :
    ∀ j, b.repr x j ∈ F := by
  classical
  let e := b.indexEquiv c
  let b' := b.reindex e
  let P : (Matrix κ κ L)ˣ :=
    ⟨c.toMatrix b', b'.toMatrix c,
      c.toMatrix_mul_toMatrix_flip b', b'.toMatrix_mul_toMatrix_flip c⟩
  have hP : ∀ i j, (P : Matrix κ κ L) i j ∈ F := by
    intro i j
    simpa only [P, Units.val_mk, b', Basis.toMatrix_apply, Basis.reindex_apply] using hbc i (e.symm j)
  have hI := MatrixSubfield.unit_inv_mem F P hP
  have hb'x : ∀ j, b'.repr x j ∈ F := by
    intro j
    rw [← c.toMatrix_mulVec_repr b' x]
    exact F.sum_mem fun i _ => F.mul_mem (hI j i) (hx i)
  intro j
  have h := hb'x (e j)
  simpa only [b', Basis.repr_reindex, Finsupp.equivMapDomain_apply,
    Equiv.symm_apply_apply] using h

end PermanentBorder.BasisFieldRecovery

namespace PermanentBorder.MatrixSubfield
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

theorem pow_mem (F : IntermediateField K L) (A : Matrix ι ι L)
    (hA : ∀ i j, A i j ∈ F) (r : ℕ) : ∀ i j, (A ^ r) i j ∈ F := by
  induction r with
  | zero => intro i j; simp only [pow_zero, one_apply]; split <;> simp
  | succ r ih => simpa only [pow_succ] using mul_mem F (A^r) A ih hA

omit [DecidableEq ι] in
theorem mulVec_mem (F : IntermediateField K L) (A : Matrix ι ι L) (v : ι → L)
    (hA : ∀ i j, A i j ∈ F) (hv : ∀ i, v i ∈ F) :
    ∀ i, (A.mulVec v) i ∈ F := by
  intro i
  exact F.sum_mem fun j _ => F.mul_mem (hA i j) (hv j)

end PermanentBorder.MatrixSubfield

end OAI
