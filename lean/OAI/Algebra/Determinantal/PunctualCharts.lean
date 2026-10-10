import OAI.Algebra.Determinantal.Nilpotents

namespace OAI

namespace PermanentBorder.CommutingPairs
open Matrix CentralizerDimension CentralizerParameters OrbitNormalization
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem nilpotent_pair_field_bound {n : ℕ} (hn : 0 < n)
    (A B : Matrix (Fin n) (Fin n) L) (hA : IsNilpotent A) (hB : IsNilpotent B)
    (hAB : A * B = B * A) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (n * n - 1 : ℕ) ∧
      (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hBd : B.det = 0 := by
    obtain ⟨r, hr⟩ := hB
    have hd : B.det ^ r = 0 := by rw [← Matrix.det_pow, hr, Matrix.det_zero]
    by_contra h
    exact pow_ne_zero r h hd
  obtain ⟨e, he, U, hU⟩ := NilpotentBlocks.canonical_nilpotent_form K (algebraMap K L) A hA
  have hP : A * (↑U⁻¹ : Matrix (Fin n) (Fin n) L) =
      (↑U⁻¹ : Matrix (Fin n) (Fin n) L) *
        (NilpotentBlocks.shapeMatrix (K := K) e he).map (algebraMap K L) := by
    rw [hU, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨F, hF, hAF, hBF⟩ := normalized_pair_field_bound A B
    (NilpotentBlocks.shapeMatrix e he) U⁻¹ hP hAB hBd
  refine ⟨F, ?_, hAF, hBF⟩
  have hpos : 0 < n * n := Nat.mul_pos hn hn
  have hc : n * n = (n * n - 1) + 1 := by omega
  rw [hc, Nat.cast_add, Nat.cast_one] at hF
  exact Cardinal.lt_natCast_add_one_iff.mp hF

end PermanentBorder.CommutingPairs

namespace PermanentBorder.FieldParameters
open Algebra MvPolynomial
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem adjoin_trdeg_le {n : ℕ} (x : Fin n → L) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range x)) ≤ (n : Cardinal) := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  have h := trdeg_le_of_surjective (MvPolynomial.aeval (R := K) x).rangeRestrict
    (AlgHom.rangeRestrict_surjective (MvPolynomial.aeval (R := K) x))
  simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast] using h

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem field_adjoin_trdeg_le {n : ℕ} (x : Fin n → L) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤ (n : Cardinal) := by
  rw [← trdeg_add_eq K (Algebra.adjoin K (Set.range x)),
    trdeg_eq_zero (R := Algebra.adjoin K (Set.range x)), add_zero]
  exact adjoin_trdeg_le x

theorem extend_field {p n : ℕ} (F : IntermediateField K L)
    (hF : Algebra.trdeg K F ≤ (p : Cardinal)) (x : Fin n → L) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ Algebra.trdeg K E ≤ (p + n : ℕ) ∧ (∀ i, x i ∈ E) := by
  let T := IntermediateField.adjoin F (Set.range x)
  let E := T.restrictScalars K
  have : FaithfulSMul F T := (faithfulSMul_iff_algebraMap_injective F T).mpr
    (algebraMap F T).injective
  have : FaithfulSMul K F := (faithfulSMul_iff_algebraMap_injective K F).mpr
    (algebraMap K F).injective
  have hFE : F ≤ E := by
    intro y hy
    exact T.algebraMap_mem ⟨y, hy⟩
  have hx : ∀ i, x i ∈ E := fun i => IntermediateField.subset_adjoin F _ (Set.mem_range_self i)
  refine ⟨E, hFE, ?_, hx⟩
  calc
    Algebra.trdeg K E = Algebra.trdeg K F + Algebra.trdeg F T := (trdeg_add_eq K F (A := T)).symm
    _ ≤ (p : Cardinal) + n := add_le_add hF (field_adjoin_trdeg_le (K := F) x)
    _ = (p + n : ℕ) := by simp only [Nat.cast_add]

end PermanentBorder.FieldParameters

namespace PermanentBorder.GenericMatrix
open Matrix MvPolynomial
universe u
variable (L : Type u) [Field L] (n : ℕ)

abbrev CoordinateRing := MvPolynomial (Fin n × Fin n) L
abbrev FunctionField := FractionRing (CoordinateRing L n)
noncomputable def coordinateMatrix : Matrix (Fin n) (Fin n) (CoordinateRing L n) :=
  fun i j => X (i,j)
noncomputable def genericMatrix : Matrix (Fin n) (Fin n) (FunctionField L n) :=
  (coordinateMatrix L n).map (algebraMap (CoordinateRing L n) (FunctionField L n))

theorem coordinate_det_ne_zero : (coordinateMatrix L n).det ≠ 0 := by
  intro h
  let f : CoordinateRing L n →ₐ[L] L := aeval (fun ij => (1 : Matrix (Fin n) (Fin n) L) ij.1 ij.2)
  have he : (coordinateMatrix L n).map f = (1 : Matrix (Fin n) (Fin n) L) := by
    ext i j
    exact aeval_X _ _
  have hh := congrArg f h
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, he, Matrix.det_one, map_zero] at hh
  exact one_ne_zero hh

theorem generic_det_ne_zero : (genericMatrix L n).det ≠ 0 := by
  change ((algebraMap (CoordinateRing L n) (FunctionField L n)).mapMatrix
    (coordinateMatrix L n)).det ≠ 0
  rw [← RingHom.map_det]
  exact fun h => coordinate_det_ne_zero L n
    ((IsFractionRing.injective (CoordinateRing L n) (FunctionField L n)) (by simpa using h))

noncomputable def genericUnit : (Matrix (Fin n) (Fin n) (FunctionField L n))ˣ :=
  ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (generic_det_ne_zero L n))).unit

@[simp] theorem genericUnit_val : (genericUnit L n : Matrix (Fin n) (Fin n) (FunctionField L n)) =
    genericMatrix L n := IsUnit.unit_spec _

theorem relative_trdeg : Algebra.trdeg L (FunctionField L n) = (n * n : ℕ) := by
  have : Algebra.IsAlgebraic (CoordinateRing L n) (FunctionField L n) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (CoordinateRing L n))
  have : FaithfulSMul (CoordinateRing L n) (FunctionField L n) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (CoordinateRing L n) (FunctionField L n))
  rw [← trdeg_add_eq L (CoordinateRing L n), trdeg_eq_zero (R := CoordinateRing L n), add_zero]
  simp only [CoordinateRing, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_prod,
    Cardinal.mk_fin, Cardinal.lift_mul, Cardinal.lift_natCast, Nat.cast_mul]

theorem field_eq_top_of_mem (K : Type u) [Field K] [Algebra K L]
    (E : IntermediateField K (FunctionField L n))
    (hc : ∀ x : L, algebraMap L (FunctionField L n) x ∈ E)
    (hx : ∀ i j, genericMatrix L n i j ∈ E) : E = ⊤ := by
  have hp : ∀ p : CoordinateRing L n,
      algebraMap (CoordinateRing L n) (FunctionField L n) p ∈ E := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C x =>
      change algebraMap (CoordinateRing L n) (FunctionField L n)
        (algebraMap L (CoordinateRing L n) x) ∈ E
      rw [← IsScalarTower.algebraMap_apply]
      exact hc x
    | add p q hp hq =>
      rw [map_add]
      exact E.add_mem hp hq
    | mul_X p ij hp =>
      rw [map_mul]
      exact E.mul_mem hp (hx ij.1 ij.2)
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨p, q, _, hz⟩ := IsFractionRing.div_surjective (CoordinateRing L n) z
  rw [← hz]
  exact E.div_mem (hp p) (hp q)

end PermanentBorder.GenericMatrix

namespace PermanentBorder.CyclicFrames
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

def MonomialBasis (r s : ι → ℕ) (A B : Matrix ι ι L) (v : ι → L) : Prop :=
  ∀ i, (A ^ r i * B ^ s i).mulVec v = Pi.single i 1

theorem recover_frame (r s : ι → ℕ) (A B A' B' Q : Matrix ι ι L)
    (v v' : ι → L) (hb : MonomialBasis r s A B v)
    (hA : A' * Q = Q * A) (hB : B' * Q = Q * B) (hv : v' = Q.mulVec v) :
    ∀ i j, Q i j = ((A' ^ r j * B' ^ s j).mulVec v') i := by
  intro i j
  have hpa : Q * A ^ r j = A' ^ r j * Q := (SemiconjBy.pow_right hA.symm _)
  have hpb : Q * B ^ s j = B' ^ s j * Q := (SemiconjBy.pow_right hB.symm _)
  have hm : (A' ^ r j * B' ^ s j) * Q = Q * (A ^ r j * B ^ s j) := by
    rw [mul_assoc, ← hpb, ← mul_assoc, ← hpa, mul_assoc]
  rw [hv, Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hb j,
    Matrix.mulVec_single]
  simp

theorem pow_mem (F : IntermediateField K L) (A : Matrix ι ι L)
    (hA : ∀ i j, A i j ∈ F) (r : ℕ) : ∀ i j, (A ^ r) i j ∈ F := by
  induction r with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split <;> simp
  | succ r hr =>
    rw [pow_succ]
    exact MatrixSubfield.mul_mem F _ _ hr hA

omit [DecidableEq ι] in
theorem mulVec_mem (F : IntermediateField K L) (A : Matrix ι ι L) (v : ι → L)
    (hA : ∀ i j, A i j ∈ F) (hv : ∀ i, v i ∈ F) : ∀ i, A.mulVec v i ∈ F := by
  intro i
  exact F.sum_mem fun j _ => F.mul_mem (hA i j) (hv j)

theorem frame_mem (F : IntermediateField K L) (r s : ι → ℕ)
    (A B A' B' Q : Matrix ι ι L) (v v' : ι → L)
    (hb : MonomialBasis r s A B v)
    (hA : A' * Q = Q * A) (hB : B' * Q = Q * B) (hv : v' = Q.mulVec v)
    (hAF : ∀ i j, A' i j ∈ F) (hBF : ∀ i j, B' i j ∈ F) (hvF : ∀ i, v' i ∈ F) :
    ∀ i j, Q i j ∈ F := by
  intro i j
  rw [recover_frame r s A B A' B' Q v v' hb hA hB hv i j]
  exact mulVec_mem F _ _ (MatrixSubfield.mul_mem F _ _
    (pow_mem F A' hAF (r j)) (pow_mem F B' hBF (s j))) hvF i

theorem original_mem (F : IntermediateField K L)
    (A B A' B' : Matrix ι ι L) (Q : (Matrix ι ι L)ˣ) (v v' : ι → L)
    (hA : A' * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * A)
    (hB : B' * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * B)
    (hv : v' = (Q : Matrix ι ι L).mulVec v)
    (hQF : ∀ i j, (Q : Matrix ι ι L) i j ∈ F)
    (hAF : ∀ i j, A' i j ∈ F) (hBF : ∀ i j, B' i j ∈ F) (hvF : ∀ i, v' i ∈ F) :
    (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) ∧ (∀ i, v i ∈ F) := by
  have hQiF := MatrixSubfield.unit_inv_mem F Q hQF
  have he (M M' : Matrix ι ι L) (hM : M' * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * M) :
      M = (↑Q⁻¹ : Matrix ι ι L) * (M' * (Q : Matrix ι ι L)) := by
    rw [hM, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [he A A' hA]
    exact MatrixSubfield.mul_mem F _ _ hQiF (MatrixSubfield.mul_mem F _ _ hAF hQF)
  · rw [he B B' hB]
    exact MatrixSubfield.mul_mem F _ _ hQiF (MatrixSubfield.mul_mem F _ _ hBF hQF)
  · have hev : v = (↑Q⁻¹ : Matrix ι ι L).mulVec v' := by
      rw [hv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hev]
    exact mulVec_mem F _ _ hQiF hvF

end PermanentBorder.CyclicFrames

namespace PermanentBorder.CyclicFrames
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Fintype ι] [DecidableEq ι]

theorem MonomialBasis.map (f : K →+* L) {r s : ι → ℕ}
    {A B : Matrix ι ι K} {v : ι → K} (h : MonomialBasis r s A B v) :
    MonomialBasis r s (A.map f) (B.map f) (f ∘ v) := by
  intro i
  have hh := congrArg (fun w : ι → K => f ∘ w) (h i)
  ext j
  have hj := congrFun hh j
  change f (((A ^ r i * B ^ s i).mulVec v) j) = f ((Pi.single i (1 : K) : ι → K) j) at hj
  rw [RingHom.map_mulVec, Matrix.map_mul] at hj
  have hpa : (A ^ r i).map f = (A.map f) ^ r i := (f.mapMatrix.map_pow A _)
  have hpb : (B ^ s i).map f = (B.map f) ^ s i := (f.mapMatrix.map_pow B _)
  rw [hpa, hpb] at hj
  rw [hj]
  by_cases hij : j = i
  · subst j
    simp
  · simp [hij]

def conjugation (Q : (Matrix ι ι L)ˣ) : Matrix ι ι L →+* Matrix ι ι L where
  toFun A := (Q : Matrix ι ι L) * A * (↑Q⁻¹ : Matrix ι ι L)
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by simp only [mul_add, add_mul]
  map_mul' A B := by
    simp only [mul_assoc]
    rw [← mul_assoc (↑Q⁻¹ : Matrix ι ι L) (↑Q : Matrix ι ι L),
      Units.inv_mul, one_mul]

theorem conjugation_intertwines (Q : (Matrix ι ι L)ˣ) (A : Matrix ι ι L) :
    conjugation Q A * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * A := by
  change ((Q : Matrix ι ι L) * A * (↑Q⁻¹ : Matrix ι ι L)) *
    (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * A
  rw [mul_assoc, Units.inv_mul, mul_one]

end PermanentBorder.CyclicFrames
namespace PermanentBorder.PunctualCharts
open Matrix Algebra CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

def tripleEntries {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L) : Set L :=
  (Set.range fun ij : Fin n × Fin n => A ij.1 ij.2) ∪
  (Set.range fun ij : Fin n × Fin n => B ij.1 ij.2) ∪ Set.range v

theorem generated_chart_field_bound {n : ℕ} (hn : 0 < n)
    (r s : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hAB : A * B = B * A)
    (hb : MonomialBasis r s A B v)
    (hgen : IntermediateField.adjoin K (tripleEntries A B v) = ⊤) :
    Algebra.trdeg K L ≤ (n - 1 : ℕ) := by
  classical
  let T := GenericMatrix.FunctionField L n
  let f := algebraMap L T
  let Q := GenericMatrix.genericUnit L n
  let A₀ : Matrix (Fin n) (Fin n) T := A.map f
  let B₀ : Matrix (Fin n) (Fin n) T := B.map f
  let v₀ : Fin n → T := f ∘ v
  let A' := conjugation Q A₀
  let B' := conjugation Q B₀
  let v' := (Q : Matrix (Fin n) (Fin n) T).mulVec v₀
  have hA' : IsNilpotent A' := (hA.map f.mapMatrix).map (conjugation Q)
  have hB' : IsNilpotent B' := (hB.map f.mapMatrix).map (conjugation Q)
  have hAB' : A' * B' = B' * A' := by
    exact ((Commute.map (show Commute A B from hAB) f.mapMatrix).map (conjugation Q)).eq
  obtain ⟨F, hF, hAF, hBF⟩ := CommutingPairs.nilpotent_pair_field_bound (K := K) hn A' B'
    hA' hB' hAB'
  obtain ⟨E, hFE, hE, hvE⟩ := FieldParameters.extend_field F hF v'
  have hAE : ∀ i j, A' i j ∈ E := fun i j => hFE (hAF i j)
  have hBE : ∀ i j, B' i j ∈ E := fun i j => hFE (hBF i j)
  have hb₀ : MonomialBasis r s A₀ B₀ v₀ := hb.map f
  have hAQ := conjugation_intertwines Q A₀
  have hBQ := conjugation_intertwines Q B₀
  have hQE : ∀ i j, (Q : Matrix (Fin n) (Fin n) T) i j ∈ E :=
    frame_mem E r s A₀ B₀ A' B' Q v₀ v' hb₀ hAQ hBQ rfl hAE hBE hvE
  obtain ⟨hA₀E, hB₀E, hv₀E⟩ := original_mem E A₀ B₀ A' B' Q v₀ v' hAQ hBQ
    rfl hQE hAE hBE hvE
  have hc : ∀ x : L, algebraMap L T x ∈ E := by
    have hle : IntermediateField.adjoin K (tripleEntries A B v) ≤
        IntermediateField.comap (IsScalarTower.toAlgHom K L T) E := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro x ((⟨⟨i,j⟩, rfl⟩ | ⟨⟨i,j⟩, rfl⟩) | ⟨i, rfl⟩)
      · exact hA₀E i j
      · exact hB₀E i j
      · exact hv₀E i
    rw [hgen] at hle
    exact fun x => hle (IntermediateField.mem_top)
  have htop : E = ⊤ := GenericMatrix.field_eq_top_of_mem L n K E hc (by
    simpa only [Q, GenericMatrix.genericUnit_val] using hQE)
  have hT : Algebra.trdeg K T ≤ (n * n - 1 + n : ℕ) := by
    rw [htop, (IntermediateField.topEquiv (F := K) (E := T)).trdeg_eq] at hE
    exact hE
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).mpr
    (algebraMap K L).injective
  have : FaithfulSMul L T := (faithfulSMul_iff_algebraMap_injective L T).mpr
    (algebraMap L T).injective
  rw [← trdeg_add_eq K L, GenericMatrix.relative_trdeg] at hT
  have heq : n * n - 1 + n = (n - 1) + n * n := by
    have hp : 0 < n * n := Nat.mul_pos hn hn
    omega
  rw [heq, Nat.cast_add] at hT
  exact (Cardinal.add_le_add_iff_of_lt_aleph0 (Cardinal.natCast_lt_aleph0)).mp hT

end PermanentBorder.PunctualCharts

namespace PermanentBorder.PunctualCharts
open Matrix Algebra CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem chart_field_bound {n : ℕ} (hn : 0 < n)
    (r s : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hAB : A * B = B * A)
    (hb : MonomialBasis r s A B v) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F ≤ (n - 1 : ℕ) ∧
      (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) ∧ (∀ i, v i ∈ F) := by
  classical
  let F := IntermediateField.adjoin K (tripleEntries A B v)
  have hAF : ∀ i j, A i j ∈ F := fun i j => IntermediateField.subset_adjoin K _
    (Or.inl (Or.inl (Set.mem_range_self (i,j))))
  have hBF : ∀ i j, B i j ∈ F := fun i j => IntermediateField.subset_adjoin K _
    (Or.inl (Or.inr (Set.mem_range_self (i,j))))
  have hvF : ∀ i, v i ∈ F := fun i => IntermediateField.subset_adjoin K _
    (Or.inr (Set.mem_range_self i))
  let A₀ : Matrix (Fin n) (Fin n) F := fun i j => ⟨A i j, hAF i j⟩
  let B₀ : Matrix (Fin n) (Fin n) F := fun i j => ⟨B i j, hBF i j⟩
  let v₀ : Fin n → F := fun i => ⟨v i, hvF i⟩
  let f := (algebraMap F L).mapMatrix (m := Fin n)
  have hf : Function.Injective f := by
    intro P Q h
    ext i j
    exact congrFun (congrFun h i) j
  have hfA : f A₀ = A := rfl
  have hfB : f B₀ = B := rfl
  have hA₀ : IsNilpotent A₀ := by
    obtain ⟨d, hd⟩ := hA
    refine ⟨d, hf ?_⟩
    rw [map_pow, hfA, map_zero, hd]
  have hB₀ : IsNilpotent B₀ := by
    obtain ⟨d, hd⟩ := hB
    refine ⟨d, hf ?_⟩
    rw [map_pow, hfB, map_zero, hd]
  have hAB₀ : A₀ * B₀ = B₀ * A₀ := by
    apply hf
    rw [map_mul, map_mul, hfA, hfB, hAB]
  have hb₀ : MonomialBasis r s A₀ B₀ v₀ := by
    intro i
    ext j
    have he := congrFun (hb i) j
    have hh := (algebraMap F L).map_mulVec (A₀ ^ r i * B₀ ^ s i) v₀ j
    have hp : (A₀ ^ r i * B₀ ^ s i).map (algebraMap F L) = A ^ r i * B ^ s i := by
      change f (A₀ ^ r i * B₀ ^ s i) = _
      rw [map_mul, map_pow, map_pow, hfA, hfB]
    rw [hp] at hh
    change algebraMap F L ((A₀ ^ r i * B₀ ^ s i).mulVec v₀ j) = _
    rw [hh]
    change ((A ^ r i * B ^ s i).mulVec v) j = _
    rw [he]
    by_cases hij : j = i
    · subst j
      simp
    · simp [hij]
  have hgen : IntermediateField.adjoin K (tripleEntries A₀ B₀ v₀) = ⊤ := by
    apply IntermediateField.map_injective F.val
    rw [IntermediateField.adjoin_map]
    have him : F.val '' tripleEntries A₀ B₀ v₀ = tripleEntries A B v := by
      simp only [tripleEntries, Set.image_union, ← Set.range_comp]
      rfl
    rw [him]
    change F = (⊤ : IntermediateField K F).map F.val
    ext x
    constructor
    · intro hx
      exact ⟨⟨x,hx⟩, IntermediateField.mem_top, rfl⟩
    · rintro ⟨x, _, rfl⟩
      exact x.property
  exact ⟨F, generated_chart_field_bound hn r s A₀ B₀ v₀ hA₀ hB₀ hAB₀ hb₀ hgen,
    hAF, hBF, hvF⟩

end PermanentBorder.PunctualCharts

end OAI
