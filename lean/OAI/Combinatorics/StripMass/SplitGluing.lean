import Mathlib
import OAI.Combinatorics.StripMass.ProjectionInjection

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

lemma functionMatrix_omit_glue_adjoint {K : Type*} [CommRing K] {n : ℕ}
    (r : Fin (n+1)) :
    (glueMatrix (Fin.last (n+1)) : Matrix _ _ K) *
        functionMatrix (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) =
      functionMatrix (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) *
        glueMatrix (Fin.last n) := by
  simpa only [Pairing.omit_last] using
    functionMatrix_glue_adjoint (K:=K) (Fin.succAboveOrderEmb r.castSucc) (Fin.last n)

lemma position_padTop_root_ne {n : ℕ} (a : Position n) :
    Fin.last n ≠ a.padTop.left ∧ Fin.last n ≠ a.padTop.right := by
  constructor
  · intro he
    have hv := congrArg Fin.val he
    have := a.left.isLt
    simp only [Position.padTop,Fin.val_last,Fin.val_castSucc] at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    have := a.right.isLt
    simp only [Position.padTop,Fin.val_last,Fin.val_castSucc] at hv
    omega

lemma mergeMap_glue_adjoint {n m : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    (glueMatrix (Fin.last (n+1)) : Matrix _ _ (SpectralField m)) *
        mergeMap r (show r+2≤n+2 by omega) =
      (mergeProjection r (show r+2≤n+2 by omega)).transpose * glueMatrix (Fin.last n) := by
  let b : Fin (n+1) := ⟨r+1,by omega⟩
  let a := PartialColumn.rowPosition r hr
  have ha : (Fin.succAboveOrderEmb b.castSucc) (Fin.last n) ≠ a.padTop.left := by
    rw [Pairing.omit_last]; exact (position_padTop_root_ne a).1
  have hb : (Fin.succAboveOrderEmb b.castSucc) (Fin.last n) ≠ a.padTop.right := by
    rw [Pairing.omit_last]; exact (position_padTop_root_ne a).2
  have h := splitProjection_glue_adjoint (Fin.succAboveOrderEmb b.castSucc)
    a.padTop (mergeWeights (constF m phase)) (Fin.last n) ha hb
  rw [Pairing.omit_last] at h
  exact h

lemma twoVacancyInsertion_glue_adjoint {K : Type*} [CommRing K] {n : ℕ}
    (r : ℕ) (hr : r+2≤n+2) :
    (glueMatrix (Fin.last (n+2)) : Matrix _ _ K) *
        twoVacancyInsertion r (show r+2≤n+3 by omega) =
      twoVacancyInsertion r (show r+2≤n+3 by omega) * glueMatrix (Fin.last n) := by
  let b : Fin (n+2) := ⟨r+1,by omega⟩
  let a : Fin (n+1) := ⟨r,by omega⟩
  let B := functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb b.castSucc))
  let A := functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.castSucc))
  calc
    _ = (glueMatrix (Fin.last (n+2))*B)*A := (Matrix.mul_assoc _ _ _).symm
    _ = (B*glueMatrix (Fin.last (n+1)))*A :=
      congrArg (fun M => M*A) (functionMatrix_omit_glue_adjoint b)
    _ = B*(glueMatrix (Fin.last (n+1))*A) := Matrix.mul_assoc _ _ _
    _ = B*(A*glueMatrix (Fin.last n)) :=
      congrArg (fun M => B*M) (functionMatrix_omit_glue_adjoint a)
    _ = (B*A)*glueMatrix (Fin.last n) := (Matrix.mul_assoc _ _ _).symm

lemma deletionMap_glue_adjoint {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    (glueMatrix (Fin.last (n+2)) : Matrix _ _ (SpectralField m)) *
        deletionMap r (show r+2≤n+3 by omega) =
      (deletionProjection r (show r+2≤n+3 by omega)).transpose * glueMatrix (Fin.last n) := by
  have adjoint {ι κ : Type} [Fintype ι] [Fintype κ]
      (G L : Matrix ι ι (SpectralField m)) (E : Matrix ι κ (SpectralField m))
      (H : Matrix κ κ (SpectralField m)) (hL : G*L=L.transpose*G) (hE : G*E=E*H) :
      G*(L*E) = (E.transpose*L).transpose*H := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
      hL, Matrix.mul_assoc, hE, ← Matrix.mul_assoc]
  let a := PartialColumn.rowPosition r hr
  let L := localR a.padTop (deletionWeights : Weights (SpectralField m))
  let E := twoVacancyInsertion (K:=SpectralField m) (n:=n+1) r (show r+2≤(n+1)+2 by omega)
  let G := glueMatrix (K:=SpectralField m) (Fin.last (n+2))
  let H := glueMatrix (K:=SpectralField m) (Fin.last n)
  have hL : G*L=L.transpose*G := localR_glue_adjoint a.padTop (Fin.last (n+2))
    (position_padTop_root_ne a).1 (position_padTop_root_ne a).2 deletionWeights
  have hE : G*E=E*H := twoVacancyInsertion_glue_adjoint r hr
  have h := adjoint G L E H hL hE
  simp only [deletionProjection] at h ⊢
  dsimp +instances only [G, L, E, H, a, deletionMap, twoVacancyInsertion,
    CStarMatrix, CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid, CStarMatrix.ofMatrix,
    Equiv.refl, Equiv.symm] at h ⊢
  simpa only [Equiv.coe_fn_mk, id_eq, PartialColumn.rowPosition, Position.padTop,
    Fin.castSucc_mk] using h


theorem sourceGlue_merge {n m : ℕ} (r : ℕ) (hr : r+2≤n+1)
    (v : SourcePairing (n+1) → SpectralField m) (w : SourcePairing n → SpectralField m) :
    sourceGlue (n+1) v ((sourceBlock (mergeMap r (show r+2≤n+2 by omega))).mulVec w) =
      sourceGlue n ((sourceBlock (mergeProjection r (show r+2≤n+2 by omega))).mulVec v) w := by
  have h : sourceBlock (glueMatrix (K:=SpectralField m) (Fin.last (n+1))) *
      sourceBlock (mergeMap (m:=m) r (show r+2≤n+2 by omega)) =
      (sourceBlock (mergeProjection (m:=m) r (show r+2≤n+2 by omega))).transpose *
      sourceBlock (glueMatrix (K:=SpectralField m) (Fin.last n)) :=
    ((glueMatrix_last (n+1)).source_mul _).symm.trans
      ((congrArg sourceBlock (mergeMap_glue_adjoint (m:=m) r hr)).trans
        ((mergeProjection_last r hr).transpose.source_mul _))
  unfold sourceGlue
  rw [Matrix.mulVec_mulVec,h,←Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]

 

theorem sourceGlue_delete {n m : ℕ} (r : ℕ) (hr : r+2≤n+2)
    (v : SourcePairing (n+2) → SpectralField m) (w : SourcePairing n → SpectralField m) :
    sourceGlue (n+2) v ((sourceBlock (deletionMap r (show r+2≤n+3 by omega))).mulVec w) =
      sourceGlue n ((sourceBlock (deletionProjection r (show r+2≤n+3 by omega))).mulVec v) w := by
  have h : sourceBlock (glueMatrix (K:=SpectralField m) (Fin.last (n+2))) *
      sourceBlock (deletionMap (m:=m) r (show r+2≤n+3 by omega)) =
      (sourceBlock (deletionProjection (m:=m) r (show r+2≤n+3 by omega))).transpose *
      sourceBlock (glueMatrix (K:=SpectralField m) (Fin.last n)) :=
    ((glueMatrix_last (n+2)).source_mul _).symm.trans
      ((congrArg sourceBlock (deletionMap_glue_adjoint (m:=m) r hr)).trans
        ((deletionProjection_last r hr).transpose.source_mul _))
  unfold sourceGlue
  rw [Matrix.mulVec_mulVec,h,←Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]

lemma sourceGlue_smul_right {K : Type*} [CommRing K] (n : ℕ) (a : K)
    (v w : SourcePairing n → K) : sourceGlue n v (a • w) = a*sourceGlue n v w := by
  simpa only [one_smul,one_mul] using sourceGlue_scale n (1:K) a v w

lemma sourceGlue_smul_left {K : Type*} [CommRing K] (n : ℕ) (a : K)
    (v w : SourcePairing n → K) : sourceGlue n (a • v) w = a*sourceGlue n v w := by
  simpa only [one_smul,mul_one] using sourceGlue_scale n a (1:K) v w

lemma sourceGlue_algMap {R K L : Type*} [CommSemiring R] [CommRing K] [CommRing L]
    [Algebra R K] [Algebra R L] (f : K →ₐ[R] L) (n : ℕ)
    (v w : SourcePairing n → K) :
    f (sourceGlue n v w) = sourceGlue n (f ∘ v) (f ∘ w) :=
  sourceGlue_map f.toRingHom n v w

 

theorem polynomialNorthGluing_merge (n : ℕ) :
    pairEvaluation n 2 (polynomialNorthGluing (n+2)) =
      mergePairScalar n ^ 2 * mergeEvaluation n (polynomialNorthGluing (n+1)) := by
  unfold polynomialNorthGluing
  rw [sourceGlue_algMap (pairEvaluation n 2)]
  have h : ((pairEvaluation n 2) ∘ polynomialNorthSource (n+2)) =
      mergePairScalar n •
        (sourceBlock (mergeMap (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
          (fun q => mergeEvaluation n (polynomialNorthSource (n+1) q)) := by
    funext p
    exact polynomialNorthSource_merge n p
  rw [h,sourceGlue_smul_right,sourceGlue_merge 0 (show 2≤n+2 by omega)]
  simp only [Function.comp_def]
  rw [polynomialNorthSource_reflected_merge n,sourceGlue_smul_left]
  rw [sourceGlue_algMap (mergeEvaluation n)]
  simp only [pow_two,mul_assoc]
  rfl

 

theorem polynomialNorthGluing_delete (n : ℕ) :
    pairEvaluation n 3 (polynomialNorthGluing (n+2)) =
      deletePairScalar n ^ 2 * deleteEvaluation n (polynomialNorthGluing n) := by
  unfold polynomialNorthGluing
  rw [sourceGlue_algMap (pairEvaluation n 3)]
  have h : ((pairEvaluation n 3) ∘ polynomialNorthSource (n+2)) =
      deletePairScalar n •
        (sourceBlock (deletionMap (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
          (fun q => deleteEvaluation n (polynomialNorthSource n q)) := by
    funext p
    exact polynomialNorthSource_delete n p
  rw [h,sourceGlue_smul_right,sourceGlue_delete 0 (show 2≤n+2 by omega)]
  simp only [Function.comp_def]
  rw [polynomialNorthSource_reflected_delete n,sourceGlue_smul_left]
  rw [sourceGlue_algMap (deleteEvaluation n)]
  simp only [pow_two,mul_assoc]
  rfl

 

 


lemma lastCoefficient_cons_padBottom {K : Type*} [CommRing K] {n : ℕ}
    (r : Tile → K) (w : Fin n → Tile → K) (p q : Pairing (n+1)) :
    lastCoefficient (Fin.cons r w) q.padBottom p.padBottom =
      r .vacant * lastCoefficient w q p := by
  have h := rawColumn_padBottom (Fin.snoc w (fun _ => (1:K))) r p q
  rw [Fin.cons_snoc_eq_snoc_cons,rawColumn_last_factor,rawColumn_last_factor] at h
  simpa only [mul_one] using h

lemma lastFactor_padBottom {K : Type*} [CommRing K] {n : ℕ}
    (d c C : K) (p q : Pairing (n+1)) :
    lastFactor d c C p.padBottom q.padBottom = lastFactor d c C p q := by
  simp only [lastFactor,←Fin.succ_last,Pairing.padBottom_occupied_succ]

lemma firstZeroPolynomial_padBottom {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) (q : Pairing (n+1)) :
    firstZeroPolynomial w d c C P q.padBottom = lastTransform w d c C P q := by
  unfold firstZeroPolynomial lastTransform
  symm
  apply Fintype.sum_of_injective Pairing.padBottom Pairing.padBottom_injective
  · intro p hp
    have h : p.Occupied 0 := by
      by_contra h
      exact hp ⟨p.restrict (Fin.succOrderEmb (n+1)),p.padBottom_restrict h⟩
    simp [vacantBottomExtension,h]
  · intro p
    rw [lastCoefficient_cons_padBottom,lastFactor_padBottom,vacantBottomExtension_padBottom]
    simp [Weights.tile]

lemma rationalFirstZeroPolynomial_vacant (n : ℕ) (q : Pairing (n+1)) :
    firstZeroPolynomial (fun j => (spectralWeights n j).tile)
      (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) q.padBottom =
      (Polynomial.X+Polynomial.C (constF n C))*rationalNodalPolynomial n q := by
  rw [firstZeroPolynomial_padBottom]
  exact sub_eq_zero.mp (rationalResidualPolynomial_zero n q)

 
def SourcePairing.padBottom {n : ℕ} (p : SourcePairing n) : SourcePairing (n+1) :=
  ⟨p.val.padBottom,(p.val.padBottom_occupied_succ (Fin.last n)).mpr p.property⟩

lemma SourcePairing.padBottom_injective {n : ℕ} :
    Function.Injective (@SourcePairing.padBottom n) := by
  intro p q h
  exact Subtype.ext (Pairing.padBottom_injective (congrArg Subtype.val h))

lemma SourcePairing.padBottom_range {n : ℕ} (p : SourcePairing (n+1)) :
    p ∈ Set.range SourcePairing.padBottom ↔ ¬p.val.Occupied 0 := by
  constructor
  · rintro ⟨q,rfl⟩
    exact q.val.padBottom_not_occupied_zero
  · intro h
    have hp := p.val.padBottom_restrict h
    let q := p.val.restrict (Fin.succOrderEmb (n+1))
    have hq : q.Occupied (Fin.last n) := by
      rw [←Pairing.padBottom_occupied_succ q (Fin.last n),hp]
      exact p.property
    exact ⟨⟨q,hq⟩,Subtype.ext hp⟩

def vacantBottomSourceExtension {K : Type*} [Zero K] {n : ℕ}
    (v : SourcePairing n → K) (p : SourcePairing (n+1)) : K :=
  if h : p ∈ Set.range SourcePairing.padBottom then v (Classical.choose h) else 0

lemma vacantBottomSourceExtension_padBottom {K : Type*} [Zero K] {n : ℕ}
    (v : SourcePairing n → K) (q : SourcePairing n) :
    vacantBottomSourceExtension v q.padBottom=v q := by
  rw [vacantBottomSourceExtension,dite_eq_left ⟨q,rfl⟩]
  congr 1
  exact SourcePairing.padBottom_injective (Classical.choose_spec (show q.padBottom ∈ Set.range SourcePairing.padBottom from ⟨q,rfl⟩))

lemma coefficient_X_add_source {n : ℕ} (p : SourcePairing n) :
    ((Polynomial.X+Polynomial.C (constF n C))*rationalNodalPolynomial n p.val).coeff n =
      northNumerator n p := by
  by_cases hn : n=0
  · subst n
    exact (p.ne_empty (p.val.eq_empty_of_le_one (by omega))).elim
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hz := rationalNodalPolynomial_degree (k+1) p.val (k+1) (by simp [p.property])
    simp only [add_mul,Polynomial.coeff_add,Polynomial.coeff_X_mul,Polynomial.coeff_C_mul,hz,
      mul_zero,add_zero,northNumerator,Nat.succ_sub_one]

 

theorem polynomialNorthSource_firstFlat (n : ℕ) (p : SourcePairing n) :
    firstFlatEvaluation n (polynomialNorthSource (n+1) p.padBottom) =
      (∏ j:Fin n,(spectralA j+constF n C))*evalLaurent (polynomialNorthSource n p) := by
  have h := congrFun (rationalNodalPolynomial_firstFlat
    (vacuumData n).interpolant (vacuumData (n+1)).P
    (vacuumData (n+1)).map_P) p.val.padBottom
  have hc := congrArg (fun P : Polynomial (SpectralField n) => P.coeff n) h
  rw [rationalFirstZeroPolynomial_vacant,Polynomial.coeff_map,Polynomial.coeff_C_mul,
    coefficient_X_add_source] at hc
  change firstFlatEvaluation n (((vacuumData (n+1)).P p.val.padBottom).coeff n) = _ at hc
  rw [polynomialNorthSource_eval_numerator]
  unfold polynomialNorthSource
  rw [map_mul]
  simp only [Nat.add_sub_cancel,SourcePairing.padBottom]
  rw [hc]
  rw [show firstFlatEvaluation n (constantL (n+1) (1/(2*(d:ℂ)))) =
    constF n (1/(2*(d:ℂ))) from torusEvaluation_constant _ _ _]
  ring

 

theorem polynomialNorthSource_firstThree (n : ℕ) :
    (fun p => firstThreeEvaluation n (polynomialNorthSource (n+1) p)) =
      (∏ j:Fin n,(spectralA j+constF n C)) •
        vacantBottomSourceExtension (fun p => evalLaurent (polynomialNorthSource n p)) := by
  funext p
  have h := congrFun (rationalNodalPolynomial_firstThree
    (polynomialVacuumVector n) (polynomialVacuumVector_eval n)
    (vacuumData (n+1)).P (vacuumData (n+1)).map_P) p.val
  have hc := congrArg (fun P : Polynomial (SpectralField n) => P.coeff n) h
  rw [Polynomial.coeff_map,Polynomial.coeff_C_mul] at hc
  change firstThreeEvaluation n (((vacuumData (n+1)).P p.val).coeff n) = _ at hc
  simp only [Pi.smul_apply,smul_eq_mul]
  by_cases hp : p ∈ Set.range SourcePairing.padBottom
  · obtain ⟨q,rfl⟩ := hp
    simp only [SourcePairing.padBottom] at hc
    rw [firstThreePolynomial_padBottom,coefficient_X_add_source] at hc
    rw [vacantBottomSourceExtension_padBottom,polynomialNorthSource_eval_numerator]
    unfold polynomialNorthSource
    rw [map_mul]
    simp only [Nat.add_sub_cancel,SourcePairing.padBottom]
    rw [hc,show firstThreeEvaluation n (constantL (n+1) (1/(2*(d:ℂ)))) =
      constF n (1/(2*(d:ℂ))) from torusEvaluation_constant _ _ _]
    ring
  · have ho : p.val.Occupied 0 := not_not.mp (fun h => hp ((SourcePairing.padBottom_range p).mpr h))
    simp only [firstThreePolynomial,vacantBottomExtension,ho,ite_true,mul_zero,
      Polynomial.coeff_zero] at hc
    simp only [vacantBottomSourceExtension,dite_eq_right hp,mul_zero]
    unfold polynomialNorthSource
    rw [map_mul]
    simp only [Nat.add_sub_cancel]
    rw [hc,mul_zero]

lemma firstFlatEvaluation_reflect {n : ℕ} (f : Laurent (n+1)) :
    firstFlatEvaluation n (reflectLaurent (n+1) f) =
      reflectSpectral n (firstThreeEvaluation n f) := by
  unfold firstFlatEvaluation firstThreeEvaluation
  rw [torusEvaluation_reflect,
    torusEvaluation_fieldMap (reflectSpectral n) (reflectSpectral_const n)]
  congr 2
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [firstFlatPoint,firstThreePoint,Fin.cons_zero,div_one,map_pow,reflectSpectral_const]
  · simp only [firstFlatPoint,firstThreePoint,Fin.cons_succ,reflectSpectral_variable]

lemma firstThreeEvaluation_reflect {n : ℕ} (f : Laurent (n+1)) :
    firstThreeEvaluation n (reflectLaurent (n+1) f) =
      reflectSpectral n (firstFlatEvaluation n f) := by
  have h := firstFlatEvaluation_reflect (reflectLaurent (n+1) f)
  rw [reflectLaurent_involutive] at h
  exact ((reflectSpectral_involutive n _).symm.trans (congrArg (reflectSpectral n) h).symm)

lemma vacantBottomSourceExtension_map {K L : Type*} [Zero K] [Zero L] {n : ℕ}
    (f : K → L) (hf : f 0=0) (v : SourcePairing n → K) (p : SourcePairing (n+1)) :
    f (vacantBottomSourceExtension v p) = vacantBottomSourceExtension (f ∘ v) p := by
  unfold vacantBottomSourceExtension
  split_ifs <;> simp [hf]

lemma sourceGlue_vacantBottom_right {K : Type*} [CommRing K] {n : ℕ}
    (v : SourcePairing (n+1) → K) (w : SourcePairing n → K) :
    sourceGlue (n+1) v (vacantBottomSourceExtension w) =
      sourceGlue n (v ∘ SourcePairing.padBottom) w := by
  rw [sourceGlue_eq_sum,sourceGlue_eq_sum]
  have hinner (p : SourcePairing (n+1)) :
      (∑ q : SourcePairing (n+1), v p *
        ((if Pairing.GluesAt (Fin.last (n+1)) p.val q.val then (1:K) else 0) *
          vacantBottomSourceExtension w q)) =
        ∑ q : SourcePairing n, v p *
          ((if Pairing.GluesAt (Fin.last (n+1)) p.val q.padBottom.val then (1:K) else 0)*w q) := by
    symm
    apply Fintype.sum_of_injective SourcePairing.padBottom SourcePairing.padBottom_injective
    · intro q hq
      simp [vacantBottomSourceExtension,hq]
    · intro q
      rw [vacantBottomSourceExtension_padBottom]
  simp_rw [hinner]
  symm
  apply Fintype.sum_of_injective SourcePairing.padBottom SourcePairing.padBottom_injective
  · intro p hp
    apply Finset.sum_eq_zero
    intro q _
    have hh : ¬Pairing.GluesAt (Fin.last (n+1)) p.val q.padBottom.val := by
      intro h
      have ho : ¬p.val.Occupied 0 := fun ho =>
        q.val.padBottom_not_occupied_zero ((h.2.1 0).mp ho)
      exact hp ((SourcePairing.padBottom_range p).mpr ho)
    rw [ite_eq_right hh,zero_mul,mul_zero]
  · intro p
    apply Finset.sum_congr rfl
    intro q _
    have hh : Pairing.GluesAt (Fin.last (n+1)) p.padBottom.val q.padBottom.val ↔
        Pairing.GluesAt (Fin.last n) p.val q.val :=
      Pairing.gluesAt_map (Fin.succOrderEmb _) (Fin.last n) p.val q.val
    simp only [hh,Function.comp_apply]

lemma sourceGlue_vacantBottom_left {K : Type*} [CommRing K] {n : ℕ}
    (v : SourcePairing n → K) (w : SourcePairing (n+1) → K) :
    sourceGlue (n+1) (vacantBottomSourceExtension v) w =
      sourceGlue n v (w ∘ SourcePairing.padBottom) := by
  rw [sourceGlue_symmetric,sourceGlue_vacantBottom_right,sourceGlue_symmetric]

 

theorem polynomialNorthGluing_firstFlat (n : ℕ) :
    firstFlatEvaluation n (polynomialNorthGluing (n+1)) =
      (∏ j:Fin n,(spectralA j+constF n C))^2 * evalLaurent (polynomialNorthGluing n) := by
  unfold polynomialNorthGluing
  rw [sourceGlue_algMap (firstFlatEvaluation n)]
  have hv : (fun p : SourcePairing (n+1) => firstFlatEvaluation n
      (reflectLaurent (n+1) (polynomialNorthSource (n+1) p))) =
      (∏ j:Fin n,(spectralA j+constF n C)) •
        vacantBottomSourceExtension (fun p => evalLaurent (reflectLaurent n (polynomialNorthSource n p))) := by
    funext p
    rw [firstFlatEvaluation_reflect,congrFun (polynomialNorthSource_firstThree n) p]
    simp only [Pi.smul_apply,smul_eq_mul,map_mul,map_prod,map_add,reflectSpectral_const,
      reflectSpectral_spectralA,vacantBottomSourceExtension_map _ (map_zero _)]
    congr 2
    funext q
    exact reflectSpectral_evalLaurent _
  change ((firstFlatEvaluation n) ∘ (fun p => reflectLaurent (n+1) (polynomialNorthSource (n+1) p))) = _ at hv
  rw [hv,sourceGlue_smul_left,sourceGlue_vacantBottom_left]
  have hw : ((firstFlatEvaluation n) ∘ polynomialNorthSource (n+1)) ∘ SourcePairing.padBottom =
      (∏ j:Fin n,(spectralA j+constF n C)) •
        (fun p => evalLaurent (polynomialNorthSource n p)) := by
    funext p
    exact polynomialNorthSource_firstFlat n p
  rw [hw,sourceGlue_smul_right]
  unfold evalLaurent
  rw [sourceGlue_map]
  simp only [pow_two,mul_assoc]
  rfl

 
theorem polynomialNorthGluing_firstThree (n : ℕ) :
    firstThreeEvaluation n (polynomialNorthGluing (n+1)) =
      (∏ j:Fin n,(spectralA j+constF n C))^2 * evalLaurent (polynomialNorthGluing n) := by
  rw [←polynomialNorthGluing_reflection (n+1),firstThreeEvaluation_reflect,
    polynomialNorthGluing_firstFlat]
  simp only [map_mul,map_pow,map_prod,map_add,reflectSpectral_const,
    reflectSpectral_spectralA,reflectSpectral_evalLaurent,polynomialNorthGluing_reflection]

 

 


 
def reflectExponentAt {n : ℕ} (i : Fin n) (e : Fin n → ℤ) : Fin n → ℤ :=
  Function.update e i (-e i)

@[simp] lemma reflectExponentAt_same {n : ℕ} (i : Fin n) (e : Fin n → ℤ) :
    reflectExponentAt i e i = -e i := by simp [reflectExponentAt]
lemma reflectExponentAt_other {n : ℕ} (i j : Fin n) (h : j ≠ i) (e : Fin n → ℤ) :
    reflectExponentAt i e j = e j := by simp [reflectExponentAt,h]
@[simp] lemma reflectExponentAt_zero {n : ℕ} (i : Fin n) :
    reflectExponentAt i 0 = 0 := by ext j; simp [reflectExponentAt]
lemma reflectExponentAt_add {n : ℕ} (i : Fin n) (e f : Fin n → ℤ) :
    reflectExponentAt i (e+f) = reflectExponentAt i e + reflectExponentAt i f := by
  ext j
  by_cases h:j=i <;> simp [reflectExponentAt,h,add_comm]
@[simp] lemma reflectExponentAt_neg {n : ℕ} (i : Fin n) (e : Fin n → ℤ) :
    reflectExponentAt i (-e) = -reflectExponentAt i e := by
  ext j
  by_cases h:j=i <;> simp [reflectExponentAt,h]
@[simp] lemma reflectExponentAt_involutive {n : ℕ} (i : Fin n) (e : Fin n → ℤ) :
    reflectExponentAt i (reflectExponentAt i e) = e := by
  ext j
  by_cases h:j=i <;> simp [reflectExponentAt,h]

def rowReflectionMonomial {n : ℕ} (i : Fin n) :
    Multiplicative (Fin n → ℤ) →* Laurent n where
  toFun e := monomialL (reflectExponentAt i e.toAdd) (phase ^ (3 * e.toAdd i))
  map_one' := by simp [monomialL]; rfl
  map_mul' e f := by
    change monomialL (reflectExponentAt i (e.toAdd+f.toAdd))
        (phase ^ (3 * (e.toAdd i+f.toAdd i))) = _
    rw [mul_add, zpow_add₀ phase_ne_zero, reflectExponentAt_add]
    exact (AddMonoidAlgebra.single_mul_single _ _ _ _).symm

def rowReflectLaurent {n : ℕ} (i : Fin n) : Laurent n →+* Laurent n :=
  (AddMonoidAlgebra.lift ℂ (Laurent n) (Fin n → ℤ) (rowReflectionMonomial i)).toRingHom

@[simp] lemma rowReflectLaurent_monomial {n : ℕ} (i : Fin n) (e : Fin n → ℤ) (z : ℂ) :
    rowReflectLaurent i (monomialL e z) =
      monomialL (reflectExponentAt i e) (z * phase ^ (3 * e i)) := by
  change AddMonoidAlgebra.lift ℂ _ _ (rowReflectionMonomial i) (AddMonoidAlgebra.single e z) = _
  rw [AddMonoidAlgebra.lift_single]
  change z • AddMonoidAlgebra.single _ _ = AddMonoidAlgebra.single _ _
  rw [AddMonoidAlgebra.smul_single, smul_eq_mul]
  rfl

lemma rowReflectLaurent_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (rowReflectLaurent i) := by
  have h : (rowReflectLaurent i).comp (rowReflectLaurent i) = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change rowReflectLaurent i (rowReflectLaurent i (monomialL _ _)) = monomialL _ _
    all_goals rw [rowReflectLaurent_monomial,rowReflectLaurent_monomial]
    all_goals simp only [reflectExponentAt_involutive,reflectExponentAt_same,mul_neg,
      mul_assoc,← zpow_add₀ phase_ne_zero,add_neg_cancel,zpow_zero,mul_one]
  exact fun f => DFunLike.congr_fun h f

def rowReflectSpectral {n : ℕ} (i : Fin n) : SpectralField n →+* SpectralField n :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing n) (SpectralField n)).comp (rowReflectLaurent i))
    ((IsFractionRing.injective (SpectralRing n) (SpectralField n)).comp
      (rowReflectLaurent_involutive i).injective)

@[simp] lemma rowReflectSpectral_evalLaurent {n : ℕ} (i : Fin n) (f : Laurent n) :
    rowReflectSpectral i (evalLaurent f) = evalLaurent (rowReflectLaurent i f) :=
  IsFractionRing.lift_algebraMap _ _

lemma rowReflectSpectral_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (rowReflectSpectral i) := by
  have h : (rowReflectSpectral i).comp (rowReflectSpectral i) = RingHom.id _ := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change rowReflectSpectral i (rowReflectSpectral i (evalLaurent f)) = evalLaurent f
    rw [rowReflectSpectral_evalLaurent,rowReflectSpectral_evalLaurent,rowReflectLaurent_involutive]
  exact fun f => DFunLike.congr_fun h f

@[simp] lemma rowReflectSpectral_const {n : ℕ} (i : Fin n) (z : ℂ) :
    rowReflectSpectral i (constF n z) = constF n z := by
  have hc : constF n z = evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc,rowReflectSpectral_evalLaurent]
  change evalLaurent (rowReflectLaurent i (monomialL 0 z)) = evalLaurent (monomialL 0 z)
  rw [rowReflectLaurent_monomial]
  simp

@[simp] lemma rowReflectSpectral_variable {n : ℕ} (i j : Fin n) :
    rowReflectSpectral i (variableF j) =
      if j=i then constF n phase ^ 3 / variableF j else variableF j := by
  change rowReflectSpectral i (evalLaurent (monomialL (variableExponent j) 1)) = _
  rw [rowReflectSpectral_evalLaurent,rowReflectLaurent_monomial]
  by_cases h:j=i
  · subst j
    have he : reflectExponentAt i (variableExponent i) = -variableExponent i := by
      ext k; by_cases hh:k=i <;> simp [reflectExponentAt,variableExponent,hh]
    rw [he]
    simp only [variableExponent,Pi.single_eq_same,one_mul,mul_one,ite_true,zpow_ofNat]
    change evalLaurent (monomialL (-variableExponent i) (phase^3)) = _
    rw [evalLaurent,map_monomialL_neg_variable]
    simp [constF,div_eq_mul_inv]
  · have he : reflectExponentAt i (variableExponent j) = variableExponent j := by
      ext k
      by_cases hh:k=i
      · subst k; simp [reflectExponentAt,variableExponent,Ne.symm h]
      · simp [reflectExponentAt,hh]
    rw [he]
    simp only [variableExponent,Pi.single_apply,ite_eq_right (Ne.symm h),mul_zero,zpow_zero,
      one_mul,ite_eq_right h]
    rfl

@[simp] lemma rowReflectSpectral_torusSin {n : ℕ} (i : Fin n) (z : SpectralField n) :
    rowReflectSpectral i (torusSin z) = torusSin (rowReflectSpectral i z) := by
  simp [torusSin,map_div₀,map_inv₀,map_ofNat]
@[simp] lemma rowReflectSpectral_torusCos {n : ℕ} (i : Fin n) (z : SpectralField n) :
    rowReflectSpectral i (torusCos z) = torusCos (rowReflectSpectral i z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]
@[simp] lemma rowReflectSpectral_torusL {n : ℕ} (i : Fin n) (z : SpectralField n) :
    rowReflectSpectral i (torusL z) = torusL (rowReflectSpectral i z) := by simp [torusL]
@[simp] lemma rowReflectSpectral_torusWeights {n : ℕ} (i : Fin n) (z : SpectralField n) :
    (torusWeights z).map (rowReflectSpectral i) = torusWeights (rowReflectSpectral i z) := by
  simp [Weights.map,torusWeights,map_div₀]

@[simp] lemma rowReflectSpectral_spectralA {n : ℕ} (i j : Fin n) :
    rowReflectSpectral i (spectralA j) = spectralA j := by
  simp only [spectralA,rowReflectSpectral_torusCos,map_div₀,map_pow,
    rowReflectSpectral_const,rowReflectSpectral_variable]
  split_ifs
  · unfold torusCos
    field_simp [variableF_ne_zero,constF_phase_ne_zero]
    ring
  · rfl
@[simp] lemma rowReflectSpectral_normalization {n : ℕ} (i : Fin n) :
    rowReflectSpectral i (spectralNormalization n) = spectralNormalization n := by
  simp only [spectralNormalization,map_scalarNormalization,rowReflectSpectral_const,
    rowReflectSpectral_spectralA]

lemma reflectLaurent_rowReflect {n : ℕ} (i : Fin n) (f : Laurent n) :
    reflectLaurent n (rowReflectLaurent i f) = rowReflectLaurent i (reflectLaurent n f) := by
  have he (e : Fin n → ℤ) : ∑ j, reflectExponentAt i e j = ∑ j,e j - 2*e i := by
    rw [reflectExponentAt,Finset.sum_update_of_mem (Finset.mem_univ i)]
    have h := Finset.sum_sdiff (f:=e) (Finset.subset_univ ({i} : Finset (Fin n)))
    simp only [Finset.sum_singleton] at h
    omega
  have h : (reflectLaurent n).comp (rowReflectLaurent i) =
      (rowReflectLaurent i).comp (reflectLaurent n) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change reflectLaurent n (rowReflectLaurent i (monomialL _ _)) =
      rowReflectLaurent i (reflectLaurent n (monomialL _ _))
    all_goals rw [rowReflectLaurent_monomial,reflectLaurent_monomial,
      reflectLaurent_monomial,rowReflectLaurent_monomial,reflectExponentAt_neg]
    all_goals simp only [mul_assoc,←zpow_add₀ phase_ne_zero,he,Pi.neg_apply]
    all_goals (congr 2; ring_nf)
  exact DFunLike.congr_fun h f

lemma reflectSpectral_rowReflect {n : ℕ} (i : Fin n) (f : SpectralField n) :
    reflectSpectral n (rowReflectSpectral i f) = rowReflectSpectral i (reflectSpectral n f) := by
  have h : (reflectSpectral n).comp (rowReflectSpectral i) =
      (rowReflectSpectral i).comp (reflectSpectral n) := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change reflectSpectral n (rowReflectSpectral i (evalLaurent f)) =
      rowReflectSpectral i (reflectSpectral n (evalLaurent f))
    simp only [reflectSpectral_evalLaurent,rowReflectSpectral_evalLaurent,reflectLaurent_rowReflect]
  exact DFunLike.congr_fun h f

lemma rowReflectLaurent_perm {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin n)) (f : Laurent n) :
    rowReflectLaurent (σ i) (permLaurent σ f) = permLaurent σ (rowReflectLaurent i f) := by
  have he (e : Fin n → ℤ) : reflectExponentAt (σ i) (e ∘ σ.symm) = reflectExponentAt i e ∘ σ.symm := by
    ext j
    by_cases h:j=σ i
    · simp [reflectExponentAt,h]
    · have h' : σ.symm j ≠ i := by intro hh; exact h ((σ.apply_symm_apply j).symm.trans (congrArg σ hh))
      simp [reflectExponentAt,h,h']
  have h : (rowReflectLaurent (σ i)).comp (permLaurent σ) =
      (permLaurent σ).comp (rowReflectLaurent i) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change rowReflectLaurent (σ i) (permLaurent σ (monomialL _ _)) =
      permLaurent σ (rowReflectLaurent i (monomialL _ _))
    all_goals rw [permLaurent_monomial,rowReflectLaurent_monomial,
      rowReflectLaurent_monomial,permLaurent_monomial]
    all_goals simp only [Function.comp_apply,Equiv.symm_apply_apply]; congr 1; exact he _
  exact DFunLike.congr_fun h f

end
end CriticalStrip.Diagram

end OAI
