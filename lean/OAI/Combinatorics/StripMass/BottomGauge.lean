import Mathlib
import OAI.Combinatorics.StripMass.SplitGluing

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

 
def occupancyGauge {K : Type*} [One K] {n : ℕ} (a : K) (p : Pairing n) (i : Fin n) : K :=
  if p.Occupied i then a else 1

@[simp] lemma occupancyGauge_empty {K : Type*} [One K] {n : ℕ} (a : K) (i : Fin n) :
    occupancyGauge a (empty n) i = 1 := by simp [occupancyGauge]

lemma rawColumn_bottom_gauge {K : Type*} [CommRing K] {n : ℕ}
    (w v : Fin (n+1) → Tile → K) (a : K)
    (htail : ∀ i : Fin n, v i.succ = w i.succ)
    (hbottom : ∀ t : Tile, ¬t.Occupied 0 →
      v 0 t * (if t.Occupied 1 then a else 1) =
      (if t.Occupied 2 then a else 1) * w 0 t)
    (p q : Pairing (n+1)) :
    rawColumn v q p * occupancyGauge a p 0 = occupancyGauge a q 0 * rawColumn w q p := by
  simp only [rawColumn,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs with h
  · rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    simp only [htail]
    have hh := hbottom (t 0) (h.south 0 rfl)
    simp only [h.west,h.east] at hh
    change v 0 (t 0) * occupancyGauge a p 0 = occupancyGauge a q 0 * w 0 (t 0) at hh
    calc
      _ = (v 0 (t 0)*occupancyGauge a p 0) * ∏ i:Fin n,w i.succ (t i.succ) := by ring
      _ = _ := by rw [hh]; ring
  · simp

lemma lastCoefficient_bottom_gauge {K : Type*} [CommRing K] {n : ℕ}
    (w v : Fin (n+1) → Tile → K) (a : K)
    (htail : ∀ i : Fin n, v i.succ = w i.succ)
    (hbottom : ∀ t : Tile, ¬t.Occupied 0 →
      v 0 t * (if t.Occupied 1 then a else 1) =
      (if t.Occupied 2 then a else 1) * w 0 t)
    (p q : Pairing (n+1+1)) :
    lastCoefficient v q p * occupancyGauge a p 0 =
      occupancyGauge a q 0 * lastCoefficient w q p := by
  simp only [lastCoefficient,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs with h
  · rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    simp only [htail]
    have hs : ¬(t 0).Occupied 0 := by simpa using h.south 0 rfl
    have hw : (t 0).Occupied 1 ↔ p.Occupied 0 := by simpa using h.west 0
    have he : (t 0).Occupied 2 ↔ q.Occupied 0 := by simpa using h.east 0
    have hh := hbottom (t 0) hs
    simp only [hw,he] at hh
    change v 0 (t 0) * occupancyGauge a p 0 = occupancyGauge a q 0 * w 0 (t 0) at hh
    calc
      _ = (v 0 (t 0)*occupancyGauge a p 0) * ∏ i:Fin n,w i.succ (t i.succ) := by ring
      _ = _ := by rw [hh]; ring
  · simp

lemma Weights.vacantSouth_gauge {K : Type*} [Field K] (w v : Weights K)
    (hA : v.A=w.U) (hB : v.B=w.B) (hU : v.U=w.A) (hw : w.U≠0)
    (t : Tile) (ht : ¬t.Occupied 0) :
    v.tile t * (if t.Occupied 1 then w.A/w.U else 1) =
      (if t.Occupied 2 then w.A/w.U else 1) * w.tile t := by
  cases t <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges,Weights.tile]
  <;> field_simp

lemma matrix_mulVec_gauge {K : Type*} [CommRing K] {I J : Type*} [Fintype I]
    (M M' : Matrix J I K) (a : I → K) (b : J → K)
    (h : ∀ j i,M' j i*a i=b j*M j i) (v : I → K) :
    M'.mulVec (fun i=>a i*v i) = fun j=>b j*M.mulVec v j := by
  funext j
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←mul_assoc,h]
  ring

lemma normalizedVacuum_gauge_pair {K : Type*} [Field K] {n : ℕ}
    (w v : Fin n → Weights K) (hw : VacuumRegular w) (hv : VacuumRegular v)
    (a : Pairing n → K) (he : a (empty n)=1)
    (hc : ∀ q p,column v q p*a p=a q*column w q p) :
    normalizedVacuum v = fun p=>a p*normalizedVacuum w p := by
  symm
  apply normalizedVacuum_unique _ hv
  constructor
  · change a (empty n)*normalizedVacuum w (empty n)=1
    rw [he,(normalizedVacuum_stationary w hw).1,one_mul]
  · rw [matrix_mulVec_gauge _ _ _ _ hc,(normalizedVacuum_stationary w hw).2]

 

 


lemma spectralRow_den_ne_zero {n : ℕ} (i : Fin n) : spectralA i + constF n C ≠ 0 := by
  rw [←twice_rowDenominator]
  exact mul_ne_zero (by norm_num) (rowDenominator_map_ne_zero i)

lemma rowReflectSpectral_weightsA {n : ℕ} (i : Fin n) :
    rowReflectSpectral i (spectralWeights n i).A = (spectralWeights n i).U := by
  have h := congrArg (rowReflectSpectral i) (clearedSpectralRow_vertical₀ i)
  simp only [clearedSpectralRow,Weights.tile,map_mul,map_add,map_ofNat,rowReflectSpectral_const,
    rowReflectSpectral_spectralA,rowReflectSpectral_torusSin,rowReflectSpectral_variable,ite_true] at h
  apply mul_left_cancel₀ (spectralRow_den_ne_zero i)
  exact h.trans (clearedSpectralRow_cap i).symm

lemma rowReflectSpectral_weightsU {n : ℕ} (i : Fin n) :
    rowReflectSpectral i (spectralWeights n i).U = (spectralWeights n i).A := by
  rw [←rowReflectSpectral_weightsA,rowReflectSpectral_involutive]

lemma rowReflectSpectral_weightsB {n : ℕ} (i : Fin n) :
    rowReflectSpectral i (spectralWeights n i).B = (spectralWeights n i).B := by
  have h := congrArg (rowReflectSpectral i) (clearedSpectralRow_diagonal₁ i)
  simp only [clearedSpectralRow,Weights.tile,map_mul,map_add,map_sub,rowReflectSpectral_const,
    rowReflectSpectral_spectralA] at h
  apply mul_left_cancel₀ (spectralRow_den_ne_zero i)
  exact h.trans (clearedSpectralRow_diagonal₁ i).symm

lemma spectralWeights_A_ne_zero {n : ℕ} (i : Fin n) : (spectralWeights n i).A≠0 := by
  have hd : constF n d ≠0 :=
    (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr (by exact_mod_cast d_ne_zero)
  have hs : torusSin (variableF i)≠0 := by
    apply torusSin_monomial_ne_zero _ _ 1 one_ne_zero
    intro he
    have h := congrFun he i
    simp [variableExponent] at h
  have h := mul_ne_zero (mul_ne_zero (by norm_num : (2:SpectralField n)≠0) hd) hs
  rw [←clearedSpectralRow_vertical₀] at h
  exact (mul_ne_zero_iff.mp h).2

lemma spectralWeights_U_ne_zero {n : ℕ} (i : Fin n) : (spectralWeights n i).U≠0 := by
  rw [←rowReflectSpectral_weightsA]
  exact (map_ne_zero (rowReflectSpectral i)).mpr (spectralWeights_A_ne_zero i)

lemma rowReflectSpectral_weights_other {n : ℕ} (i j : Fin n) (h : j≠i) :
    (spectralWeights n j).map (rowReflectSpectral i) = spectralWeights n j := by
  simp only [spectralWeights,rowReflectSpectral_torusWeights,map_div₀,map_pow,
    rowReflectSpectral_const,rowReflectSpectral_variable,ite_eq_right h]

def rowGauge {n : ℕ} (i : Fin n) : SpectralField n :=
  (spectralWeights n i).A / (spectralWeights n i).U

lemma rowGauge_ne_zero {n : ℕ} (i : Fin n) : rowGauge i ≠0 :=
  div_ne_zero (spectralWeights_A_ne_zero i) (spectralWeights_U_ne_zero i)

lemma reflectSpectral_rowGauge {n : ℕ} (i : Fin n) :
    reflectSpectral n (rowGauge i) = (rowGauge i)⁻¹ := by
  have h : (spectralWeights n i).map (reflectSpectral n) =
      (spectralWeights n i).map (rowReflectSpectral i) := by
    simp only [spectralWeights,reflectSpectral_torusWeights,rowReflectSpectral_torusWeights,
      map_div₀,map_pow,reflectSpectral_const,rowReflectSpectral_const,
      reflectSpectral_variable,rowReflectSpectral_variable,ite_true]
  have ha := congrArg Weights.A h
  have hu := congrArg Weights.U h
  change reflectSpectral n (spectralWeights n i).A = rowReflectSpectral i (spectralWeights n i).A at ha
  change reflectSpectral n (spectralWeights n i).U = rowReflectSpectral i (spectralWeights n i).U at hu
  simp only [rowGauge,map_div₀,ha,hu,rowReflectSpectral_weightsA,rowReflectSpectral_weightsU,inv_div]

lemma rowReflectSpectral_bottom_tile (n : ℕ) (t : Tile) (ht : ¬t.Occupied 0) :
    rowReflectSpectral (0:Fin (n+1)) ((spectralWeights (n+1) 0).tile t) *
      (if t.Occupied 1 then rowGauge (0:Fin (n+1)) else 1) =
    (if t.Occupied 2 then rowGauge (0:Fin (n+1)) else 1) * (spectralWeights (n+1) 0).tile t := by
  have h := Weights.vacantSouth_gauge (spectralWeights (n+1) 0)
      ((spectralWeights (n+1) 0).map (rowReflectSpectral 0))
      (rowReflectSpectral_weightsA 0) (rowReflectSpectral_weightsB 0)
      (rowReflectSpectral_weightsU 0) (spectralWeights_U_ne_zero 0) t ht
  simpa [Weights.map_tile, rowGauge] using h

lemma rowReflectSpectral_bottom_column (n : ℕ) (p q : Pairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1)) (column (spectralWeights (n+1)) q p) *
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 =
    occupancyGauge (rowGauge (0:Fin (n+1))) q 0 * column (spectralWeights (n+1)) q p := by
  rw [column_eq_raw]
  have hmap := congrFun (congrFun (rawColumn_map (rowReflectSpectral (0:Fin (n+1)))
    (fun i=>(spectralWeights (n+1) i).tile)) q) p
  rw [Matrix.map_apply] at hmap
  rw [hmap]
  apply rawColumn_bottom_gauge _ _ _ _ (rowReflectSpectral_bottom_tile n) p q
  intro i
  have h := rowReflectSpectral_weights_other (0:Fin (n+1)) i.succ (Fin.succ_ne_zero i)
  funext t
  have hh := congrArg (fun w=>w.tile t) h
  simpa [Weights.map_tile] using hh

lemma rowReflectSpectral_bottom_lastCoefficient (n : ℕ) (p q : Pairing (n+1+1)) :
    rowReflectSpectral (0:Fin (n+1)) (lastCoefficient (fun i=>(spectralWeights (n+1) i).tile) q p) *
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 =
    occupancyGauge (rowGauge (0:Fin (n+1))) q 0 *
      lastCoefficient (fun i=>(spectralWeights (n+1) i).tile) q p := by
  rw [←lastCoefficient_map]
  apply lastCoefficient_bottom_gauge _ _ _ _ (rowReflectSpectral_bottom_tile n) p q
  intro i
  have h := rowReflectSpectral_weights_other (0:Fin (n+1)) i.succ (Fin.succ_ne_zero i)
  funext t
  have hh := congrArg (fun w=>w.tile t) h
  simpa [Weights.map_tile] using hh

lemma rowReflectSpectral_bottom_vacuum (n : ℕ) (p : Pairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1)) (normalizedVacuum (spectralWeights (n+1)) p) =
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 * normalizedVacuum (spectralWeights (n+1)) p := by
  have hm := normalizedVacuum_map (rowReflectSpectral (0:Fin (n+1))) (spectralWeights (n+1))
    (spectral_regular (n+1))
  have hv := (spectral_regular (n+1)).map (rowReflectSpectral (0:Fin (n+1))) (spectralWeights (n+1))
  have hc (q p : Pairing (n+1)) : column
      (fun i=>(spectralWeights (n+1) i).map (rowReflectSpectral 0)) q p *
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 =
    occupancyGauge (rowGauge (0:Fin (n+1))) q 0 * column (spectralWeights (n+1)) q p := by
    rw [←column_map]
    exact rowReflectSpectral_bottom_column n p q
  rw [normalizedVacuum_gauge_pair _ _ (spectral_regular (n+1)) hv _
    (occupancyGauge_empty _ _) hc] at hm
  exact congrFun hm p

lemma rowReflectSpectral_bottom_rationalVacuum (n : ℕ) (p : Pairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1)) (rationalVacuum (n+1) p) =
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 * rationalVacuum (n+1) p := by
  simp only [rationalVacuum,map_mul,rowReflectSpectral_normalization,rowReflectSpectral_bottom_vacuum]
  ring

 

 


lemma matrix_one_sub_gauge {K : Type*} [CommRing K] {I : Type*} [Fintype I] [DecidableEq I]
    (M M' : Matrix I I K) (a : I → K)
    (h : ∀ j i, M' j i*a i=a j*M j i) :
    ∀ j i, (1-M') j i*a i=a j*(1-M) j i := by
  classical
  intro j i
  simp only [Matrix.sub_apply,sub_mul,mul_sub,h]
  congr 1
  by_cases he : j=i
  · subst i; simp
  · simp [he]

lemma rowReflectSpectral_bottom_sourceTransfer (n : ℕ)
    (p q : SourcePairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1))
      (sourceTransfer (fun i=>(spectralWeights (n+1) i).tile) q p) *
      occupancyGauge (rowGauge (0:Fin (n+1))) p.val 0 =
    occupancyGauge (rowGauge (0:Fin (n+1))) q.val 0 *
      sourceTransfer (fun i=>(spectralWeights (n+1) i).tile) q p :=
  rowReflectSpectral_bottom_lastCoefficient n p.val q.val

lemma rowReflectSpectral_bottom_northSource (n : ℕ)
    (p : Pairing (n+1)) (q : SourcePairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1))
      (northSource (fun i=>(spectralWeights (n+1) i).tile) q p) *
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 =
    occupancyGauge (rowGauge (0:Fin (n+1))) q.val 0 *
      northSource (fun i=>(spectralWeights (n+1) i).tile) q p := by
  classical
  have h := rowReflectSpectral_bottom_lastCoefficient n p.padTop q.val
  have he : occupancyGauge (rowGauge (0:Fin (n+1))) p.padTop 0 =
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 := by
    change (if p.padTop.Occupied (0:Fin (n+1)).castSucc then _ else _) = _
    simp only [Pairing.padTop_occupied_castSucc,occupancyGauge]
  simpa only [northSource,he] using h

 

lemma rowReflectSpectral_bottom_northNumerator (n : ℕ) (p : SourcePairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1)) (northNumerator (n+1) p) =
      occupancyGauge (rowGauge (0:Fin (n+1))) p.val 0 * northNumerator (n+1) p := by
  classical
  let f := rowReflectSpectral (0:Fin (n+1))
  let T := sourceTransfer (fun i=>(spectralWeights (n+1) i).tile)
  let B := northSource (fun i=>(spectralWeights (n+1) i).tile)
  let a := fun q : SourcePairing (n+1) => occupancyGauge (rowGauge (0:Fin (n+1))) q.val 0
  let b := fun q : Pairing (n+1) => occupancyGauge (rowGauge (0:Fin (n+1))) q 0
  have hT : ∀ j i,T.map f j i*a i=a j*T j i :=
    fun j i => rowReflectSpectral_bottom_sourceTransfer n i j
  have hB : ∀ j i,B.map f j i*b i=a j*B j i :=
    fun j i => rowReflectSpectral_bottom_northSource n i j
  have hmap : (1-T).map f = 1-T.map f := by
    ext j i
    simp only [Matrix.map_apply,Matrix.sub_apply,map_sub,Matrix.one_apply,apply_ite,map_one,map_zero]
  have hd : (1-T.map f).det≠0 := by
    rw [←hmap]
    change (f.mapMatrix (1-T)).det≠0
    rw [←RingHom.map_det]
    exact (map_ne_zero f).mpr (spectral_source_regular (n+1))
  have he := congrArg (fun v : SourcePairing (n+1) → SpectralField (n+1) =>
      fun q => f (v q)) (northNumerator_equation (n+1))
  have hv : (fun q => f (rationalVacuum (n+1) q)) =
      fun q => b q*rationalVacuum (n+1) q := by
    funext q
    exact rowReflectSpectral_bottom_rationalVacuum n q
  have hf : f (2*constF (n+1) d)=2*constF (n+1) d := by
    simp only [f, map_mul,map_ofNat,rowReflectSpectral_const]
  have he' : (1-T.map f).mulVec (fun q=>f (northNumerator (n+1) q)) =
      fun q=>(2*constF (n+1) d)*(B.map f).mulVec (fun q=>b q*rationalVacuum (n+1) q) q := by
    funext q
    have hh := congrFun he q
    change f ((1-T).mulVec (northNumerator (n+1)) q) =
      f ((2*constF (n+1) d)*B.mulVec (rationalVacuum (n+1)) q) at hh
    rw [RingHom.map_mulVec,hmap,map_mul,hf,
      RingHom.map_mulVec] at hh
    change _ = (2*constF (n+1) d)*(B.map f).mulVec (fun q=>f (rationalVacuum (n+1) q)) q at hh
    rw [hv] at hh
    exact hh
  have hm := matrix_mulVec_gauge (1-T) (1-T.map f) a a
    (matrix_one_sub_gauge T (T.map f) a hT) (northNumerator (n+1))
  have hh : (fun q=> f (northNumerator (n+1) q)) =
      (fun q=>a q*northNumerator (n+1) q) := by
    apply Matrix.mulVec_injective_of_det_ne_zero hd
    rw [he',hm,matrix_mulVec_gauge B (B.map f) b a hB]
    change (fun q=>(2*constF (n+1) d)*(a q*B.mulVec (rationalVacuum (n+1)) q)) =
      fun q=>a q*(1-T).mulVec (northNumerator (n+1)) q
    rw [northNumerator_equation]
    funext q
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  exact congrFun hh p

lemma polynomialNorthSource_bottom_reflection (n : ℕ) (p : SourcePairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1)) (evalLaurent (polynomialNorthSource (n+1) p)) =
      occupancyGauge (rowGauge (0:Fin (n+1))) p.val 0 *
        evalLaurent (polynomialNorthSource (n+1) p) := by
  classical
  simp only [polynomialNorthSource_eval_numerator,map_mul,rowReflectSpectral_const,
    rowReflectSpectral_bottom_northNumerator]
  ring

lemma map_occupancyGauge {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    {n : ℕ} (a : K) (p : Pairing n) (i : Fin n) :
    f (occupancyGauge a p i) = occupancyGauge (f a) p i := by
  classical
  unfold occupancyGauge
  split_ifs <;> simp

lemma sourceGlue_gauge {K : Type*} [Field K] (n : ℕ) (a : K) (ha : a≠0)
    (v w : SourcePairing n → K) (i : Fin (n+1)) :
    sourceGlue n (fun p=>occupancyGauge a⁻¹ p.val i*v p)
      (fun p=>occupancyGauge a p.val i*w p) = sourceGlue n v w := by
  classical
  rw [sourceGlue_eq_sum,sourceGlue_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  split_ifs with h
  · rw [one_mul,one_mul]
    simp only [occupancyGauge,h.2.1 i]
    split_ifs
    · field_simp
    · simp
  · simp

 

theorem polynomialNorthGluing_bottom_reflection (n : ℕ) :
    rowReflectLaurent (0:Fin (n+1)) (polynomialNorthGluing (n+1)) =
      polynomialNorthGluing (n+1) := by
  classical
  apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
  change evalLaurent (rowReflectLaurent 0 (polynomialNorthGluing (n+1))) =
    evalLaurent (polynomialNorthGluing (n+1))
  rw [←rowReflectSpectral_evalLaurent,polynomialNorthGluing_eval,sourceGlue_map]
  simp only [Function.comp_def,←reflectSpectral_rowReflect,
    polynomialNorthSource_bottom_reflection,map_mul,map_occupancyGauge,
    reflectSpectral_rowGauge]
  exact sourceGlue_gauge _ _ (rowGauge_ne_zero _) _ _ _

 

theorem polynomialNorthGluing_row_reflection {n : ℕ} (i : Fin n) :
    rowReflectLaurent i (polynomialNorthGluing n) = polynomialNorthGluing n := by
  classical
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := i.isLt; omega : n≠0)
  have h : ∀ k (hk : k<n+1), rowReflectLaurent ⟨k,hk⟩ (polynomialNorthGluing (n+1)) =
      polynomialNorthGluing (n+1) := by
    intro k
    induction k with
    | zero => intro hk; exact polynomialNorthGluing_bottom_reflection n
    | succ k ih =>
      intro hk
      let j : Fin (n+1) := ⟨k,by omega⟩
      let j' : Fin (n+1) := ⟨k+1,hk⟩
      have hx := polynomialNorthGluing_exchange k (by omega : k+2≤n+1)
      have hr := rowReflectLaurent_perm j (Equiv.swap j j') (polynomialNorthGluing (n+1))
      simp only [Equiv.swap_apply_left] at hr
      change permLaurent (Equiv.swap j j') (polynomialNorthGluing (n+1)) = _ at hx
      rw [hx,ih] at hr
      exact hr.trans hx
  exact h i.val i.isLt

end
 

 

noncomputable section
open scoped Classical BigOperators LaurentPolynomial

lemma permLaurent_one {n : ℕ} (f : Laurent n) : permLaurent 1 f = f := by
  have h : permLaurent (1 : Equiv.Perm (Fin n)) = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change permLaurent 1 (monomialL _ _) = monomialL _ _
    all_goals simp only [permLaurent_monomial,
      Equiv.Perm.one_def,Equiv.refl_symm,Equiv.coe_refl,Function.comp_id]
  exact DFunLike.congr_fun h f

lemma permLaurent_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (f : Laurent n) :
    permLaurent (σ*τ) f = permLaurent σ (permLaurent τ f) := by
  have h : permLaurent (σ*τ) = (permLaurent σ).comp (permLaurent τ) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change permLaurent (σ*τ) (monomialL _ _) = permLaurent σ (permLaurent τ (monomialL _ _))
    all_goals simp only [permLaurent_monomial,
      Equiv.Perm.mul_def,Equiv.symm_trans,Equiv.coe_trans,Function.comp_assoc]
  exact DFunLike.congr_fun h f

 
lemma permLaurent_invariant_of_adjacent {n : ℕ} (f : Laurent n)
    (h : ∀ r (hr : r+2≤n), permLaurent (Equiv.swap (⟨r,by omega⟩:Fin n)
      ⟨r+1,by omega⟩) f = f) (σ : Equiv.Perm (Fin n)) : permLaurent σ f = f := by
  cases n with
  | zero =>
    have he : σ=1 := Subsingleton.elim _ _
    rw [he,permLaurent_one]
  | succ n =>
    let S : Submonoid (Equiv.Perm (Fin (n+1))) :=
      { carrier := {τ | permLaurent τ f=f}
        one_mem' := permLaurent_one f
        mul_mem' := by
          intro τ υ hτ hυ
          change permLaurent (τ*υ) f = f
          rw [permLaurent_mul,hυ,hτ] }
    have hm : Submonoid.closure (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) ≤ S := by
      rw [Submonoid.closure_le]
      rintro _ ⟨i,rfl⟩
      exact h i.val (by have := i.isLt; omega)
    rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hm
    exact hm (show σ ∈ (⊤ : Submonoid _) from trivial)

lemma polynomialNorthGluing_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permLaurent σ (polynomialNorthGluing n) = polynomialNorthGluing n :=
  permLaurent_invariant_of_adjacent _ polynomialNorthGluing_exchange σ

 

lemma laurent_eq_zero_of_many_roots {K : Type*} [Field K]
    (f : LaurentPolynomial K) (m : ℕ)
    (hb : LaurentInterval f (-(m:ℤ)) m) (s : Finset K) (hc : 2*m<s.card)
    (hz : ∀ z∈s,z≠0)
    (he : ∀ z (h:z∈s), LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z h)) f=0) :
    f=0 := by
  let p := LaurentPolynomial.trunc (f*LaurentPolynomial.T m)
  have hp : p.degree < s.card := by
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [laurent_trunc_coeff,laurent_shift_coeff]
    by_contra hn
    have := hb ((k:ℤ)-m) hn
    omega
  have hev (z : K) (hs:z∈s) : p.eval z=0 := by
    have h:=congrArg (LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z hs))) hb.shift_trunc
    rw [LaurentPolynomial.eval₂_toLaurent] at h
    change p.eval z = _ at h
    rw [(LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z hs))).map_mul,
      he z hs,zero_mul] at h
    exact h
  have hp0 : p=0 := Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s hp hev
  have hh:=hb.shift_trunc
  change p.toLaurent=_ at hh
  rw [hp0,map_zero] at hh
  exact (LaurentPolynomial.isUnit_T (R:=K) (m:ℤ)).mul_left_eq_zero.mp hh.symm

lemma torusEvaluation_rowReflect {n m : ℕ} (i : Fin n)
    (z : Fin n → SpectralField m) (hz : ∀ j,z j≠0) (f : Laurent n) :
    torusEvaluation z hz (rowReflectLaurent i f) =
      torusEvaluation (Function.update z i (constF m phase^3/z i))
        (fun j => by by_cases h:j=i <;> simp [h,hz,constF_phase_ne_zero]) f := by
  have hmono (e : Fin n → ℤ) (c : ℂ) :
      torusEvaluation z hz (rowReflectLaurent i (monomialL e c)) =
        torusEvaluation (Function.update z i (constF m phase^3/z i))
          (fun j => by by_cases h:j=i <;> simp [h,hz,constF_phase_ne_zero]) (monomialL e c) := by
    rw [rowReflectLaurent_monomial,torusEvaluation_monomial,torusEvaluation_monomial]
    rw [←Finset.mul_prod_erase _ (fun j => z j ^ reflectExponentAt i e j) (Finset.mem_univ i),
      ←Finset.mul_prod_erase _ (fun j => (Function.update z i (constF m phase^3/z i)) j ^ e j) (Finset.mem_univ i)]
    have hh : (∏ j ∈ Finset.univ.erase i, z j ^ reflectExponentAt i e j) =
        ∏ j ∈ Finset.univ.erase i, (Function.update z i (constF m phase^3/z i)) j ^ e j := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j≠i := (Finset.mem_erase.mp hj).1
      simp only [reflectExponentAt,Function.update_of_ne hji]
    rw [hh]
    simp only [reflectExponentAt,Function.update_self,zpow_neg,
      constF,map_mul,map_zpow₀,zpow_mul,div_eq_mul_inv]
    simp only [mul_zpow,inv_zpow]
    ac_rfl
  have he : (torusEvaluation z hz).toRingHom.comp (rowReflectLaurent i) =
      (torusEvaluation (Function.update z i (constF m phase^3/z i))
        (fun j => by by_cases h:j=i <;> simp [h,hz,constF_phase_ne_zero])).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals exact hmono _ _
  exact DFunLike.congr_fun he f

end
end CriticalStrip.Diagram

end OAI
