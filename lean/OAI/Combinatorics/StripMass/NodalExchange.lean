import Mathlib
import OAI.Combinatorics.StripMass.CramerBounds

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma topPerm_swap {n : ℕ} (a b : Fin n) :
    topPerm (Equiv.swap a b)=Equiv.swap a.castSucc b.castSucc := by
  apply Equiv.ext
  intro j
  induction j using Fin.lastCases with
  | last => simp [Equiv.swap_apply_def,Ne.symm (Fin.castSucc_ne_last a),Ne.symm (Fin.castSucc_ne_last b)]
  | cast j =>
    simp only [topPerm_cast,Equiv.swap_apply_def,Fin.castSucc_inj]
    split_ifs <;> rfl

lemma rationalVacuum_exchange {n : ℕ} (r : ℕ) (hr : r+2≤n)
    : let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) ⟨r+1,by omega⟩;
    rationalVacuum n = (localR (PartialColumn.rowPosition r hr)
      (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩))).mulVec
        (fun p => permSpectral σ (rationalVacuum n p)) := by
  dsimp only
  let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) ⟨r+1,by omega⟩
  have hh (p : Pairing n) : permSpectral σ (rationalVacuum n p)=
      spectralNormalization n * normalizedVacuum (fun i => spectralWeights n (σ i)) p := by
    rw [rationalVacuum,map_mul,permSpectral_normalization,permSpectral_vacuum]
  change rationalVacuum n = (localR (PartialColumn.rowPosition r hr)
    (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩))).mulVec
      (fun p => permSpectral σ (rationalVacuum n p))
  simp_rw [hh]
  change spectralNormalization n • normalizedVacuum (spectralWeights n)=
    (localR (PartialColumn.rowPosition r hr)
      (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩))).mulVec
      (spectralNormalization n • normalizedVacuum (fun i => spectralWeights n (σ i)))
  rw [Matrix.mulVec_smul,←spectral_vacuum_exchange r hr]

lemma nodalVacuum_exchange {n : ℕ} (r : ℕ) (hr : r+2≤n) (i : Fin n)
    : let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) ⟨r+1,by omega⟩;
    nodalVacuum i = (localR (PartialColumn.rowPosition r hr).padTop
      (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩))).mulVec
        (fun p => permSpectral σ (nodalVacuum (σ i) p)) := by
  dsimp only
  let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) ⟨r+1,by omega⟩
  let a : Fin n:=⟨r,by omega⟩
  let b : Fin n:=⟨r+1,by omega⟩
  let z : SpectralField n:=variableF b/variableF a
  let x : Fin (n+1) → SpectralField n :=
    Fin.snoc (fun j => constF n phase^3/variableF j) (constF n phase^3/deletionNode i)
  have xc (j : Fin n) : x j.castSucc=constF n phase^3/variableF j := by
    simp only [x,Fin.snoc_castSucc]
  have hw : (fun j => torusWeights (x j))=nodalWeights i := by
    funext j
    induction j using Fin.lastCases <;> simp [x,nodalWeights,spectralWeights]
  have hp : (PartialColumn.rowPosition r (show r+2≤n+1 by omega))=
      (PartialColumn.rowPosition r hr).padTop := rfl
  have hswap : Equiv.swap (⟨r,by omega⟩ : Fin (n+1)) ⟨r+1,by omega⟩=topPerm σ :=
    (topPerm_swap a b).symm
  have hs : σ (σ i)=i := Equiv.swap_apply_self a b i
  have hreg := nodal_regular_reindex σ (σ i)
  rw [hs] at hreg
  have hx : z*x ⟨r+1,by omega⟩=x ⟨r,by omega⟩ := by
    change z*x b.castSucc=x a.castSucc
    rw [xc,xc]
    dsimp only [z]
    field_simp [variableF_ne_zero]
  have hL (j : Fin n) : torusL (x j.castSucc)≠0 := by
    rw [xc]
    rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero j
  have H:=normalizedVacuum_torus_exchange r (show r+2≤n+1 by omega) x z
    (div_ne_zero (variableF_ne_zero b) (variableF_ne_zero a))
    (by change x b.castSucc≠0; rw [xc]; exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero b))
    (torusL_ratio_ne_zero a b) (hL b) (hL a) hx
    (by rw [hw]; exact nodal_regular i)
    (by change VacuumRegular (fun j => (fun k => torusWeights (x k)) (Equiv.swap _ _ j));
        rw [hw,hswap]; exact hreg)
  rw [hw,hswap,hp] at H
  have hwpoint (j : Fin (n+1)) := congrFun hw j
  simp_rw [hwpoint] at H
  have hv (p : Pairing (n+1)) : permSpectral σ (nodalVacuum (σ i) p)=
      nodalScalar i*normalizedVacuum (fun j => nodalWeights i (topPerm σ j)) p := by
    rw [permSpectral_nodalVacuum,hs]
  change nodalVacuum i = (localR (PartialColumn.rowPosition r hr).padTop
    (torusWeights z)).mulVec (fun p => permSpectral σ (nodalVacuum (σ i) p))
  simp_rw [hv]
  change nodalScalar i • normalizedVacuum (nodalWeights i)=
    (localR (PartialColumn.rowPosition r hr).padTop (torusWeights z)).mulVec
      (nodalScalar i • normalizedVacuum (fun j => nodalWeights i (topPerm σ j)))
  rw [Matrix.mulVec_smul,←H]

end

 

 

noncomputable section
open scoped Classical
open Finset

lemma localR_padTop_zero_last {K : Type*} [CommRing K] {n : ℕ} (a : Position n)
    (w : Weights K) (p q : Pairing (n+1))
    (h : ¬ (q.Occupied (Fin.last n) ↔ p.Occupied (Fin.last n))) :
    localR a.padTop w q p=0 := by
  apply localR_zero_of_support a.padTop w p q (Fin.last n) _ _ h
  · exact Ne.symm (Fin.castSucc_ne_last _)
  · exact Ne.symm (Fin.castSucc_ne_last _)

lemma lastPolynomial_unique {K : Type*} [Field K] {n : ℕ}
    (P Q : Pairing (n+1) → Polynomial K)
    (hP : LastDegree n P) (hQ : LastDegree n Q)
    (v : Fin n → K) (hv : Function.Injective v)
    (hlead : ∀ p : Pairing n, (P p.padTop).coeff n=(Q p.padTop).coeff n)
    (hnode : ∀ p i, (P p).eval (v i)=(Q p).eval (v i)) : P=Q := by
  funext p
  apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq univ hv.injOn
  · simp only [card_univ,Fintype.card_fin]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [Polynomial.coeff_sub]
    by_cases hp : p.Occupied (Fin.last n)
    · rw [hP p k (by simpa only [hp,ite_true] using hk),
        hQ p k (by simpa only [hp,ite_true] using hk), sub_self]
    · by_cases he : k=n
      · subst k
        have h:=hlead (p.restrict Fin.castSuccOrderEmb)
        rw [Pairing.padTop_restrict p hp] at h
        exact sub_eq_zero.mpr h
      · rw [hP p k (by simp only [hp,ite_false]; omega),
          hQ p k (by simp only [hp,ite_false]; omega),sub_self]
  · intro i _
    exact hnode p i

 

def nodalExchangePolynomial {n : ℕ} (r : ℕ) (hr : r+2≤n)
    (p : Pairing (n+1)) : Polynomial (SpectralField n) :=
  ∑ q, Polynomial.C (localR (PartialColumn.rowPosition r hr).padTop
      (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)) p q) *
    (rationalNodalPolynomial n q).map
      (permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩))

lemma nodalExchangePolynomial_coeff {n : ℕ} (r : ℕ) (hr : r+2≤n)
    (p : Pairing (n+1)) (k : ℕ) :
    (nodalExchangePolynomial r hr p).coeff k =
    ∑ q, localR (PartialColumn.rowPosition r hr).padTop
      (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)) p q *
      permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
        ((rationalNodalPolynomial n q).coeff k) := by
  simp only [nodalExchangePolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,
    Polynomial.coeff_map]

lemma nodalExchangePolynomial_degree {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    LastDegree n (nodalExchangePolynomial r hr) := by
  intro p k hk
  rw [nodalExchangePolynomial_coeff]
  apply sum_eq_zero
  intro q _
  by_cases hh : p.Occupied (Fin.last n) ↔ q.Occupied (Fin.last n)
  · rw [rationalNodalPolynomial_degree n q k (by rwa [←hh]),map_zero,mul_zero]
  · rw [localR_padTop_zero_last _ _ q p hh,zero_mul]

lemma nodalExchangePolynomial_leading {n : ℕ} (r : ℕ) (hr : r+2≤n) (p : Pairing n) :
    (nodalExchangePolynomial r hr p.padTop).coeff n=rationalVacuum n p := by
  rw [nodalExchangePolynomial_coeff]
  rw [congrFun (rationalVacuum_exchange r hr) p]
  simp only [Matrix.mulVec,dotProduct]
  symm
  apply Fintype.sum_of_injective Pairing.padTop Pairing.padTop_injective
  · intro q hq
    rw [localR_padTop_outside _ _ q p hq,zero_mul]
  · intro q
    rw [localR_padTop,rationalNodalPolynomial_leading]

lemma nodalExchangePolynomial_node {n : ℕ} (r : ℕ) (hr : r+2≤n)
    (p : Pairing (n+1)) (i : Fin n) :
    (if p.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) *
      (nodalExchangePolynomial r hr p).eval (deletionBeta i) =nodalVacuum i p := by
  let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) ⟨r+1,by omega⟩
  have hσ (j : Fin n) : σ (σ j)=j := Equiv.swap_apply_self _ _ _
  have hβ : permSpectral σ (deletionBeta (σ i))=deletionBeta i := by
    rw [permSpectral_deletionBeta,hσ]
  have hsin : permSpectral σ (torusSin (deletionNode (σ i)))=torusSin (deletionNode i) := by
    simp only [permSpectral_torusSin,permSpectral_deletionNode,hσ]
  rw [congrFun (nodalVacuum_exchange r hr i) p]
  simp only [nodalExchangePolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,mul_sum,Matrix.mulVec,dotProduct]
  apply sum_congr rfl
  intro q _
  change (if p.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) *
    (localR _ _ p q * ((rationalNodalPolynomial n q).map (permSpectral σ)).eval (deletionBeta i)) =
      localR _ _ p q * permSpectral σ (nodalVacuum (σ i) q)
  by_cases hh : p.Occupied (Fin.last n) ↔ q.Occupied (Fin.last n)
  · rw [hh,←rationalNodalPolynomial_at_node q (σ i),map_mul]
    rw [←hβ,Polynomial.eval_map_apply]
    have hs : permSpectral σ (if q.Occupied (Fin.last n) then torusSin (deletionNode (σ i)) else 1)=
        (if q.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) := by
      split_ifs <;> simp only [hsin,map_one]
    rw [hs]
    ring
  · rw [localR_padTop_zero_last _ _ q p hh,zero_mul,mul_zero,zero_mul]

 

theorem rationalNodalPolynomial_covariance {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    rationalNodalPolynomial n=nodalExchangePolynomial r hr := by
  apply lastPolynomial_unique _ _ (rationalNodalPolynomial_degree n)
    (nodalExchangePolynomial_degree r hr) deletionBeta (deletionBeta_injective n)
  · intro p
    rw [rationalNodalPolynomial_leading,nodalExchangePolynomial_leading]
  · intro p i
    have h := (rationalNodalPolynomial_at_node p i).trans
      (nodalExchangePolynomial_node r hr p i).symm
    apply mul_left_cancel₀ _ h
    split_ifs
    · exact deletionNode_sine_ne_zero i
    · exact one_ne_zero

end

 

 

noncomputable section
open scoped Classical

lemma signSpectral_nodal_eval {n : ℕ} (k i : Fin n) (p : Pairing (n+1)) :
    ((rationalNodalPolynomial n p).map (signSpectral k)).eval (deletionBeta i)=
      occupancySign p k.castSucc*(rationalNodalPolynomial n p).eval (deletionBeta i) := by
  have hh:=congrArg (signSpectral k) (rationalNodalPolynomial_at_node p i)
  rw [map_mul,signSpectral_nodalVacuum] at hh
  have hev : signSpectral k ((rationalNodalPolynomial n p).eval (deletionBeta i))=
      ((rationalNodalPolynomial n p).map (signSpectral k)).eval (deletionBeta i) := by
    rw [←Polynomial.eval_map_apply,signSpectral_deletionBeta]
  rw [hev,←rationalNodalPolynomial_at_node p i] at hh
  by_cases hp:p.Occupied (Fin.last n)
  · have hs : occupancySign (K:=SpectralField n) p (Fin.last n)= -1 := by simp [occupancySign,hp]
    simp only [hp,ite_true,signSpectral_torusSin,signSpectral_deletionNode,nodeSign,hs] at hh
    by_cases hi:i=k
    · simp only [ite_eq_left hi,torusSin_neg] at hh
      apply mul_left_cancel₀ (deletionNode_sine_ne_zero i)
      linear_combination -hh
    · simp only [ite_eq_right hi,mul_one] at hh
      apply mul_left_cancel₀ (deletionNode_sine_ne_zero i)
      linear_combination hh
  · have hs : occupancySign (K:=SpectralField n) p (Fin.last n)=1 := by simp [occupancySign,hp]
    simpa only [hp,ite_false,map_one,one_mul,nodeSign,hs,ite_self,mul_one] using hh

 

theorem rationalNodalPolynomial_parity {n : ℕ} (k : Fin n) (p : Pairing (n+1)) :
    (rationalNodalPolynomial n p).map (signSpectral k)=
      Polynomial.C (occupancySign p k.castSucc)*rationalNodalPolynomial n p := by
  have h: (fun p : Pairing (n+1) => (rationalNodalPolynomial n p).map (signSpectral k))=
      (fun p => Polynomial.C (occupancySign p k.castSucc)*rationalNodalPolynomial n p) := by
    apply lastPolynomial_unique
    · intro p j hj
      rw [Polynomial.coeff_map,rationalNodalPolynomial_degree n p j hj,map_zero]
    · intro p j hj
      rw [Polynomial.coeff_C_mul,rationalNodalPolynomial_degree n p j hj,mul_zero]
    case v => exact deletionBeta
    case hv => exact deletionBeta_injective n
    · intro p
      rw [Polynomial.coeff_map,Polynomial.coeff_C_mul,rationalNodalPolynomial_leading,
        rationalVacuum_sign]
      simp [occupancySign]
    · intro p i
      rw [Polynomial.eval_mul,Polynomial.eval_C]
      exact signSpectral_nodal_eval k i p
  exact congrFun h p


 

 


lemma rationalNodalPolynomial_eval_div {n : ℕ} (i : Fin n) (p : Pairing (n+1)) :
    (rationalNodalPolynomial n p).eval (deletionBeta i)=
      nodalVacuum i p / (if p.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) := by
  apply (eq_div_iff (by split_ifs; exact deletionNode_sine_ne_zero i; exact one_ne_zero)).mpr
  rw [mul_comm]
  exact rationalNodalPolynomial_at_node p i

lemma nodalDatumL_map_eval {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (p : Pairing (n+2)) :
    evalLaurent (nodalDatumL W i p)=(rationalNodalPolynomial (n+1) p).eval (deletionBeta i) := by
  rw [nodalDatumL_map W hW,rationalNodalPolynomial_eval_div]

lemma nodalDatumL_sign {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (k i : Fin (n+1)) (p : Pairing (n+2)) :
    signLaurent k (nodalDatumL W i p)=
      (if p.Occupied k.castSucc then -nodalDatumL W i p else nodalDatumL W i p) := by
  apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
  change evalLaurent (signLaurent k (nodalDatumL W i p))=evalLaurent _
  rw [←signSpectral_evalLaurent,nodalDatumL_map_eval W hW]
  have h:=signSpectral_nodal_eval k i p
  rw [←Polynomial.eval_map_apply,signSpectral_deletionBeta,h]
  split_ifs with hp
  · simp only [evalLaurent,map_neg,occupancySign,hp,ite_true,neg_one_mul]
    rw [←evalLaurent,nodalDatumL_map_eval W hW]
  · simp only [occupancySign,hp,ite_false,one_mul]
    rw [nodalDatumL_map_eval W hW]

end

 

 

noncomputable section

theorem torus_sine_pair {n : ℕ} (z : SpectralField n) (hz : z ≠ 0) :
    2 * torusSin z * torusSin (constF n phase ^ 3 / z) =
      torusCos (z^2 / constF n phase ^ 3) - constF n c := by
  have hq := constF_phase_ne_zero n
  rw [torusSin_product _ _ hz (div_ne_zero (pow_ne_zero _ hq) hz)]
  have h₁ : z / (constF n phase ^ 3 / z) = z^2 / constF n phase ^ 3 := by field_simp
  have h₂ : z * (constF n phase ^ 3 / z) = constF n phase ^ 3 := by field_simp
  rw [h₁, h₂, torusCos_phase_pow]
  rfl

theorem torus_twice_denominator {n : ℕ} (z : SpectralField n) (hz : z ≠ 0) :
    2 * torusL (constF n phase ^ 3 / z) =
      torusCos (z^2 / constF n phase ^ 3) + constF n C := by
  have hq := constF_phase_ne_zero n
  have h₅ : constF n phase ^ 2 * (constF n phase ^ 3 / z) = constF n phase ^ 5 / z := by ring
  have h₆ : constF n phase ^ 3 * (constF n phase ^ 3 / z) = constF n phase ^ 6 / z := by ring
  rw [torusL, h₅, h₆, ← mul_assoc, torusSin_product _ _
    (div_ne_zero (pow_ne_zero _ hq) hz) (div_ne_zero (pow_ne_zero _ hq) hz)]
  have hdiv : (constF n phase ^ 5 / z) / (constF n phase ^ 6 / z) =
      (constF n phase)⁻¹ := by field_simp
  have hmul : (constF n phase ^ 5 / z) * (constF n phase ^ 6 / z) =
      -(z^2 / constF n phase ^ 3)⁻¹ := by
    have h := constF_phase_eight n
    field_simp
    exact h
  rw [hdiv, hmul, torusCos_inv, torusCos_neg, torusCos_inv,
    ← pow_one (constF n phase), torusCos_phase_pow]
  simp only [Nat.cast_one, one_mul, sub_neg_eq_add]
  rw [add_comm]
  rfl

theorem torus_last_cleared {n : ℕ} (z : SpectralField n) (hz : z ≠ 0)
    (hL : torusL (constF n phase ^ 3 / z) ≠ 0) :
    let b := torusCos (z^2 / constF n phase ^ 3)
    let r := fun t => (b + constF n C) * (torusWeights (constF n phase^3/z)).tile t
    r .vacant = b + constF n C ∧
    r .cap = 2 * constF n d * torusSin (constF n phase^3/z) ∧
    r .vertical₀ = 2 * constF n d * torusSin z ∧
    r .diagonal₁ = b - constF n c := by
  dsimp only
  rw [← torus_twice_denominator z hz]
  have hq := constF_phase_ne_zero n
  have h₃ : constF n phase^3 / (constF n phase^3/z) = z := by field_simp
  simp only [torusWeights, Weights.tile, mul_one, h₃]
  constructor
  · trivial
  constructor
  · field_simp
  constructor
  · field_simp
  · rw [← torus_sine_pair z hz]
    field_simp

 

theorem torus_column_lastValue {n k : ℕ} (w : Fin n → Weights (SpectralField k))
    (z : SpectralField k) (hz : z ≠ 0) (hL : torusL (constF k phase^3/z) ≠ 0)
    (P : Pairing (n+1) → Polynomial (SpectralField k)) :
    (torusCos (z^2/constF k phase^3) + constF k C) •
      (column (Fin.snoc w (torusWeights (constF k phase^3/z)))).mulVec
        (lastValue (RingHom.id _) (torusCos (z^2/constF k phase^3)) (torusSin z) P) =
      lastValue (RingHom.id _) (torusCos (z^2/constF k phase^3)) (torusSin z)
        (lastTransform (fun i => (w i).tile) (constF k d) (constF k c) (constF k C) P) := by
  have h := torus_last_cleared z hz hL
  have he := rawColumn_lastValue (RingHom.id _) (fun i => (w i).tile)
    (constF k d) (constF k c) (constF k C)
    (torusCos (z^2/constF k phase^3)) (torusSin z) (torusSin (constF k phase^3/z))
    (fun t => (torusCos (z^2/constF k phase^3) + constF k C) *
      (torusWeights (constF k phase^3/z)).tile t) P h.1 h.2.1 h.2.2.1 h.2.2.2
    (torus_sine_pair z hz)
  rw [← he]
  have hrow : Fin.snoc (fun i => (w i).tile)
      (fun t => (torusCos (z^2/constF k phase^3) + constF k C) *
        (torusWeights (constF k phase^3/z)).tile t) =
      fun i t => (Fin.snoc (fun _ => 1) (torusCos (z^2/constF k phase^3) + constF k C) :
        Fin (n+1) → SpectralField k) i *
          ((Fin.snoc w (torusWeights (constF k phase^3/z)) : Fin (n+1) → Weights (SpectralField k)) i).tile t := by
    funext i t
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]
    | cast i => simp only [Fin.snoc_castSucc, one_mul]
  simp only [RingHom.id_apply] at *
  rw [hrow, rawColumn_scale, Matrix.smul_mulVec]
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const_one, one_mul]
  rfl


 

 

open Finset
open scoped Classical

 

def rationalResidualPolynomial (n : ℕ) (p : Pairing (n+1)) : Polynomial (SpectralField n) :=
  lastTransform (fun i => (spectralWeights n i).tile)
      (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) p -
    (Polynomial.X + Polynomial.C (constF n C)) * rationalNodalPolynomial n p

theorem rationalVacuum_stationary (n : ℕ) :
    (column (spectralWeights n)).mulVec (rationalVacuum n) = rationalVacuum n := by
  change (column (spectralWeights n)).mulVec
    (spectralNormalization n • normalizedVacuum (spectralWeights n)) =
      spectralNormalization n • normalizedVacuum (spectralWeights n)
  rw [Matrix.mulVec_smul, (spectral_normalizedVacuum_stationary n).2]

 

theorem rationalResidualPolynomial_degree {n : ℕ} (p : Pairing (n+1)) (k : ℕ)
    (hk : n < k) : (rationalResidualPolynomial n p).coeff k = 0 := by
  have hP := rationalNodalPolynomial_degree n
  have hT := lastTransform_degree (fun i => (spectralWeights n i).tile)
    (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) hP
  obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
  by_cases hp : p.Occupied (Fin.last n)
  · rw [rationalResidualPolynomial, Polynomial.coeff_sub,
      hT p (j+1) (by simp only [hp, ite_true]; omega)]
    have h₀ := hP p j (by simp only [hp, ite_true]; omega)
    have h₁ := hP p (j+1) (by simp only [hp, ite_true]; omega)
    simp [add_mul, h₀, h₁]
  · have h₁ := hP p (j+1) (by simp only [hp, ite_false]; omega)
    by_cases he : j = n
    · subst j
      let q := p.restrict Fin.castSuccOrderEmb
      have hpad : q.padTop = p := Pairing.padTop_restrict p hp
      rw [← hpad, rationalResidualPolynomial, Polynomial.coeff_sub, lastTransform_leading _ _ _ _ _ hP q]
      have hlead : (fun p : Pairing n => (rationalNodalPolynomial n p.padTop).coeff n) =
          rationalVacuum n := funext rationalNodalPolynomial_leading
      rw [hlead, ← column_eq_raw, rationalVacuum_stationary]
      have hz : (rationalNodalPolynomial n q.padTop).coeff (n+1) = 0 := by simpa [hpad] using h₁
      simp [add_mul, rationalNodalPolynomial_leading, hz]
    · have h₀ := hP p j (by simp only [hp, ite_false]; omega)
      rw [rationalResidualPolynomial, Polynomial.coeff_sub,
        hT p (j+1) (by simp only [hp, ite_false]; omega)]
      simp [add_mul, h₀, h₁]

 

theorem rationalResidualPolynomial_at_node {n : ℕ} (p : Pairing (n+1)) (i : Fin n) :
    (rationalResidualPolynomial n p).eval (deletionBeta i) = 0 := by
  have hz : deletionNode i ≠ 0 := mul_ne_zero (variableF_ne_zero i)
    (pow_ne_zero _ (constF_phase_ne_zero n))
  have harg : constF n phase^3 / deletionNode i = (variableF i)⁻¹ := by
    unfold deletionNode
    field_simp [constF_phase_ne_zero]
  have hL : torusL (constF n phase^3 / deletionNode i) ≠ 0 := by
    rw [harg, ← inverseRowDenominator_map]
    exact inverseRowDenominator_map_ne_zero i
  have he := torus_column_lastValue (spectralWeights n) (deletionNode i) hz hL
    (rationalNodalPolynomial n)
  have hdata : lastValue (RingHom.id _) (deletionBeta i) (torusSin (deletionNode i))
      (rationalNodalPolynomial n) = nodalVacuum i := by
    funext q
    simpa only [lastValue, Polynomial.eval₂_id, ite_mul, one_mul] using
      rationalNodalPolynomial_at_node q i
  change (deletionBeta i + constF n C) •
    (column (nodalWeights i)).mulVec
      (lastValue (RingHom.id _) (deletionBeta i) (torusSin (deletionNode i))
        (rationalNodalPolynomial n)) = _ at he
  rw [hdata, nodalVacuum_stationary] at he
  have hep := congrFun he p
  simp only [Pi.smul_apply, smul_eq_mul] at hep
  rw [← congrFun hdata p] at hep
  change (deletionBeta i + constF n C) *
    lastValue (RingHom.id _) (deletionBeta i) (torusSin (deletionNode i))
      (rationalNodalPolynomial n) p =
    lastValue (RingHom.id _) (deletionBeta i) (torusSin (deletionNode i))
      (lastTransform (fun i => (spectralWeights n i).tile) (constF n d) (constF n c)
        (constF n C) (rationalNodalPolynomial n)) p at hep
  by_cases hp : p.Occupied (Fin.last n)
  · simp only [lastValue, hp, ite_true, Polynomial.eval₂_id] at hep
    have hc := deletionNode_sine_ne_zero i
    rw [rationalResidualPolynomial, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    apply sub_eq_zero.mpr
    apply mul_left_cancel₀ hc
    calc
      _ = (deletionBeta i + constF n C) *
          (torusSin (deletionNode i) * (rationalNodalPolynomial n p).eval (deletionBeta i)) := hep.symm
      _ = _ := by ring
  · simp only [lastValue, hp, ite_false, Polynomial.eval₂_id] at hep
    simp only [rationalResidualPolynomial, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_eq_zero.mpr hep.symm

 

def rationalResidualCoefficient (n : ℕ) (p : Pairing (n+1)) : SpectralField n :=
  (rationalResidualPolynomial n p).coeff n

theorem rationalResidualPolynomial_factor {n : ℕ} (p : Pairing (n+1)) :
    rationalResidualPolynomial n p =
      Polynomial.C (rationalResidualCoefficient n p) * Lagrange.nodal univ deletionBeta := by
  apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq univ (deletionBeta_injective n).injOn
  · simp only [card_univ, Fintype.card_fin]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    by_cases he : k = n
    · subst k
      have hnod : (Lagrange.nodal univ (@deletionBeta n)).coeff n = 1 := by
        simpa only [Lagrange.natDegree_nodal, card_univ, Fintype.card_fin] using
          (Lagrange.nodal_monic (s := (univ : Finset (Fin n))) (v := @deletionBeta n)).coeff_natDegree
      simp [hnod, rationalResidualCoefficient]
    · rw [rationalResidualPolynomial_degree p k (by omega)]
      have hnod : (Lagrange.nodal univ (@deletionBeta n)).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        simp only [Lagrange.degree_nodal, card_univ, Fintype.card_fin]
        exact_mod_cast (show n < k by omega)
      simp [hnod]
  · intro i _
    rw [rationalResidualPolynomial_at_node, Polynomial.eval_mul, Polynomial.eval_C,
      Lagrange.eval_nodal_at_node (mem_univ _), mul_zero]

end
end CriticalStrip.Diagram

end OAI
