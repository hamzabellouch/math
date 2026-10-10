import Mathlib
import OAI.Combinatorics.StripMass.InterpolantCovariance

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

 

theorem plainKernel_cons_flat {K : Type*} [Field K] {n : ℕ} (dd rr cc CC : K)
    (a : Fin n → K) (hshift : cc+rr = CC)
    (hroot : ∀ z, discriminant dd cc z = (z-cc)*(z+CC))
    (hfirst : ∀ i, a i ≠ cc) (hsecond : ∀ i, a i+CC ≠ 0) :
    plainKernel dd rr (Fin.cons cc a) = frontBorder (plainKernel dd rr a) (-1) := by
  have hrow : ∀ i : Fin n, plainKernel dd rr (Fin.cons cc a) 0 i.succ = -1 := by
    intro i
    simp only [plainKernel,Fin.cons_zero,Fin.cons_succ,hroot]
    have hc : cc+a i+rr = a i+CC := by rw [← hshift]; ring
    rw [hc]
    field_simp [sub_ne_zero.mpr (hfirst i),hsecond i]
    ring
  funext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [plainKernel]
    | succ j => exact hrow j
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      rw [plainKernel_skew _ _ _ 0 i.succ,hrow]
      simp
    | succ j => rfl

 

theorem pfaffian_augmented_cons_flat {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (dd rr cc CC : K) (a : Fin n → K) (hshift : cc+rr = CC)
    (hroot : ∀ z, discriminant dd cc z = (z-cc)*(z+CC))
    (hfirst : ∀ i, a i ≠ cc) (hsecond : ∀ i, a i+CC ≠ 0) :
    pfaffian (augmentedKernel dd rr (Fin.cons cc a)) =
      (-1)^n * pfaffian (augmentedKernel dd rr a) := by
  obtain ⟨m,hm|hm⟩ : ∃ m, n = 2*m ∨ n = 2*m+1 := ⟨n/2,by omega⟩
  · subst n
    rw [pfaffian_augmented_odd, pfaffian_augmented_even]
    apply Eq.trans (congrArg (fun M => pfaffian (backBorder M))
      (plainKernel_cons_flat dd rr cc CC a hshift hroot hfirst hsecond))
    rw [pfaffian_back_front _ (plainKernel_skew _ _ _)]
    simp [pow_mul]
  · subst n
    have hcast : 2*m+1+1 = 2*(m+1) := by omega
    have he := pfaffian_augmented_even (m+1) dd rr (Fin.cons cc a)
    apply Eq.trans he
    apply Eq.trans (congrArg pfaffian (plainKernel_cons_flat dd rr cc CC a hshift hroot hfirst hsecond))
    have h := pfaffian_frontBorder_scale (plainKernel dd rr a) (plainKernel_skew _ _ _) (1:K) (-1)
    simp only [neg_one_mul] at h
    apply Eq.trans h
    rw [pfaffian_front_back _ (plainKernel_skew _ _ _),pfaffian_augmented_odd]
    simp [pow_add,pow_mul]

theorem scalarNormalization_cons_flat {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (dd rr cc CC : K) (a : Fin n → K) (hshift : cc+rr = CC)
    (hroot : ∀ z, discriminant dd cc z = (z-cc)*(z+CC))
    (hfirst : ∀ i, a i ≠ cc) (hsecond : ∀ i, a i+CC ≠ 0) :
    scalarNormalization dd rr (Fin.cons cc a) =
      (∏ i : Fin n, (a i+CC)) * scalarNormalization dd rr a := by
  have hf : ∀ i, discriminant dd cc (a i)/(cc-a i) = -(a i+CC) := by
    intro i
    rw [hroot]
    field_simp [sub_ne_zero.mpr (hfirst i).symm]
    ring
  unfold scalarNormalization
  rw [← prod_upperPair, ← prod_upperPair]
  have hp := prod_upperPair_succ (fun (i j : Fin (n+1)) =>
    discriminant dd ((Fin.cons cc a : Fin (n+1) → K) i) ((Fin.cons cc a : Fin (n+1) → K) j) /
      ((Fin.cons cc a : Fin (n+1) → K) i-(Fin.cons cc a : Fin (n+1) → K) j))
  apply Eq.trans (congrArg (fun z => z * pfaffian (augmentedKernel dd rr (Fin.cons cc a))) hp)
  simp only [Fin.cons_zero,Fin.cons_succ,hf]
  rw [Finset.prod_neg, Finset.card_univ,Fintype.card_fin,
    pfaffian_augmented_cons_flat dd rr cc CC a hshift hroot hfirst hsecond]
  have hs : (-1:K)^n * (-1)^n = 1 := by rw [← mul_pow]; simp
  calc
    _ = ((-1:K)^n * (-1)^n) * ((∏ i : Fin n, (a i+CC)) *
      ((∏ e : UpperPair n, discriminant dd (a e.val.1) (a e.val.2)/(a e.val.1-a e.val.2)) *
        pfaffian (augmentedKernel dd rr a))) := by ring
    _ = _ := by rw [hs,one_mul]

end

 

 

noncomputable section
open scoped Classical

lemma cosineVar_ne_const {n : ℕ} (i : Fin n) (z : ℂ) :
    cosineVar i ≠ cosineConst n z := by
  intro h
  have he := (IsFractionRing.injective (CosineRing n) (CosineField n)) h
  have := congrArg (MvPolynomial.eval (fun _ : Fin n => z+1)) he
  simp at this

lemma cosineVar_injective (n : ℕ) : Function.Injective (@cosineVar n) :=
  (IsFractionRing.injective (CosineRing n) (CosineField n)).comp MvPolynomial.X_injective

lemma flat_discriminant_map {K : Type*} [CommRing K] (f : ℂ →+* K)
    (dd cc CC : ℂ) (hlin : 2*dd*cc=CC-cc) (hconst : cc^2-dd^2= -cc*CC) (z : K) :
    discriminant (f dd) (f cc) z=(z-f cc)*(z+f CC) := by
  have hl := congrArg f hlin
  have hc := congrArg f hconst
  simp only [map_mul,map_ofNat,map_sub,map_pow,map_neg] at hl hc
  unfold discriminant
  linear_combination z*hl+hc

 

theorem scalarPolynomial_cons_flat_identity (n : ℕ) (dd rr cc CC : ℂ)
    (hdd : dd≠0) (hshift : cc+rr=CC) (hlin : 2*dd*cc=CC-cc)
    (hconst : cc^2-dd^2= -cc*CC) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cons (MvPolynomial.C cc) MvPolynomial.X)
      (scalarPolynomial (n+1) dd rr hdd)=
      (∏ i : Fin n, (MvPolynomial.X i + MvPolynomial.C CC))*scalarPolynomial n dd rr hdd := by
  let f : ℂ →+* CosineField n := (algebraMap (CosineRing n) (CosineField n)).comp MvPolynomial.C
  have hc (z : ℂ) : f z=cosineConst n z := rfl
  have hv : MvPolynomial.eval₂Hom f (@cosineVar n)=algebraMap (CosineRing n) (CosineField n) := by
    apply MvPolynomial.ringHom_ext <;> intro z <;> simp [f,cosineVar]
  have hi : Function.Injective (Fin.cons (f cc) (@cosineVar n)) := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact (cosineVar_ne_const j cc (by simpa [hc] using hij.symm)).elim
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (cosineVar_ne_const i cc (by simpa [hc] using hij)).elim
      | succ j => exact congrArg Fin.succ (cosineVar_injective n (by simpa using hij))
  have hfirst (i : Fin n) : cosineVar i≠f cc := cosineVar_ne_const i cc
  have hsecond (i : Fin n) : cosineVar i+f CC≠0 := by
    intro he
    apply cosineVar_ne_const i (-CC)
    rw [←hc,map_neg]
    exact eq_neg_of_add_eq_zero_left he
  have hroot (z : CosineField n) : discriminant (f dd) (f cc) z=(z-f cc)*(z+f CC) :=
    flat_discriminant_map f dd cc CC hlin hconst z
  have hD (i j : Fin (n+1)) (hij:i≠j) :
      discriminant (f dd) ((Fin.cons (f cc) (@cosineVar n) : Fin (n+1) → CosineField n) i)
        ((Fin.cons (f cc) (@cosineVar n) : Fin (n+1) → CosineField n) j)≠0 := by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => simpa only [Fin.cons_zero,Fin.cons_succ,hroot] using
          mul_ne_zero (sub_ne_zero.mpr (hfirst j)) (hsecond j)
    | succ i =>
      induction j using Fin.cases with
      | zero =>
          simp only [Fin.cons_zero,Fin.cons_succ]
          rw [discriminant_symm,hroot]
          exact mul_ne_zero (sub_ne_zero.mpr (hfirst i)) (hsecond i)
      | succ j => exact discriminant_cosineVar_ne dd hdd i j
  apply IsFractionRing.injective (CosineRing n) (CosineField n)
  rw [MvPolynomial.map_eval₂Hom,map_mul]
  have hm : (algebraMap (CosineRing n) (CosineField n))
      (∏ i : Fin n,(MvPolynomial.X i+MvPolynomial.C CC))=
      ∏ i : Fin n,(algebraMap (CosineRing n) (CosineField n))
        (MvPolynomial.X i+MvPolynomial.C CC) := map_prod _ _ _
  rw [hm]
  have ha : (fun i : Fin (n+1) => (algebraMap (CosineRing n) (CosineField n))
      ((Fin.cons (MvPolynomial.C cc) MvPolynomial.X : Fin (n+1) → CosineRing n) i))=
      Fin.cons (f cc) cosineVar := by
    funext i
    induction i using Fin.cases <;> rfl
  rw [ha]
  change MvPolynomial.eval₂Hom f (Fin.cons (f cc) cosineVar) _ = _
  rw [scalarPolynomial_eval f (n+1) dd rr hdd _ hi hD]
  rw [scalarNormalization_cons_flat _ _ _ _ _ (by simpa only [←map_add] using congrArg f hshift)
    hroot hfirst hsecond]
  rw [←scalarPolynomial_eval f n dd rr hdd _ (cosineVar_injective n)
    (fun i j _ => discriminant_cosineVar_ne dd hdd i j),hv]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_add]
  rfl

 
theorem scalarPolynomial_eval_cons_flat {K : Type*} [CommRing K] (f : ℂ →+* K)
    (n : ℕ) (dd rr cc CC : ℂ) (hdd : dd≠0) (hshift : cc+rr=CC)
    (hlin : 2*dd*cc=CC-cc) (hconst : cc^2-dd^2= -cc*CC) (a : Fin n → K) :
    MvPolynomial.eval₂Hom f (Fin.cons (f cc) a) (scalarPolynomial (n+1) dd rr hdd)=
      (∏ i : Fin n, (a i + f CC))*MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  have h := congrArg (MvPolynomial.eval₂Hom f a)
    (scalarPolynomial_cons_flat_identity n dd rr cc CC hdd hshift hlin hconst)
  rw [MvPolynomial.map_eval₂Hom] at h
  have hc : (MvPolynomial.eval₂Hom f a).comp MvPolynomial.C=f := by
    ext z
    simp
  have hv : (fun i : Fin (n+1) => (MvPolynomial.eval₂Hom f a)
      ((Fin.cons (MvPolynomial.C cc) MvPolynomial.X : Fin (n+1) → CosineRing n) i))=
      Fin.cons (f cc) a := by
    funext i
    induction i using Fin.cases <;> simp
  rw [hc,hv] at h
  simpa only [map_mul,map_prod,map_add,MvPolynomial.eval₂Hom_X',MvPolynomial.eval₂Hom_C] using h

end

 

 

noncomputable section

lemma cos_five_lambda_eq : Real.cos (5*lambda)= -c := by
  rw [show 5*lambda=Real.pi-3*lambda by simp [lambda]; ring,Real.cos_pi_sub]
  rfl

lemma c_add_rho_eq_C : c+rho=C := by
  have h₁ := Real.cos_add (3*lambda) (2*lambda)
  have h₂ := Real.cos_sub (3*lambda) (2*lambda)
  rw [show 3*lambda+2*lambda=5*lambda by ring,cos_five_lambda_eq] at h₁
  rw [show 3*lambda-2*lambda=lambda by ring] at h₂
  change -c=c*d-Real.sin (3*lambda)*Real.sin (2*lambda) at h₁
  change C=c*d+Real.sin (3*lambda)*Real.sin (2*lambda) at h₂
  rw [rho_eq_two_c_d]
  linarith

lemma discriminant_flat_complex (z : ℂ) :
    discriminant (d:ℂ) (c:ℂ) z=(z-(c:ℂ))*(z+(C:ℂ)) := by
  have h:=discriminant_cosine_roots_complex (3*lambda) z
  rw [show 3*lambda-6*lambda= -(3*lambda) by ring,Real.cos_neg,
    show 3*lambda+6*lambda=lambda+Real.pi by simp [lambda]; ring,Real.cos_add_pi] at h
  simpa only [c,C,Complex.ofReal_neg,sub_neg_eq_add] using h

lemma flat_scalar_linear : 2*(d:ℂ)*(c:ℂ)=(C:ℂ)-(c:ℂ) := by
  have h:=congrArg (fun x : ℝ => (x:ℂ)) c_add_rho_eq_C
  rw [rho_eq_two_c_d] at h
  push_cast at h
  linear_combination h

lemma flat_scalar_constant : (c:ℂ)^2-(d:ℂ)^2= -(c:ℂ)*(C:ℂ) := by
  simpa [discriminant] using discriminant_flat_complex 0

lemma source_scalarPolynomial_flat {K : Type*} [CommRing K] (f : ℂ →+* K)
    (n : ℕ) (a : Fin n → K) :
    MvPolynomial.eval₂Hom f (Fin.cons (f (c:ℂ)) a)
      (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))=
    (∏ i, (a i + f (C:ℂ)))*MvPolynomial.eval₂Hom f a
      (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero)) :=
  scalarPolynomial_eval_cons_flat f n d rho c C _ (by exact_mod_cast c_add_rho_eq_C)
    flat_scalar_linear flat_scalar_constant a

lemma torusSin_phase_pow (n : ℕ) (k : ℕ) :
    torusSin (constF n phase^k)=constF n (Real.sin ((k:ℝ)*lambda)) := by
  have h := congrArg (constF n) (phase_sine (k:ℤ))
  simpa [torusSin,constF,map_ofNat] using h

@[simp] lemma torusSin_one (n : ℕ) : torusSin (1:SpectralField n)=0 := by
  simp [torusSin]

lemma sin_two_lambda_eq_d : Real.sin (2*lambda)=d := by
  rw [show 2*lambda=Real.pi/4 by simp [lambda]; ring,d,
    show 2*lambda=Real.pi/4 by simp [lambda]; ring,Real.sin_pi_div_four,Real.cos_pi_div_four]

lemma sin_five_lambda_eq : Real.sin (5*lambda)=Real.sin (3*lambda) := by
  rw [show 5*lambda=Real.pi-3*lambda by simp [lambda]; ring,Real.sin_pi_sub]

lemma torusL_one (n : ℕ) :
    torusL (1:SpectralField n)=constF n d*constF n (Real.sin (3*lambda)) := by
  rw [torusL,mul_one,mul_one,torusSin_phase_pow,torusSin_phase_pow]
  simp only [Nat.cast_ofNat,sin_two_lambda_eq_d]

lemma torusL_phase_three (n : ℕ) :
    torusL (constF n phase^3)=constF n d*constF n (Real.sin (3*lambda)) := by
  rw [torusL,←pow_add,←pow_add]
  norm_num only [Nat.reduceAdd]
  rw [torusSin_phase_pow,torusSin_phase_pow]
  simp only [Nat.cast_ofNat]
  rw [sin_five_lambda_eq,sin_six_lambda,mul_comm]

lemma sin_three_lambda_pos : 0 < Real.sin (3*lambda) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · unfold lambda
    positivity
  · unfold lambda
    linarith [Real.pi_pos]

lemma torusL_one_ne_zero (n : ℕ) : torusL (1:SpectralField n)≠0 := by
  rw [torusL_one]
  apply mul_ne_zero
  · exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr (by exact_mod_cast d_ne_zero)
  · exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr
      (by exact_mod_cast ne_of_gt sin_three_lambda_pos)

lemma torusWeights_one (n : ℕ) : torusWeights (1:SpectralField n)=identityWeights := by
  have hd := torusL_one_ne_zero n
  have hq:=constF_phase_ne_zero n
  unfold torusWeights
  simp only [div_one,torusSin_one,zero_mul,mul_zero,zero_div,torusSin_phase_pow,Nat.cast_ofNat,
    sin_two_lambda_eq_d,torusL_one]
  have hn:=torusL_one n
  rw [hn] at hd
  simp only [mul_comm (constF n (Real.sin (3*lambda))),div_self hd]
  rfl

lemma torusWeights_phase_three (n : ℕ) :
    torusWeights (constF n phase^3)=deletionWeights := by
  have hd : constF n d*constF n (Real.sin (3*lambda))≠0 := by
    simpa only [torusL_one] using torusL_one_ne_zero n
  have hq:=constF_phase_ne_zero n
  have he : constF n phase^3/constF n phase=constF n phase^2 := by field_simp
  unfold torusWeights
  simp only [div_self (pow_ne_zero 3 hq),torusSin_one,mul_zero,zero_mul,zero_div,he,
    torusSin_phase_pow,Nat.cast_ofNat,sin_two_lambda_eq_d,torusL_phase_three,div_self hd]
  rfl


 

 

 

open Finset
open scoped Classical

 
def vacantBottomExtension {M : Type*} [Zero M] {n : ℕ}
    (v : Pairing n → M) (p : Pairing (n+1)) : M :=
  if p.Occupied 0 then 0 else v (p.restrict (Fin.succOrderEmb n))

@[simp] theorem vacantBottomExtension_padBottom {M : Type*} [Zero M] {n : ℕ}
    (v : Pairing n → M) (p : Pairing n) : vacantBottomExtension v p.padBottom = v p := by
  simp only [vacantBottomExtension, Pairing.padBottom_not_occupied_zero, ite_false]
  simp [Pairing.padBottom, Pairing.restrict_map]

theorem Pairing.padBottom_injective {n : ℕ} : Function.Injective (@Pairing.padBottom n) := by
  intro p q h
  have := congrArg (fun r => r.restrict (Fin.succOrderEmb n)) h
  simpa [Pairing.padBottom, Pairing.restrict_map] using this

 
theorem Pairing.padBottom_padTop {n : ℕ} (p : Pairing n) :
    p.padBottom.padTop = p.padTop.padBottom := by
  apply Subtype.ext
  simp only [Pairing.padTop, Pairing.padBottom, Pairing.map, Finset.map_map]
  congr 1

 
theorem rawColumn_padBottom {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (r : Tile → K) (p q : Pairing n) :
    rawColumn (Fin.cons r w) q.padBottom p.padBottom = r .vacant * rawColumn w q p := by
  classical
  unfold rawColumn
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Tile))
    (fun tt : Tile × Configuration n =>
      if Realizes p.padBottom q.padBottom (Fin.cons tt.1 tt.2)
      then ∏ i : Fin (n+1), ((Fin.cons r w : Fin (n+1) → Tile → K) i)
        ((Fin.cons tt.1 tt.2 : Configuration (n+1)) i) else 0)
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [realizes_cons_bottom_iff]
  rw [Finset.sum_eq_single Tile.vacant]
  · simp only [true_and, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp [Fin.prod_univ_succ]
  · intro a ha hav
    simp [hav]
  · simp

 
def firstZeroRaw {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (v : Pairing n → K) : Pairing (n+1) → K :=
  (rawColumn (Fin.cons (deletionWeights : Weights K).tile w)).mulVec
    (vacantBottomExtension v)

theorem mulVec_vacantBottomExtension {K : Type*} [CommRing K] {n : ℕ}
    (A : Matrix (Pairing (n+1)) (Pairing (n+1)) K) (v : Pairing n → K)
    (q : Pairing (n+1)) :
    A.mulVec (vacantBottomExtension v) q = ∑ p, A q p.padBottom * v p := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  symm
  apply Fintype.sum_of_injective Pairing.padBottom Pairing.padBottom_injective
  · intro p hp
    have h : p.Occupied 0 := by
      by_contra h
      exact hp ⟨p.restrict (Fin.succOrderEmb n), p.padBottom_restrict h⟩
    simp [vacantBottomExtension, h]
  · intro p; simp

 
theorem firstZeroRaw_vacant {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (v : Pairing n → K) (q : Pairing n) :
    firstZeroRaw w v q.padBottom = (rawColumn w).mulVec v q := by
  rw [firstZeroRaw, mulVec_vacantBottomExtension]
  simp only [rawColumn_padBottom, Weights.tile, deletionWeights, one_mul, Matrix.mulVec, dotProduct]

 
theorem deletion_column_mulVec {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Weights K) (v : Pairing (n+1) → K) :
    (column (Fin.cons deletionWeights w)).mulVec v =
      firstZeroRaw (fun i => (w i).tile) (fun p => v p.padBottom) := by
  classical
  funext q
  rw [firstZeroRaw, mulVec_vacantBottomExtension]
  simp only [Matrix.mulVec, dotProduct]
  symm
  apply Fintype.sum_of_injective Pairing.padBottom Pairing.padBottom_injective
  · intro p hp
    have h : p.Occupied 0 := by
      by_contra h
      exact hp ⟨p.restrict (Fin.succOrderEmb n), p.padBottom_restrict h⟩
    rw [column_deletion_bottom_col _ rfl _ _ h, zero_mul]
  · intro p
    congr 1
    change rawColumn _ q p.padBottom = rawColumn _ q p.padBottom
    congr 3
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

 

theorem normalizedVacuum_firstZero {K : Type*} [Field K] {n : ℕ}
    (w : Fin n → Weights K) (hw : VacuumRegular w) :
    normalizedVacuum (Fin.cons deletionWeights w) =
      firstZeroRaw (fun i => (w i).tile) (normalizedVacuum w) := by
  have hs := normalizedVacuum_stationary w hw
  have hr : VacuumRegular (Fin.cons deletionWeights w) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inr rfl)]
    exact hw
  symm
  apply normalizedVacuum_unique _ hr
  constructor
  · rw [← Pairing.padBottom_empty, firstZeroRaw_vacant]
    change (column w).mulVec (normalizedVacuum w) (empty n) = 1
    rw [hs.2, hs.1]
  · rw [deletion_column_mulVec]
    congr 1
    funext p
    rw [firstZeroRaw_vacant]
    exact congrFun hs.2 p

 
theorem lastValue_vacantBottomExtension {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) {n : ℕ} (b s : L) (P : Pairing (n+1) → Polynomial K) :
    lastValue f b s (vacantBottomExtension P) =
      vacantBottomExtension (lastValue f b s P) := by
  funext p
  by_cases hp : p.Occupied 0
  · simp [lastValue, vacantBottomExtension, hp]
  · rw [← p.padBottom_restrict hp]
    simp only [vacantBottomExtension_padBottom, lastValue,
      ← Fin.succ_last, Pairing.padBottom_occupied_succ]

 

theorem LastDegree.vacantBottomExtension {K : Type*} [CommRing K] {n m : ℕ}
    {P : Pairing (n+1) → Polynomial K} (hP : LastDegree m P) :
    LastDegree m (vacantBottomExtension P) := by
  intro p k hk
  by_cases hp : p.Occupied 0
  · simp [CriticalStrip.Diagram.vacantBottomExtension, hp]
  · rw [← p.padBottom_restrict hp] at hk ⊢
    rw [vacantBottomExtension_padBottom]
    apply hP
    simpa only [← Fin.succ_last, Pairing.padBottom_occupied_succ] using hk

 

theorem vacantBottomExtension_leading {K : Type*} [CommRing K] {n : ℕ}
    (P : Pairing (n+1) → Polynomial K) (m : ℕ) :
    (fun p : Pairing (n+1) => (vacantBottomExtension P p.padTop).coeff m) =
      vacantBottomExtension (fun p : Pairing n => (P p.padTop).coeff m) := by
  funext p
  by_cases hp : p.Occupied 0
  · have hp' : p.padTop.Occupied 0 := by
      simpa using (Pairing.padTop_occupied_castSucc p 0).mpr hp
    simp [vacantBottomExtension, hp, hp']
  · rw [← p.padBottom_restrict hp, Pairing.padBottom_padTop]
    simp

 
def firstZeroPolynomial {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) : Pairing (n+2) → Polynomial K :=
  lastTransform (Fin.cons (deletionWeights : Weights K).tile w) d c C
    (vacantBottomExtension P)

theorem firstZeroPolynomial_degree {K : Type*} [CommRing K] {n m : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) (hP : LastDegree m P) :
    LastDegree (m+1) (firstZeroPolynomial w d c C P) :=
  lastTransform_degree _ _ _ _ _ hP.vacantBottomExtension

theorem firstZeroPolynomial_leading {K : Type*} [CommRing K] {n m : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) (hP : LastDegree m P) (q : Pairing (n+1)) :
    (firstZeroPolynomial w d c C P q.padTop).coeff (m+1) =
      firstZeroRaw w (fun p => (P p.padTop).coeff m) q := by
  rw [firstZeroPolynomial, lastTransform_leading _ _ _ _ _ hP.vacantBottomExtension,
    vacantBottomExtension_leading]
  rfl

@[simp] theorem map_deletion_tile {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (t : Tile) :
    f ((deletionWeights : Weights K).tile t) = (deletionWeights : Weights L).tile t := by
  cases t <;> simp [deletionWeights, Weights.tile]

 

theorem firstZeroPolynomial_evaluation {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) {n : ℕ} (w : Fin n → Tile → K) (d c C : K)
    (b s t : L) (r : Tile → L) (P : Pairing (n+1) → Polynomial K)
    (hv : r .vacant = b + f C) (hc : r .cap = 2 * f d * t)
    (hu : r .vertical₀ = 2 * f d * s) (hb : r .diagonal₁ = b - f c)
    (hst : 2 * s * t = b - f c) :
    firstZeroRaw (Fin.snoc (fun i a => f (w i a)) r) (lastValue f b s P) =
      lastValue f b s (firstZeroPolynomial w d c C P) := by
  have h := rawColumn_lastValue f (Fin.cons (deletionWeights : Weights K).tile w)
    d c C b s t r (vacantBottomExtension P) hv hc hu hb hst
  rw [lastValue_vacantBottomExtension] at h
  have hmap : (fun (i : Fin (n+1)) (a : Tile) =>
      f ((Fin.cons (deletionWeights : Weights K).tile w : Fin (n+1) → Tile → K) i a)) =
      Fin.cons (deletionWeights : Weights L).tile (fun i a => f (w i a)) := by
    funext i a
    refine Fin.cases ?_ (fun j => ?_) i
    · cases a <;> simp only [Fin.cons_zero, deletionWeights, Weights.tile, map_zero, map_one]
    · rfl
  rw [hmap, ← Fin.cons_snoc_eq_snoc_cons] at h
  exact h

end

 

 

noncomputable section
open Finset

theorem firstZeroRaw_rowScale {K : Type*} [CommRing K] {n : ℕ}
    (a : Fin n → K) (w : Fin n → Tile → K) (v : Pairing n → K) :
    firstZeroRaw (fun i t => a i * w i t) v =
      (∏ i, a i) • firstZeroRaw w v := by
  have h : Fin.cons (deletionWeights : Weights K).tile (fun i t => a i * w i t) =
      (fun (i : Fin (n+1)) t => (Fin.cons 1 a : Fin (n+1) → K) i *
        (Fin.cons (deletionWeights : Weights K).tile w : Fin (n+1) → Tile → K) i t) := by
    funext i t
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rfl
  rw [firstZeroRaw, h, rawColumn_scale]
  simp [Fin.prod_univ_succ, firstZeroRaw, Matrix.smul_mulVec]

 

theorem firstZeroPolynomial_spectral {n k : ℕ}
    (w : Fin n → Tile → SpectralField k) (i : Fin k)
    (P : Pairing (n+1) → Polynomial (SpectralField k)) :
    firstZeroRaw (Fin.snoc w (clearedSpectralRow i))
        (lastValue (RingHom.id _) (spectralA i) (torusSin (variableF i)) P) =
      lastValue (RingHom.id _) (spectralA i) (torusSin (variableF i))
        (firstZeroPolynomial w (constF k d) (constF k c) (constF k C) P) := by
  apply firstZeroPolynomial_evaluation (RingHom.id _) w (constF k d) (constF k c)
    (constF k C) (spectralA i) (torusSin (variableF i))
    (torusSin (constF k phase ^ 3 / variableF i)) (clearedSpectralRow i) P
  · exact clearedSpectralRow_vacant i
  · exact clearedSpectralRow_cap i
  · exact clearedSpectralRow_vertical₀ i
  · exact clearedSpectralRow_diagonal₁ i
  · exact spectral_sine_pair i

end
end CriticalStrip.Diagram

end OAI
