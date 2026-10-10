import Mathlib
import OAI.Algebra.FiniteTensor.ArtinCoefficients

namespace OAI

/-! Weierstrass reconstitution and finite constraints for distinguished division. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {R σ κ : Type*} [CommRing R]

 theorem polynomial_eval_divisor_congruence (h : R) (f : MvPolynomial σ R)
    (a b : σ → R) (hab : ∀ i,h∣a i-b i) : h∣eval a f-eval b f := by
  let J : Ideal R := Ideal.span {h}
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub,sub_eq_zero]
  have he : (Ideal.Quotient.mk J).comp (eval a)=(Ideal.Quotient.mk J).comp (eval b) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i
      simp only [RingHom.comp_apply,eval_X]
      exact sub_eq_zero.mp ((map_sub _ _ _).symm.trans
        (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hab i))))
  exact RingHom.congr_fun he f

 theorem unit_add_jacobson {w h : R} (hw : IsUnit w)
    (hh : h∈Ideal.jacobson (⊥ : Ideal R)) : IsUnit (w+h) := by
  obtain ⟨u,rfl⟩ := hw
  have hu := Ideal.mem_jacobson_bot.mp hh (↑u⁻¹ : R)
  have ht := u.isUnit.mul hu
  convert ht using 1
  simp [mul_add,mul_left_comm,add_comm]

 

theorem weierstrass_prepared_minor
    (f : κ → MvPolynomial σ R) (D : MvPolynomial σ R)
    (r q : σ → R) (h w : R) (hw : IsUnit w)
    (hh : h∈Ideal.jacobson (⊥ : Ideal R))
    (hf : ∀ k,h^2∣eval r (f k)) (hD : eval r D=h*w) :
    let a := fun i=>r i+h^2*q i
    (∃ v : R,IsUnit v ∧ eval a D=h*v) ∧
      ∀ k,(eval a D)^2∣eval a (f k) := by
  let a := fun i=>r i+h^2*q i
  have hcon (i : σ) : h^2∣a i-r i := by
    exact ⟨q i,by dsimp [a]; ring⟩
  obtain ⟨z,hz⟩ := polynomial_eval_divisor_congruence (h^2) D a r hcon
  have he : eval a D=h*(w+h*z) := by rw [hD] at hz; linear_combination hz
  have hun : IsUnit (w+h*z) := unit_add_jacobson hw ((Ideal.jacobson ⊥).mul_mem_right _ hh)
  refine ⟨⟨w+h*z,hun,he⟩,fun k=>?_⟩
  have hfa : h^2∣eval a (f k) := by
    have hc := polynomial_eval_divisor_congruence (h^2) (f k) a r hcon
    convert dvd_add hc (hf k) using 1
    ring
  rw [he,mul_pow]
  rw [mul_comm]
  exact (hun.pow 2).mul_left_dvd.mpr hfa

 
def minorPolynomial [Fintype κ] [DecidableEq κ]
    (f : κ → MvPolynomial (κ ⊕ σ) R) : MvPolynomial (κ ⊕ σ) R :=
  Matrix.det (fun k i=>pderiv (Sum.inl i) (f k))

 theorem eval_minorPolynomial [Fintype κ] [DecidableEq κ]
    (f : κ → MvPolynomial (κ ⊕ σ) R) (a : (κ ⊕ σ) → R) :
    eval a (minorPolynomial f)=Matrix.det (fun k i=>eval a (pderiv (Sum.inl i) (f k))) := by
  unfold minorPolynomial
  exact RingHom.map_det (eval a) _

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {R σ κ : Type*} [CommRing R]

 

theorem reconstitute_close (J : Ideal R) (h h' : R) (r r' q q' : σ → R)
    (hh : h'-h∈J) (hr : ∀ i,r' i-r i∈J) (hq : ∀ i,q' i-q i∈J) (i : σ) :
    r' i+h'^2*q' i-(r i+h^2*q i)∈J := by
  have hh2 : h'^2-h^2∈J := by
    convert J.mul_mem_right (h'+h) hh using 1
    ring
  have hs := J.add_mem (J.add_mem (hr i) (J.mul_mem_right (q' i) hh2))
    (J.mul_mem_left (h^2) (hq i))
  convert hs using 1
  ring

 

theorem weierstrass_reconstitution
    (J : Ideal R) (f : κ → MvPolynomial σ R) (D : MvPolynomial σ R)
    (h h' w' : R) (r r' q q' : σ → R)
    (hh0 : h'≠0) (hhjac : h'∈Ideal.jacobson (⊥ : Ideal R)) (hw : IsUnit w')
    (hf : ∀ k,h'^2∣eval r' (f k)) (hD : eval r' D=h'*w')
    (hh : h'-h∈J) (hr : ∀ i,r' i-r i∈J) (hq : ∀ i,q' i-q i∈J) :
    let a := fun i=>r' i+h'^2*q' i
    (eval a D≠0) ∧ (∀ k,(eval a D)^2∣eval a (f k)) ∧
      ∀ i,a i-(r i+h^2*q i)∈J := by
  obtain ⟨⟨v,hv,hvEq⟩,hdiv⟩ := weierstrass_prepared_minor f D r' q' h' w' hw hhjac hf hD
  refine ⟨?_,hdiv,reconstitute_close J h h' r r' q q' hh hr hq⟩
  rw [hvEq]
  exact fun hz=>hh0 ((hv.mul_left_eq_zero).mp hz)

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable {B A σ : Type*} [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] [Algebra B A]

 

omit [IsDomain A] in
theorem reconstitute_algebraic (h : Polynomial A) (r : σ → Polynomial A)
    (q : σ → PowerSeries A)
    (hh : ∀ j,IsAlgebraic B (h.coeff j))
    (hr : ∀ i j,IsAlgebraic B ((r i).coeff j))
    (hq : ∀ i,IsAlgebraic (Polynomial B) (q i)) (i : σ) :
    IsAlgebraic (Polynomial B) ((r i : PowerSeries A)+(h : PowerSeries A)^2*q i) := by
  exact (polynomial_series_algebraic_coefficients (r i) (hr i)).add
    (((polynomial_series_algebraic_coefficients h hh).pow 2).mul (hq i))

end
end PD4Tensor.Spreading

 

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {R S σ κ : Type*} [CommRing R] [CommRing S]

abbrev RemainderVariables (σ κ : Type*) := Unit ⊕ (σ ⊕ (κ ⊕ Unit))

def remainderPoint (h : S) (r : σ → S) (k : κ → S) (w : S) : RemainderVariables σ κ → S :=
  Sum.elim (fun _=>h) (Sum.elim r (Sum.elim k (fun _=>w)))

def remainderEmbedding : σ → RemainderVariables σ κ := fun i=>Sum.inr (Sum.inl i)

def remainderEquation (f : κ → MvPolynomial σ R) (D : MvPolynomial σ R) :
    κ ⊕ Unit → MvPolynomial (RemainderVariables σ κ) R :=
  Sum.elim (fun j=>rename remainderEmbedding (f j)-
    X (Sum.inl ())^2*X (Sum.inr (Sum.inr (Sum.inl j))))
    (fun _=>rename remainderEmbedding D-X (Sum.inl ())*X (Sum.inr (Sum.inr (Sum.inr ()))))

 theorem eval_remainderEmbedding (φ : R →+* S) (h : S) (r : σ → S) (k : κ → S) (w : S)
    (p : MvPolynomial σ R) :
    eval₂ φ (remainderPoint h r k w) (rename remainderEmbedding p)=eval₂ φ r p := by
  rw [eval₂_rename]
  rfl

 

theorem remainder_equations_iff (φ : R →+* S)
    (f : κ → MvPolynomial σ R) (D : MvPolynomial σ R)
    (h : S) (r : σ → S) (k : κ → S) (w : S) :
    (∀ j,eval₂ φ (remainderPoint h r k w) (remainderEquation f D j)=0) ↔
      (∀ j,eval₂ φ r (f j)=h^2*k j) ∧ eval₂ φ r D=h*w := by
  constructor
  · intro he
    constructor
    · intro j
      have hh := he (Sum.inl j)
      change eval₂ φ (remainderPoint h r k w)
        (rename remainderEmbedding (f j)-X (Sum.inl ())^2*X (Sum.inr (Sum.inr (Sum.inl j))))=0 at hh
      simpa only [eval₂_sub,eval₂_mul,eval₂_pow,eval₂_X,eval₂_rename,Function.comp_def,remainderEmbedding,
        remainderPoint,Sum.elim_inl,Sum.elim_inr,sub_eq_zero] using hh
    · have hh := he (Sum.inr ())
      change eval₂ φ (remainderPoint h r k w)
        (rename remainderEmbedding D-X (Sum.inl ())*X (Sum.inr (Sum.inr (Sum.inr ()))))=0 at hh
      simpa only [eval₂_sub,eval₂_mul,eval₂_X,eval₂_rename,Function.comp_def,remainderEmbedding,
        remainderPoint,Sum.elim_inl,Sum.elim_inr,sub_eq_zero] using hh
  · rintro ⟨hf,hD⟩ (j|j)
    · change eval₂ φ (remainderPoint h r k w)
        (rename remainderEmbedding (f j)-X (Sum.inl ())^2*X (Sum.inr (Sum.inr (Sum.inl j))))=0
      simpa only [eval₂_sub,eval₂_mul,eval₂_pow,eval₂_X,eval₂_rename,Function.comp_def,remainderEmbedding,
        remainderPoint,Sum.elim_inl,Sum.elim_inr,sub_eq_zero] using hf j
    · change eval₂ φ (remainderPoint h r k w)
        (rename remainderEmbedding D-X (Sum.inl ())*X (Sum.inr (Sum.inr (Sum.inr ()))))=0
      simpa only [eval₂_sub,eval₂_mul,eval₂_X,eval₂_rename,Function.comp_def,remainderEmbedding,
        remainderPoint,Sum.elim_inl,Sum.elim_inr,sub_eq_zero] using hD

omit [CommRing S] in
 theorem remainder_point_reconstruct (p : RemainderVariables σ κ → S) :
    remainderPoint (p (Sum.inl ())) (fun i=>p (Sum.inr (Sum.inl i)))
      (fun j=>p (Sum.inr (Sum.inr (Sum.inl j)))) (p (Sum.inr (Sum.inr (Sum.inr ()))))=p := by
  funext x
  rcases x with x|(x|(x|x))
  · cases x; rfl
  · rfl
  · rfl
  · cases x; rfl

end
end PD4Tensor.Spreading

 

namespace PD4Tensor.Spreading
noncomputable section
variable {A : Type*} [CommRing A]

 theorem powerSeries_constant_mem (I : Ideal A) {f : PowerSeries A}
    (hf : f∈I.map (PowerSeries.C : A →+* PowerSeries A)) :
    PowerSeries.constantCoeff f∈I := by
  have hle : I.map (PowerSeries.C : A →+* PowerSeries A)≤I.comap PowerSeries.constantCoeff := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    simpa using ha
  exact hle hf

 theorem powerSeries_map_jacobson (I : Ideal A) (hI : I≤Ideal.jacobson (⊥ : Ideal A)) :
    I.map (PowerSeries.C : A →+* PowerSeries A)≤Ideal.jacobson (⊥ : Ideal (PowerSeries A)) := by
  intro f hf
  rw [Ideal.mem_jacobson_bot]
  intro g
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_add,map_mul,map_one]
  exact Ideal.mem_jacobson_bot.mp (hI (powerSeries_constant_mem I hf)) _

 theorem powerSeries_unit_close (I : Ideal A) (hI : I≤Ideal.jacobson (⊥ : Ideal A))
    (f g : PowerSeries A) (hf : IsUnit f)
    (hgf : g-f∈I.map (PowerSeries.C : A →+* PowerSeries A)) : IsUnit g := by
  obtain ⟨u,rfl⟩ := hf
  have hj := powerSeries_map_jacobson I hI hgf
  have hu := Ideal.mem_jacobson_bot.mp hj (↑u⁻¹ : PowerSeries A)
  have hh := u.isUnit.mul hu
  convert hh using 1
  calc
    g=(↑u*↑u⁻¹ : PowerSeries A)*(g-↑u)+↑u := by simp
    _=↑u*((g-↑u)*↑u⁻¹+1) := by ring

 theorem powerSeries_jacobson_close (I : Ideal A) (hI : I≤Ideal.jacobson (⊥ : Ideal A))
    (f g : PowerSeries A) (hf : f∈Ideal.jacobson (⊥ : Ideal (PowerSeries A)))
    (hgf : g-f∈I.map (PowerSeries.C : A →+* PowerSeries A)) :
    g∈Ideal.jacobson (⊥ : Ideal (PowerSeries A)) := by
  convert (Ideal.jacobson (⊥ : Ideal (PowerSeries A))).add_mem
    (powerSeries_map_jacobson I hI hgf) hf using 1
  abel

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {B A σ κ : Type*} [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
  [Algebra B A] [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

abbrev seriesCoefficientMap : Polynomial B →+* PowerSeries A :=
  Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom (algebraMap B A))

omit [IsDomain B] [IsDomain A] [Fintype σ] [DecidableEq σ] in
 theorem eval_seriesCoefficientMap (r : σ → Polynomial A) (f : MvPolynomial σ (Polynomial B)) :
    eval (fun i=>(r i : PowerSeries A)) (map (seriesCoefficientMap (B:=B) (A:=A)) f)=
      (eval₂ (Polynomial.mapRingHom (algebraMap B A)) r f : Polynomial A) := by
  rw [←eval₂_eq_eval_map]
  exact (hom_eval₂ f (Polynomial.mapRingHom (algebraMap B A))
    Polynomial.coeToPowerSeries.ringHom r).symm

 

omit [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ] in
theorem coefficient_prepared_point
    (I : Ideal A) (hI : I≤Ideal.jacobson (⊥ : Ideal A))
    (f : κ → MvPolynomial σ (Polynomial B)) (D : MvPolynomial σ (Polynomial B))
    (p : RemainderVariables σ κ → Polynomial A)
    (hpmonic : (p (Sum.inl ())).Monic)
    (hpjac : (p (Sum.inl ()) : PowerSeries A)∈Ideal.jacobson (⊥ : Ideal (PowerSeries A)))
    (hpunit : IsUnit (p (Sum.inr (Sum.inr (Sum.inr ()))) : PowerSeries A))
    (x : CoefficientVariables p → A)
    (hxalg : ∀ v,IsAlgebraic B (x v))
    (hxclose : ∀ v,x v-coefficientPoint p v∈I)
    (hxsol : ∀ e,eval₂ (algebraMap B A) x
      (coefficientEquation p (remainderEquation f D) e)=0)
    (q : σ → PowerSeries A) (hq : ∀i,IsAlgebraic (Polynomial B) (q i)) :
    ∃ a : σ → PowerSeries A,
      (∀ i,IsAlgebraic (Polynomial B) (a i)) ∧
      (eval a (map (seriesCoefficientMap (B:=B) (A:=A)) D)≠0) ∧
      (∀ k,eval a (map (seriesCoefficientMap (B:=B) (A:=A)) D)^2∣
        eval a (map (seriesCoefficientMap (B:=B) (A:=A)) (f k))) ∧
      ∀ i,a i-((p (Sum.inr (Sum.inl i)) : PowerSeries A)+
        (p (Sum.inl ()) : PowerSeries A)^2*q i)∈I.map (PowerSeries.C : A →+* PowerSeries A) := by
  let p' := realizeCoefficients p x
  let h := p (Sum.inl ())
  let h' := p' (Sum.inl ())
  let r := fun i=>p (Sum.inr (Sum.inl i))
  let r' := fun i=>p' (Sum.inr (Sum.inl i))
  let k' := fun j=>p' (Sum.inr (Sum.inr (Sum.inl j)))
  let w' := p' (Sum.inr (Sum.inr (Sum.inr ())))
  have he := (coefficient_equations_iff (algebraMap B A) p (remainderEquation f D) x).mp hxsol
  have hep : remainderPoint h' r' k' w'=p' := remainder_point_reconstruct p'
  have hs : (∀ j,eval₂ (Polynomial.mapRingHom (algebraMap B A)) r' (f j)=h'^2*k' j) ∧
      eval₂ (Polynomial.mapRingHom (algebraMap B A)) r' D=h'*w' := by
    apply (remainder_equations_iff _ f D h' r' k' w').mp
    intro e
    rw [hep]
    exact he e
  have hc (v : RemainderVariables σ κ) :
      (p' v : PowerSeries A)-(p v : PowerSeries A)∈I.map (PowerSeries.C : A →+* PowerSeries A) :=
    realizeCoefficients_series_close p x I hxclose v
  have hh0 : (h' : PowerSeries A)≠0 := by
    exact_mod_cast monic_coefficient_close_ne_zero I hI h h' hpmonic
      (realizeCoefficients_close p x I hxclose (Sum.inl ()))
  have hhjac : (h' : PowerSeries A)∈Ideal.jacobson (⊥ : Ideal (PowerSeries A)) :=
    powerSeries_jacobson_close I hI _ _ hpjac (hc (Sum.inl ()))
  have hwunit : IsUnit (w' : PowerSeries A) :=
    powerSeries_unit_close I hI _ _ hpunit (hc (Sum.inr (Sum.inr (Sum.inr ()))))
  have hf (j : κ) : (h' : PowerSeries A)^2∣eval (fun i=>(r' i : PowerSeries A))
      (map (seriesCoefficientMap (B:=B) (A:=A)) (f j)) := by
    rw [eval_seriesCoefficientMap,hs.1 j,Polynomial.coe_mul,Polynomial.coe_pow]
    exact dvd_mul_right _ _
  have hD : eval (fun i=>(r' i : PowerSeries A))
      (map (seriesCoefficientMap (B:=B) (A:=A)) D)=(h' : PowerSeries A)*(w' : PowerSeries A) := by
    rw [eval_seriesCoefficientMap,hs.2,Polynomial.coe_mul]
  obtain ⟨hn,hdiv,hclose⟩ := weierstrass_reconstitution
    (I.map (PowerSeries.C : A →+* PowerSeries A))
    (fun k=>map (seriesCoefficientMap (B:=B) (A:=A)) (f k))
    (map (seriesCoefficientMap (B:=B) (A:=A)) D)
    (h : PowerSeries A) (h' : PowerSeries A) (w' : PowerSeries A)
    (fun i=>(r i : PowerSeries A)) (fun i=>(r' i : PowerSeries A)) q q
    hh0 hhjac hwunit hf hD (hc (Sum.inl ()))
    (fun i=>hc (Sum.inr (Sum.inl i))) (fun i=>by simp)
  refine ⟨fun i=>(r' i : PowerSeries A)+(h' : PowerSeries A)^2*q i,?_,hn,hdiv,hclose⟩
  intro i
  exact reconstitute_algebraic h' r' q
    (realizeCoefficients_algebraic p x hxalg (Sum.inl ()))
    (fun i=>realizeCoefficients_algebraic p x hxalg (Sum.inr (Sum.inl i))) hq i

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open Polynomial PowerSeries MvPolynomial
variable {A σ κ : Type*} [CommRing A]

 
theorem distinguished_dvd_of_series_dvd (I : Ideal A) [IsAdicComplete I A]
    {h p : Polynomial A} (hh : h.IsDistinguishedAt I)
    (hp : (h : PowerSeries A) ∣ (p : PowerSeries A)) : h ∣ p := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hh.algEquivQuotient.injective
  rw [map_zero]
  change Ideal.Quotient.mk (Ideal.span {(h : PowerSeries A)}) (p : PowerSeries A) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hp)

 
theorem eval₂_dvd_sub (d : PowerSeries A) (f : MvPolynomial σ (Polynomial A))
    (u v : σ → PowerSeries A) (h : ∀ i,d ∣ u i-v i) :
    d ∣ eval₂ Polynomial.coeToPowerSeries.ringHom u f -
      eval₂ Polynomial.coeToPowerSeries.ringHom v f := by
  let J : Ideal (PowerSeries A) := Ideal.span {d}
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub,sub_eq_zero]
  have he : (Ideal.Quotient.mk J).comp (eval₂Hom Polynomial.coeToPowerSeries.ringHom u) =
      (Ideal.Quotient.mk J).comp (eval₂Hom Polynomial.coeToPowerSeries.ringHom v) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [RingHom.comp_apply,eval₂Hom_X']
      exact sub_eq_zero.mp ((map_sub _ _ _).symm.trans
        (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h i))))
  exact RingHom.congr_fun he f

 

theorem finite_weierstrass_constraints
    (I : Ideal A) [IsAdicComplete I A]
    (h : Polynomial A) (hh : h.IsDistinguishedAt I)
    (a : σ → PowerSeries A) (f : κ → MvPolynomial σ (Polynomial A))
    (hf : ∀ k,eval₂ Polynomial.coeToPowerSeries.ringHom a (f k)=0)
    (D : MvPolynomial σ (Polynomial A))
    (hD : (h : PowerSeries A) ∣ eval₂ Polynomial.coeToPowerSeries.ringHom a D) :
    ∃ r : σ → Polynomial A,
      (∀ i,(r i).degree <
        (((h*h : Polynomial A) : PowerSeries A).map (Ideal.Quotient.mk I)).order.toNat) ∧
      (∀ i,((h*h : Polynomial A) : PowerSeries A) ∣ a i-(r i : PowerSeries A)) ∧
      (∀ k,h*h ∣ eval r (f k)) ∧ h ∣ eval r D := by
  let H := (hh.mul hh).isWeierstrassDivisorAt'
  let r : σ → Polynomial A := fun i=>H.mod (a i)
  have hd (i : σ) := H.isWeierstrassDivisionAt_div_mod (a i)
  have hdiv (i : σ) : ((h*h : Polynomial A) : PowerSeries A) ∣
      a i-(r i : PowerSeries A) := by
    exact ⟨H.div (a i), by linear_combination (hd i).eq_mul_add⟩
  refine ⟨r,fun i=>(hd i).degree_lt,hdiv,?_,?_⟩
  · intro k
    apply distinguished_dvd_of_series_dvd I (hh.mul hh)
    have hz := eval₂_dvd_sub ((h*h : Polynomial A) : PowerSeries A) (f k) a
      (fun i=>(r i : PowerSeries A)) hdiv
    rw [hf k,zero_sub] at hz
    have hm := MvPolynomial.map_eval Polynomial.coeToPowerSeries.ringHom r (f k)
    rw [MvPolynomial.eval_map] at hm
    change ((eval r (f k) : Polynomial A) : PowerSeries A) =
      eval₂ Polynomial.coeToPowerSeries.ringHom (fun i=>(r i : PowerSeries A)) (f k) at hm
    rw [←hm] at hz
    exact dvd_neg.mp hz
  · apply distinguished_dvd_of_series_dvd I hh
    have hv (i : σ) : (h : PowerSeries A) ∣ a i-(r i : PowerSeries A) :=
      dvd_trans (by simp only [Polynomial.coe_mul]; exact dvd_mul_right _ _) (hdiv i)
    have hz := eval₂_dvd_sub (h : PowerSeries A) D a (fun i=>(r i : PowerSeries A)) hv
    have hm := MvPolynomial.map_eval Polynomial.coeToPowerSeries.ringHom r D
    rw [MvPolynomial.eval_map] at hm
    change ((eval r D : Polynomial A) : PowerSeries A) =
      eval₂ Polynomial.coeToPowerSeries.ringHom (fun i=>(r i : PowerSeries A)) D at hm
    rw [←hm] at hz
    have hh := dvd_sub hD hz
    convert hh using 1
    ring

end
end PD4Tensor.Spreading
end

end OAI
