import OAI.Algebra.AffineCancellation.Primitive
import OAI.Algebra.AffineCancellation.LaurentDerivation
import OAI.Algebra.AffineCancellation.ReesClearing

namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
lemma uniform_clear (f : Fin 6 → L) :
    ∃ n : ℕ, ∀ i, ∃ b : B, embedding q^n*f i=embedding b := by
  classical
  choose n b hb using fun i => clear_all (f i)
  refine ⟨∑ i, n i, fun i => ⟨q^((∑ j,n j)-n i)*b i,?_⟩⟩
  have hi : n i ≤ ∑ j, n j := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  rw [map_mul,map_pow,← hb,← mul_assoc,← pow_add,Nat.sub_add_cancel hi]
lemma stable_of_generators (E : Derivation ℂ L L)
    (h : ∀ i : Fin 6, ∃ t : B, E (embedding (π (X i)))=embedding t) :
    ∀ b : B, ∃ t : B, E (embedding b)=embedding t := by
  intro b
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ b
  change ∃ t, E (embedding (π r))=embedding t
  induction r using MvPolynomial.induction_on with
  | C z => exact ⟨0,by simp only [MvPolynomial.C_eq_algebraMap,AlgHom.commutes,
      Derivation.map_algebraMap,map_zero]⟩
  | add r s hr hs =>
    obtain ⟨r',hr'⟩ := hr
    obtain ⟨s',hs'⟩ := hs
    exact ⟨r'+s',by rw [map_add,map_add,map_add,hr',hs',map_add]⟩
  | mul_X r i hr =>
    obtain ⟨r',hr'⟩ := hr
    obtain ⟨s',hs'⟩ := h i
    refine ⟨π r*s'+π (X i)*r',?_⟩
    rw [map_mul,map_mul,Derivation.leibniz,hr',hs',smul_eq_mul,smul_eq_mul,
      map_add,map_mul,map_mul]
lemma clear_annihilate (D : Derivation ℂ A A) (n : ℕ)
    (h : ∀ b : B, embedding q^n * LaurentDerivation.extension D (embedding b)=0) : D=0 := by
  let D' := LaurentDerivation.extension D
  have hq : D' (embedding q)=0 := by rw [embedding_q]; exact LaurentDerivation.extension_T D 1
  have hnon : embedding q^n ≠ 0 := pow_ne_zero n (by rw [embedding_q]; exact (isUnit_T _).ne_zero)
  ext a
  obtain ⟨m,b,hb⟩ := clear_all (c a)
  have hd : D' (embedding b)=0 := (mul_eq_zero.mp (h b)).resolve_left hnon
  have he := congrArg D' hb
  rw [Derivation.leibniz,Derivation.leibniz_pow,hq,smul_zero,smul_zero,smul_zero,add_zero,hd] at he
  have ha : D' (c a)=0 := (smul_eq_zero.mp he).resolve_left (pow_ne_zero m (by rw [embedding_q]; exact (isUnit_T _).ne_zero))
  change LaurentDerivation.extension D (LaurentPolynomial.C a)=0 at ha
  rw [LaurentDerivation.extension_C] at ha
  have hz := congrArg (fun t : L => t.coeff 0) ha
  simpa [LaurentPolynomial.C_apply] using hz
lemma scaled_is_ln (D : Derivation ℂ A A) (hD : LND.LocallyNilpotent D) (n : ℕ) :
    LND.LocallyNilpotent (k := ℂ) (R := L) (embedding q^n • LaurentDerivation.extension D) := by
  apply LND.replica _ (LaurentDerivation.locallyNilpotent D hD)
  rw [Derivation.leibniz_pow,embedding_q,LaurentDerivation.extension_T,smul_zero,smul_zero]
lemma scaled_fixes (D : Derivation ℂ A A) (r : A) (hDr : D r=0) (i : ℤ) (s : B)
    (hs : embedding s=T i*c r) (n : ℕ) :
    (embedding q^n • LaurentDerivation.extension D) (embedding s)=0 := by
  have he : LaurentDerivation.extension D (embedding s)=0 := by
    rw [hs,Derivation.leibniz]
    have hr : LaurentDerivation.extension D (c r)=0 := by
      change LaurentDerivation.extension D (LaurentPolynomial.C r)=0
      rw [LaurentDerivation.extension_C,hDr,map_zero]
    rw [hr,LaurentDerivation.extension_T,smul_zero,smul_zero,add_zero]
  exact (congrArg (fun z : L => embedding q^n*z) he).trans (mul_zero _)

lemma restrict_stable (E' : Derivation ℂ L L) (hE' : LND.LocallyNilpotent (k := ℂ) (R := L) E')
    (hstable : ∀ b : B, ∃ t : B, E' (embedding b)=embedding t) :
    ∃ E : Derivation ℂ B B, LND.LocallyNilpotent E ∧ ∀ b, E' (embedding b)=embedding (E b) := by
  have hfac : ∀ b : B, ∃ t : B, E' (embedding b)=1*embedding t := by simpa only [one_mul] using hstable
  let E := FactorDerivation.derivation (k := ℂ) (R := L) embedding embedding_injective E' 1 one_ne_zero hfac
  have hspec (b : B) : E' (embedding b)=embedding (E b) := by
    simpa only [one_mul] using FactorDerivation.apply_spec (k := ℂ) (R := L) embedding embedding_injective E' 1 one_ne_zero hfac b
  exact ⟨E,LND.cancel_factor_locallyNilpotent (k := ℂ) (R := L) embedding embedding_injective E' hE' E one_ne_zero (by simpa only [one_mul] using hspec),hspec⟩
lemma scaled_restriction (D : Derivation ℂ A A) (hD : LND.LocallyNilpotent D)
    (hDn : D ≠ 0) (r : A) (hDr : D r=0) (i : ℤ) (s : B)
    (hs : embedding s=T i*c r) :
    ∃ E : Derivation ℂ B B, LND.LocallyNilpotent E ∧ E ≠ 0 ∧ E q=0 ∧ E s=0 := by
  obtain ⟨n,hn⟩ := uniform_clear (fun i => LaurentDerivation.extension D (embedding (π (X i))))
  let E' := embedding q^n • LaurentDerivation.extension D
  have hgen (i : Fin 6) : ∃ t : B, E' (embedding (π (X i)))=embedding t := hn i
  obtain ⟨E,hE,hspec⟩ := restrict_stable E' (scaled_is_ln D hD n) (stable_of_generators E' hgen)
  refine ⟨E,hE,?_,?_,?_⟩
  · intro hz
    apply hDn
    apply clear_annihilate D n
    intro b
    change E' (embedding b)=0
    rw [hspec,hz,Derivation.zero_apply,map_zero]
  · apply embedding_injective
    rw [map_zero,← hspec]
    change embedding q^n*LaurentDerivation.extension D (embedding q)=0
    rw [embedding_q,LaurentDerivation.extension_T,mul_zero]
  · apply embedding_injective
    rw [map_zero,← hspec]
    exact scaled_fixes D r hDr i s hs n

def up : Degeneration.P →ₐ[ℂ] B := aeval ![π (X 1),π (X 2),π (X 3),π (X 4),π (X 5)]
lemma red_up : red.comp up=Degeneration.π := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [up,redEval,redValues,Matrix.cons_val,
    Degeneration.p,Degeneration.s,Degeneration.u,Degeneration.F,Degeneration.J]
lemma red_surjective : Function.Surjective red := by
  intro r
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ r
  exact ⟨up p,DFunLike.congr_fun red_up p⟩
lemma primitive_reduction (E : Derivation ℂ B B) (hE : LND.LocallyNilpotent E)
    (hEn : E ≠ 0) (hEq : E q=0) (s : B) (hEs : E s=0) :
    ∃ D : Derivation ℂ Degeneration.G Degeneration.G,
      LND.LocallyNilpotent D ∧ D ≠ 0 ∧ D (red s)=0 := by
  obtain ⟨b,hb⟩ : ∃ b, E b ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hEn
    ext b
    exact hn b
  obtain ⟨n,t,ht,he⟩ := maximum_q_factor hb
  obtain ⟨E',hE',hEq',hEs',r,hr⟩ := LND.primitive_of_order q q_nonzero s b t
    (mt (red_zero_iff t).mpr ht) n E hE hEq hEs he
  have hk (b : B) (hb : red b=0) : red (E' b)=0 := by
    obtain ⟨t,rfl⟩ := (red_zero_iff b).mp hb
    simp only [Derivation.leibniz,hEq',smul_eq_mul,mul_zero,add_zero,
      map_mul,red_q,zero_mul]
  let D := Derivation.liftOfSurjective red_surjective hk
  have hspec (b : B) : D (red b)=red (E' b) := Derivation.liftOfSurjective_apply red_surjective hk b
  have hiter (b : B) (n : ℕ) : (D : Degeneration.G → Degeneration.G)^[n] (red b)=red ((E' : B → B)^[n] b) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih,hspec,Function.iterate_succ_apply']
  refine ⟨D,?_,?_,?_⟩
  · intro b
    obtain ⟨b,rfl⟩ := red_surjective b
    obtain ⟨n,hn⟩ := hE' b
    exact ⟨n,by rw [hiter,hn,map_zero]⟩
  · intro hz
    apply hr
    apply (red_zero_iff (E' r)).mp
    rw [← hspec,hz,Derivation.zero_apply]
  · rw [hspec,hEs',map_zero]
end ComplexCancellation.Rees

end

end OAI
