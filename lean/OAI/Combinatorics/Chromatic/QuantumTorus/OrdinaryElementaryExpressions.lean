import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.HomogeneousElementaryExpressions

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section

variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]

def ElementaryExpr.ordinary : {N:ℕ} → ElementaryExpr N → MvPolynomial σ R
  | _,.zero _ => 0
  | _,.one => 1
  | _,.atom k => MvPolynomial.esymm σ R k
  | _,.add f g => ordinary f+ordinary g
  | _,.neg f => -ordinary f
  | _,.mul f g => ordinary f*ordinary g

lemma elementary_isHomogeneous (k:ℕ) : (MvPolynomial.esymm σ R k).IsHomogeneous k := by
  unfold MvPolynomial.esymm
  apply MvPolynomial.IsHomogeneous.sum
  intro s hs
  have hc:s.card=k:=(Finset.mem_powersetCard_univ.mp hs)
  simpa [hc] using MvPolynomial.IsHomogeneous.prod s (fun a:σ=>MvPolynomial.X (R:=R) a)
    (fun _=>1) (fun a _=>MvPolynomial.isHomogeneous_X R a)

lemma ElementaryExpr.ordinary_homogeneous {N:ℕ} (f:ElementaryExpr N) :
    (f.ordinary (σ:=σ) (R:=R)).IsHomogeneous N := by
  induction f with
  | zero N => exact MvPolynomial.isHomogeneous_zero σ R N
  | one => exact MvPolynomial.isHomogeneous_one σ R
  | atom k => exact elementary_isHomogeneous k
  | add f g hf hg=>exact hf.add hg
  | neg f hf=>exact hf.neg
  | mul f g hf hg=>exact hf.mul hg

lemma ElementaryExpr.ordinary_cast {N K:ℕ} (h:N=K) (f:ElementaryExpr N) :
    (h ▸ f).ordinary (σ:=σ) (R:=R)=f.ordinary := by subst K; rfl

def ElementaryExpr.natural : ℕ → ElementaryExpr 0
  | 0=>.zero 0
  | k+1=>.add (natural k) .one

def ElementaryExpr.integer : ℤ → ElementaryExpr 0
  | .ofNat k => natural k
  | .negSucc k => .neg (natural (k+1))

lemma ElementaryExpr.ordinary_natural (k:ℕ) :
    (ElementaryExpr.natural k).ordinary (σ:=σ) (R:=R)=MvPolynomial.C (k:R) := by
  induction k with
  | zero=>simp [natural,ordinary]
  | succ k ih=>simp [natural,ordinary,ih,Nat.cast_add,Nat.cast_one]

lemma ElementaryExpr.ordinary_integer (z:ℤ) :
    (ElementaryExpr.integer z).ordinary (σ:=σ) (R:=R)=MvPolynomial.C (z:R) := by
  cases z with
  | ofNat k=>simpa [integer] using ordinary_natural (σ:=σ) (R:=R) k
  | negSucc k=>simp [integer,ordinary,ordinary_natural,Int.cast_negSucc]

lemma ElementaryExpr.exists_power {k:ℕ} (f:ElementaryExpr k) (e:ℕ) :
    ∃g:ElementaryExpr (k*e),g.ordinary (σ:=σ) (R:=R)=f.ordinary^e := by
  induction e with
  | zero=>exact ⟨.one,rfl⟩
  | succ e ih=>
    obtain ⟨g,hg⟩:=ih
    rw [Nat.mul_succ]
    refine ⟨.mul g f,?_⟩
    change g.ordinary*f.ordinary=f.ordinary^(e+1)
    rw [hg,pow_succ]

lemma ElementaryExpr.exists_product {ι:Type*} (s:Finset ι) (k:ι → ℕ)
    (f:∀a,ElementaryExpr (k a)) :
    ∃g:ElementaryExpr (∑a∈s,k a),g.ordinary (σ:=σ) (R:=R)=∏a∈s,(f a).ordinary := by
  induction s using Finset.induction with
  | empty=>exact ⟨.one,rfl⟩
  | @insert a s ha ih=>
    obtain ⟨g,hg⟩:=ih
    rw [Finset.sum_insert ha,Finset.prod_insert ha]
    refine ⟨.mul (f a) g,?_⟩
    change (f a).ordinary*g.ordinary=_
    rw [hg]

lemma homogeneousExpression_representation {N:ℕ} (p:MvPolynomial σ ℤ)
    (hp:p.IsSymmetric) (hN:p.IsHomogeneous N) :
    ∃f:ElementaryExpr N,f.ordinary=p := by
  let m:=Fintype.card σ
  obtain ⟨q,hq⟩:=MvPolynomial.esymmAlgHom_surjective (σ:=σ) ℤ (n:=m) le_rfl ⟨p,hp⟩
  let E:=MvPolynomial.esymmAlgHom σ ℤ m
  have he:∀d:Fin m →₀ ℕ,∀z:ℤ,∃K,∃f:ElementaryExpr K,
      f.ordinary=(E (MvPolynomial.monomial d z):MvPolynomial σ ℤ):=by
    intro d z
    choose g hg using fun a:Fin m=>ElementaryExpr.exists_power (σ:=σ) (R:=ℤ) (.atom (a.val+1)) (d a)
    obtain ⟨f,hf⟩:=ElementaryExpr.exists_product (σ:=σ) (R:=ℤ) Finset.univ
      (fun a:Fin m=>(a.val+1)*d a) g
    refine ⟨_,.mul (.integer z) f,?_⟩
    change ((ElementaryExpr.integer z).ordinary)*f.ordinary=_
    rw [ElementaryExpr.ordinary_integer,hf]
    simp only [hg,ElementaryExpr.ordinary]
    simp [E,MvPolynomial.esymmAlgHom,MvPolynomial.aeval_monomial,Finsupp.prod_fintype]
  have hterm:∀d:Fin m →₀ ℕ,∃f:ElementaryExpr N,f.ordinary=
      MvPolynomial.homogeneousComponent N (E (MvPolynomial.monomial d (q.coeff d)):MvPolynomial σ ℤ):=by
    intro d
    obtain ⟨K,f,hf⟩:=he d (q.coeff d)
    rw [←hf,MvPolynomial.homogeneousComponent_of_mem f.ordinary_homogeneous]
    by_cases h:N=K
    · refine ⟨h.symm ▸ f,?_⟩
      simp only [h,ite_true,ElementaryExpr.ordinary_cast]
    · exact ⟨.zero N,by simp [h,ElementaryExpr.ordinary]⟩
  have hs:∀s:Finset (Fin m →₀ ℕ),∃f:ElementaryExpr N,f.ordinary=
      ∑d∈s,MvPolynomial.homogeneousComponent N (E (MvPolynomial.monomial d (q.coeff d)):MvPolynomial σ ℤ):=by
    intro s
    induction s using Finset.induction with
    | empty=>exact ⟨.zero N,by simp [ElementaryExpr.ordinary]⟩
    | @insert d s hd ih=>
      obtain ⟨f,hf⟩:=hterm d
      obtain ⟨g,hg⟩:=ih
      exact ⟨.add f g,by simp [ElementaryExpr.ordinary,hf,hg,Finset.sum_insert hd]⟩
  obtain ⟨f,hf⟩:=hs q.support
  refine ⟨f,?_⟩
  rw [←map_sum] at hf
  have H:(∑d∈q.support,(E (MvPolynomial.monomial d (q.coeff d)):MvPolynomial σ ℤ))=p:=by
    let E' : MvPolynomial (Fin m) ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
      (MvPolynomial.symmetricSubalgebra σ ℤ).val.comp E
    change (∑d∈q.support,E' (MvPolynomial.monomial d (q.coeff d)))=p
    rw [←map_sum,←MvPolynomial.as_sum]
    exact congrArg Subtype.val hq
  rw [H,MvPolynomial.homogeneousComponent_eq_self hN] at hf
  exact hf
end
end ElementaryPositivity.QuantumTorus

end

end OAI
