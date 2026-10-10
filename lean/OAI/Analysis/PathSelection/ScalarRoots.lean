import Mathlib
import OAI.Analysis.PathSelection.AnalyticFactors

namespace OAI

/-! Scalar roots, reflection and real algebraic roots. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Metric Filter Topology Complex Polynomial
open scoped BigOperators
namespace DegeneratingTrees.ScalarEvaluation
variable {K α : Type*} [Field K] [Algebra ℂ K] {l : Filter α}
variable (e : ScalarEvaluation K α l)

lemma monic_irreducible_has_root [NeBot l]
    (hlim : e.HasScalarLimits) (hdiv : e.HasDivisibleSizes) (hhol : e.HolomorphicallyClosed)
    (P : K[X]) (hP : P.Monic) (hI : Irreducible P) : ∃ x : K, P.eval x = 0 := by
  classical
  have hd : 0 < P.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hI)
  have hdK : (P.natDegree : K) ≠ 0 := by
    intro hz
    have he : algebraMap ℂ K (P.natDegree : ℂ) = algebraMap ℂ K 0 := by simpa using hz
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd) ((algebraMap ℂ K).injective he)
  let r : K := -P.coeff (P.natDegree-1) / (P.natDegree : K)
  let Q : K[X] := taylor r P
  have hQm : Q.Monic := by simpa [Q,Monic] using hP
  have hQd : Q.natDegree = P.natDegree := natDegree_taylor P r
  have hQpos : 0 < Q.natDegree := by omega
  have hQI : Irreducible Q := by
    have hi := hI.map (taylorEquiv r)
    change Irreducible (taylor r P) at hi
    exact hi
  have hQdep : Q.coeff (Q.natDegree-1) = 0 := by
    rw [hQd]
    change (taylor r P).coeff (P.natDegree-1) = 0
    rw [taylor_coeff_penultimate hP hd]
    dsimp [r]
    field_simp
    ring
  by_cases hcoeff : ∀ i : Fin Q.natDegree, Q.coeff i = 0
  · have hQpure : Q = X^Q.natDegree := by
      calc
        Q = monicFamily (fun i : Fin Q.natDegree => Q.coeff i) := eq_monicFamily hQm
        _ = X^Q.natDegree := by
          simp only [monicFamily]
          have hs : (∑ i : Fin Q.natDegree, monomial i (Q.coeff i)) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            simp [hcoeff i]
          rw [hs,add_zero]
    refine ⟨r,?_⟩
    have hv : Q.eval 0 = 0 := by rw [hQpure,eval_X_pow,zero_pow (Nat.ne_of_gt hQpos)]
    simpa [Q,taylor_apply,eval_comp] using hv
  · push Not at hcoeff
    obtain ⟨ρ,hρ,c,hc,i,hci⟩ := e.normalize_finite_coefficients hlim hdiv
      (fun i : Fin Q.natDegree => Q.coeff i) (fun i => Q.natDegree-i.val)
      (fun i => by omega) hcoeff
    let R : K[X] := monicFamily (fun i : Fin Q.natDegree => Q.coeff i / ρ^(Q.natDegree-i.val))
    have hRm : R.Monic := monicFamily_monic _
    have hRd : R.natDegree = Q.natDegree := monicFamily_natDegree _
    have hRI : Irreducible R := rescale_monic_irreducible hQm hQI ρ hρ
    let L : ℂ[X] := monicFamily c
    have hLm : L.Monic := monicFamily_monic c
    have hLd : L.natDegree = Q.natDegree := monicFamily_natDegree c
    have hLdep : L.coeff (L.natDegree-1) = 0 := by
      rw [hLd]
      let j : Fin Q.natDegree := ⟨Q.natDegree-1,by omega⟩
      have he : Q.coeff j = 0 := hQdep
      have ht := hc j
      rw [he,zero_div] at ht
      have hz : c j = 0 := tendsto_nhds_unique ht (tendsto_const_nhds.congr' e.zero.symm)
      simpa [L,monicFamily_coeff,j,show Q.natDegree-1 < Q.natDegree by omega] using hz
    have hLnot : L ≠ X^L.natDegree := by
      intro he
      have hv := congrArg (fun p : ℂ[X] => p.coeff i.val) he
      simp only [hLd,coeff_X_pow,ite_eq_right (ne_of_lt i.isLt)] at hv
      have hco : L.coeff i = c i := by simp [L,monicFamily_coeff,i.isLt]
      rw [hco] at hv
      exact hci hv
    obtain ⟨a,ha,hsmall⟩ := proper_root_cluster hLm (by omega) hLdep hLnot
    have hf := e.factor_of_finite_coeff_limits hhol hRm
    rw [hRd] at hf
    have hcR : ∀ i : Fin Q.natDegree, Tendsto (e.value (R.coeff i)) l (𝓝 (c i)) := by
      intro i
      simpa [R,monicFamily_coeff,i.isLt] using hc i
    obtain ⟨V,hVm,hVd,hVP⟩ := hf c hcR a
    exact (irreducible_no_proper_monic_factor hRI hVm hVP
      (by simpa [hVd,L] using ha) (by simpa [hVd,hRd,hLd,L] using hsmall)).elim

 

theorem isAlgClosed [NeBot l] (hlim : e.HasScalarLimits)
    (hdiv : e.HasDivisibleSizes) (hhol : e.HolomorphicallyClosed) : IsAlgClosed K :=
  IsAlgClosed.of_exists_root K (e.monic_irreducible_has_root hlim hdiv hhol)

end DegeneratingTrees.ScalarEvaluation

 

 

 

open Set Filter Topology Complex
open scoped ComplexConjugate
namespace DegeneratingTrees.ScalarEvaluation
variable {K α : Type*} [Field K] [Algebra ℂ K] {l : Filter α}
variable (e : ScalarEvaluation K α l)

def Reflected : Prop := ∀ a : K, ∃ b : K,
  e.value b =ᶠ[l] fun x => conj (e.value a x)

lemma eq_of_eventuallyEq [NeBot l] {a b : K} (h : e.value a =ᶠ[l] e.value b) : a = b :=
  e.toGermHom.injective (Germ.coe_eq.mpr h)

def reflectedValue (h : e.Reflected) (a : K) : K := (h a).choose
lemma reflectedValue_spec (h : e.Reflected) (a : K) :
    e.value (e.reflectedValue h a) =ᶠ[l] fun x => conj (e.value a x) :=
  (h a).choose_spec

lemma reflectedValue_involutive [NeBot l] (h : e.Reflected) :
    Function.Involutive (e.reflectedValue h) := by
  intro a
  apply e.eq_of_eventuallyEq
  filter_upwards [e.reflectedValue_spec h (e.reflectedValue h a), e.reflectedValue_spec h a] with x hx hy
  simp [hx,hy]

def conjugation [NeBot l] (h : e.Reflected) : K ≃+* K where
  toFun := e.reflectedValue h
  invFun := e.reflectedValue h
  left_inv := e.reflectedValue_involutive h
  right_inv := e.reflectedValue_involutive h
  map_add' a b := by
    apply e.eq_of_eventuallyEq
    filter_upwards [e.reflectedValue_spec h (a+b), e.add a b,
      e.add (e.reflectedValue h a) (e.reflectedValue h b),
      e.reflectedValue_spec h a, e.reflectedValue_spec h b] with x h₁ h₂ h₃ h₄ h₅
    simp [h₁,h₂,h₃,h₄,h₅]
  map_mul' a b := by
    apply e.eq_of_eventuallyEq
    filter_upwards [e.reflectedValue_spec h (a*b), e.mul a b,
      e.mul (e.reflectedValue h a) (e.reflectedValue h b),
      e.reflectedValue_spec h a, e.reflectedValue_spec h b] with x h₁ h₂ h₃ h₄ h₅
    simp [h₁,h₂,h₃,h₄,h₅]

lemma conjugation_spec [NeBot l] (h : e.Reflected) (a : K) :
    e.value (e.conjugation h a) =ᶠ[l] fun x => conj (e.value a x) :=
  e.reflectedValue_spec h a

lemma conjugation_const [NeBot l] (h : e.Reflected) (z : ℂ) :
    e.conjugation h (algebraMap ℂ K z) = algebraMap ℂ K (conj z) := by
  apply e.eq_of_eventuallyEq
  filter_upwards [e.conjugation_spec h (algebraMap ℂ K z), e.const z, e.const (conj z)] with x hx hy hz
  simp [hx,hy,hz]

lemma conjugation_involutive [NeBot l] (h : e.Reflected) :
    Function.Involutive (e.conjugation h) := e.reflectedValue_involutive h

def realPart [NeBot l] (h : e.Reflected) : Subfield K :=
  (e.conjugation h).toRingHom.eqLocusField (RingHom.id K)

lemma mem_realPart [NeBot l] (h : e.Reflected) {a : K} :
    a ∈ e.realPart h ↔ ∀ᶠ x in l, (e.value a x).im = 0 := by
  change e.conjugation h a = a ↔ _
  constructor
  · intro ha
    filter_upwards [e.conjugation_spec h a] with x hx
    rw [ha] at hx
    exact conj_eq_iff_im.mp hx.symm
  · intro ha
    apply e.eq_of_eventuallyEq
    filter_upwards [ha, e.conjugation_spec h a] with x hx hy
    rw [hy,conj_eq_iff_im.mpr hx]

lemma sumSq_eval_nonneg [NeBot l] (h : e.Reflected) {a : e.realPart h} (ha : IsSumSq a) :
    ∀ᶠ x in l, 0 ≤ (e.value (a : K) x).re := by
  induction ha with
  | zero =>
    filter_upwards [e.zero] with x hx
    simp [hx]
  | @sq_add a s hs ih =>
    filter_upwards [ih, (e.mem_realPart h).mp a.property, e.mul (a:K) (a:K),
      e.add ((a:K)*(a:K)) (s:K)] with x hi hr hm ha
    change 0 ≤ (e.value ((a:K)*(a:K)+(s:K)) x).re
    rw [ha,Complex.add_re,hm,Complex.mul_re,hr]
    nlinarith [sq_nonneg (e.value (a:K) x).re]

lemma realPart_semireal [NeBot l] (h : e.Reflected) : IsSemireal (e.realPart h) := by
  apply IsSemireal.of_not_isSumSq_neg_one
  intro hs
  have ht := e.sumSq_eval_nonneg h hs
  obtain ⟨x,hx,hneg,h1⟩ := (ht.and ((e.neg 1).and e.one)).exists
  simp [hneg,h1] at hx
  linarith

end DegeneratingTrees.ScalarEvaluation

 

 

 

open Polynomial
namespace DegeneratingTrees

lemma odd_multiset_involution_fixed {A : Type*} (σ : A → A) (hinv : Function.Involutive σ)
    (s : Multiset A) (hs : s.map σ = s) (ho : Odd s.card) :
    ∃ a ∈ s, σ a = a := by
  classical
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    obtain ⟨a,ha⟩ := Multiset.card_pos_iff_exists_mem.mp ho.pos
    by_cases hf : σ a = a
    · exact ⟨a,ha,hf⟩
    have hb : σ a ∈ s := hs ▸ Multiset.mem_map_of_mem σ ha
    have hb' : σ a ∈ s.erase a := (Multiset.mem_erase_of_ne hf).mpr hb
    let t := (s.erase a).erase (σ a)
    have hlt : t < s := lt_trans (Multiset.erase_lt.mpr hb') (Multiset.erase_lt.mpr ha)
    have ht : t.map σ = t := by
      dsimp [t]
      rw [Multiset.map_erase σ hinv.injective, Multiset.map_erase σ hinv.injective,
        hs,hinv a,Multiset.erase_comm]
    have hot : Odd t.card := by
      dsimp [t]
      rw [Multiset.card_erase_of_mem hb',Multiset.card_erase_of_mem ha]
      obtain ⟨k,hk⟩ := ho
      refine ⟨k-1,?_⟩
      have hc : 0 < (s.erase a).card := Multiset.card_pos_iff_exists_mem.mpr ⟨σ a,hb'⟩
      rw [Multiset.card_erase_of_mem ha] at hc
      simp only [Nat.pred_eq_sub_one] at hc ⊢
      omega
    obtain ⟨b,hbt,hbf⟩ := ih t hlt ht hot
    exact ⟨b,Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hbt),hbf⟩

lemma fixed_subfield_odd_root {K : Type*} [Field K] [IsAlgClosed K]
    (σ : K ≃+* K) (hinv : Function.Involutive σ)
    (P : (σ.toRingHom.eqLocusField (RingHom.id K))[X]) (ho : Odd P.natDegree) :
    ∃ a : σ.toRingHom.eqLocusField (RingHom.id K), P.IsRoot a := by
  let R := σ.toRingHom.eqLocusField (RingHom.id K)
  let Q : K[X] := P.map R.subtype
  have hσQ : Q.map σ.toRingHom = Q := by
    ext i
    simp only [Polynomial.coeff_map,Q]
    exact (P.coeff i).property
  have hd : Q.natDegree = P.natDegree := natDegree_map_eq_of_injective R.subtype.injective P
  have hcard : Q.roots.card = Q.natDegree := (IsAlgClosed.splits Q).natDegree_eq_card_roots.symm
  have hm : Q.roots.map σ = Q.roots := by
    change Q.roots.map σ.toRingHom = Q.roots
    rw [roots_map_of_injective_of_card_eq_natDegree (f := σ.toRingHom) σ.injective hcard,hσQ]
  obtain ⟨a,ha,hfix⟩ := odd_multiset_involution_fixed σ hinv Q.roots hm (by simpa [hcard,hd] using ho)
  refine ⟨⟨a,hfix⟩,?_⟩
  have hQne : Q ≠ 0 := by
    intro hz
    have : P.natDegree = 0 := by simpa [hz] using hd.symm
    have hpos := ho.pos
    omega
  have hr := (mem_roots hQne).mp ha
  change P.eval ⟨a,hfix⟩ = 0
  apply R.subtype.injective
  rw [map_zero,←eval₂_at_apply]
  simpa [Polynomial.IsRoot,Q,Polynomial.eval_map] using hr

end DegeneratingTrees

 

 

 

open Set Filter Topology Complex Polynomial
open scoped ComplexConjugate
namespace DegeneratingTrees.ScalarEvaluation
variable {K α : Type*} [Field K] [Algebra ℂ K] {l : Filter α}
variable (e : ScalarEvaluation K α l)

lemma realPart_square_or_neg [NeBot l] [IsAlgClosed K] (h : e.Reflected)
    (a : e.realPart h) : IsSquare a ∨ IsSquare (-a) := by
  obtain ⟨r,hr⟩ := IsAlgClosed.exists_pow_nat_eq (a : K) zero_lt_two
  have he : (e.conjugation h r)^2 = r^2 := by
    rw [← map_pow,hr]
    exact a.property
  rcases eq_or_eq_neg_of_sq_eq_sq (e.conjugation h r) r he with hp | hn
  · left
    refine ⟨⟨r,hp⟩,?_⟩
    apply Subtype.ext
    change (a:K) = r*r
    simpa [pow_two] using hr.symm
  · right
    have hI : (algebraMap ℂ K I)^2 = -1 := by
      rw [←map_pow,Complex.I_sq,map_neg,map_one]
    have hfix : e.conjugation h (r * algebraMap ℂ K I) = r * algebraMap ℂ K I := by
      rw [map_mul,hn,e.conjugation_const,Complex.conj_I,map_neg,neg_mul_neg]
    refine ⟨⟨r*algebraMap ℂ K I,hfix⟩,?_⟩
    apply Subtype.ext
    change -(a:K) = (r*algebraMap ℂ K I) * (r*algebraMap ℂ K I)
    rw [←pow_two,mul_pow,hr,hI,mul_neg_one]

 

theorem realPart_isRealClosed [NeBot l] (hlim : e.HasScalarLimits)
    (hdiv : e.HasDivisibleSizes) (hhol : e.HolomorphicallyClosed) (href : e.Reflected) :
    IsRealClosed (e.realPart href) := by
  let : IsAlgClosed K := e.isAlgClosed hlim hdiv hhol
  exact {
    toIsSemireal := e.realPart_semireal href
    isSquare_or_isSquare_neg := e.realPart_square_or_neg href
    exists_isRoot_of_odd_natDegree := fun hp =>
      fixed_subfield_odd_root (e.conjugation href) (e.conjugation_involutive href) _ hp
  }
end DegeneratingTrees.ScalarEvaluation
end

end OAI
