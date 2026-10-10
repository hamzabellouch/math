import OAI.Geometry.QuadricBundles.BinaryForms

namespace OAI

noncomputable section

namespace QuadricCounterexample.LaurentCech
open Finset
open scoped Classical
noncomputable section
abbrev Chart := Fin 2 × Fin 2
abbrev Exponent := ℤ × ℤ
abbrev LaurentCoefficients := Exponent →₀ ℂ

def ScalarAllows (d : ℕ) (i : Fin 2) (e : ℤ) : Prop :=
  if i=0 then e≤d else 0≤e

def ChartAllows (d : ℕ × ℕ) (i : Chart) (e : Exponent) : Prop :=
  ScalarAllows d.1 i.1 e.1 ∧ ScalarAllows d.2 i.2 e.2

def OverlapAllows (d : ℕ × ℕ) (i j : Chart) (e : Exponent) : Prop :=
  (i.1=j.1 → ScalarAllows d.1 i.1 e.1) ∧
  (i.2=j.2 → ScalarAllows d.2 i.2 e.2)

lemma scalar_bad_unique (d : ℕ) {i j : Fin 2} {e : ℤ}
    (hi : ¬ScalarAllows d i e) (hj : ¬ScalarAllows d j e) : i=j := by
  fin_cases i <;> fin_cases j <;> simp_all [ScalarAllows] <;> omega

lemma forbidden_coefficient_zero (d : ℕ × ℕ) (p : Chart → Chart → LaurentCoefficients)
    (hc : ∀ i j k, p i j+p j k=p i k)
    (hs : ∀ i j e, ¬OverlapAllows d i j e → p i j e=0)
    (i j : Chart) (e : Exponent) (hi : ¬ChartAllows d i e) (hj : ¬ChartAllows d j e) :
    p i j e=0 := by
  rcases not_and_or.mp hi with hi | hi <;> rcases not_and_or.mp hj with hj | hj
  · have he := scalar_bad_unique d.1 hi hj
    exact hs i j e (fun h ↦ hi (h.1 he))
  · let k : Chart := (i.1,j.2)
    have h1 : p i k e=0 := hs i k e (fun h ↦ hi (h.1 rfl))
    have h2 : p k j e=0 := hs k j e (fun h ↦ hj (h.2 rfl))
    have he := congrArg (fun a : LaurentCoefficients ↦ a e) (hc i k j)
    simpa only [Finsupp.add_apply,h1,h2,zero_add] using he.symm
  · let k : Chart := (j.1,i.2)
    have h1 : p i k e=0 := hs i k e (fun h ↦ hi (h.2 rfl))
    have h2 : p k j e=0 := hs k j e (fun h ↦ hj (h.1 rfl))
    have he := congrArg (fun a : LaurentCoefficients ↦ a e) (hc i k j)
    simpa only [Finsupp.add_apply,h1,h2,zero_add] using he.symm
  · have he := scalar_bad_unique d.2 hi hj
    exact hs i j e (fun h ↦ hi (h.2 he))

def badChart (d : ℕ × ℕ) (e : Exponent) : Chart :=
  if h : ∃ i, ¬ChartAllows d i e then h.choose else (0,0)

lemma badChart_bad (d : ℕ × ℕ) (e : Exponent) (h : ∃ i, ¬ChartAllows d i e) :
    ¬ChartAllows d (badChart d e) e := by
  simpa only [badChart,dite_eq_left h] using h.choose_spec

def correction (d : ℕ × ℕ) (q : Chart → LaurentCoefficients) : LaurentCoefficients :=
  ∑ i : Chart, (q i).filter (fun e ↦ badChart d e=i)

lemma correction_apply (d : ℕ × ℕ) (q : Chart → LaurentCoefficients) (e : Exponent) :
    correction d q e=q (badChart d e) e := by
  simp only [correction,Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.filter_apply]
  rw [Finset.sum_eq_single (badChart d e)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem split_cocycle (d : ℕ × ℕ) (p : Chart → Chart → LaurentCoefficients)
    (hc : ∀ i j k, p i j+p j k=p i k)
    (hs : ∀ i j e, ¬OverlapAllows d i j e → p i j e=0) :
    ∃ q : Chart → LaurentCoefficients,
      (∀ i e, ¬ChartAllows d i e → q i e=0) ∧
      ∀ i j, p i j=q j-q i := by
  let q₀ : Chart → LaurentCoefficients := fun i ↦ p (0,0) i
  let c := correction d q₀
  refine ⟨fun i ↦ q₀ i-c,?_,?_⟩
  · intro i e hi
    have hb := badChart_bad d e ⟨i,hi⟩
    have hij := forbidden_coefficient_zero d p hc hs (badChart d e) i e hb hi
    have he := congrArg (fun a : LaurentCoefficients ↦ a e) (hc (0,0) (badChart d e) i)
    simp only [Finsupp.add_apply,hij,add_zero] at he
    simp only [Finsupp.sub_apply,c,correction_apply,q₀]
    exact sub_eq_zero.mpr he.symm
  · intro i j
    have h := hc (0,0) i j
    dsimp only [q₀]
    rw [← h]
    abel

end
end QuadricCounterexample.LaurentCech

namespace QuadricCounterexample.LaurentCech
open Set MvPolynomial Finsupp
open scoped BigOperators
noncomputable section

def eval (p : LaurentCoefficients) (z : BaseCoordinates) : ℂ :=
  p.sum fun e c ↦ c * z.1^e.1 * z.2^e.2
lemma eval_add (p q : LaurentCoefficients) (z : BaseCoordinates) :
    eval (p+q) z=eval p z+eval q z := by
  apply Finsupp.sum_add_index <;> intros <;> ring
lemma eval_zero (z : BaseCoordinates) : eval 0 z=0 := by simp [eval]
lemma eval_sub (p q : LaurentCoefficients) (z : BaseCoordinates) :
    eval (p-q) z=eval p z-eval q z := by
  have h := eval_add (p-q) q z
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm
lemma eval_single (e : Exponent) (c : ℂ) (z : BaseCoordinates) :
    eval (Finsupp.single e c) z=c*z.1^e.1*z.2^e.2 := by simp [eval]

def exponent (d : Fin 2 →₀ ℕ) : Exponent := (d 0,d 1)
def ofPolynomial (p : BasePolynomial) : LaurentCoefficients :=
  Finsupp.mapDomain exponent (AddMonoidAlgebra.coeff p)
lemma ofPolynomial_add (p q : BasePolynomial) : ofPolynomial (p+q)=ofPolynomial p+ofPolynomial q :=
  by simp [ofPolynomial,AddMonoidAlgebra.coeff_add,Finsupp.mapDomain_add]
lemma ofPolynomial_monomial (d : Fin 2 →₀ ℕ) (c : ℂ) :
    ofPolynomial (MvPolynomial.monomial d c)=Finsupp.single (exponent d) c :=
  by simp [ofPolynomial, MvPolynomial.monomial,AddMonoidAlgebra.lsingle_apply]
lemma eval_ofPolynomial (p : BasePolynomial) (z : BaseCoordinates) :
    eval (ofPolynomial p) z=baseEval p z := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [ofPolynomial_add,eval_add,baseEval_add,hp,hq]
  | monomial d c =>
    rw [ofPolynomial_monomial,eval_single]
    simp only [baseEval,MvPolynomial.eval_monomial,exponent,zpow_natCast]
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_two]; ring
    · intro i; simp

lemma exponent_injective : Function.Injective exponent := by
  intro a b h
  have h0 : a 0=b 0 := by exact_mod_cast (show (a 0 : ℤ)=(b 0 : ℤ) from congrArg Prod.fst h)
  have h1 : a 1=b 1 := by exact_mod_cast (show (a 1 : ℤ)=(b 1 : ℤ) from congrArg Prod.snd h)
  ext i; fin_cases i <;> assumption
lemma ofPolynomial_injective : Function.Injective ofPolynomial := by
  intro p q h
  have he : AddMonoidAlgebra.coeff p=AddMonoidAlgebra.coeff q := Finsupp.mapDomain_injective exponent_injective h
  exact AddMonoidAlgebra.coeff_injective he

def shift (e : Exponent) (p : LaurentCoefficients) : LaurentCoefficients :=
  Finsupp.mapDomain (fun a ↦ e+a) p
lemma shift_injective (e : Exponent) : Function.Injective (shift e) :=
  Finsupp.mapDomain_injective (fun _ _ h ↦ add_left_cancel h)
lemma eval_shift (e : Exponent) (p : LaurentCoefficients) {z : BaseCoordinates}
    (hz : z.1≠0 ∧ z.2≠0) :
    eval (shift e p) z=z.1^e.1*z.2^e.2*eval p z := by
  unfold eval shift
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by ring)]
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro a c
  simp only [Prod.fst_add,Prod.snd_add,zpow_add₀ hz.1,zpow_add₀ hz.2]
  ring

lemma exists_shift_nonneg (p : LaurentCoefficients) :
    ∃ e : Exponent, ∀ a∈(shift e p).support, 0≤a.1 ∧ 0≤a.2 := by
  have h (a : Exponent) : ∃ n : ℕ, -a.1≤n ∧ -a.2≤n := by
    obtain ⟨n,hn⟩ := exists_nat_ge (max (-a.1) (-a.2))
    exact ⟨n,le_trans (le_max_left _ _) hn,le_trans (le_max_right _ _) hn⟩
  choose n hn using h
  let N : ℕ := ∑ a∈p.support, n a
  refine ⟨(N,N),?_⟩
  intro a ha
  have hs : a∈Finset.image (fun a : Exponent ↦ ((N : ℤ),(N : ℤ))+a) p.support :=
    Finsupp.mapDomain_support ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
  have hn' : (n b : ℤ)≤N := by exact_mod_cast Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hb
  simp only [Prod.fst_add,Prod.snd_add]
  constructor <;> linarith [(hn b).1,(hn b).2]

def naturalExponent (a : Exponent) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a.1.toNat,a.2.toNat]
def toPolynomial (p : LaurentCoefficients) : BasePolynomial :=
  p.sum fun a c ↦ MvPolynomial.monomial (naturalExponent a) c
lemma ofPolynomial_toPolynomial (p : LaurentCoefficients)
    (hp : ∀ a∈p.support, 0≤a.1 ∧ 0≤a.2) :
    ofPolynomial (toPolynomial p)=p := by
  have hm : ofPolynomial (toPolynomial p)=p.sum (fun a c ↦ Finsupp.single (exponent (naturalExponent a)) c) := by
    unfold toPolynomial
    unfold Finsupp.sum
    induction p.support using Finset.induction_on with
    | empty => simp [ofPolynomial]
    | @insert a t hat ih => simp only [Finset.sum_insert hat,ofPolynomial_add,ofPolynomial_monomial,ih]
  rw [hm]
  conv_rhs => rw [← Finsupp.sum_single p]
  apply Finsupp.sum_congr
  intro a ha
  congr 1
  ext <;> simp [exponent,naturalExponent,Int.toNat_of_nonneg (hp a ha).1,
    Int.toNat_of_nonneg (hp a ha).2]

end
end QuadricCounterexample.LaurentCech

namespace QuadricCounterexample.LaurentCech
open Set
noncomputable section
lemma baseEval_on_torus_injective {p q : BasePolynomial}
    (he : ∀ z : BaseCoordinates, z.1≠0 ∧ z.2≠0 → baseEval p z=baseEval q z) : p=q := by
  have hd : Dense ({(0 : ℂ)}ᶜ ×ˢ {(0 : ℂ)}ᶜ) :=
    (dense_compl_singleton (0 : ℂ)).prod (dense_compl_singleton (0 : ℂ))
  have hc (r : BasePolynomial) : Continuous (baseEval r) :=
    continuousOn_univ.mp (analytic_baseEval r).continuousOn
  have hfun : baseEval p=baseEval q := Continuous.ext_on hd (hc p) (hc q) (fun z hz ↦ he z hz)
  apply MvPolynomial.funext
  intro x
  have hx : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  exact congrFun hfun (x 0,x 1)

lemma eval_injective_on_torus {p q : LaurentCoefficients}
    (he : ∀ z : BaseCoordinates, z.1≠0 ∧ z.2≠0 → eval p z=eval q z) : p=q := by
  obtain ⟨e,hs⟩ := exists_shift_nonneg (p-q)
  let r := toPolynomial (shift e (p-q))
  have hr : ofPolynomial r=shift e (p-q) := ofPolynomial_toPolynomial _ hs
  have hr0 : r=0 := by
    apply baseEval_on_torus_injective
    intro z hz
    rw [← eval_ofPolynomial,hr,eval_shift e (p-q) hz,eval_sub]
    rw [he z hz]
    simp
  apply sub_eq_zero.mp
  apply shift_injective e
  rw [← hr,hr0]
  simp [ofPolynomial,shift]
end
end QuadricCounterexample.LaurentCech

namespace QuadricCounterexample.LaurentCech
open Set Finsupp
open scoped BigOperators
noncomputable section

def transformExponent (d : ℕ × ℕ) (i : Chart) (a : Exponent) : Exponent :=
  (if i.1=0 then (d.1 : ℤ)-a.1 else a.1,
   if i.2=0 then (d.2 : ℤ)-a.2 else a.2)
lemma transformExponent_involutive (d : ℕ × ℕ) (i : Chart) :
    Function.Involutive (transformExponent d i) := by
  intro a
  ext <;> simp [transformExponent] <;> split_ifs <;> simp_all

def transform (d : ℕ × ℕ) (i : Chart) (p : LaurentCoefficients) : LaurentCoefficients :=
  Finsupp.mapDomain (transformExponent d i) p
lemma transform_involutive (d : ℕ × ℕ) (i : Chart) : Function.Involutive (transform d i) := by
  intro p
  unfold transform
  rw [← Finsupp.mapDomain_comp]
  have h : transformExponent d i ∘ transformExponent d i=id := funext (transformExponent_involutive d i)
  rw [h,Finsupp.mapDomain_id]

lemma exponent_nonneg (a : Fin 2 →₀ ℕ) : 0≤(exponent a).1 ∧ 0≤(exponent a).2 := by
  exact ⟨Nat.cast_nonneg _,Nat.cast_nonneg _⟩
lemma ofPolynomial_nonneg (p : BasePolynomial) {a : Exponent} (ha : a∈(ofPolynomial p).support) :
    0≤a.1 ∧ 0≤a.2 := by
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  exact exponent_nonneg b
lemma chartAllows_transform_iff (d : ℕ × ℕ) (i : Chart) (a : Exponent) :
    ChartAllows d i (transformExponent d i a) ↔ 0≤a.1 ∧ 0≤a.2 := by
  simp only [ChartAllows, ScalarAllows,transformExponent]
  split_ifs <;> constructor <;> intro h <;> constructor <;> omega
lemma transform_nonneg_iff (d : ℕ × ℕ) (i : Chart) (a : Exponent) :
    0≤(transformExponent d i a).1 ∧ 0≤(transformExponent d i a).2 ↔ ChartAllows d i a := by
  have h := (chartAllows_transform_iff d i (transformExponent d i a)).symm
  rw [transformExponent_involutive d i a] at h
  exact h
lemma transform_polynomial_support (d : ℕ × ℕ) (i : Chart) (p : BasePolynomial)
    {a : Exponent} (ha : a∈(transform d i (ofPolynomial p)).support) : ChartAllows d i a := by
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  exact (chartAllows_transform_iff d i b).mpr (ofPolynomial_nonneg p hb)
lemma exists_polynomial_of_chartAllows (d : ℕ × ℕ) (i : Chart) (p : LaurentCoefficients)
    (hp : ∀ a∈p.support, ChartAllows d i a) :
    ∃ q : BasePolynomial, transform d i (ofPolynomial q)=p := by
  have hnon : ∀ a∈(transform d i p).support, 0≤a.1 ∧ 0≤a.2 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
    exact (transform_nonneg_iff d i b).mpr (hp b hb)
  refine ⟨toPolynomial (transform d i p),?_⟩
  rw [ofPolynomial_toPolynomial _ hnon]
  exact transform_involutive d i p

def masterCoordinates (i : Chart) (z : BaseCoordinates) : BaseCoordinates :=
  (if i.1=0 then z.1⁻¹ else z.1, if i.2=0 then z.2⁻¹ else z.2)
def masterFrame (d : ℕ × ℕ) (i : Chart) (z : BaseCoordinates) : ℂ :=
  (if i.1=0 then z.1^d.1 else 1) * (if i.2=0 then z.2^d.2 else 1)
lemma masterCoordinates_nonzero (i : Chart) {z : BaseCoordinates} (hz : z.1≠0 ∧ z.2≠0) :
    (masterCoordinates i z).1≠0 ∧ (masterCoordinates i z).2≠0 := by
  dsimp [masterCoordinates]
  split_ifs <;> exact ⟨by simpa using hz.1,by simpa using hz.2⟩
lemma masterCoordinates_involutive (i : Chart) : Function.Involutive (masterCoordinates i) := by
  intro z
  ext <;> simp [masterCoordinates] <;> split_ifs <;> simp_all

lemma scalar_transform_eval (d : ℕ) (i : Fin 2) (a : ℤ) {z : ℂ} (hz : z≠0) :
    z^(if i=0 then (d : ℤ)-a else a)=
      (if i=0 then z^d else 1)*(if i=0 then z⁻¹ else z)^a := by
  by_cases hi : i=0
  · simp only [hi,ite_true,zpow_sub₀ hz,zpow_natCast, inv_zpow,div_eq_mul_inv]
  · simp [hi]
lemma eval_transform (d : ℕ × ℕ) (i : Chart) (p : LaurentCoefficients)
    {z : BaseCoordinates} (hz : z.1≠0 ∧ z.2≠0) :
    eval (transform d i p) z=masterFrame d i z*eval p (masterCoordinates i z) := by
  unfold eval transform
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by ring)]
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro a ha
  simp only [transformExponent,masterFrame,masterCoordinates,
    scalar_transform_eval _ _ _ hz.1,scalar_transform_eval _ _ _ hz.2]
  ring
lemma eval_transform_polynomial (d : ℕ × ℕ) (i : Chart) (p : BasePolynomial)
    {z : BaseCoordinates} (hz : z.1≠0 ∧ z.2≠0) :
    eval (transform d i (ofPolynomial p)) z=masterFrame d i z*baseEval p (masterCoordinates i z) := by
  rw [eval_transform d i _ hz,eval_ofPolynomial]
end
end QuadricCounterexample.LaurentCech

namespace QuadricCounterexample
open MvPolynomial Set
noncomputable section

lemma denominator_dvd_power (q r : BasePolynomial)
    (hq : ∀ z : BaseCoordinates, baseEval r z ≠ 0 → baseEval q z ≠ 0) :
    ∃ n : ℕ, q ∣ r^n := by
  let J : Ideal BasePolynomial := Ideal.span {q}
  have hv : r ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ J) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    have he : z=![z 0,z 1] := by ext k; fin_cases k <;> rfl
    have hqz : MvPolynomial.eval z q=0 := by
      rw [MvPolynomial.zeroLocus_span] at hz
      simpa only [aeval_eq_eval] using hz q (Set.mem_singleton q)
    by_contra hr
    apply hq (z 0,z 1)
    · simpa only [baseEval,← he,aeval_eq_eval] using hr
    · simpa only [baseEval,← he] using hqz
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hv
  obtain ⟨n,hn⟩ := hv
  exact ⟨n,Ideal.mem_span_singleton.mp hn⟩

lemma UniformlyRegularOn.exists_power_denominator (r : BasePolynomial)
    {f : BaseCoordinates → ℂ} (hf : UniformlyRegularOn {z | baseEval r z ≠ 0} f) :
    ∃ n : ℕ, ∃ p : BasePolynomial, ∀ z, baseEval r z ≠ 0 →
      f z=baseEval p z/(baseEval r z)^n := by
  obtain ⟨p,q,hq,hf⟩ := hf
  obtain ⟨n,t,ht⟩ := denominator_dvd_power q r hq
  refine ⟨n,p*t,?_⟩
  intro z hz
  have hqe := hq z hz
  have he := congrArg (fun a : BasePolynomial ↦ baseEval a z) ht
  change baseEval (r^n) z=baseEval (q*t) z at he
  have hpw : baseEval (r^n) z=(baseEval r z)^n := by simp [baseEval]
  rw [hpw,baseEval_mul] at he
  rw [hf z hz,baseEval_mul]
  field_simp
  linear_combination baseEval p z * he

lemma UniformlyRegularOn.exists_polynomial {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn Set.univ f) : ∃ p : BasePolynomial, f=baseEval p := by
  have hr : {z : BaseCoordinates | baseEval (1 : BasePolynomial) z ≠ 0}=Set.univ := by ext; simp
  obtain ⟨n,p,hp⟩ := UniformlyRegularOn.exists_power_denominator 1 (by simpa only [hr] using hf)
  refine ⟨p,funext fun z ↦ ?_⟩
  simpa using hp z (by simp)

end
end QuadricCounterexample

namespace QuadricCounterexample.LaurentCech
open Set MvPolynomial Finsupp
open scoped BigOperators
noncomputable section

def inverseExponent (n : ℕ) (i j : Chart) : Exponent :=
  (if i.1=j.1 then 0 else -(n : ℤ),if i.2=j.2 then 0 else -(n : ℤ))
lemma eval_inverseExponent (n : ℕ) (i j : Chart) (z : BaseCoordinates) :
    z.1^(inverseExponent n i j).1*z.2^(inverseExponent n i j).2=
      ((baseEval (overlapPolynomial i j) z)^n)⁻¹ := by
  simp only [inverseExponent,overlapPolynomial,baseEval_mul]
  split_ifs <;> simp [baseEval,mul_pow,mul_comm]
lemma torus_mem_overlap (i j : Chart) {z : BaseCoordinates} (hz : z.1≠0 ∧ z.2≠0) :
    z ∈ coordinateOverlap i j := (coordinateOverlap_iff i j z).mpr ⟨Or.inr hz.1,Or.inr hz.2⟩

lemma transform_overlap_support (d : ℕ × ℕ) (n : ℕ) (i j : Chart) (p : BasePolynomial)
    {a : Exponent} (ha : a∈(transform d i (shift (inverseExponent n i j) (ofPolynomial p))).support) :
    OverlapAllows d i j a := by
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hb)
  have hn := ofPolynomial_nonneg p hc
  constructor
  · intro hij
    dsimp [ScalarAllows,transformExponent,inverseExponent]
    simp only [hij,ite_true,zero_add]
    split_ifs <;> omega
  · intro hij
    dsimp [ScalarAllows,transformExponent,inverseExponent]
    simp only [hij,ite_true,zero_add]
    split_ifs <;> omega

lemma exists_overlap_laurent (d : ℕ × ℕ) (i j : Chart) (f : BaseCoordinates → ℂ)
    (hf : UniformlyRegularOn (coordinateOverlap i j) f) :
    ∃ p : LaurentCoefficients, (∀ a∈p.support,OverlapAllows d i j a) ∧
      ∀ z : BaseCoordinates, z.1≠0 ∧ z.2≠0 →
        eval p z=masterFrame d i z*f (masterCoordinates i z) := by
  obtain ⟨n,q,hq⟩ := UniformlyRegularOn.exists_power_denominator (overlapPolynomial i j) hf
  refine ⟨transform d i (shift (inverseExponent n i j) (ofPolynomial q)),
    fun _ ha ↦ transform_overlap_support d n i j q ha,?_⟩
  intro z hz
  have hw := masterCoordinates_nonzero i hz
  rw [eval_transform d i _ hz,eval_shift _ _ hw,eval_ofPolynomial,
    hq _ (torus_mem_overlap i j hw),eval_inverseExponent]
  ring

def lineFactor (d : ℕ × ℕ) (i j : Chart) (z : BaseCoordinates) : ℂ :=
  firstFactor i j z^d.1*secondFactor i j z^d.2
lemma lineFactor_regular (d : ℕ × ℕ) (i j : Chart) (U : Set BaseCoordinates) :
    UniformlyRegularOn U (lineFactor d i j) :=
  ((firstFactor_regular i j U).pow d.1).mul ((secondFactor_regular i j U).pow d.2)
lemma masterFrame_ne_zero (d : ℕ × ℕ) (i : Chart) {z : BaseCoordinates} (hz : z.1≠0 ∧ z.2≠0) :
    masterFrame d i z≠0 := by
  dsimp [masterFrame]
  split_ifs <;> simp_all
lemma masterCoordinates_change (i j : Chart) (z : BaseCoordinates) :
    coordinateChange i j (masterCoordinates i z)=masterCoordinates j z := by
  rcases i with ⟨i1,i2⟩; rcases j with ⟨j1,j2⟩
  ext <;> simp only [coordinateChange,scalarCoordinateChange,masterCoordinates]
  · fin_cases i1 <;> fin_cases j1 <;> simp
  · fin_cases i2 <;> fin_cases j2 <;> simp
lemma masterFrame_change (d : ℕ × ℕ) (i j : Chart) {z : BaseCoordinates}
    (hz : z.1≠0 ∧ z.2≠0) :
    masterFrame d i z*lineFactor d i j (masterCoordinates i z)=masterFrame d j z := by
  have hs (n : ℕ) (a b : Fin 2) (w : ℂ) (hw : w≠0) :
      (if a=0 then w^n else 1)*
        (scalarFactor a b (if a=0 then w⁻¹ else w))^n=(if b=0 then w^n else 1) := by
    fin_cases a <;> fin_cases b <;> simp [scalarFactor,hw]
  dsimp only [masterFrame,lineFactor,firstFactor,secondFactor,masterCoordinates]
  calc
    _ = ((if i.1=0 then z.1^d.1 else 1)*
       (scalarFactor i.1 j.1 (if i.1=0 then z.1⁻¹ else z.1))^d.1)*
       ((if i.2=0 then z.2^d.2 else 1)*
       (scalarFactor i.2 j.2 (if i.2=0 then z.2⁻¹ else z.2))^d.2) := by ring
    _ = _ := by rw [hs d.1 i.1 j.1 z.1 hz.1,hs d.2 i.2 j.2 z.2 hz.2]

lemma uniformlyRegular_eq_of_torus {i j : Chart} {f g : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn (coordinateOverlap i j) f)
    (hg : UniformlyRegularOn (coordinateOverlap i j) g)
    (he : ∀ z : BaseCoordinates,z.1≠0 ∧ z.2≠0 → f z=g z) :
    EqOn f g (coordinateOverlap i j) := by
  let r : BasePolynomial := X 0*X 1
  have hr : r≠0 := mul_ne_zero (X_ne_zero 0) (X_ne_zero 1)
  apply continuous_cancel_polynomial (coordinateOverlap_open i j)
    (hf.regular.analyticOnNhd (coordinateOverlap_open i j)).continuousOn
    (hg.regular.analyticOnNhd (coordinateOverlap_open i j)).continuousOn hr
  intro z _
  by_cases h : z.1≠0 ∧ z.2≠0
  · rw [he z h]
  · have ht : baseEval r z=0 := by simpa [r,baseEval,mul_eq_zero,not_and_or] using not_and_or.mp h
    simp [ht]

theorem split_regular_line_cocycle (d : ℕ × ℕ) (f : Chart → Chart → BaseCoordinates → ℂ)
    (hf : ∀ i j, UniformlyRegularOn (coordinateOverlap i j) (f i j))
    (hc : ∀ i j k z, z∈coordinateOverlap i j → z∈coordinateOverlap i k →
      f i j z+lineFactor d i j z*f j k (coordinateChange i j z)=f i k z) :
    ∃ q : Chart → BasePolynomial, ∀ i j z, z∈coordinateOverlap i j →
      f i j z=lineFactor d i j z*baseEval (q j) (coordinateChange i j z)-baseEval (q i) z := by
  choose p hp he using fun i j ↦ exists_overlap_laurent d i j (f i j) (hf i j)
  have pc : ∀ i j k,p i j+p j k=p i k := by
    intro i j k
    apply eval_injective_on_torus
    intro z hz
    rw [eval_add,he i j z hz,he j k z hz,he i k z hz]
    rw [← masterFrame_change d i j hz,mul_assoc,← mul_add]
    rw [← masterCoordinates_change i j z,hc i j k _
      (torus_mem_overlap i j (masterCoordinates_nonzero i hz))
      (torus_mem_overlap i k (masterCoordinates_nonzero i hz))]
  have ps : ∀ i j e, ¬OverlapAllows d i j e → p i j e=0 := by
    intro i j e h
    by_contra hn
    exact h (hp i j e (Finsupp.mem_support_iff.mpr hn))
  obtain ⟨a,ha,hae⟩ := split_cocycle d p pc ps
  have ha' : ∀ i e,e∈(a i).support → ChartAllows d i e := by
    intro i e he
    by_contra h
    exact Finsupp.mem_support_iff.mp he (ha i e h)
  choose q hq using fun i ↦ exists_polynomial_of_chartAllows d i (a i) (ha' i)
  refine ⟨q,?_⟩
  intro i j
  apply uniformlyRegular_eq_of_torus (hf i j)
  · exact ((lineFactor_regular d i j _).mul ((uniformlyRegular_polynomial univ (q j)).comp
      (coordinateChange_fst_regular i j) (coordinateChange_snd_regular i j)
      (fun _ _ ↦ mem_univ _))).sub (uniformlyRegular_polynomial _ (q i))
  · intro z hz
    let w := masterCoordinates i z
    have hw := masterCoordinates_nonzero i hz
    have hm : masterCoordinates i w=z := masterCoordinates_involutive i z
    have ht := congrArg (fun s ↦ eval s w) (hae i j)
    rw [eval_sub,he i j w hw,← hq i,← hq j,
      eval_transform_polynomial d j _ hw,eval_transform_polynomial d i _ hw] at ht
    rw [← masterFrame_change d i j hw,← masterCoordinates_change i j w,hm] at ht
    apply (mul_left_cancel₀ (masterFrame_ne_zero d i hw))
    linear_combination ht
end
end QuadricCounterexample.LaurentCech

end

end OAI
