import Mathlib
import OAI.Combinatorics.StripMass.BottomGauge

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators LaurentPolynomial

abbrev ArchShiftIndex := Bool × Bool × Fin 2

def archRootShift : ArchShiftIndex → ℕ
  | (false,false,s) => s.val+2
  | (false,true,s) => s.val+10
  | (true,false,s) => 14-s.val
  | (true,true,s) => 6-s.val

lemma archRootShift_lt (k : ArchShiftIndex) : archRootShift k<16 := by
  rcases k with ⟨a,b,s⟩
  cases a <;> cases b <;> fin_cases s <;> decide

lemma archRootShift_injective : Function.Injective archRootShift := by
  decide

def archRootCoefficient (b : Bool) (k : ArchShiftIndex) : ℂ :=
  if b then phase^3/(phase^archRootShift k) else phase^archRootShift k

lemma archRootCoefficient_ne_zero (b : Bool) (k : ArchShiftIndex) :
    archRootCoefficient b k≠0 := by
  cases b <;> simp [archRootCoefficient,phase_ne_zero]

lemma archRootCoefficient_injective (b : Bool) : Function.Injective (archRootCoefficient b) := by
  intro k l h
  apply archRootShift_injective
  apply phase_primitive.pow_inj (archRootShift_lt k) (archRootShift_lt l)
  cases b with
  | false => exact h
  | true =>
    simp only [archRootCoefficient,ite_true] at h
    apply inv_injective
    exact mul_left_cancel₀ (pow_ne_zero 3 phase_ne_zero)
      (by simpa only [div_eq_mul_inv] using h)

abbrev ArchRootIndex (n : ℕ) := Option (Fin (n+1) × Bool × ArchShiftIndex)

def archRootExponent {n : ℕ} : ArchRootIndex n → Fin (n+2) → ℤ
  | none => 0
  | some (j,b,_) => if b then -(variableExponent j.succ) else variableExponent j.succ

def archRootScalar {n : ℕ} : ArchRootIndex n → ℂ
  | none => 1
  | some (_,b,k) => archRootCoefficient b k

def archRoot {n : ℕ} (k : ArchRootIndex n) : SpectralField (n+2) :=
  evalLaurent (monomialL (archRootExponent k) (archRootScalar k))

lemma archRootScalar_ne_zero {n : ℕ} (k : ArchRootIndex n) : archRootScalar k≠0 := by
  cases k with
  | none => exact one_ne_zero
  | some k => exact archRootCoefficient_ne_zero k.2.1 k.2.2

lemma archRoot_ne_zero {n : ℕ} (k : ArchRootIndex n) : archRoot k≠0 := by
  intro h
  have he : monomialL (archRootExponent k) (archRootScalar k)=0 :=
    IsFractionRing.injective (SpectralRing (n+2)) (SpectralField (n+2))
      (by simpa only [archRoot, evalLaurent,map_zero] using h)
  exact archRootScalar_ne_zero k (AddMonoidAlgebra.single_eq_zero.mp he)

lemma archRootExponent_support {n : ℕ} (j : Fin (n+1)) (b : Bool) (k : ArchShiftIndex) (i : Fin (n+2)) :
    archRootExponent (some (j,b,k)) i≠0 ↔ i=j.succ := by
  cases b <;> simp [archRootExponent,variableExponent,Pi.single_apply]

lemma archRoot_injective {n : ℕ} : Function.Injective (@archRoot n) := by
  intro x y h
  have he : monomialL (archRootExponent x) (archRootScalar x) =
      monomialL (archRootExponent y) (archRootScalar y) :=
    IsFractionRing.injective (SpectralRing (n+2)) (SpectralField (n+2)) h
  rcases AddMonoidAlgebra.single_inj.mp he with ⟨he,hc⟩|⟨hz,_⟩
  · cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        have hh := (archRootExponent_support y.1 y.2.1 y.2.2 y.1.succ).mpr rfl
        rw [←he] at hh
        exact (hh rfl).elim
    | some x =>
      cases y with
      | none =>
        have hh := (archRootExponent_support x.1 x.2.1 x.2.2 x.1.succ).mpr rfl
        rw [he] at hh
        exact (hh rfl).elim
      | some y =>
        rcases x with ⟨j,b,k⟩
        rcases y with ⟨l,a,r⟩
        have hi : j=l := by
          have hh := (archRootExponent_support j b k j.succ).mpr rfl
          rw [he] at hh
          exact Fin.succ_injective _ ((archRootExponent_support l a r j.succ).mp hh)
        subst l
        have hb : b=a := by
          have hh := congrFun he j.succ
          cases b <;> cases a <;> simp [archRootExponent,variableExponent] at hh ⊢
        subst a
        have hk := archRootCoefficient_injective b hc
        rw [hk]
  · exact (archRootScalar_ne_zero _ hz).elim

lemma archRoot_none (n : ℕ) : archRoot (none : ArchRootIndex n) = 1 := by
  simp [archRoot,archRootExponent,archRootScalar,monomialL,evalLaurent,← AddMonoidAlgebra.one_def]

lemma archRoot_some {n : ℕ} (j : Fin (n+1)) (b : Bool) (k : ArchShiftIndex) :
    archRoot (some (j,b,k)) =
      if b then constF (n+2) phase^3/(constF (n+2) phase^archRootShift k*variableF j.succ)
      else constF (n+2) phase^archRootShift k*variableF j.succ := by
  cases b <;> simp [archRoot,archRootExponent,archRootScalar,archRootCoefficient,
    evalLaurent_monomial_product,variableExponent,Pi.single_apply,constF,div_eq_mul_inv,
    Finset.prod_ite_eq']
  all_goals ac_rfl

 

lemma arch_pair_zero {n m : ℕ} (f : Laurent (n+2))
    (hp : ∀ σ,permLaurent σ f=f) (s : ℕ) (hs : pairEvaluation n s f=0)
    (j : Fin (n+1)) (z : Fin (n+2) → SpectralField m) (hz : ∀ i,z i≠0)
    (he : z j.succ=constF m phase^s*z 0) : torusEvaluation z hz f=0 := by
  let σ := Equiv.swap (1:Fin (n+2)) j.succ
  have hσ0 : σ 0=0 := Equiv.swap_apply_of_ne_of_ne (by intro h; have : (0:ℕ)=1 := congrArg Fin.val h; omega) (Fin.succ_ne_zero j).symm
  have hσ1 : σ 1=j.succ := Equiv.swap_apply_left _ _
  have hzero := pairEvaluation_zero_universal s f hs (z ∘ σ) (fun i=>hz _)
    (by simpa only [Function.comp_apply,hσ0,hσ1] using he)
  rw [←torusEvaluation_permLaurent,hp] at hzero
  exact hzero

lemma arch_pair_zero_reverse {n m : ℕ} (f : Laurent (n+2))
    (hp : ∀ σ,permLaurent σ f=f) (s : ℕ) (hs : pairEvaluation n s f=0)
    (j : Fin (n+1)) (z : Fin (n+2) → SpectralField m) (hz : ∀ i,z i≠0)
    (he : z 0=constF m phase^s*z j.succ) : torusEvaluation z hz f=0 := by
  let σ := Equiv.swap (0:Fin (n+2)) j.succ
  have hzero := arch_pair_zero f hp s hs j (z ∘ σ) (fun i=>hz _)
    (by simpa only [σ,Function.comp_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] using he)
  rw [←torusEvaluation_permLaurent,hp] at hzero
  exact hzero

 

 


 
def archEvaluate {n : ℕ} (f : Laurent (n+1)) (x : SpectralField (n+1)) (hx : x≠0) : SpectralField (n+1) :=
  torusEvaluation (Function.update variableF 0 x)
    (fun j => by by_cases h:j=0 <;> simp [h,hx,variableF_ne_zero]) f

lemma archEvaluate_neg {n : ℕ} (f : Laurent (n+1)) (h : signLaurent 0 f = f)
    (x : SpectralField (n+1)) (hx : x≠0) :
    archEvaluate f (-x) (neg_ne_zero.mpr hx) = archEvaluate f x hx := by
  have he := torusEvaluation_signLaurent 0 (Function.update variableF 0 x)
    (fun j => by by_cases h:j=0 <;> simp [h,hx,variableF_ne_zero]) f
  rw [h] at he
  simpa only [Function.update_self,Function.update_idem,archEvaluate] using he.symm

lemma archEvaluate_reflect {n : ℕ} (f : Laurent (n+1)) (h : rowReflectLaurent 0 f = f)
    (x : SpectralField (n+1)) (hx : x≠0) :
    archEvaluate f (constF (n+1) phase^3/x)
      (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) hx) = archEvaluate f x hx := by
  have he := torusEvaluation_rowReflect 0 (Function.update variableF 0 x)
    (fun j => by by_cases h:j=0 <;> simp [h,hx,variableF_ne_zero]) f
  rw [h] at he
  simpa only [Function.update_self,Function.update_idem,archEvaluate] using he.symm

lemma archEvaluate_pair {n : ℕ} (f : Laurent (n+2))
    (hp : ∀ σ,permLaurent σ f=f) (s : ℕ) (hs : pairEvaluation n s f=0)
    (j : Fin (n+1)) (b : Bool) :
    archEvaluate f ((if b then (constF (n+2) phase^s)⁻¹ else constF (n+2) phase^s)*variableF j.succ)
      (by cases b <;> simp [constF_phase_ne_zero,variableF_ne_zero]) = 0 := by
  unfold archEvaluate
  cases b with
  | false =>
    apply arch_pair_zero_reverse f hp s hs j
    simp only [Function.update_self,Function.update_of_ne (Fin.succ_ne_zero j),Bool.false_eq_true,ite_false]
  | true =>
    apply arch_pair_zero f hp s hs j
    simp only [Function.update_self,Function.update_of_ne (Fin.succ_ne_zero j),ite_true]
    field_simp [constF_phase_ne_zero]

lemma archShift_value (k : ArchShiftIndex) :
    phase^archRootShift k =
      (if k.2.1 then -1 else 1) *
        (if k.1 then (phase^(k.2.2.val+2))⁻¹ else phase^(k.2.2.val+2)) := by
  rcases k with ⟨a,b,s⟩
  have hp := phase_more_powers
  cases a <;> cases b <;> fin_cases s <;>
    simp [archRootShift,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2]

lemma archEvaluate_shift {n : ℕ} (f : Laurent (n+2))
    (hp : ∀ σ,permLaurent σ f=f) (hsg : signLaurent 0 f=f)
    (h2 : pairEvaluation n 2 f=0) (h3 : pairEvaluation n 3 f=0)
    (j : Fin (n+1)) (k : ArchShiftIndex) :
    archEvaluate f (constF (n+2) phase^archRootShift k*variableF j.succ)
      (mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (variableF_ne_zero _)) = 0 := by
  have hbase := archEvaluate_pair f hp (k.2.2.val+2)
    (by rcases k with ⟨a,b,s⟩; fin_cases s <;> assumption) j k.1
  have hm : constF (n+2) phase^archRootShift k*variableF j.succ =
      if k.2.1 then -((if k.1 then (constF (n+2) phase^(k.2.2.val+2))⁻¹
        else constF (n+2) phase^(k.2.2.val+2))*variableF j.succ)
      else ((if k.1 then (constF (n+2) phase^(k.2.2.val+2))⁻¹
        else constF (n+2) phase^(k.2.2.val+2))*variableF j.succ) := by
    have hc := congrArg (algebraMap ℂ (SpectralField (n+2))) (archShift_value k)
    rcases k with ⟨a,b,s⟩
    cases a <;> cases b <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,map_pow,map_mul,map_neg,map_one,map_inv₀] at hc ⊢
    all_goals dsimp only [constF]; rw [hc]; simp
  cases hb : k.2.1
  · simpa only [hm,hb,Bool.false_eq_true,ite_false] using hbase
  · have hh := (archEvaluate_neg f hsg _ _).trans hbase
    simpa only [hm,hb,ite_true] using hh

 

lemma archEvaluate_roots {n : ℕ} (f : Laurent (n+2))
    (hp : ∀ σ,permLaurent σ f=f) (hsg : signLaurent 0 f=f)
    (hr : rowReflectLaurent 0 f=f) (hflat : firstFlatEvaluation (n+1) f=0)
    (h2 : pairEvaluation n 2 f=0) (h3 : pairEvaluation n 3 f=0)
    (k : ArchRootIndex n) : archEvaluate f (archRoot k) (archRoot_ne_zero k)=0 := by
  cases k with
  | none =>
    unfold archEvaluate
    apply firstFlatEvaluation_zero_universal f hflat
    simp only [Function.update_self,archRoot_none]
  | some k =>
    rcases k with ⟨j,b,k⟩
    cases b with
    | false =>
      simpa only [archRoot_some,Bool.false_eq_true,ite_false] using archEvaluate_shift f hp hsg h2 h3 j k
    | true =>
      have hh := (archEvaluate_reflect f hr _ _).trans (archEvaluate_shift f hp hsg h2 h3 j k)
      simpa only [archRoot_some,ite_true] using hh

 

theorem archLaurent_interpolation_zero {n : ℕ} (f : Laurent (n+2))
    (hb : LaurentBox f (fun _ =>4*(n+2)))
    (hp : ∀ σ,permLaurent σ f=f) (hsg : signLaurent 0 f=f)
    (hr : rowReflectLaurent 0 f=f) (hflat : firstFlatEvaluation (n+1) f=0)
    (h2 : pairEvaluation n 2 f=0) (h3 : pairEvaluation n 3 f=0) : f=0 := by
  apply fullPeel_injective (0:Fin (n+2))
  rw [map_zero]
  refine laurent_eq_zero_of_many_roots (fullPeel (0:Fin (n+2)) f) (4*(n+2))
    (hb.fullPeel 0) (Finset.univ.image (@archRoot n)) ?_
    (fun z hz => by obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz; exact archRoot_ne_zero k) ?_
  · rw [Finset.card_image_of_injective _ archRoot_injective,Finset.card_univ]
    simp only [ArchRootIndex,ArchShiftIndex,Fintype.card_option,Fintype.card_prod,
      Fintype.card_fin,Fintype.card_bool]
    omega
  · intro z hz
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
    rw [fullPeel_eval]
    exact archEvaluate_roots f hp hsg hr hflat h2 h3 k

end
 

 

noncomputable section
open scoped Classical BigOperators

 

def previousCoeff {K : Type*} [Semiring K] (n : ℕ) (P : Polynomial K) : K :=
  if n=0 then 0 else P.coeff (n-1)

lemma previousCoeff_map {K L : Type*} [Semiring K] [Semiring L]
    (g : K →+* L) (n : ℕ) (P : Polynomial K) :
    previousCoeff n (P.map g) = g (previousCoeff n P) := by
  by_cases h:n=0 <;> simp [previousCoeff,h]

 
def nextScalar {K : Type*} [CommRing K] (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) : Polynomial K :=
  firstScalarHom f a (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))

lemma map_scalarValue {K L : Type*} [CommRing K] [CommRing L]
    (g : K →+* L) (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    g (scalarValue f a) = scalarValue (g.comp f) (g ∘ a) := by
  exact MvPolynomial.map_eval₂Hom _ _ _ _

lemma nextScalar_map {K L : Type*} [CommRing K] [CommRing L]
    (g : K →+* L) (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    (nextScalar f a).map g = nextScalar (g.comp f) (g ∘ a) :=
  map_firstScalarHom g f a _

lemma nextScalar_top {K : Type*} [CommRing K]
    (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    (nextScalar f a).coeff n = scalarValue f a :=
  scalarPolynomial_first_top_continuation f n _ _ _ _

lemma nextScalar_degree {K : Type*} [CommRing K]
    (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) : (nextScalar f a).natDegree ≤ n :=
  scalarPolynomial_first_degree f n _ _ _ _

 
def headPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cases 0 (fun i => (σ i).succ)
  invFun := Fin.cases 0 (fun i => (σ.symm i).succ)
  left_inv i := by induction i using Fin.cases <;> simp
  right_inv i := by induction i using Fin.cases <;> simp

lemma nextScalar_permute {K : Type*} [CommRing K]
    (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    nextScalar f (a ∘ σ) = nextScalar f a := by
  have h := scalarValue_permute (Polynomial.C.comp f)
    (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) (headPerm σ)
  have hv : (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) ∘ headPerm σ =
      Fin.cons Polynomial.X (fun i => Polynomial.C (a (σ i))) := by
    funext i
    induction i using Fin.cases <;> rfl
  rw [hv] at h
  exact h

 

def scalarArchNumerator {K : Type*} [CommRing K]
    (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) : K :=
  (∑ i,a i) * scalarValue f a ^ 2 - f (2*(d:ℂ)-1) * scalarValue f a * previousCoeff n (nextScalar f a)

lemma map_scalarArchNumerator {K L : Type*} [CommRing K] [CommRing L]
    (g : K →+* L) (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    g (scalarArchNumerator f a) = scalarArchNumerator (g.comp f) (g ∘ a) := by
  simp only [scalarArchNumerator,map_sub,map_mul,map_sum,map_pow,map_scalarValue,
    ←previousCoeff_map,nextScalar_map,RingHom.comp_apply,Function.comp_apply]

lemma scalarArchNumerator_permute {K : Type*} [CommRing K]
    (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    scalarArchNumerator f (a ∘ σ) = scalarArchNumerator f a := by
  rw [scalarArchNumerator,scalarValue_permute,nextScalar_permute]
  have h : (∑i,a (σ i))=∑i,a i := Equiv.sum_comp σ a
  exact congrArg (fun z => z*scalarValue f a^2-f (2*(d:ℂ)-1)*scalarValue f a*previousCoeff n (nextScalar f a)) h

def rowCosineL {n : ℕ} (i : Fin n) : Laurent n :=
  cosineL ((2:ℤ) • variableExponent i) (phase^3)⁻¹

lemma rowCosineL_map {n : ℕ} (i : Fin n) : evalLaurent (rowCosineL i)=spectralA i := by
  rw [rowCosineL,cosineL_map _ _ (inv_ne_zero (pow_ne_zero _ phase_ne_zero)),map_monomialL_two_variable]
  simp only [constF,map_inv₀,map_pow]
  congr 1
  simp [constF,div_eq_mul_inv,mul_comm]

lemma rowCosineL_algebraMap {n : ℕ} (i : Fin n) :
    algebraMap (SpectralRing n) (SpectralField n) (rowCosineL i)=spectralA i := rowCosineL_map i

lemma rowCosineL_box {n : ℕ} (i : Fin n) : LaurentBox (rowCosineL i) (fun _=>2) := by
  apply LaurentBox.cosine
  intro j
  by_cases h:j=i <;> simp [variableExponent,h]

lemma evalLaurent_constant_comp (n : ℕ) :
    (algebraMap (SpectralRing n) (SpectralField n)).comp (constantL n) =
      algebraMap ℂ (SpectralField n) := by
  ext z
  exact map_constantL n z

lemma scalarValue_rowCosine (n : ℕ) :
    scalarValue (constantL n) rowCosineL = polynomialVacuumVector n (empty n) := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  rw [show algebraMap (SpectralRing n) (SpectralField n) _ = _ from
    map_scalarValue _ (constantL n) rowCosineL]
  simp only [evalLaurent_constant_comp,Function.comp_def,rowCosineL_algebraMap]
  change scalarValue _ spectralA = evalLaurent (polynomialVacuumVector n (empty n))
  rw [polynomialVacuumVector_eval,rationalVacuum_empty]
  exact scalarPolynomial_eval_spectral n

lemma nextScalar_rowCosine (n : ℕ) :
    nextScalar (constantL n) rowCosineL = (vacuumData n).P (empty (n+1)) := by
  apply Polynomial.map_injective (algebraMap (SpectralRing n) (SpectralField n))
    (IsFractionRing.injective _ _)
  rw [nextScalar_map,(vacuumData n).map_P,rationalNodalPolynomial_empty]
  simp only [evalLaurent_constant_comp,Function.comp_def,rowCosineL_algebraMap,nextScalar]

 
def archCandidate (n : ℕ) : Laurent n := scalarArchNumerator (constantL n) rowCosineL

lemma archCandidate_eval (n : ℕ) :
    evalLaurent (archCandidate n)=scalarArchNumerator (algebraMap ℂ (SpectralField n)) spectralA := by
  unfold archCandidate evalLaurent
  rw [map_scalarArchNumerator]
  simp only [evalLaurent_constant_comp,Function.comp_def,rowCosineL_algebraMap]

lemma scalarValue_rowCosine_box (n : ℕ) :
    LaurentBox (scalarValue (constantL n) rowCosineL) (fun _=>2*(n-1)) := by
  rw [scalarValue_rowCosine]
  cases n with
  | zero => intro e he i; exact Fin.elim0 i
  | succ n => exact (vacuumData n).box _

lemma previousCoeff_nextScalar_box (n : ℕ) :
    LaurentBox (previousCoeff n (nextScalar (constantL n) rowCosineL)) (fun _=>2*n) := by
  rw [nextScalar_rowCosine,previousCoeff]
  split_ifs
  · exact LaurentBox.zero _
  · exact (vacuumData n).box_P _ _

lemma archCandidate_box (n : ℕ) : LaurentBox (archCandidate n) (fun _=>4*n) := by
  unfold archCandidate scalarArchNumerator
  apply LaurentBox.sub
  · have h := (LaurentBox.sum Finset.univ rowCosineL (fun _=>2) (fun i _=>rowCosineL_box i)).mul
      ((scalarValue_rowCosine_box n).pow 2)
    apply h.mono
    intro i
    have := i.isLt
    simp only [Pi.add_apply]
    omega
  · have h := ((LaurentBox.constant (2*(d:ℂ)-1)).mul (scalarValue_rowCosine_box n)).mul (previousCoeff_nextScalar_box n)
    apply h.mono
    intro i
    simp only [Pi.add_apply,Pi.zero_apply]
    omega

lemma archCandidate_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permLaurent σ (archCandidate n) = archCandidate n := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (permLaurent σ (archCandidate n))=evalLaurent (archCandidate n)
  rw [←permSpectral_evalLaurent,archCandidate_eval]
  rw [map_scalarArchNumerator]
  have hc : (permSpectral σ).comp (algebraMap ℂ (SpectralField n)) =
      algebraMap ℂ (SpectralField n) := by ext z; exact permSpectral_const σ z
  simp only [hc,Function.comp_def,permSpectral_spectralA]
  exact scalarArchNumerator_permute (algebraMap ℂ (SpectralField n)) spectralA σ

lemma archCandidate_parity {n : ℕ} (i : Fin n) : signLaurent i (archCandidate n)=archCandidate n := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (signLaurent i (archCandidate n))=evalLaurent (archCandidate n)
  rw [←signSpectral_evalLaurent,archCandidate_eval,map_scalarArchNumerator]
  have hc : (signSpectral i).comp (algebraMap ℂ (SpectralField n)) =
      algebraMap ℂ (SpectralField n) := by ext z; exact signSpectral_const i z
  simp only [hc,Function.comp_def,signSpectral_spectralA]

lemma archCandidate_row_reflection {n : ℕ} (i : Fin n) :
    rowReflectLaurent i (archCandidate n)=archCandidate n := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (rowReflectLaurent i (archCandidate n))=evalLaurent (archCandidate n)
  rw [←rowReflectSpectral_evalLaurent,archCandidate_eval,map_scalarArchNumerator]
  have hc : (rowReflectSpectral i).comp (algebraMap ℂ (SpectralField n)) =
      algebraMap ℂ (SpectralField n) := by ext z; exact rowReflectSpectral_const i z
  simp only [hc,Function.comp_def,rowReflectSpectral_spectralA]

 

 


lemma previousCoeff_C_mul {K : Type*} [CommRing K] (n : ℕ) (a : K) (P : Polynomial K) :
    previousCoeff n (Polynomial.C a * P) = a * previousCoeff n P := by
  by_cases h : n=0 <;> simp [previousCoeff,h,Polynomial.coeff_C_mul]

lemma previousCoeff_linear {K : Type*} [CommRing K] (n : ℕ) (a : K) (P : Polynomial K) :
    previousCoeff (n+1) ((Polynomial.X+Polynomial.C a)*P) =
      previousCoeff n P + a*P.coeff n := by
  cases n with
  | zero => simp [previousCoeff,add_mul]
  | succ n => simp [previousCoeff,add_mul,Polynomial.coeff_X_mul,Polynomial.coeff_C_mul]

lemma previousCoeff_quadratic {K : Type*} [CommRing K]
    (n : ℕ) (a b : K) (P : Polynomial K) (hP : P.natDegree ≤ n) :
    previousCoeff (n+2) (((Polynomial.X-Polynomial.C a)*(Polynomial.X-Polynomial.C b))*P) =
      previousCoeff n P - (a+b)*P.coeff n := by
  have hz : P.coeff (n+1)=0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have he : ((Polynomial.X-Polynomial.C a)*(Polynomial.X-Polynomial.C b))*P =
      (Polynomial.X+Polynomial.C (-a))*((Polynomial.X+Polynomial.C (-b))*P) := by simp; ring
  rw [he,show n+2=(n+1)+1 by omega,previousCoeff_linear,previousCoeff_linear]
  simp only [add_mul,Polynomial.coeff_add,Polynomial.coeff_X_mul,Polynomial.coeff_C_mul,hz,mul_zero,add_zero]
  ring

lemma specialization_constant_comp {n m : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField m) :
    φ.toRingHom.comp (constantL n) = algebraMap ℂ (SpectralField m) := by
  ext z
  exact φ.commutes z

lemma torusEvaluation_rowCosine {n m : ℕ} (z : Fin n → SpectralField m) (hz : ∀i,z i≠0) (i : Fin n) :
    torusEvaluation z hz (rowCosineL i) = torusCos ((z i)^2/constF m phase^3) := by
  have ha := RationalAt.algebraMap (φ := (torusEvaluation z hz).toRingHom)
    (F := SpectralField n) (rowCosineL i)
  rw [rowCosineL_algebraMap] at ha
  exact ha.unique (rationalAt_torusCos _ (((rationalAt_variable z hz i).pow 2).div
    ((rationalAt_const (torusEvaluation z hz) phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero _)))
    (div_ne_zero (pow_ne_zero _ (hz i)) (pow_ne_zero _ (constF_phase_ne_zero _))))

lemma firstFlatEvaluation_rowCosine {n : ℕ} (i : Fin (n+1)) :
    firstFlatEvaluation n (rowCosineL i) = (Fin.cons (constF n c) spectralA : Fin (n+1) → SpectralField n) i := by
  have ha := RationalAt.algebraMap (φ := (firstFlatEvaluation n).toRingHom)
    (F := SpectralField (n+1)) (rowCosineL i)
  rw [rowCosineL_algebraMap] at ha
  exact ha.unique (rationalAt_firstFlat_spectralA i)

lemma nextScalar_firstFlat (n : ℕ) :
    (nextScalar (constantL (n+1)) rowCosineL).map (firstFlatEvaluation n).toRingHom =
      Polynomial.C (∏ j:Fin n, (spectralA j+constF n C)) *
        ((Polynomial.X+Polynomial.C (constF n C))*nextScalar (algebraMap ℂ (SpectralField n)) spectralA) := by
  rw [nextScalar_rowCosine]
  have h := congrFun (rationalNodalPolynomial_firstFlat
    (vacuumData n).interpolant (vacuumData (n+1)).P (vacuumData (n+1)).map_P)
    (empty (n+1)).padBottom
  rw [rationalFirstZeroPolynomial_vacant,Pairing.padBottom_empty,rationalNodalPolynomial_empty] at h
  exact h

lemma matrixPolynomial_merge_empty {n m : ℕ} (r : ℕ) (hr : r+2≤n+1)
    (P : Pairing n → Polynomial (SpectralField m)) :
    matrixPolynomial (mergeMap r hr) P (empty (n+1))=P (empty n) := by
  ext k
  rw [matrixPolynomial_coeff,mergeMap_mulVec_empty]

lemma matrixPolynomial_delete_empty {n m : ℕ} (r : ℕ) (hr : r+2≤n+2)
    (P : Pairing n → Polynomial (SpectralField m)) :
    matrixPolynomial (deletionMap r hr) P (empty (n+2))=P (empty n) := by
  ext k
  rw [matrixPolynomial_coeff,deletionMap_mulVec_empty]

lemma nextScalar_pair_merge (n : ℕ) :
    (nextScalar (constantL (n+2)) rowCosineL).map (pairEvaluation n 2).toRingHom =
      Polynomial.C (mergePairScalar n) * ((Polynomial.X+Polynomial.C (fcos 0 (-1))) *
        (nextScalar (constantL (n+1)) rowCosineL).map (mergeEvaluation n).toRingHom) := by
  rw [nextScalar_rowCosine,nextScalar_rowCosine]
  have h := congrFun (rationalNodalPolynomial_pair_merge
    (polynomialVacuumVector (n+1)) (polynomialVacuumVector_eval (n+1))
    (vacuumData (n+1)).P (vacuumData (n+1)).map_P (vacuumData (n+1)).eval_P
    (vacuumData (n+2)).P (vacuumData (n+2)).map_P) (empty (n+3))
  rw [matrixPolynomial_merge_empty] at h
  simpa only [mergePairPolynomial,mul_assoc] using h

lemma nextScalar_pair_delete (n : ℕ) :
    (nextScalar (constantL (n+2)) rowCosineL).map (pairEvaluation n 3).toRingHom =
      Polynomial.C (deletePairScalar n) * (((Polynomial.X-Polynomial.C (fcos 0 (-9)))*(Polynomial.X-Polynomial.C (fcos 0 9))) *
        (nextScalar (constantL n) rowCosineL).map (deleteEvaluation n).toRingHom) := by
  rw [nextScalar_rowCosine,nextScalar_rowCosine]
  have h := congrFun (rationalNodalPolynomial_pair_delete
    (polynomialVacuumVector (n+1)) (polynomialVacuumVector_eval (n+1))
    (vacuumData n).P (vacuumData n).map_P (vacuumData n).eval_P
    (vacuumData (n+2)).P (vacuumData (n+2)).map_P) (empty (n+3))
  rw [matrixPolynomial_delete_empty] at h
  simpa only [deletePairPolynomial,mul_assoc] using h

lemma nextScalar_specialize {n m : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField m) :
    (nextScalar (constantL n) rowCosineL).map φ.toRingHom =
      nextScalar (algebraMap ℂ (SpectralField m)) (fun i =>φ (rowCosineL i)) := by
  rw [nextScalar_map,specialization_constant_comp]
  rfl

lemma scalarValue_specialize {n m : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField m) :
    φ (scalarValue (constantL n) rowCosineL)=
      scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>φ (rowCosineL i)) := by
  rw [show φ (scalarValue (constantL n) rowCosineL)=φ.toRingHom _ from rfl,
    map_scalarValue,specialization_constant_comp]
  rfl

lemma archCandidate_specialize {n m : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField m) :
    φ (archCandidate n)=
      scalarArchNumerator (algebraMap ℂ (SpectralField m)) (fun i =>φ (rowCosineL i)) := by
  unfold archCandidate
  rw [show φ (scalarArchNumerator (constantL n) rowCosineL)=φ.toRingHom _ from rfl,
    map_scalarArchNumerator,specialization_constant_comp]
  rfl

end
end CriticalStrip.Diagram

end OAI
