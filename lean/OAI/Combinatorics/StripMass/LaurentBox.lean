import Mathlib
import OAI.Combinatorics.StripMass.DiagonalFactors

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical Pointwise

 
def LaurentBox {n : ℕ} (f : Laurent n) (b : Fin n → ℕ) : Prop :=
  ∀ e, f.coeff e≠0 → ∀ i, -(b i:ℤ)≤e i ∧ e i≤b i

lemma LaurentBox.zero {n : ℕ} (b : Fin n → ℕ) : LaurentBox 0 b := by
  intro e he
  exact (he rfl).elim

lemma LaurentBox.mono {n : ℕ} {f : Laurent n} {b c : Fin n → ℕ}
    (hf : LaurentBox f b) (hbc : ∀ i,b i≤c i) : LaurentBox f c := by
  intro e he i
  have := hf e he i
  have := hbc i
  constructor <;> omega

lemma LaurentBox.add {n : ℕ} {f g : Laurent n} {b : Fin n → ℕ}
    (hf : LaurentBox f b) (hg : LaurentBox g b) : LaurentBox (f+g) b := by
  intro e he i
  by_cases hh:f.coeff e=0
  · exact hg e (by simpa [AddMonoidAlgebra.coeff_add,hh] using he) i
  · exact hf e hh i

lemma LaurentBox.neg {n : ℕ} {f : Laurent n} {b : Fin n → ℕ}
    (hf : LaurentBox f b) : LaurentBox (-f) b := by
  intro e he i
  exact hf e (by simpa using he) i

lemma LaurentBox.sub {n : ℕ} {f g : Laurent n} {b : Fin n → ℕ}
    (hf : LaurentBox f b) (hg : LaurentBox g b) : LaurentBox (f-g) b := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

lemma LaurentBox.mul {n : ℕ} {f g : Laurent n} {b c : Fin n → ℕ}
    (hf : LaurentBox f b) (hg : LaurentBox g c) : LaurentBox (f*g) (b+c) := by
  intro e he i
  have hs := AddMonoidAlgebra.support_coeff_mul_subset f g (Finsupp.mem_support_iff.mpr he)
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.mem_add.mp hs
  have hx := hf x (Finsupp.mem_support_iff.mp hx) i
  have hy := hg y (Finsupp.mem_support_iff.mp hy) i
  have hh := congrFun hxy i
  simp only [Pi.add_apply] at hh ⊢
  push_cast
  constructor <;> omega

lemma LaurentBox.single {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (b : Fin n → ℕ)
    (h : ∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) : LaurentBox (monomialL e z) b := by
  intro f hf i
  have hh:f=e := by
    by_contra hh
    exact hf (by simp [monomialL,AddMonoidAlgebra.coeff_single,Ne.symm hh])
  subst f
  exact h i

lemma LaurentBox.constant {n : ℕ} (z : ℂ) : LaurentBox (constantL n z) 0 :=
  LaurentBox.single 0 z 0 (by simp)

lemma LaurentBox.one {n : ℕ} : LaurentBox (1:Laurent n) 0 := by
  rw [←monomialL_zero_one]
  exact LaurentBox.single 0 1 0 (by simp)

lemma LaurentBox.sine {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (b : Fin n → ℕ)
    (h : ∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) : LaurentBox (sineL e z) b := by
  unfold sineL
  have hf:=LaurentBox.single e z b h
  have hg:=LaurentBox.single (-e) z⁻¹ b (by intro i; have :=h i; simp only [Pi.neg_apply]; omega)
  simpa using (hf.sub hg).mul (LaurentBox.constant ((2*Complex.I)⁻¹))

lemma LaurentBox.sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Laurent n)
    (b : Fin n → ℕ) (h : ∀ i∈s,LaurentBox (f i) b) : LaurentBox (∑ i∈s,f i) b := by
  induction s using Finset.induction_on with
  | empty => simpa using LaurentBox.zero b
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))

lemma LaurentBox.prod {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Laurent n)
    (b : ι → Fin n → ℕ) (h : ∀ i∈s,LaurentBox (f i) (b i)) :
    LaurentBox (∏ i∈s,f i) (∑ i∈s,b i) := by
  induction s using Finset.induction_on with
  | empty => simpa using LaurentBox.one (n:=n)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    exact (h a (by simp)).mul (ih (fun i hi => h i (by simp [hi])))

end

 

 

noncomputable section
open scoped LaurentPolynomial Classical

variable {K : Type*} [Field K]

lemma laurent_mul_top_coeff (f g : LaurentPolynomial K) (a b : ℤ)
    (hf : ∀ e,f.coeff e≠0 → e≤a) (hg : ∀ e,g.coeff e≠0 → e≤b) :
    (f*g).coeff (a+b)=f.coeff a*g.coeff b := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  change (∑ e ∈ f.coeff.support, f.coeff e*g.coeff (-e+(a+b)))=_
  rw [Finset.sum_eq_single a]
  · congr 1
    congr 1
    ring
  · intro e he hea
    have hle:=hf e (Finsupp.mem_support_iff.mp he)
    have hz:g.coeff (-e+(a+b))=0 := by
      by_contra hh
      have := hg _ hh
      omega
    rw [hz,mul_zero]
  · intro ha
    rw [Finsupp.notMem_support_iff.mp ha,zero_mul]

lemma laurent_mul_bottom_coeff (f g : LaurentPolynomial K) (a b : ℤ)
    (hf : ∀ e,f.coeff e≠0 → a≤e) (hg : ∀ e,g.coeff e≠0 → b≤e) :
    (f*g).coeff (a+b)=f.coeff a*g.coeff b := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  change (∑ e ∈ f.coeff.support, f.coeff e*g.coeff (-e+(a+b)))=_
  rw [Finset.sum_eq_single a]
  · congr 1
    congr 1
    ring
  · intro e he hea
    have hle:=hf e (Finsupp.mem_support_iff.mp he)
    have hz:g.coeff (-e+(a+b))=0 := by
      by_contra hh
      have := hg _ hh
      omega
    rw [hz,mul_zero]
  · intro ha
    rw [Finsupp.notMem_support_iff.mp ha,zero_mul]

 

theorem LaurentInterval.quotient {f g : LaurentPolynomial K} {a b c d : ℤ}
    (h : LaurentInterval (f*g) a b) (hg : LaurentInterval g c d)
    (hc : g.coeff c≠0) (hd : g.coeff d≠0) : LaurentInterval f (a-c) (b-d) := by
  intro e he
  have hs : f.coeff.support.Nonempty := ⟨e,Finsupp.mem_support_iff.mpr he⟩
  let lo:=f.coeff.support.min' hs
  let hi:=f.coeff.support.max' hs
  have hlo : f.coeff lo≠0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hs)
  have hhi : f.coeff hi≠0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ hs)
  have hlow (k : ℤ) (hk:f.coeff k≠0) : lo≤k :=
    Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hk)
  have hhigh (k : ℤ) (hk:f.coeff k≠0) : k≤hi :=
    Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hk)
  have hl : (f*g).coeff (lo+c)≠0 := by
    rw [laurent_mul_bottom_coeff f g lo c hlow (fun k hk => (hg k hk).1)]
    exact mul_ne_zero hlo hc
  have hh : (f*g).coeff (hi+d)≠0 := by
    rw [laurent_mul_top_coeff f g hi d hhigh (fun k hk => (hg k hk).2)]
    exact mul_ne_zero hhi hd
  have h₁ := (h (lo+c) hl).1
  have h₂ := (h (hi+d) hh).2
  have h₃ := hlow e he
  have h₄ := hhigh e he
  omega

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

lemma peelLaurentEquiv_coeff_coeff {n : ℕ} (i : Fin (n+1)) (f:Laurent (n+1))
    (k : ℤ) (e : Fin n → ℤ) :
    ((peelLaurentEquiv i f).coeff k).coeff e=f.coeff (Fin.insertNth i k e) := by
  change (AddMonoidAlgebra.mapDomainRingEquiv ℂ (peelExponent i) f).coeff (k,e)=_
  rw [AddMonoidAlgebra.coeff_mapDomainRingEquiv]
  rfl

lemma peelLaurent_coeff {n : ℕ} (i : Fin (n+1)) (f:Laurent (n+1)) (k : ℤ) :
    (peelLaurent i f).coeff k=evalLaurent ((peelLaurentEquiv i f).coeff k) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

lemma peelLaurent_coeff_ne_zero_iff {n : ℕ} (i : Fin (n+1)) (f:Laurent (n+1)) (k : ℤ) :
    (peelLaurent i f).coeff k≠0 ↔ ∃ e : Fin n → ℤ,f.coeff (Fin.insertNth i k e)≠0 := by
  rw [peelLaurent_coeff]
  constructor
  · intro h
    by_contra hh
    push Not at hh
    have hz:(peelLaurentEquiv i f).coeff k=0 := by
      ext e
      simpa only [peelLaurentEquiv_coeff_coeff,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using hh e
    exact h (by rw [hz]; exact map_zero _)
  · rintro ⟨e,he⟩ hz
    have hh:(peelLaurentEquiv i f).coeff k=0 :=
      (IsFractionRing.injective (SpectralRing n) (SpectralField n)) (hz.trans (map_zero _).symm)
    have :=congrArg (fun g:Laurent n => g.coeff e) hh
    rw [peelLaurentEquiv_coeff_coeff] at this
    exact he this

lemma LaurentBox.peel {n : ℕ} {f : Laurent (n+1)} {b : Fin (n+1) → ℕ}
    (hf:LaurentBox f b) (i:Fin (n+1)) : LaurentInterval (peelLaurent i f) (-(b i:ℤ)) (b i) := by
  intro k hk
  obtain ⟨e,he⟩:=(peelLaurent_coeff_ne_zero_iff i f k).mp hk
  simpa only [Fin.insertNth_apply_same] using hf _ he i

lemma LaurentBox.of_peel {n : ℕ} {f : Laurent (n+1)} {b : Fin (n+1) → ℕ}
    (hf:∀ i:Fin (n+1),LaurentInterval (peelLaurent i f) (-(b i:ℤ)) (b i)) : LaurentBox f b := by
  intro e he i
  apply hf i (e i)
  apply (peelLaurent_coeff_ne_zero_iff i f (e i)).mpr
  exact ⟨Fin.removeNth i e,by simpa only [Fin.insertNth_removeNth,Function.update_eq_self] using he⟩

end

 

 

noncomputable section
open scoped LaurentPolynomial Classical

 

lemma laurent_linear_dvd {R : Type*} [CommRing R] (f : LaurentPolynomial R) (u : Rˣ)
    (h : LaurentPolynomial.eval₂ (RingHom.id R) u f=0) :
    LaurentPolynomial.T 1-LaurentPolynomial.C (u:R) ∣ f := by
  obtain ⟨m,p,hp⟩:=LaurentPolynomial.exists_T_pow f
  have he:p.eval (u:R)=0 := by
    have hh:=congrArg (LaurentPolynomial.eval₂ (RingHom.id R) u) hp
    rw [LaurentPolynomial.eval₂_toLaurent,map_mul,h,zero_mul] at hh
    exact hh
  obtain ⟨q,hq⟩:=Polynomial.dvd_iff_isRoot.mpr he
  refine ⟨q.toLaurent*LaurentPolynomial.T (-(m:ℤ)),?_⟩
  have hh:=congrArg (fun g : LaurentPolynomial R => g*LaurentPolynomial.T (-(m:ℤ))) hp
  rw [hq,map_mul,map_sub,Polynomial.toLaurent_X,Polynomial.toLaurent_C] at hh
  simpa only [mul_assoc,←LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero,mul_one]
    using hh.symm

lemma laurent_eval_linear {R : Type*} [CommRing R] (u v : Rˣ) :
    LaurentPolynomial.eval₂ (RingHom.id R) u
      (LaurentPolynomial.T 1-LaurentPolynomial.C (v:R))=(u:R)-(v:R) := by
  simp [LaurentPolynomial.eval₂_T,LaurentPolynomial.eval₂_C]

 

lemma laurent_prod_linear_dvd {R : Type*} [CommRing R] [IsDomain R]
    (f : LaurentPolynomial R) (s : Finset Rˣ)
    (h : ∀ u∈s,LaurentPolynomial.eval₂ (RingHom.id R) u f=0) :
    (∏ u∈s,(LaurentPolynomial.T 1-LaurentPolynomial.C (u:R))) ∣ f := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨g,hg⟩:=laurent_linear_dvd f a (h a (Finset.mem_insert_self a s))
    have hs (u : Rˣ) (hu:u∈s) : LaurentPolynomial.eval₂ (RingHom.id R) u g=0 := by
      have hh:=h u (Finset.mem_insert_of_mem hu)
      rw [hg,map_mul,laurent_eval_linear] at hh
      apply (mul_eq_zero.mp hh).resolve_left
      apply sub_ne_zero.mpr
      intro e
      have eu:u=a := Units.ext e
      exact ha (eu ▸ hu)
    obtain ⟨q,hq⟩:=ih g hs
    rw [Finset.prod_insert ha]
    refine ⟨q,?_⟩
    rw [hg,hq,mul_assoc]

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

 

theorem prod_dvd_of_evaluation_packets {R K ι κ : Type*}
    [CommRing R] [CommRing K] [IsDomain K]
    (s : Finset ι) (D : ι → R) (φ : ι → κ → R →+* K)
    (hker : ∀ i∈s, ∀ f:R, (∀ k,φ i k f=0) → D i ∣ f)
    (hcross : ∀ i∈s, ∀ j∈s, i≠j → ∀ k,φ i k (D j)≠0)
    (f : R) (hf : ∀ i∈s, ∀ k,φ i k f=0) : (∏ i∈s,D i) ∣ f := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨g,hg⟩:=hker i (Finset.mem_insert_self _ _) f (hf i (Finset.mem_insert_self _ _))
    have hsg (j : ι) (hj:j∈s) (k : κ) : φ j k g=0 := by
      have hh:=hf j (Finset.mem_insert_of_mem hj) k
      rw [hg,map_mul] at hh
      apply (mul_eq_zero.mp hh).resolve_left
      exact hcross j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _)
        (fun he => hi (he ▸ hj)) k
    obtain ⟨q,hq⟩:=ih (fun j hj => hker j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      g hsg
    refine ⟨q,?_⟩
    rw [Finset.prod_insert hi,hg,hq,mul_assoc]

lemma laurent_prod_linear_indexed_dvd {R ι : Type*} [CommRing R] [IsDomain R]
    [Fintype ι] (u : ι → Rˣ) (hu : Function.Injective u)
    (f : LaurentPolynomial R) (h : ∀ i,LaurentPolynomial.eval₂ (RingHom.id R) (u i) f=0) :
    (∏ i,(LaurentPolynomial.T 1-LaurentPolynomial.C ((u i):R))) ∣ f := by
  have hh:=laurent_prod_linear_dvd f (Finset.univ.image u) (by
    intro v hv
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
    exact h i)
  simpa only [Finset.prod_image (fun i _ j _ hij => hu hij)] using hh

end

 

 

noncomputable section
open scoped LaurentPolynomial Classical

def monomialUnit {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz:z≠0) : (Laurent n)ˣ where
  val := monomialL e z
  inv := monomialL (-e) z⁻¹
  val_inv := by simp [monomialL_mul,hz]
  inv_val := by simp [monomialL_mul,hz]

lemma peelLaurentEquiv_insert {n : ℕ} (i : Fin (n+1)) (f : Laurent n) :
    peelLaurentEquiv i (insertLaurent i f)=LaurentPolynomial.C f := by
  have h : (peelLaurentEquiv i).toRingHom.comp (insertLaurent i)=LaurentPolynomial.C := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change peelLaurentEquiv i (insertLaurent i (monomialL _ _))=_
    all_goals
      rw [insertLaurent_monomial,peelLaurentEquiv_monomial]
      simp only [Fin.insertNth_apply_same,Fin.removeNth_insertNth]
      rfl
  exact DFunLike.congr_fun h f

 
def substituteLaurent {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ) :
    Laurent (n+1) →+* Laurent n :=
  (LaurentPolynomial.eval₂ (RingHom.id _) u).comp (peelLaurentEquiv i).toRingHom

@[simp] lemma substituteLaurent_insert {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ)
    (f : Laurent n) : substituteLaurent i u (insertLaurent i f)=f := by
  change LaurentPolynomial.eval₂ (RingHom.id _) u (peelLaurentEquiv i (insertLaurent i f))=f
  rw [peelLaurentEquiv_insert,LaurentPolynomial.eval₂_C]
  rfl

 
def cosineCollisionRoots {R : Type*} [CommRing R] (a u : Rˣ) : Fin 4 → Rˣ :=
  ![u,-u,a⁻¹*u⁻¹,-(a⁻¹*u⁻¹)]

def cosineCollisionPacket {R : Type*} [CommRing R] (a u : Rˣ) : LaurentPolynomial R :=
  LaurentPolynomial.C (a:R)*LaurentPolynomial.T 2+
    LaurentPolynomial.C ((a⁻¹:Rˣ):R)*LaurentPolynomial.T (-2)-
    LaurentPolynomial.C ((a:R)*(u:R)^2+((a⁻¹:Rˣ):R)*((u⁻¹:Rˣ):R)^2)

lemma cosineCollision_factorization {R : Type*} [CommRing R] (a u : Rˣ) :
    (∏ k:Fin 4, (LaurentPolynomial.T 1-LaurentPolynomial.C ((cosineCollisionRoots a u k):R)))=
      (LaurentPolynomial.C ((a⁻¹:Rˣ):R)*LaurentPolynomial.T 2)*cosineCollisionPacket a u := by
  simp only [cosineCollisionRoots,Fin.prod_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one,Units.val_neg,Units.val_mul,
    map_neg,map_mul,cosineCollisionPacket,map_add,map_pow]
  have h2 : (LaurentPolynomial.T (1:ℤ) : LaurentPolynomial R)^2=LaurentPolynomial.T 2 := by
    rw [pow_two,←LaurentPolynomial.T_add]; rfl
  have h4 : (LaurentPolynomial.T (1:ℤ) : LaurentPolynomial R)^4=LaurentPolynomial.T 2*LaurentPolynomial.T 2 := by
    rw [←h2]; ring
  have haa : LaurentPolynomial.C ((a⁻¹:Rˣ):R)*LaurentPolynomial.C (a:R)=1 := by
    rw [←map_mul]; simp
  have huu : LaurentPolynomial.C ((u⁻¹:Rˣ):R)*LaurentPolynomial.C (u:R)=1 := by
    rw [←map_mul]; simp
  have hT : (LaurentPolynomial.T (2:ℤ) : LaurentPolynomial R)*LaurentPolynomial.T (-2)=1 := by
    rw [←LaurentPolynomial.T_add]; rfl
  linear_combination
    ((LaurentPolynomial.T 1)^2+LaurentPolynomial.T 2)*h2 +
    (LaurentPolynomial.C (u:R)^2+LaurentPolynomial.C ((a⁻¹:Rˣ):R)^2*LaurentPolynomial.C ((u⁻¹:Rˣ):R)^2)*(-h2) -
    (LaurentPolynomial.T 2)^2*haa +
    (LaurentPolynomial.C (u:R)^2*LaurentPolynomial.T 2)*haa +
    LaurentPolynomial.C ((a⁻¹:Rˣ):R)^2*((LaurentPolynomial.C ((u⁻¹:Rˣ):R)*LaurentPolynomial.C (u:R)+1)*huu-hT)

lemma cosineCollisionPacket_dvd {R : Type*} [CommRing R] [IsDomain R]
    (a u : Rˣ) (hi:Function.Injective (cosineCollisionRoots a u)) (f : LaurentPolynomial R)
    (h:∀ k,LaurentPolynomial.eval₂ (RingHom.id R) (cosineCollisionRoots a u k) f=0) :
    cosineCollisionPacket a u ∣ f := by
  have hh:=laurent_prod_linear_indexed_dvd (cosineCollisionRoots a u) hi f h
  rw [cosineCollision_factorization] at hh
  exact dvd_trans (dvd_mul_left _ _) hh

end

 

 

noncomputable section
open Finset

theorem pairFirst_injective (n : ℕ) : Function.Injective (pairFirst n) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [pairFirst] at this
  omega

theorem pairSecond_injective (n : ℕ) : Function.Injective (pairSecond n) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [pairSecond] at this
  omega

theorem upperPair_incident_iff {n : ℕ} (i j v : Fin n) (h : i ≠ j) :
    ((upperPair i j h).val.1 = v ∨ (upperPair i j h).val.2 = v) ↔ i = v ∨ j = v := by
  unfold upperPair
  split_ifs <;> simp [or_comm]

theorem pairIndex_unique {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i j : Fin (n/2)) (v : Fin n)
    (hi : σ (pairFirst n i) = v ∨ σ (pairSecond n i) = v)
    (hj : σ (pairFirst n j) = v ∨ σ (pairSecond n j) = v) : i = j := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact pairFirst_injective n (σ.injective (hi.trans hj.symm))
  · exact False.elim (pairFirst_ne_pairSecond i j (σ.injective (hi.trans hj.symm)))
  · exact False.elim (pairFirst_ne_pairSecond j i (σ.injective (hj.trans hi.symm)))
  · exact pairSecond_injective n (σ.injective (hi.trans hj.symm))

 
theorem selectedPairs_incident_unique {n : ℕ} (σ : Equiv.Perm (Fin n))
    (e f : UpperPair n) (he : e ∈ selectedPairs σ) (hf : f ∈ selectedPairs σ)
    (v : Fin n) (hev : e.val.1 = v ∨ e.val.2 = v) (hfv : f.val.1 = v ∨ f.val.2 = v) :
    e = f := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hf
  apply congrArg (permutationPair σ)
  apply pairIndex_unique σ i j v
  · exact (upperPair_incident_iff _ _ _ _).mp hev
  · exact (upperPair_incident_iff _ _ _ _).mp hfv

 
theorem pairIndex_cover {n : ℕ} (hn : n % 2 = 0) (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    ∃ i : Fin (n/2), σ (pairFirst n i) = v ∨ σ (pairSecond n i) = v := by
  let p := σ.symm v
  let i : Fin (n/2) := ⟨p.val/2, by have := p.isLt; omega⟩
  refine ⟨i,?_⟩
  by_cases hp : p.val%2 = 0
  · left
    have h : pairFirst n i = p := by apply Fin.ext; dsimp [pairFirst,i]; omega
    rw [h]
    exact σ.apply_symm_apply v
  · right
    have h : pairSecond n i = p := by apply Fin.ext; dsimp [pairSecond,i]; omega
    rw [h]
    exact σ.apply_symm_apply v

def firstPair (m : ℕ) : UpperPair (2*(m+1)) := ⟨(0,1), by
  change (0 : Fin (2*m+2)) < 1
  exact Fin.zero_lt_one⟩

theorem firstPair_eq_upperPair (m : ℕ) :
    firstPair m = upperPair 0 1 (by exact ne_of_lt (firstPair m).property) := by
  have h : (0 : Fin (2*(m+1))) < 1 := (firstPair m).property
  simp only [upperPair, h, dite_true, firstPair]

 
def repairFirstDenominator {R : Type*} [One R] {m : ℕ}
    (D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R) :
    Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R := fun i j =>
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else D i j

 
def isolateFirstNumerator {R : Type*} [Zero R] {m : ℕ}
    (N : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R) :
    Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R := fun i j =>
  if (i = 0 ∧ j ≠ 1) ∨ (j = 0 ∧ i ≠ 1) then 0 else N i j

theorem isolateFirstNumerator_selected {R : Type*} [Zero R] {m : ℕ}
    (N : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R)
    (σ : Equiv.Perm (Fin (2*(m+1)))) (hσ : firstPair m ∈ selectedPairs σ)
    (i : Fin (2*(m+1)/2)) :
    isolateFirstNumerator N (σ (pairFirst _ i)) (σ (pairSecond _ i)) =
      N (σ (pairFirst _ i)) (σ (pairSecond _ i)) := by
  classical
  unfold isolateFirstNumerator
  rw [ite_eq_right]
  rintro (h | h)
  all_goals
    have he : permutationPair σ i = firstPair m := selectedPairs_incident_unique σ _ _
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) hσ 0
      ((upperPair_incident_iff _ _ _ _).mpr (by aesop)) (Or.inl rfl)
    rw [firstPair_eq_upperPair] at he
    rcases (upperPair_eq_iff _ _).mp he with hc | hc
    · simp_all
    · simp_all

 

theorem repairFirstDenominator_compl {R : Type*} [One R] {m : ℕ}
    (D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R)
    (σ : Equiv.Perm (Fin (2*(m+1)))) (hσ : firstPair m ∈ selectedPairs σ)
    (e : UpperPair (2*(m+1))) (he : e ∈ (selectedPairs σ)ᶜ) :
    repairFirstDenominator D e.val.1 e.val.2 = D e.val.1 e.val.2 := by
  unfold repairFirstDenominator
  rw [ite_eq_right]
  rintro (h | h)
  · have heq : e = firstPair m := Subtype.ext (Prod.ext h.1 h.2)
    exact (Finset.mem_compl.mp he) (heq.symm ▸ hσ)
  · have := e.property
    rw [h.1,h.2] at this
    exact (not_lt_of_ge (firstPair m).property.le) this

end
end CriticalStrip.Diagram

end OAI
