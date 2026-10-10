import OAI.Analysis.Littlewood.FiniteRank

namespace OAI

universe uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

lemma choose_odd_lengths {J : Type uJ} [Fintype J] [Nonempty J]
    (w : J → ℝ) (hw : ∀ j, 0<w j) (hs : 2*∑ j, w j<1) :
    ∃ d : J → ℕ, ∀ i, w i < (2*(d i : ℝ)+1)/(2*∑ j, (2*(d j : ℝ)+1)) := by
  let r : ℝ := Fintype.card J
  have hr : 0<r := Nat.cast_pos.mpr Fintype.card_pos
  let M : ℝ := (3*r+1)/(1-2*∑ j, w j)
  have hM : 0<M := by dsimp [M]; positivity
  let d : J → ℕ := fun j ↦ ⌈M*w j⌉₊
  have hdi (i : J) : M*w i ≤ (d i : ℝ) := Nat.le_ceil _
  have hdi' (i : J) : (d i : ℝ)<M*w i+1 := Nat.ceil_lt_add_one (mul_pos hM (hw i)).le
  have hL : (∑ j, (2*(d j : ℝ)+1)) < M := by
    have hlt : (∑ j, (2*(d j : ℝ)+1)) < ∑ j, (2*(M*w j)+3) := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
      intro j _; linarith [hdi' j]
    have he : (∑ j, (2*(M*w j)+3)) = 2*M*(∑ j, w j)+3*r := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul]
      dsimp [r]; ring
    rw [he] at hlt
    have heM : M*(1-2*∑ j, w j)=3*r+1 := by
      dsimp [M]; field_simp [ne_of_gt (sub_pos.mpr hs)]
    nlinarith
  refine ⟨d,?_⟩
  intro i
  have hL0 : 0<(∑ j, (2*(d j : ℝ)+1)) :=
    Finset.sum_pos (fun j _ ↦ by positivity) Finset.univ_nonempty
  rw [lt_div_iff₀ (by positivity)]
  have hmul := mul_lt_mul_of_pos_right hL (hw i)
  nlinarith [hdi i]

variable {r : ℕ}
def slotPrefix (L : Fin r → ℕ) (i : Fin r) : ℕ := ∑ j ∈ Finset.Iio i, L j

def periodLength (L : Fin r → ℕ) : ℕ := ∑ j, L j

lemma prefix_add_length_le (L : Fin r → ℕ) (i : Fin r) :
    slotPrefix L i+L i ≤ periodLength L := by
  classical
  have hi : i∉Finset.Iio i := by simp
  dsimp [slotPrefix,periodLength]
  rw [add_comm,← Finset.sum_insert hi]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma prefix_separated (L : Fin r → ℕ) {i j : Fin r} (hij : i<j) :
    slotPrefix L i+L i ≤ slotPrefix L j := by
  classical
  have hi : i∉Finset.Iio i := by simp
  change (∑ k ∈ Finset.Iio i, L k)+L i ≤ ∑ k ∈ Finset.Iio j, L k
  rw [add_comm,← Finset.sum_insert hi]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rcases Finset.mem_insert.mp hk with h | h
  · subst k; simpa using hij
  · exact Finset.mem_Iio.mpr (lt_trans (Finset.mem_Iio.mp h) hij)

/-- Site immediately to the left of a slot. The actual sites are
left+1,...,left+L_i. Each full chunk keeps R-1 translated periods. -/
def slotLeft (L : Fin r → ℕ) (R : ℕ) (shift chunk period : ℕ) (i : Fin r) : ℕ :=
  chunk*(R*periodLength L)+period*periodLength L+shift+slotPrefix L i

lemma slotLeft_bounds (L : Fin r → ℕ) (R : ℕ) {shift chunk period : ℕ}
    (hs : shift<periodLength L) (hp : period+1<R) (i : Fin r) :
    chunk*(R*periodLength L) ≤ slotLeft L R shift chunk period i ∧
    slotLeft L R shift chunk period i+L i < (chunk+1)*(R*periodLength L) := by
  have hi := prefix_add_length_le L i
  have hp' : (period+2)*periodLength L ≤ R*periodLength L :=
    Nat.mul_le_mul_right _ (by omega)
  dsimp [slotLeft]
  constructor
  · omega
  · simp only [Nat.add_mul] at hp' ⊢
    omega

lemma slots_separated_same_chunk (L : Fin r → ℕ) (R shift chunk : ℕ)
    {p q : ℕ} {i j : Fin r} (h : p<q ∨ p=q ∧ i<j) :
    slotLeft L R shift chunk p i+L i ≤ slotLeft L R shift chunk q j := by
  have hi := prefix_add_length_le L i
  dsimp [slotLeft]
  rcases h with h | ⟨rfl,h⟩
  · have hp : (p+1)*periodLength L ≤ q*periodLength L :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hp
    omega
  · have hj := prefix_separated L h
    omega

lemma slots_separated_chunks (L : Fin r → ℕ) (R : ℕ) {s t k l p q : ℕ}
    (hs : s<periodLength L) (hp : p+1<R) (hkl : k<l) (i j : Fin r) :
    slotLeft L R s k p i+L i < slotLeft L R t l q j := by
  have hleft := (slotLeft_bounds L R (chunk := k) hs hp i).2
  have hle : (k+1)*(R*periodLength L) ≤ l*(R*periodLength L) :=
    Nat.mul_le_mul_right _ (by omega)
  dsimp [slotLeft] at *
  omega

def signedSite (q : ℕ) (e : Bool) (x : ℕ) : ZMod q := if e then x else -x

lemma signedSite_injective {q A x y : ℕ} (hq : 2*A<q)
    (hx : 0<x) (hxA : x≤A) (hy : 0<y) (hyA : y≤A) (e f : Bool) :
    signedSite q e x=signedSite q f y ↔ e=f ∧ x=y := by
  have hxy : x+y<q := by omega
  have hn : (x : ZMod q)≠-(y : ZMod q) := by
    intro h
    have hz : ((x+y : ℕ) : ZMod q)=0 := by push_cast; rw [h]; simp
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have he := Nat.eq_zero_of_dvd_of_lt hd hxy
    omega
  have heq : (x : ZMod q)=(y : ZMod q) ↔ x=y := by
    rw [ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (by omega : x<q),Nat.mod_eq_of_lt (by omega : y<q)]
  cases e <;> cases f <;> simp [signedSite,heq,hn, neg_eq_iff_eq_neg]

abbrev oddLengths (d : Fin r → ℕ) : Fin r → ℕ := fun i ↦ 2*d i+1

def siteCenter (d : Fin r → ℕ) (R shift chunk period : ℕ) (i : Fin r) : ℕ :=
  slotLeft (oddLengths d) R shift chunk period i+d i+1

lemma periodLength_pos (d : Fin r → ℕ) (i : Fin r) : 0<periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
  omega

lemma centerOffset_bounds (d : Fin r → ℕ) (i : Fin r) :
    0<slotPrefix (oddLengths d) i+d i+1 ∧
    slotPrefix (oddLengths d) i+d i+1≤periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
  omega

lemma siteCenter_bounds (d : Fin r → ℕ) {R shift chunk period : ℕ}
    (hs : shift<periodLength (oddLengths d)) (hp : period+1<R) (i : Fin r) :
    chunk*(R*periodLength (oddLengths d)) < siteCenter d R shift chunk period i ∧
    siteCenter d R shift chunk period i < (chunk+1)*(R*periodLength (oddLengths d)) := by
  obtain ⟨hlo,hhi⟩ := slotLeft_bounds (oddLengths d) R (chunk := chunk) hs hp i
  dsimp [siteCenter,oddLengths] at *
  omega

lemma siteCenter_chunk (d : Fin r → ℕ) {R shift chunk period : ℕ}
    (hs : shift<periodLength (oddLengths d)) (hp : period+1<R) (i : Fin r) :
    siteCenter d R shift chunk period i / (R*periodLength (oddLengths d)) = chunk := by
  have hR : 0<R := by omega
  have hL := periodLength_pos d i
  have hc := (siteCenter_bounds d (chunk := 0) hs hp i).2
  dsimp [siteCenter,slotLeft] at hc ⊢
  simp only [Nat.zero_mul,Nat.zero_add,Nat.zero_add,Nat.one_mul] at hc
  have he : chunk*(R*periodLength (oddLengths d))+period*periodLength (oddLengths d)+shift+
      slotPrefix (oddLengths d) i+d i+1 =
      (period*periodLength (oddLengths d)+shift+slotPrefix (oddLengths d) i+d i+1)+
      chunk*(R*periodLength (oddLengths d)) := by omega
  rw [he,Nat.add_mul_div_right _ _ (mul_pos hR hL),Nat.div_eq_of_lt hc]
  simp

lemma interior_center_exists (d : Fin r → ℕ) {R t : ℕ}
    (ht : t<(R-2)*periodLength (oddLengths d)) (i : Fin r) :
    ∃ p s : ℕ, p+1<R ∧ s<periodLength (oddLengths d) ∧
      p*periodLength (oddLengths d)+s+slotPrefix (oddLengths d) i+d i+1 =
        periodLength (oddLengths d)+1+t := by
  let L := periodLength (oddLengths d)
  let c := slotPrefix (oddLengths d) i+d i+1
  have hL : 0<L := periodLength_pos d i
  have hc := centerOffset_bounds d i
  change 0<c ∧ c≤L at hc
  let u := L+1+t-c
  have hR : 2<R := by
    by_contra h
    have he : R-2=0 := by omega
    rw [he,Nat.zero_mul] at ht
    omega
  have hu : u<(R-1)*L := by
    have he : (R-1)*L=(R-2)*L+L := by
      rw [show R-1=(R-2)+1 by omega,Nat.add_mul,Nat.one_mul]
    dsimp [u,L] at *
    omega
  refine ⟨u/L,u%L,?_,Nat.mod_lt _ hL,?_⟩
  · have hh := (Nat.div_lt_iff_lt_mul hL).mpr hu
    omega
  · have he := Nat.mod_add_div u L
    rw [Nat.mul_comm L] at he
    have hcu : c≤L+1+t := by omega
    dsimp [u,c,L] at *
    omega

def interiorSite (d : Fin r → ℕ) (R k t : ℕ) : ℕ :=
  k*(R*periodLength (oddLengths d))+periodLength (oddLengths d)+1+t

lemma interiorSite_bounds (d : Fin r → ℕ) {R k t : ℕ} (i : Fin r)
    (ht : t<(R-2)*periodLength (oddLengths d)) :
    k*(R*periodLength (oddLengths d)) < interiorSite d R k t ∧
    interiorSite d R k t < (k+1)*(R*periodLength (oddLengths d)) := by
  obtain ⟨p,s,hp,hs,he⟩ := interior_center_exists d ht i
  have he' : interiorSite d R k t=siteCenter d R s k p i := by
    dsimp [interiorSite,siteCenter,slotLeft]
    omega
  rw [he']
  exact siteCenter_bounds d hs hp i

lemma interiorSite_chunk (d : Fin r → ℕ) {R k t : ℕ} (i : Fin r)
    (ht : t<(R-2)*periodLength (oddLengths d)) :
    interiorSite d R k t/(R*periodLength (oddLengths d))=k := by
  obtain ⟨p,s,hp,hs,he⟩ := interior_center_exists d ht i
  have he' : interiorSite d R k t=siteCenter d R s k p i := by
    dsimp [interiorSite,siteCenter,slotLeft]
    omega
  rw [he']
  exact siteCenter_chunk d hs hp i

lemma interior_signed_injective (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    Function.Injective (fun x : (Fin K × Fin ((R-2)*periodLength (oddLengths d))) × Bool ↦
      signedSite q x.2 (interiorSite d R x.1.1 x.1.2)) := by
  rintro ⟨⟨k,t⟩,e⟩ ⟨⟨l,u⟩,f⟩ he
  have hk := interiorSite_bounds d (k := (k : ℕ)) i t.isLt
  have hl := interiorSite_bounds d (k := (l : ℕ)) i u.isLt
  have hk' : interiorSite d R k t ≤ K*(R*periodLength (oddLengths d)) :=
    hk.2.le.trans (Nat.mul_le_mul_right _ (by omega))
  have hl' : interiorSite d R l u ≤ K*(R*periodLength (oddLengths d)) :=
    hl.2.le.trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨hef,he'⟩ := (signedSite_injective hq (by omega) hk' (by omega) hl' e f).mp he
  have hkl : (k : ℕ)=(l : ℕ) := by
    have hc := congrArg (fun c ↦ c/(R*periodLength (oddLengths d))) he'
    simpa only [interiorSite_chunk d i t.isLt,interiorSite_chunk d i u.isLt] using hc
  have htu : (t : ℕ)=(u : ℕ) := by
    dsimp [interiorSite] at he'
    rw [hkl] at he'
    omega
  cases Fin.ext hkl
  cases Fin.ext htu
  cases hef
  rfl

abbrev SlotChoices (d : Fin r → ℕ) (K : ℕ) :=
  Fin K → Fin (periodLength (oddLengths d)) × Bool

def slotHit (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (ω : SlotChoices d K) (u : ZMod q) : Prop :=
  ∃ k : Fin K, ∃ p : Fin (R-1),
    u=signedSite q (ω k).2 (siteCenter d R (ω k).1 k p i)

lemma interior_hit_coordinate (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q)
    (k : Fin K) (t : Fin ((R-2)*periodLength (oddLengths d))) (e : Bool) :
    ∃ s : Fin (periodLength (oddLengths d)), ∀ ω : SlotChoices d K,
      slotHit d R K q i ω (signedSite q e (interiorSite d R k t)) ↔ ω k=(s,e) := by
  obtain ⟨p,s,hp,hs,he⟩ := interior_center_exists d t.isLt i
  let p₀ : Fin (R-1) := ⟨p,by omega⟩
  let s₀ : Fin (periodLength (oddLengths d)) := ⟨s,hs⟩
  have he' : interiorSite d R k t=siteCenter d R s₀ k p₀ i := by
    dsimp [interiorSite,siteCenter,slotLeft,s₀,p₀]
    omega
  refine ⟨s₀,?_⟩
  intro ω
  constructor
  · rintro ⟨l,u,hu⟩
    have hk := interiorSite_bounds d (k := (k : ℕ)) i t.isLt
    have hl := siteCenter_bounds d (R := R) (chunk := (l : ℕ)) (period := (u : ℕ)) (ω l).1.isLt (by have := u.isLt; omega) i
    have hk' : interiorSite d R k t≤K*(R*periodLength (oddLengths d)) :=
      hk.2.le.trans (Nat.mul_le_mul_right _ (by omega))
    have hl' : siteCenter d R (ω l).1 l u i≤K*(R*periodLength (oddLengths d)) :=
      hl.2.le.trans (Nat.mul_le_mul_right _ (by omega))
    obtain ⟨hes,hc⟩ := (signedSite_injective hq (by omega) hk' (by omega) hl' e (ω l).2).mp hu
    have hkl : (k : ℕ)=(l : ℕ) := by
      have hc' := congrArg (fun n ↦ n/(R*periodLength (oddLengths d))) hc
      simpa only [interiorSite_chunk d i t.isLt,
        siteCenter_chunk d (R := R) (period := (u : ℕ)) (ω l).1.isLt (by have := u.isLt; omega) i] using hc'
    have hkl' : k=l := Fin.ext hkl
    subst l
    have hp' : p*periodLength (oddLengths d)+s=
        (u : ℕ)*periodLength (oddLengths d)+(ω k).1 := by
      rw [he'] at hc
      dsimp [siteCenter,slotLeft,p₀,s₀] at hc
      omega
    have hmod := congrArg (fun n ↦ n%periodLength (oddLengths d)) hp'
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hs, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt (ω k).1.isLt] at hmod
    apply Prod.ext
    · exact Fin.ext hmod.symm
    · exact hes.symm
  · intro hω
    refine ⟨k,p₀,?_⟩
    rw [hω]
    exact congrArg (signedSite q e) he'

/-- The finite residue neighborhood used to detect same-chunk collisions. -/
def shortResidues (q B : ℕ) : Finset (ZMod q) :=
  (Finset.Icc (-(B : ℤ)) B).image (fun c : ℤ ↦ (c : ZMod q))

lemma shortResidues_card (q B : ℕ) : (shortResidues q B).card≤2*B+1 := by
  apply Finset.card_image_le.trans
  simp [Int.card_Icc]
  omega

lemma same_chunk_collision (d : Fin r → ℕ) (R q : ℕ) (i : Fin r)
    {k t u : ℕ} (ht : t<(R-2)*periodLength (oddLengths d))
    (hu : u<(R-2)*periodLength (oddLengths d)) (e f : Bool) :
    signedSite q e (interiorSite d R k t)+signedSite q f (interiorSite d R k u)
      ∈shortResidues q (R*periodLength (oddLengths d)) ∨
    signedSite q e (interiorSite d R k t)-signedSite q f (interiorSite d R k u)
      ∈shortResidues q (R*periodLength (oddLengths d)) := by
  have ht' := interiorSite_bounds d (k := k) i ht
  have hu' := interiorSite_bounds d (k := k) i hu
  simp only [Nat.add_mul, Nat.one_mul] at ht' hu'
  let a : ℤ := interiorSite d R k t
  let b : ℤ := interiorSite d R k u
  have hdiff : a-b∈Finset.Icc (-(R*periodLength (oddLengths d) : ℕ) : ℤ)
      (R*periodLength (oddLengths d)) := by
    simp only [Finset.mem_Icc]
    dsimp [a,b]

    constructor <;> omega
  have hdiff' : b-a∈Finset.Icc (-(R*periodLength (oddLengths d) : ℕ) : ℤ)
      (R*periodLength (oddLengths d)) := by
    simp only [Finset.mem_Icc] at hdiff ⊢
    constructor <;> omega
  have hd : ((a-b : ℤ) : ZMod q)∈shortResidues q (R*periodLength (oddLengths d)) :=
    Finset.mem_image.mpr ⟨a-b,hdiff,rfl⟩
  have hd' : ((b-a : ℤ) : ZMod q)∈shortResidues q (R*periodLength (oddLengths d)) :=
    Finset.mem_image.mpr ⟨b-a,hdiff',rfl⟩
  dsimp [a,b] at hd hd'
  push_cast at hd hd'
  cases e <;> cases f <;> simp only [signedSite,Bool.false_eq_true,↓reduceIte]
  · exact Or.inr (by simpa only [sub_eq_add_neg,neg_neg,add_comm] using hd')
  · exact Or.inl (by simpa only [sub_eq_add_neg,add_comm] using hd')
  · exact Or.inl (by simpa only [sub_eq_add_neg] using hd)
  · exact Or.inr hd

end
end Packing
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {r : ℕ}

abbrev InteriorCatalog (d : Fin r → ℕ) (R K : ℕ) :=
  Fin K × Fin ((R-2)*periodLength (oddLengths d)) × Bool

def catalogValue (d : Fin r → ℕ) (R K q : ℕ) (c : InteriorCatalog d R K) : ZMod q :=
  signedSite q c.2.2 (interiorSite d R c.1 c.2.1)

def catalogSet (d : Fin r → ℕ) (R K q : ℕ) : Finset (ZMod q) :=
  Finset.univ.image (catalogValue d R K q)

lemma catalogValue_injective (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    Function.Injective (catalogValue d R K q) := by
  rintro ⟨k,t,b⟩ ⟨l,u,e⟩ h
  have hh : ((k,t),b)=((l,u),e) := interior_signed_injective d R K q i hq h
  obtain ⟨hkt,hbe⟩ := Prod.mk.inj hh
  cases hkt
  cases hbe
  rfl

lemma catalogSet_card (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    (catalogSet d R K q).card=2*K*((R-2)*periodLength (oddLengths d)) := by
  rw [catalogSet,Finset.card_image_of_injective _ (catalogValue_injective d R K q i hq)]
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  ring

lemma catalog_chunk_system (d : Fin r → ℕ) (R K q : ℕ) [NeZero q] (i₀ : Fin r)
    (hK : 0<K) (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    ∃ chunk : ZMod q → Fin K,
      (∀ c : InteriorCatalog d R K, chunk (catalogValue d R K q c)=c.1) ∧
      (∀ i t, t∈catalogSet d R K q →
        ∃ a : Fin (periodLength (oddLengths d)) × Bool,
          ∀ ω : SlotChoices d K, slotHit d R K q i ω t ↔ ω (chunk t)=a) ∧
      (∀ k, (Finset.univ.filter (fun t : ZMod q ↦ chunk t=k)).card≤
        q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) ∧
      (∀ t∈catalogSet d R K q, ∀ u∈catalogSet d R K q, chunk t=chunk u →
        t+u∈shortResidues q (R*periodLength (oddLengths d)) ∨
        t-u∈shortResidues q (R*periodLength (oddLengths d))) := by
  classical
  let chunk : ZMod q → Fin K := fun t ↦
    if h : ∃ c : InteriorCatalog d R K, catalogValue d R K q c=t then h.choose.1
    else ⟨0,hK⟩
  have hinj := catalogValue_injective d R K q i₀ hq
  have hchunk (c : InteriorCatalog d R K) : chunk (catalogValue d R K q c)=c.1 := by
    dsimp [chunk]
    split_ifs with h
    · exact congrArg Prod.fst (hinj h.choose_spec)
    · exact (h ⟨c,rfl⟩).elim
  refine ⟨chunk,hchunk,?_,?_,?_⟩
  · intro i t ht
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨s,hs⟩ := interior_hit_coordinate d R K q i hq c.1 c.2.1 c.2.2
    refine ⟨(s,c.2.2),?_⟩
    rw [hchunk]
    exact hs
  · intro k
    let T : Finset (ZMod q) := Finset.univ.image (fun c :
      Fin ((R-2)*periodLength (oddLengths d)) × Bool ↦ catalogValue d R K q (k,c))
    have hsub : (Finset.univ.filter (fun t : ZMod q ↦ chunk t=k)) ⊆
        ((Finset.univ : Finset (ZMod q)) \ catalogSet d R K q) ∪ T := by
      intro t ht
      by_cases hg : t∈catalogSet d R K q
      · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hg
        have hk : c.1=k := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and,hchunk] using ht
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨c.2,Finset.mem_univ _,by cases hk; rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hg⟩)
    have hT : T.card≤2*((R-2)*periodLength (oddLengths d)) := by
      apply Finset.card_image_le.trans_eq
      simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
      ring
    calc
      _ ≤ (((Finset.univ : Finset (ZMod q)) \ catalogSet d R K q) ∪ T).card := Finset.card_le_card hsub
      _ ≤ ((Finset.univ : Finset (ZMod q)) \ catalogSet d R K q).card+T.card := Finset.card_union_le _ _
      _ ≤ _ := by
        rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,ZMod.card]
        omega
  · intro t ht u hu htu
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hu
    have hce : c.1=e.1 := by simpa only [hchunk] using htu
    dsimp [catalogValue]
    rw [hce]
    exact same_chunk_collision d R q i₀ c.2.1.isLt e.2.1.isLt c.2.2 e.2.2

lemma actual_centers_injective (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) (ω : SlotChoices d K) :
    Function.Injective (fun c : Fin K × Fin (R-1) ↦
      signedSite q (ω c.1).2 (siteCenter d R (ω c.1).1 c.1 c.2 i)) := by
  intro c e h
  have hc : (c.2 : ℕ)+1<R := by have := c.2.isLt; omega
  have he : (e.2 : ℕ)+1<R := by have := e.2.isLt; omega
  have hcb := siteCenter_bounds d (R := R) (chunk := (c.1 : ℕ)) (ω c.1).1.isLt hc i
  have heb := siteCenter_bounds d (R := R) (chunk := (e.1 : ℕ)) (ω e.1).1.isLt he i
  have hcB : siteCenter d R (ω c.1).1 c.1 c.2 i≤K*(R*periodLength (oddLengths d)) :=
    hcb.2.le.trans (Nat.mul_le_mul_right _ (by have := c.1.isLt; omega))
  have heB : siteCenter d R (ω e.1).1 e.1 e.2 i≤K*(R*periodLength (oddLengths d)) :=
    heb.2.le.trans (Nat.mul_le_mul_right _ (by have := e.1.isLt; omega))
  have hs := ((signedSite_injective hq (by omega) hcB (by omega) heB _ _).mp h).2
  have hk : c.1=e.1 := by
    apply Fin.ext
    have hh := congrArg (fun n ↦ n/(R*periodLength (oddLengths d))) hs
    simpa only [siteCenter_chunk d (ω c.1).1.isLt hc i,
      siteCenter_chunk d (ω e.1).1.isLt he i] using hh
  have hp : c.2=e.2 := by
    apply Fin.ext
    rw [hk] at hs
    dsimp [siteCenter,slotLeft] at hs
    have hmul : (c.2 : ℕ)*periodLength (oddLengths d)=
        (e.2 : ℕ)*periodLength (oddLengths d) := by omega
    exact Nat.eq_of_mul_eq_mul_right (periodLength_pos d i) hmul
  exact Prod.ext hk hp

attribute [local instance] Classical.propDecidable

lemma slotHit_card (d : Fin r → ℕ) (R K q : ℕ) [NeZero q] (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) (ω : SlotChoices d K) :
    (Finset.univ.filter (fun t : ZMod q ↦ slotHit d R K q i ω t)).card=K*(R-1) := by
  classical
  have he : (Finset.univ.filter (fun t : ZMod q ↦ slotHit d R K q i ω t))=
      Finset.univ.image (fun c : Fin K × Fin (R-1) ↦
        signedSite q (ω c.1).2 (siteCenter d R (ω c.1).1 c.1 c.2 i)) := by
    apply Finset.ext
    intro t

    rw [Finset.mem_filter]
    simp only [Finset.mem_univ,true_and,Finset.mem_image,slotHit]
    constructor
    · rintro ⟨k,p,h⟩; exact ⟨(k,p),h.symm⟩
    · rintro ⟨⟨k,p⟩,h⟩; exact ⟨k,p,h.symm⟩
  rw [he,Finset.card_image_of_injective _ (actual_centers_injective d R K q i hq ω)]
  simp

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI
