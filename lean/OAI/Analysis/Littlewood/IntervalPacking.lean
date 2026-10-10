import OAI.Analysis.Littlewood.SlotParameters

namespace OAI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

lemma scaled_slot_conditions {q v e p T n b r : ℝ} (hq : 0<q) (hp : 0<p)
    (hv : q^2≤v) (h1 : 1/q≤e*p) (h2 : T/q≤p) (h3 : T/q≤n-b)
    (h4 : b≤e*p/2) (h5 : n≤r) :
    T≤(v/q)*p ∧ T≤q*n-q*b ∧ v/q^2≤e*((v/q)*p) ∧
      (q*n)*(v/q^2)≤(r/p)*((v/q)*p) ∧
      (q*b)*(v/q^2)≤e*((v/q)*p)/2 := by
  let C := v/q^2
  have hC : 1≤C := (le_div_iff₀ (sq_pos_of_pos hq)).mpr (by simpa using hv)
  have hC0 : 0≤C := le_trans zero_le_one hC
  have hD : (v/q)*p=q*p*C := by dsimp [C]; field_simp
  have h1' : 1≤q*(e*p) := by simpa only [mul_comm] using (div_le_iff₀ hq).mp h1
  have h2' : T≤q*p := by simpa only [mul_comm] using (div_le_iff₀ hq).mp h2
  have h3' : T≤q*(n-b) := by simpa only [mul_comm] using (div_le_iff₀ hq).mp h3
  rw [hD]
  refine ⟨h2'.trans ?_,by nlinarith only [h3'],?_,?_,?_⟩
  · nlinarith only [hC,mul_pos hq hp]
  · change C≤e*(q*p*C)
    have h := mul_le_mul_of_nonneg_right h1' hC0
    nlinarith only [h]
  · change (q*n)*C≤(r/p)*(q*p*C)
    rw [show (r/p)*(q*p*C)=q*r*C by field_simp]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hq.le) hC0
  · change (q*b)*C≤e*(q*p*C)/2
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hq.le) hC0
    nlinarith only [h]

lemma choose_matching_loss {r L : ℕ} (hr : 0<r) (hL : 0<L) {t : ℝ}
    (ht0 : 0≤t) (ht : t<1/(2*L : ℝ)) :
    ∃ η : ℝ, 0<η ∧ η≤1 ∧ (r : ℝ)*t<(1-η)*((r : ℝ)/(2*L)) := by
  let η := (1-2*L*t)/2
  have hL' : (0 : ℝ)<2*L := by positivity
  have ht' := (lt_div_iff₀ hL').mp ht
  have hlt : t<(1-η)/(2*L) := by apply (lt_div_iff₀ hL').mpr; dsimp [η]; nlinarith
  have hr' : (0 : ℝ)<r := by exact_mod_cast hr
  refine ⟨η,by dsimp [η]; nlinarith,by dsimp [η]; nlinarith,?_⟩
  calc
    (r : ℝ)*t < r*((1-η)/(2*L)) := mul_lt_mul_of_pos_left hlt hr'
    _ = (1-η)*((r : ℝ)/(2*L)) := by ring

lemma integer_slot_matching {r m : ℕ} (hr : 2≤r)
    (a : Fin r → Fin m → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ))≠0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ))≠c • (fun k ↦ (a j k : ℚ)))
    (d : Fin r → ℕ) {t : ℝ} (ht0 : 0<t) (ht : t<1/(2*periodLength (oddLengths d) : ℝ)) :
    ∃ q R K : ℕ, q.Prime ∧ 3≤R ∧ 0<K ∧ 2*(K*(R*periodLength (oddLengths d)))<q ∧
      ∃ ω : SlotChoices d K, ∃ M : Finset (Fin m → ZMod q),
        (∀ y∈M, ∀ i, slotHit d R K q i ω (dotProduct (fun k ↦ (a i k : ZMod q)) y)) ∧
        (∀ y∈M, ∀ z∈M, y≠z → ∀ i,
          dotProduct (fun k ↦ (a i k : ZMod q)) y≠dotProduct (fun k ↦ (a i k : ZMod q)) z) ∧
        t*q<(M.card : ℝ) := by
  classical
  let i₀ : Fin r := ⟨0,by omega⟩
  let i₁ : Fin r := ⟨1,by omega⟩
  have hi : i₀≠i₁ := by intro h; have := congrArg Fin.val h; simp [i₀,i₁] at this
  have hr0 : 0<r := by omega
  let L := periodLength (oddLengths d)
  have hL : 0<L := periodLength_pos d i₀
  let p : ℝ := (1/(2*L : ℝ))^(r-1)
  have hp : 0<p := by dsimp [p]; positivity
  obtain ⟨η,hη,hη₁,hmargin⟩ := choose_matching_loss hr0 hL ht0.le ht
  obtain ⟨e,T,he,hT,hmatch⟩ := random_slot_matching (I := Fin r)
    (by simpa only [Fintype.card_fin] using (show 1≤r by omega)) (K₀ := (r : ℝ)/p) (by positivity) hη hη₁
  obtain ⟨R,hR,hBR,hSR,hNR,hMR⟩ := packing_choose_R hr0 hL he hp hmargin
  have hR0 : 0<R := by omega
  obtain ⟨Q,hQ⟩ := Filter.eventually_atTop.mp (packing_eventual_parameters hL hR0 he hp hBR hSR hNR hMR (T := T))
  obtain ⟨Q₀,hQ₀⟩ := integer_rows_eventual_pair_rank a ha hnp
  obtain ⟨q,hqq,hprime⟩ := Nat.exists_infinite_primes (max Q (max (Q₀+1) (2*R*L+1)))
  have hq0 : 0<q := hprime.pos
  have : Fact q.Prime := ⟨hprime⟩
  have hqpos : (0 : ℝ)<q := by exact_mod_cast hq0
  have hqq' : 2*R*L<q := by omega
  have hqpar := hQ q (by omega)
  let K := chunkCount (2*R*L) q
  have hK : 0<K := chunkCount_pos (by positivity) hqq'
  have hqslot : 2*(K*(R*L))<q := by
    have h := (chunkCount_bounds (show 0<2*R*L by positivity) hq0).1
    nlinarith only [h]
  let g : Fin r → (Fin m → ZMod q) →ₗ[ZMod q] ZMod q :=
    fun i ↦ dotForm (fun k ↦ (a i k : ZMod q))
  have hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j)) :=
    hQ₀ q inferInstance (by omega)
  have hg (i : Fin r) : Function.Surjective (g i) := by
    have hj : ∃ j : Fin r, i≠j := by
      by_cases h : i=i₀
      · exact ⟨i₁,h ▸ hi⟩
      · exact ⟨i₀,h⟩
    obtain ⟨j,hj⟩ := hj
    intro s
    obtain ⟨y,hy⟩ := hpair i j hj (s,0)
    exact ⟨y,congrArg Prod.fst hy⟩
  have hV : (q : ℝ)^2≤Fintype.card (Fin m → ZMod q) := by
    have h := Fintype.card_le_of_surjective _ (hpair i₀ i₁ hi)
    have h' : q*q≤Fintype.card (Fin m → ZMod q) := by
      simpa only [Fintype.card_prod,ZMod.card] using h
    rw [pow_two]
    exact_mod_cast h'
  have hc := scaled_slot_conditions hqpos hp hV hqpar.1 hqpar.2.1 hqpar.2.2.1
    hqpar.2.2.2.1 hqpar.2.2.2.2.1
  have : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  obtain ⟨ω,M,hM,hdis,hsize⟩ := hmatch g (fun i s ω ↦ slotHit d R K q i ω s)
    p (max (packingAV r L R q) 0) ((q : ℝ)*packingBV r L R e p q) ((q : ℝ)*packingNV r L R q)
    hg hpair hp (mul_nonneg hqpos.le (packingBV_nonneg r L R q e p))
    (fun i ↦ (concrete_slot_variance_le_av d R i₀ (by omega) hqq' g hg hpair i).trans (le_max_left _ _))
    (by simp only [Fintype.card_fin,ZMod.card,packingBV]; ring_nf; exact le_rfl)
    (fun ω ↦ concrete_slot_nv d i₀ (by omega) ω)
    (by simpa only [ZMod.card] using hc.1)
    hc.2.1
    (by simpa only [ZMod.card] using hc.2.2.1)
    (by simpa only [ZMod.card] using hc.2.2.2.1)
    (by simpa only [ZMod.card] using hc.2.2.2.2)
  refine ⟨q,R,K,hprime,hR,hK,hqslot,ω,M,?_,?_,?_⟩
  · intro y hy i
    have hm := hM hy
    simp only [slotEdges,Finset.mem_filter,Finset.mem_univ,true_and] at hm
    exact hm i
  · intro y hy z hz hyz i hEq
    have hd := hdis hy hz hyz
    have hyv : (i,g i y)∈slotSupport g y := by simp [slotSupport]
    change g i y=g i z at hEq
    have hzv : (i,g i y)∈slotSupport g z := by rw [hEq]; simp [slotSupport]
    exact Finset.disjoint_left.mp hd hyv hzv
  · have hstrict := mul_lt_mul_of_pos_right hqpar.2.2.2.2.2 hqpos
    simp only [Fintype.card_fin] at hsize
    have hrpos : (0 : ℝ)<r := by exact_mod_cast hr0
    nlinarith only [hstrict,hsize,hrpos]

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

def circleInterval (c : UnitAddCircle) (ℓ : ℝ) : Set UnitAddCircle :=
  {z | ∃ t : ℝ, |t|≤ℓ/2 ∧ z=c+(t : UnitAddCircle)}

lemma circleInterval_disjoint_of_lifts {a b u v : ℝ}
    (ha : |a|+u/2<1/2) (hb : |b|+v/2<1/2) (hsep : (u+v)/2< |a-b|) :
    Disjoint (circleInterval (a : UnitAddCircle) u) (circleInterval (b : UnitAddCircle) v) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t,ht,hz⟩ ⟨s,hs,hz'⟩
  have he : ((a+t : ℝ) : UnitAddCircle)=((b+s : ℝ) : UnitAddCircle) := by
    simpa only [AddCircle.coe_add] using hz.symm.trans hz'
  have ht' : |a+t|<1/2 := by linarith [abs_add_le a t]
  have hs' : |b+s|<1/2 := by linarith [abs_add_le b s]
  have he' : a+t=b+s := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (a := (-1/2 : ℝ)) (p := (1 : ℝ))
    (show a+t∈Set.Ico (-1/2 : ℝ) (-1/2+1) from ⟨by linarith [(abs_lt.mp ht').1],by linarith [(abs_lt.mp ht').2]⟩)
    (show b+s∈Set.Ico (-1/2 : ℝ) (-1/2+1) from ⟨by linarith [(abs_lt.mp hs').1],by linarith [(abs_lt.mp hs').2]⟩)).mp he
  have h : |a-b|≤(u+v)/2 := by
    rw [show a-b=s-t by linarith]
    have hst := abs_sub s t
    linarith
  exact (not_lt_of_ge h) hsep

lemma slots_separated {r K R : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (k l : Fin K) (p t : Fin (R-1)) (i j : Fin r)
    (hne : (k,p,i)≠(l,t,j)) :
    slotLeft (oddLengths d) R (ω k).1 k p i+oddLengths d i≤
      slotLeft (oddLengths d) R (ω l).1 l t j ∨
    slotLeft (oddLengths d) R (ω l).1 l t j+oddLengths d j≤
      slotLeft (oddLengths d) R (ω k).1 k p i := by
  have hp : (p : ℕ)+1<R := by omega
  have ht : (t : ℕ)+1<R := by omega
  rcases lt_trichotomy k l with hkl | rfl | hlk
  · exact Or.inl (slots_separated_chunks _ R (ω k).1.isLt hp hkl i j).le
  · rcases lt_trichotomy p t with hpt | rfl | htp
    · exact Or.inl (slots_separated_same_chunk _ R (ω k).1 k (i := i) (j := j) (Or.inl hpt))
    · have hij : i≠j := fun h ↦ hne (by rw [h])
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Or.inl (slots_separated_same_chunk _ R (ω k).1 k (i := i) (j := j) (Or.inr ⟨rfl,hij⟩))
      · exact Or.inr (slots_separated_same_chunk _ R (ω k).1 k (i := j) (j := i) (Or.inr ⟨rfl,hji⟩))
    · exact Or.inr (slots_separated_same_chunk _ R (ω k).1 k (i := j) (j := i) (Or.inl htp))
  · exact Or.inr (slots_separated_chunks _ R (ω l).1.isLt ht hlk j i).le

lemma actual_centers_separated {r K R : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (k l : Fin K) (p t : Fin (R-1)) (i j : Fin r)
    (hne : (k,p,i)≠(l,t,j)) :
    ((oddLengths d i : ℝ)+oddLengths d j)/2 ≤
      |(siteCenter d R (ω k).1 k p i : ℝ)-siteCenter d R (ω l).1 l t j| := by
  obtain h | h := slots_separated d ω k l p t i j hne
  · have h' : ((slotLeft (oddLengths d) R (ω k).1 k p i : ℕ) : ℝ)+oddLengths d i≤
        slotLeft (oddLengths d) R (ω l).1 l t j := by exact_mod_cast h
    apply le_trans _ (neg_le_abs _)
    dsimp [siteCenter,oddLengths] at *
    push_cast at *
    linarith
  · have h' : ((slotLeft (oddLengths d) R (ω l).1 l t j : ℕ) : ℝ)+oddLengths d j≤
        slotLeft (oddLengths d) R (ω k).1 k p i := by exact_mod_cast h
    apply le_trans _ (le_abs_self _)
    dsimp [siteCenter,oddLengths] at *
    push_cast at *
    linarith

lemma siteCenter_margin {r K R : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (k : Fin K) (p : Fin (R-1)) (i : Fin r) :
    (oddLengths d i : ℝ)/2 < siteCenter d R (ω k).1 k p i ∧
    (siteCenter d R (ω k).1 k p i : ℝ)+(oddLengths d i : ℝ)/2 <
      K*(R*periodLength (oddLengths d)) := by
  have h := (slotLeft_bounds (oddLengths d) R (chunk := (k : ℕ)) (ω k).1.isLt
    (show (p : ℕ)+1<R by omega) i).2
  have hk : ((k : ℕ)+1)*(R*periodLength (oddLengths d))≤K*(R*periodLength (oddLengths d)) :=
    Nat.mul_le_mul_right _ (by omega)
  have hb : (slotLeft (oddLengths d) R (ω k).1 k p i : ℝ)+oddLengths d i+1≤
      K*(R*periodLength (oddLengths d)) := by
    have hh : slotLeft (oddLengths d) R (ω k).1 k p i+oddLengths d i+1≤K*(R*periodLength (oddLengths d)) := by omega
    exact_mod_cast hh
  have hz : (0 : ℝ) ≤ slotLeft (oddLengths d) R (ω k).1 k p i := Nat.cast_nonneg _
  dsimp [siteCenter,oddLengths] at *
  push_cast at *
  constructor <;> linarith

def signedLift (e : Bool) (x : ℝ) : ℝ := if e then x else -x

lemma signedLift_abs (e : Bool) (x : ℝ) : |signedLift e x|=|x| := by cases e <;> simp [signedLift]

lemma signedLift_separation {x y u v : ℝ} (hx : u/2<x) (hy : v/2<y)
    (e f : Bool) (h : e=f → (u+v)/2≤|x-y|) :
    (u+v)/2≤|signedLift e x-signedLift f y| := by
  cases e <;> cases f <;> simp only [signedLift,Bool.false_eq_true,↓reduceIte] at *
  · simpa only [neg_sub_neg,abs_sub_comm] using h trivial
  · have hh : (u+v)/2<x+y := by linarith
    have hl := le_abs_self (x+y)
    rw [show -x-y=-(x+y) by ring,abs_neg]
    exact hh.le.trans hl
  · have hh : (u+v)/2<x+y := by linarith
    rw [sub_neg_eq_add]
    exact hh.le.trans (le_abs_self _)
  · exact h trivial

lemma circle_slots_disjoint {r K R q : ℕ} (d : Fin r → ℕ) (ω : SlotChoices d K)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q)
    (k l : Fin K) (p t : Fin (R-1)) (i j : Fin r) (e f : Bool)
    (hne : (e,k,p,i)≠(f,l,t,j)) {u v : ℝ}
    (hu : u<(oddLengths d i : ℝ)/q) (hv : v<(oddLengths d j : ℝ)/q) :
    Disjoint (circleInterval ((signedLift e (siteCenter d R (ω k).1 k p i)/q : ℝ) : UnitAddCircle) u)
      (circleInterval ((signedLift f (siteCenter d R (ω l).1 l t j)/q : ℝ) : UnitAddCircle) v) := by
  have hq0 : (0 : ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hq' : (2 : ℝ)*(K*(R*periodLength (oddLengths d)))<q := by exact_mod_cast hq
  have ⟨hxi,hx⟩ := siteCenter_margin d ω k p i
  have ⟨hyj,hy⟩ := siteCenter_margin d ω l t j
  have hxi0 : (0 : ℝ)<siteCenter d R (ω k).1 k p i := lt_trans (by dsimp [oddLengths]; positivity) hxi
  have hyj0 : (0 : ℝ)<siteCenter d R (ω l).1 l t j := lt_trans (by dsimp [oddLengths]; positivity) hyj
  apply circleInterval_disjoint_of_lifts
  · rw [abs_div,signedLift_abs,abs_of_pos hq0,abs_of_pos hxi0]
    have hu' := (lt_div_iff₀ hq0).mp hu
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    have hxx : 2*(siteCenter d R (ω k).1 k p i : ℝ)+u*q<q := by linarith
    have hd : (2*(siteCenter d R (ω k).1 k p i : ℝ)+u*q)/q<1 := (div_lt_iff₀ hq0).mpr (by simpa using hxx)
    have he : (siteCenter d R (ω k).1 k p i / (q : ℝ)+u/2)*2 = (2*(siteCenter d R (ω k).1 k p i : ℝ)+u*q)/q := by field_simp
    rw [he]
    exact hd
  · rw [abs_div,signedLift_abs,abs_of_pos hq0,abs_of_pos hyj0]
    have hv' := (lt_div_iff₀ hq0).mp hv
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    have hyy : 2*(siteCenter d R (ω l).1 l t j : ℝ)+v*q<q := by linarith
    have hd : (2*(siteCenter d R (ω l).1 l t j : ℝ)+v*q)/q<1 := (div_lt_iff₀ hq0).mpr (by simpa using hyy)
    have he : (siteCenter d R (ω l).1 l t j / (q : ℝ)+v/2)*2 = (2*(siteCenter d R (ω l).1 l t j : ℝ)+v*q)/q := by field_simp
    rw [he]
    exact hd
  · rw [← sub_div,abs_div,abs_of_pos hq0]
    apply (lt_div_iff₀ hq0).mpr
    have hu' := (lt_div_iff₀ hq0).mp hu
    have hv' := (lt_div_iff₀ hq0).mp hv
    have hsep := signedLift_separation hxi hyj e f (by
      intro hef
      apply actual_centers_separated d ω k l p t i j
      intro heq
      apply hne
      obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj heq |>.imp_left id
      exact hef ▸ rfl)
    nlinarith only [hu',hv',hsep]

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

def signedCircle (e : Bool) (z : UnitAddCircle) : UnitAddCircle := if e then z else -z

lemma zmod_dot_circle {q m : ℕ} [NeZero q] (a : Fin m → ℤ) (y : Fin m → ZMod q) :
    ZMod.toAddCircle (dotProduct (fun k ↦ (a k : ZMod q)) y)=
      ∑ k, (a k) • ZMod.toAddCircle (y k) := by
  simp only [dotProduct,← zsmul_eq_mul,map_sum,map_zsmul]

lemma signedSite_circle {q : ℕ} [NeZero q] (e f : Bool) (c : ℕ) :
    signedCircle e (ZMod.toAddCircle (signedSite q f c))=
      ((signedLift (e==f) c/(q : ℝ) : ℝ) : UnitAddCircle) := by
  cases e <;> cases f <;>
    simp [signedCircle,signedSite,signedLift,ZMod.toAddCircle_natCast,neg_div]

theorem signed_interval_packing {r m : ℕ} (hr : 2≤r)
    (a : Fin r → Fin m → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ))≠0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ))≠c • (fun k ↦ (a j k : ℚ)))
    (w : Fin r → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → Fin m → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : Fin r, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by
  classical
  have : Nonempty (Fin r) := ⟨⟨0,by omega⟩⟩
  obtain ⟨d,hd⟩ := choose_odd_lengths w hw hs
  let L := periodLength (oddLengths d)
  have hLi (i : Fin r) : (0 : ℝ)<oddLengths d i := by dsimp [oddLengths]; positivity
  have hL : (0 : ℝ)<L := by exact_mod_cast periodLength_pos d (Classical.arbitrary (Fin r))
  have hdr (i : Fin r) : w i/(oddLengths d i : ℝ)<1/(2*L) := by
    have hdi : w i<(oddLengths d i : ℝ)/(2*L) := by
      simpa only [L,periodLength,oddLengths,Nat.cast_sum,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hd i
    rw [div_lt_div_iff₀ (hLi i) (by positivity)]
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ)<2*L)).mp hdi
    simpa only [one_mul] using hh
  obtain ⟨i₀,_,himax⟩ := Finset.exists_max_image Finset.univ (fun i ↦ w i/(oddLengths d i : ℝ)) Finset.univ_nonempty
  obtain ⟨t,htlow,hthi⟩ := exists_between (hdr i₀)
  have ht0 : 0<t := (div_pos (hw i₀) (hLi i₀)).trans htlow
  have hti (i : Fin r) : w i/(oddLengths d i : ℝ)<t := (himax i (Finset.mem_univ i)).trans_lt htlow
  obtain ⟨q,R,K,hq,hR,hK,hqslot,ω,M,hhit,hdis,hsize⟩ := integer_slot_matching hr a ha hnp d ht0 hthi
  have : NeZero q := ⟨hq.ne_zero⟩
  have hq0 : (0 : ℝ)<q := by exact_mod_cast hq.pos
  have hM0 : 0<M.card := by have hh := (mul_pos ht0 hq0).trans hsize; exact_mod_cast hh
  have hMpos : (0 : ℝ)<M.card := by exact_mod_cast hM0
  let y : Fin M.card → M := M.equivFin.symm
  have hyinj : Function.Injective y := M.equivFin.symm.injective
  have hyhit (i : Fin r) (h : Fin M.card) : ∃ k : Fin K, ∃ p : Fin (R-1),
      dotProduct (fun k ↦ (a i k : ZMod q)) (y h).val=
        signedSite q (ω k).2 (siteCenter d R (ω k).1 k p i) := hhit (y h) (y h).property i
  choose k p hcenter using hyhit
  let θ : Fin M.card → Fin m → UnitAddCircle := fun h l ↦ ZMod.toAddCircle ((y h).val l)
  have hwidth (i : Fin r) : w i/(M.card : ℝ)<(oddLengths d i : ℝ)/q := by
    have hh := (div_lt_iff₀ (hLi i)).mp (hti i)
    have hhmul := mul_lt_mul_of_pos_right hh hq0
    have hsmul := mul_lt_mul_of_pos_left hsize (hLi i)
    rw [div_lt_div_iff₀ hMpos hq0]
    nlinarith only [hhmul,hsmul]
  have hcircle (e : Bool) (i : Fin r) (h : Fin M.card) :
      signedCircle e (∑ l, a i l • θ h l)=
        ((signedLift (e==(ω (k i h)).2) (siteCenter d R (ω (k i h)).1 (k i h) (p i h) i)/q : ℝ) : UnitAddCircle) := by
    change signedCircle e (∑ l, a i l • ZMod.toAddCircle ((y h).val l))=_
    rw [← zmod_dot_circle,hcenter i h]
    exact signedSite_circle e (ω (k i h)).2 _
  refine ⟨M.card,by omega,θ,?_⟩
  intro e f i j h v hne
  rw [hcircle,hcircle]
  apply circle_slots_disjoint d ω hqslot (k i h) (k j v) (p i h) (p j v) i j
    (e==(ω (k i h)).2) (f==(ω (k j v)).2) ?_ (hwidth i) (hwidth j)
  intro heq
  obtain ⟨hef,hpair⟩ := Prod.mk.inj heq
  obtain ⟨hk,hpair⟩ := Prod.mk.inj hpair
  obtain ⟨hp,hij⟩ := Prod.mk.inj hpair
  subst j
  have hdot : dotProduct (fun l ↦ (a i l : ZMod q)) (y h).val=
      dotProduct (fun l ↦ (a i l : ZMod q)) (y v).val := by
    rw [hcenter,hcenter,hk,hp]
  have hy : (y h).val=(y v).val := by
    by_contra hy
    exact hdis (y h) (y h).property (y v) (y v).property hy i hdot
  have hv : h=v := hyinj (Subtype.ext hy)
  subst v
  have hef' : e=f := by cases e <;> cases f <;> cases (ω (k i h)).2 <;> simp_all
  exact hne (by rw [hef'])

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

lemma signed_interval_packing_fintype {I J : Type} [Fintype I] [Fintype J]
    (hr : 2≤Fintype.card I) (a : I → J → ℤ)
    (ha : ∀ i, a i≠0)
    (hnp : ∀ i j, i≠j → ∀ c : ℝ, ¬∀ k, (a j k : ℝ)=c*(a i k : ℝ))
    (w : I → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → J → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : I, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by
  classical
  let E := Fintype.equivFin I
  let F := Fintype.equivFin J
  let A (i : Fin (Fintype.card I)) (k : Fin (Fintype.card J)) := a (E.symm i) (F.symm k)
  have hA (i) : (fun k ↦ (A i k : ℚ))≠0 := by
    intro hz
    apply ha (E.symm i)
    funext k
    have hh := congrFun hz (F k)
    simpa only [A,Equiv.symm_apply_apply,Pi.zero_apply,Int.cast_eq_zero] using hh
  have hNP (i j) (hij : i≠j) (c : ℚ) :
      (fun k ↦ (A j k : ℚ))≠c • (fun k ↦ (A i k : ℚ)) := by
    intro he
    apply hnp (E.symm i) (E.symm j) (fun h ↦ hij (E.symm.injective h)) (c : ℝ)
    intro k
    have hh := congrFun he (F k)
    simp only [A,Equiv.symm_apply_apply,Pi.smul_apply,smul_eq_mul] at hh
    exact_mod_cast hh
  obtain ⟨H,hH,θ,hθ⟩ := signed_interval_packing hr A hA hNP (w ∘ E.symm)
    (fun i ↦ hw _) (by simpa only [Function.comp_apply,Equiv.sum_comp] using hs)
  refine ⟨H,hH,(fun h k ↦ θ h (F k)),?_⟩
  intro e f i j h v hne
  have hh := hθ e f (E i) (E j) h v (by
    intro he
    apply hne
    obtain ⟨hef,hij,hv⟩ := Prod.mk.inj he |>.imp id Prod.mk.inj
    exact Prod.ext hef (Prod.ext (E.injective hij) hv))
  simpa only [A,Function.comp_apply,Equiv.symm_apply_apply,← Equiv.sum_comp F] using hh

/-- The minor degenerate-cardinality case is absorbed by a zero-coefficient
fresh frequency. Only geometry is padded; the auxiliary polynomial is unchanged. -/
theorem signed_interval_packing_general {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] (a : I → J → ℤ) (ha : ∀ i, a i≠0)
    (hnp : ∀ i j, i≠j → ∀ c : ℝ, ¬∀ k, (a j k : ℝ)=c*(a i k : ℝ))
    (w : I → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → J → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : I, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by
  classical
  let A : Option I → Option J → ℤ := fun i k ↦ match i,k with
    | none,none => 1 | some i,some k => a i k | _,_ => 0
  let W : Option I → ℝ := fun i ↦ match i with
    | none => (1-2*∑ i, w i)/4 | some i => w i
  have hcard : 2≤Fintype.card (Option I) := by
    rw [Fintype.card_option]
    have := Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)
    omega
  have hA (i : Option I) : A i≠0 := by
    cases i with
    | none => intro h; have := congrFun h none; simp [A] at this
    | some i =>
      intro h
      apply ha i
      funext k
      have := congrFun h (some k)
      simpa [A] using this
  have hNP (i j : Option I) (hij : i≠j) (c : ℝ) :
      ¬∀ k, (A j k : ℝ)=c*(A i k : ℝ) := by
    intro he
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some j =>
        apply ha j
        funext k
        have hh := he (some k)
        simpa [A] using hh
    | some i =>
      cases j with
      | none => have hh := he none; norm_num [A] at hh
      | some j =>
        exact hnp i j (fun h ↦ hij (congrArg some h)) c (fun k ↦ by simpa [A] using he (some k))
  have hW (i : Option I) : 0<W i := by
    cases i with
    | none => dsimp [W]; linarith
    | some i => exact hw i
  have hsum : 2*∑ i, W i<1 := by
    rw [Fintype.sum_option]
    change 2*((1-2*∑ i, w i)/4+∑ i, w i)<1
    linarith
  obtain ⟨H,hH,θ,hθ⟩ := signed_interval_packing_fintype hcard A hA hNP W hW hsum
  refine ⟨H,hH,(fun h k ↦ θ h (some k)),?_⟩
  intro e f i j h v hne
  have hh := hθ e f (some i) (some j) h v (by
    intro he
    apply hne
    obtain ⟨hef,hij,hv⟩ := Prod.mk.inj he |>.imp id Prod.mk.inj
    exact Prod.ext hef (Prod.ext (Option.some.inj hij) hv))
  simpa only [Fintype.sum_option,A,zero_smul,zero_add,W] using hh

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI
