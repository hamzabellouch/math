import OAI.Algebra.Determinantal.PlaneHilbert

namespace OAI

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

noncomputable def filtered (q : Plane (K := K) →ₐ[K] R) : ℕ → Submodule K R
  | 0 => ⊥
  | n+1 => (restrictTotalDegree (Fin 2) K n).map q.toLinearMap

instance filtered_finite (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    Module.Finite K (filtered q n) := by
  cases n with
  | zero => exact inferInstanceAs (Module.Finite K (⊥ : Submodule K R))
  | succ n => exact Module.Finite.map _ _

lemma mem_filtered_succ (q : Plane (K := K) →ₐ[K] R) (n : ℕ) (z : R) :
    z ∈ filtered q (n+1) ↔ ∃ p : Plane (K := K), p.totalDegree ≤ n ∧ q p = z := by
  simp only [filtered,Submodule.mem_map,mem_restrictTotalDegree,AlgHom.toLinearMap_apply]

lemma filtered_mono (q : Plane (K := K) →ₐ[K] R) : Monotone (filtered q) := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => exact bot_le
  | succ n =>
    intro z hz
    obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q n z).mp hz
    exact (mem_filtered_succ q (n+1) _).mpr ⟨p,by omega,rfl⟩

lemma homogeneous_mem_filtered (q : Plane (K := K) →ₐ[K] R) {n : ℕ}
    (p : H (K := K) (n : ℤ)) : q p.val ∈ filtered q (n+1) := by
  exact (mem_filtered_succ q n _).mpr
    ⟨p.val,(intWeight_homogeneous p.property).totalDegree_le,rfl⟩

lemma mul_X_filtered (q : Plane (K := K) →ₐ[K] R) (i : Fin 2) {n : ℕ}
    {z : R} (hz : z ∈ filtered q n) : q (X i) * z ∈ filtered q (n+1) := by
  cases n with
  | zero =>
    have hz0 : z = 0 := hz
    simp [hz0]
  | succ n =>
    obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q n z).mp hz
    apply (mem_filtered_succ q (n+1) _).mpr
    refine ⟨X i*p,?_,map_mul _ _ _⟩
    have hx : (X i : Plane (K := K)).totalDegree = 1 := totalDegree_X i
    exact (totalDegree_mul _ _).trans (by rw [hx]; omega)

noncomputable def topComponent (n : ℕ) : Plane (K := K) →ₗ[K] H (K := K) (n : ℤ) :=
  (homogeneousComponent n).codRestrict _ (fun p =>
    homogeneous_intWeight (homogeneousComponent_isHomogeneous n p))

lemma sub_topComponent_degree {p : Plane (K := K)} {n : ℕ}
    (hp : p.totalDegree ≤ n+1) : (p-(topComponent (n+1) p).val).totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro s hs
  have hc : (p-(topComponent (n+1) p).val).coeff s ≠ 0 := mem_support_iff.mp hs
  change s.degree ≤ n
  by_contra! hn
  apply hc
  change (p-homogeneousComponent (n+1) p).coeff s = 0
  rw [coeff_sub,coeff_homogeneousComponent]
  by_cases he : s.degree = n+1
  · simp [he]
  · have hlt : p.totalDegree < s.degree := by omega
    simp [he,coeff_eq_zero_of_totalDegree_lt hlt]

lemma sub_topComponent_mem_filtered (q : Plane (K := K) →ₐ[K] R)
    {p : Plane (K := K)} {n : ℕ} (hp : p.totalDegree ≤ n) :
    q p - q (topComponent n p).val ∈ filtered q n := by
  cases n with
  | zero =>
    have he : p = (topComponent 0 p).val := by
      change p = homogeneousComponent 0 p
      rw [homogeneousComponent_zero]
      exact (totalDegree_eq_zero_iff_eq_C).mp (Nat.eq_zero_of_le_zero hp)
    rw [← he, sub_self]
    exact (filtered q 0).zero_mem
  | succ n =>
    exact (mem_filtered_succ q n _).mpr
      ⟨p-(topComponent (n+1) p).val,sub_topComponent_degree hp,map_sub _ _ _⟩

noncomputable def leadingMap (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    H (K := K) (n : ℤ) →ₗ[K] R ⧸ filtered q n :=
  (filtered q n).mkQ.comp (q.toLinearMap.comp (H (K := K) (n : ℤ)).subtype)

noncomputable abbrev leadingRelations (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    Submodule K (H (K := K) (n : ℤ)) := LinearMap.ker (leadingMap q n)

lemma mem_leadingRelations (q : Plane (K := K) →ₐ[K] R) (n : ℕ)
    (p : H (K := K) (n : ℤ)) : p ∈ leadingRelations q n ↔ q p.val ∈ filtered q n := by
  simp only [leadingRelations,LinearMap.mem_ker,leadingMap,LinearMap.comp_apply,
    Submodule.subtype_apply,AlgHom.toLinearMap_apply,Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

lemma varMul_leadingRelations (q : Plane (K := K) →ₐ[K] R) (i : Fin 2) (n : ℕ) :
    (leadingRelations q n).map (varMul i n) ≤ leadingRelations q (n+1) := by
  rintro _ ⟨p,hp,rfl⟩
  change p ∈ leadingRelations q n at hp
  rw [mem_leadingRelations] at hp ⊢
  change q (X i*p.val) ∈ _
  rw [map_mul]
  exact mul_X_filtered q i hp

lemma leadingMap_range (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    LinearMap.range (leadingMap q n) = (filtered q (n+1)).map (filtered q n).mkQ := by
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨q p.val,homogeneous_mem_filtered q p,rfl⟩
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q n r).mp hr
    refine ⟨topComponent n p,?_⟩
    change Submodule.Quotient.mk (q (topComponent n p).val) = Submodule.Quotient.mk (q p)
    apply (Submodule.Quotient.eq _).mpr
    simpa only [neg_sub] using (filtered q n).neg_mem (sub_topComponent_mem_filtered q hp)

noncomputable def filteredH (q : Plane (K := K) →ₐ[K] R) (n : ℕ) : ℕ :=
  Module.finrank K (H (K := K) (n : ℤ) ⧸ leadingRelations q n)

lemma filteredH_add_rank (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    filteredH q n + Module.finrank K (filtered q n) = Module.finrank K (filtered q (n+1)) := by
  let f := (filtered q n).mkQ.domRestrict (filtered q (n+1))
  have hr : LinearMap.range f = LinearMap.range (leadingMap q n) := by
    rw [leadingMap_range,LinearMap.range_domRestrict]
  have hk : LinearMap.ker f = (filtered q n).comap (filtered q (n+1)).subtype := by
    simp only [f,LinearMap.domRestrict,LinearMap.ker_comp,Submodule.ker_mkQ]
  have hh := f.finrank_range_add_finrank_ker
  rw [hr,hk,(Submodule.comapSubtypeEquivOfLe (filtered_mono q (Nat.le_succ n))).finrank_eq] at hh
  unfold filteredH
  rw [(leadingMap q n).quotKerEquivRange.finrank_eq]
  exact hh

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]
variable (W : (n : ℕ) → Submodule K (H (K := K) (n : ℤ)))

noncomputable def quotientH (n : ℕ) : ℕ := Module.finrank K (H (K := K) (n : ℤ) ⧸ W n)
lemma quotientH_add_rank (n : ℕ) : quotientH W n + Module.finrank K (W n) = n+1 := by
  rw [quotientH, Submodule.finrank_quotient_add_finrank, finrank_piece]
  omega
lemma quotientH_le (n : ℕ) : quotientH W n ≤ n+1 := by
  have := quotientH_add_rank W n
  omega
variable (hW : ∀ (i : Fin 2) (n : ℕ), (W n).map (varMul i n) ≤ W (n+1))
include hW in
lemma quotientH_succ_le_of_deficit {n : ℕ}
    (hn : quotientH W n < n+1) : quotientH W (n+1) ≤ quotientH W n := by
  have h0 : W n ≠ ⊥ := by
    intro h
    have hh := quotientH_add_rank W n
    rw [h, finrank_bot] at hh
    omega
  have hh := finrank_varMul_sup (W n) h0
  have hl : Module.finrank K ↥((W n).map (varMul 0 n) ⊔ (W n).map (varMul 1 n)) ≤
      Module.finrank K (W (n+1)) := Submodule.finrank_mono (sup_le (hW 0 n) (hW 1 n))
  have h1 := quotientH_add_rank W n
  have h2 := quotientH_add_rank W (n+1)
  omega
include hW in
lemma quotientH_le_of_deficit {n m : ℕ}
    (hn : quotientH W n < n+1) (hnm : n ≤ m) : quotientH W m ≤ quotientH W n := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
    exact (quotientH_succ_le_of_deficit W hW (by omega : quotientH W m < m+1)).trans ih

include hW in
lemma quotientH_normalized {n m : ℕ} (hnm : n ≤ m) :
    (n+1) * quotientH W m ≤ (m+1) * quotientH W n := by
  rcases (quotientH_le W n).eq_or_lt with he|hl
  · rw [he]
    have := quotientH_le W m
    nlinarith
  · have hh := quotientH_le_of_deficit W hW hl hnm
    nlinarith

theorem quotientH_coprime_bound
    {a b : Plane (K := K)} {e f : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (hb : b.IsWeightedHomogeneous weight f)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : IsRelPrime a b) (n : ℕ)
    (haW : multiplicationRange ha (n : ℤ) ≤ W n)
    (hbW : multiplicationRange hb (n : ℤ) ≤ W n) :
    quotientH W n + ((n : ℤ)-e+1).toNat + ((n : ℤ)-f+1).toNat ≤
      n+1 + ((n : ℤ)-(e+f)+1).toNat := by
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (multiplicationRange ha (n : ℤ)) (multiplicationRange hb (n : ℤ))
  rw [multiplicationRange_inf ha hb hb0 hab,
    finrank_multiplicationRange ha ha0, finrank_multiplicationRange hb hb0,
    finrank_multiplicationRange (ha.mul hb) (mul_ne_zero ha0 hb0)] at hh
  have hl : Module.finrank K ↥(multiplicationRange ha (n : ℤ) ⊔
      multiplicationRange hb (n : ℤ)) ≤ Module.finrank K (W n) :=
    Submodule.finrank_mono (sup_le haW hbW)
  have heq := quotientH_add_rank W n
  omega

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open Finset
variable (h : ℕ → ℕ)
noncomputable def hSum (n : ℕ) : ℕ := ∑ i ∈ range n, h i
lemma hSum_mono : Monotone (hSum h) := by
  intro a b hab
  exact sum_le_sum_of_subset_of_nonneg (range_mono hab) (by intros; omega)
lemma hSum_succ (n : ℕ) : hSum h (n+1) = hSum h n + h n := sum_range_succ _ _

lemma hSum_double_le
    (hnorm : ∀ n m, n ≤ m → (n+1)*h m ≤ (m+1)*h n) (n : ℕ) :
    hSum h (2*n) ≤ 4*hSum h n := by
  induction n with
  | zero => simp [hSum]
  | succ n ih =>
    have h1 := hnorm n (2*n) (by omega)
    have h2 := hnorm n (2*n+1) (by omega)
    have hh : h (2*n) + h (2*n+1) ≤ 4*h n := by nlinarith
    rw [show 2*(n+1) = (2*n+1)+1 by omega, hSum_succ, hSum_succ, hSum_succ]
    omega

lemma hSum_half_length (B : ℕ)
    (hle : ∀ n, h n ≤ n+1)
    (hdec : ∀ n m, h n < n+1 → n ≤ m → h m ≤ h n)
    (htail : ∀ n, B ≤ n → h n ≤ 2*B-n) :
    hSum h (2*B) ≤ 2*hSum h B := by
  have hp : ∀ i ∈ range B, h (B+i) ≤ h (B-1-i) := by
    intro i hi
    have hiB := mem_range.mp hi
    rcases (hle (B-1-i)).eq_or_lt with he|hl
    · rw [he]
      have ht := htail (B+i) (by omega)
      omega
    · exact hdec (B-1-i) (B+i) hl (by omega)
  have hs := sum_le_sum hp
  rw [sum_range_reflect] at hs
  have he : hSum h (2*B) = hSum h B + ∑ i ∈ range B, h (B+i) := by
    rw [show 2*B = B+B by omega, hSum, sum_range_add]
    rfl
  rw [he]
  dsimp only [hSum] at *
  omega

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

lemma mul_filtered_by_homogeneous (q : Plane (K := K) →ₐ[K] R) {n m : ℕ}
    {z : R} (hz : z ∈ filtered q n) (p : H (K := K) (m : ℤ)) :
    z * q p.val ∈ filtered q (n+m) := by
  cases n with
  | zero =>
    have hz0 : z = 0 := hz
    simp [hz0]
  | succ n =>
    obtain ⟨a,ha,rfl⟩ := (mem_filtered_succ q n z).mp hz
    rw [show n+1+m = (n+m)+1 by omega]
    apply (mem_filtered_succ q (n+m) _).mpr
    refine ⟨a*p.val,?_,map_mul _ _ _⟩
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add ha (intWeight_homogeneous p.property).totalDegree_le)

lemma multiplicationRange_le_leading (q : Plane (K := K) →ₐ[K] R)
    {a : Plane (K := K)} {e : ℕ} (ha : a.IsWeightedHomogeneous weight (e : ℤ))
    (hqa : q a ∈ filtered q e) (n : ℕ) :
    multiplicationRange ha (n : ℤ) ≤ leadingRelations q n := by
  rintro _ ⟨p,rfl⟩
  rw [mem_leadingRelations]
  change q (a*p.val) ∈ _
  rw [map_mul]
  by_cases hen : e ≤ n
  · let p' : H (K := K) ((n-e : ℕ) : ℤ) := ⟨p.val, by
      have hh : (n : ℤ)-e = ((n-e : ℕ) : ℤ) := by omega
      exact hh ▸ p.property⟩
    have hh := mul_filtered_by_homogeneous q hqa p'
    simpa only [Nat.add_sub_of_le hen] using hh
  · have hr : Module.finrank K (H (K := K) ((n : ℤ)-e)) = 0 := by
      rw [finrank_piece]; omega
    obtain ⟨c,hc,hcp⟩ := Module.finrank_eq_zero_iff.mp hr p
    have hp0 : p = 0 := (smul_eq_zero.mp hcp).resolve_left hc
    rw [hp0]
    simp

lemma filtered_rank_eq_hSum (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    Module.finrank K (filtered q n) = hSum (filteredH q) n := by
  induction n with
  | zero =>
    change Module.finrank K (⊥ : Submodule K R) = 0
    exact finrank_bot K R
  | succ n ih =>
    rw [hSum_succ,← ih]
    have := filteredH_add_rank q n
    omega

lemma filtered_eq_top_of_tail (q : Plane (K := K) →ₐ[K] R)
    (hq : Function.Surjective q) (N : ℕ)
    (hz : ∀ n, N ≤ n → filteredH q n = 0) : filtered q N = ⊤ := by
  have he : ∀ n, N ≤ n → filtered q n = filtered q N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      have hh := filteredH_add_rank q n
      rw [hz n hn,zero_add] at hh
      exact (Submodule.eq_of_le_of_finrank_eq (filtered_mono q (Nat.le_succ n)) hh).symm.trans ih
  apply top_unique
  intro z _
  obtain ⟨p,rfl⟩ := hq z
  have hm : q p ∈ filtered q (max N (p.totalDegree+1)) :=
    filtered_mono q (le_max_right ..)
      ((mem_filtered_succ q p.totalDegree (q p)).mpr ⟨p,le_rfl,rfl⟩)
  rwa [he _ (le_max_left ..)] at hm

theorem finite_interpolation_half (q : Plane (K := K) →ₐ[K] R)
    (hq : Function.Surjective q) {a b : Plane (K := K)} {e f B : ℕ}
    (ha : a.IsWeightedHomogeneous weight (e : ℤ))
    (hb : b.IsWeightedHomogeneous weight (f : ℤ))
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : IsRelPrime a b)
    (hqa : q a ∈ filtered q e) (hqb : q b ∈ filtered q f)
    (he : e ≤ B+1) (hf : f ≤ B+1) (hef : e+f ≤ 2*B+1) :
    filtered q (2*B) = ⊤ ∧ Module.finrank K R ≤ 2*Module.finrank K (filtered q B) := by
  have ht : ∀ n, B ≤ n → filteredH q n ≤ 2*B-n := by
    intro n hn
    have hh := quotientH_coprime_bound (leadingRelations q) ha hb ha0 hb0 hab n
      (multiplicationRange_le_leading q ha hqa n)
      (multiplicationRange_le_leading q hb hqb n)
    change filteredH q n + _ + _ ≤ _ at hh
    omega
  have htop := filtered_eq_top_of_tail q hq (2*B) (by
    intro n hn
    have hh := ht n (by omega)
    omega)
  refine ⟨htop,?_⟩
  have hh := hSum_half_length (filteredH q) B
    (quotientH_le (leadingRelations q))
    (fun n m hn hnm => quotientH_le_of_deficit (leadingRelations q)
      (varMul_leadingRelations q) hn hnm) ht
  rw [← filtered_rank_eq_hSum, ← filtered_rank_eq_hSum, htop,finrank_top] at hh
  exact hh

lemma filtered_rank_double_le (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    Module.finrank K (filtered q (2*n)) ≤ 4*Module.finrank K (filtered q n) := by
  rw [filtered_rank_eq_hSum, filtered_rank_eq_hSum]
  exact hSum_double_le (filteredH q)
    (fun n m hnm => quotientH_normalized (leadingRelations q)
      (varMul_leadingRelations q) hnm) n

end PermanentBorder.PlaneHilbert

namespace PermanentBorder.LowPlane
open MvPolynomial
variable {K : Type*} [Field K]

abbrev Index (B : ℕ) := {s : Fin 2 →₀ ℕ // s.degree < B}

instance index_finite (B : ℕ) : Finite (Index B) := by
  apply Set.Finite.to_subtype
  exact (Finsupp.finite_of_degree_le B).subset (fun _ h => Nat.le_of_lt h)

noncomputable instance index_fintype (B : ℕ) : Fintype (Index B) := Fintype.ofFinite _

lemma plane_degree (s : Fin 2 →₀ ℕ) : s.degree = s 0+s 1 := by
  change s.sum (fun _ a => a) = _
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_two]

noncomputable def indexEquiv (B : ℕ) : Index B ≃ {p : Fin (B+1) × Fin (B+1) // p.1 < p.2} where
  toFun s := ⟨(⟨s.val 0,by have h:=s.property; rw [plane_degree] at h; omega⟩,
    ⟨s.val 0+s.val 1+1,by have h:=s.property; rw [plane_degree] at h; omega⟩),by simp⟩
  invFun p := ⟨Finsupp.single 0 p.val.1.val+Finsupp.single 1 (p.val.2.val-p.val.1.val-1),by
    rw [plane_degree]
    simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from by decide),
      Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 from by decide),add_zero,zero_add]
    have h:=p.property; have h':=p.val.2.isLt
    change p.val.1.val < p.val.2.val at h
    omega⟩
  left_inv s := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simp
    · simp; omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · simp
    · simp only [Finsupp.add_apply,Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from by decide),
        Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 from by decide),add_zero,zero_add]
      have h:=p.property
      change p.val.1.val < p.val.2.val at h
      omega

lemma card_index (B : ℕ) : Fintype.card (Index B) = (B+1).choose 2 := by
  rw [Fintype.card_congr (indexEquiv B),Fintype.card_subtype]
  simpa only [Fintype.card_fin] using Fintype.card_product_filter_lt (α := Fin (B+1))

lemma expansion {B : ℕ} (p : MvPolynomial (Fin 2) K)
    (hp : ∀ s ∈ p.support, s.degree < B) :
    p = ∑ s : Index B, p.coeff s.val • monomial s.val (1 : K) := by
  classical
  ext t
  rw [coeff_sum]
  by_cases ht : t.degree < B
  · rw [Finset.sum_eq_single (⟨t,ht⟩ : Index B)]
    · simp
    · intro s _ hs
      have he : s.val ≠ t := fun h => hs (Subtype.ext h)
      simp [coeff_monomial,he]
    · simp
  · have hz : p.coeff t=0 := by
      by_contra hn
      exact ht (hp t (mem_support_iff.mpr hn))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro s _
    have he : s.val ≠ t := fun he => ht (he ▸ s.property)
    simp [coeff_monomial,he]

lemma remainder_expansion {B : ℕ} (p t : MvPolynomial (Fin 2) K)
    (hp : ∀ s, B ≤ s.degree → p.coeff s = t.coeff s) :
    p = t + ∑ s : Index B, (p-t).coeff s.val • monomial s.val (1 : K) := by
  have h := expansion (p-t) (by
    intro s hs
    have hc := mem_support_iff.mp hs
    rw [coeff_sub,sub_ne_zero] at hc
    exact lt_of_not_ge (fun hh => hc (hp s hh)))
  rw [← h]
  abel

end PermanentBorder.LowPlane

namespace PermanentBorder.LinearParameters
open Module
variable {K L S ι κ : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup S] [Module L S] [Fintype ι] [Fintype κ]

lemma independent_coefficients_mem (F : IntermediateField K L) (c : Basis κ L S)
    (v : ι → S) (hv : LinearIndependent L v) (x : ι → L)
    (hvc : ∀ i j, c.repr (v i) j ∈ F)
    (hx : ∀ j, c.repr (∑ i, x i • v i) j ∈ F) : ∀ i, x i ∈ F := by
  classical
  have ht : (⊤ : Submodule L S) ≤ Submodule.span L (Set.range v ∪ Set.range c) := by
    rw [← c.span_eq]
    exact Submodule.span_mono Set.subset_union_right
  let hs : Set.range v ⊆ Set.range v ∪ Set.range c := Set.subset_union_left
  let b := Basis.extendLe hv.linearIndepOn_id hs ht
  let j : ι → hv.linearIndepOn_id.extend hs :=
    fun i => ⟨v i,hv.linearIndepOn_id.subset_extend hs ⟨i,rfl⟩⟩
  have hj : Function.Injective j := by
    intro i i' he
    exact hv.injective (congrArg Subtype.val he)
  have hb : ∀ i, b (j i) = v i := fun i => Basis.extendLe_apply_self ..
  have hbc : ∀ i t, c.repr (b t) i ∈ F := by
    intro i t
    have hh := Basis.extendLe_subset hv.linearIndepOn_id hs ht
      (Set.mem_range_self t)
    rcases hh with ⟨a,ha⟩|⟨a,ha⟩
    · rw [← ha]; exact hvc a i
    · rw [← ha,c.repr_self]
      by_cases h : a=i <;> simp [h]
  have hh := BasisFieldRecovery.repr_mem F b c hbc _ hx
  intro i
  have he : b.repr (∑ a, x a • v a) (j i) = x i := by
    simp only [← hb,map_sum,map_smul,Basis.repr_self,Finsupp.finsetSum_apply,
      Finsupp.smul_apply,smul_eq_mul,Finsupp.single_apply]
    simp only [hj.eq_iff]
    simp
  rw [← he]
  exact hh (j i)

end PermanentBorder.LinearParameters

end OAI
