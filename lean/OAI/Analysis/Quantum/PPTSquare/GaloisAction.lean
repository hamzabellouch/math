import Mathlib.RingTheory.Frobenius
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial
namespace CertificateGalois
attribute [local instance] Classical.propDecidable

variable {S ι : Type*} [CommRing S] [IsDomain S] [Fintype ι]

omit [IsDomain S] in
lemma root_of_product (r : ι → S) (i : ι) :
    (∏ j, (X - C (r j))).eval (r i) = 0 := by
  classical
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

lemma exists_index_of_product_root (r : ι → S) (a : S)
    (ha : (∏ j, (X - C (r j))).eval a = 0) : ∃ i, a = r i := by
  classical
  simp only [eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero] at ha
  exact ha

lemma perm_of_integer_roots (r : ι → S) (hr : Function.Injective r)
    (f : ℤ[X]) (hf : f.map (Int.castRingHom S) = ∏ j, (X - C (r j)))
    (σ : S ≃+* S) : ∃ π : Equiv.Perm ι, ∀ i, σ (r i) = r (π i) := by
  classical
  have roots (i : ι) : ∃ j, σ (r i) = r j := by
    apply exists_index_of_product_root
    rw [← hf]
    have h := congrArg σ (root_of_product r i)
    rw [← hf, map_zero] at h
    have hs : (f.map (Int.castRingHom S)).map σ.toRingHom = f.map (Int.castRingHom S) := by
      rw [Polynomial.map_map]
      congr 1
      ext z
      simp
    have he : (f.map (Int.castRingHom S)).eval₂ σ.toRingHom (σ (r i)) = 0 :=
      (Polynomial.eval₂_at_apply σ.toRingHom (r i)).trans h
    rwa [Polynomial.eval₂_eq_eval_map, hs] at he
  choose τ hτ using roots
  have hinj : Function.Injective τ := by
    intro i j hij
    apply hr
    apply σ.injective
    rw [hτ, hτ, hij]
  exact ⟨Equiv.ofBijective τ ⟨hinj, Finite.surjective_of_injective hinj⟩, hτ⟩

omit [IsDomain S] in
lemma map_product_integer_roots (r : ι → S) (f : ℤ[X])
    (hf : f.map (Int.castRingHom S) = ∏ j, (X - C (r j)))
    {T : Type*} [CommRing T] (φ : S →+* T) :
    f.map (Int.castRingHom T) = ∏ j, (X - C (φ (r j))) := by
  have h := congrArg (Polynomial.map φ) hf
  have hφ : φ.comp (Int.castRingHom S) = Int.castRingHom T := by ext; simp
  simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_map, hφ] using h

omit [IsDomain S] in
lemma reduction_injective (r : ι → S) (f : ℤ[X])
    (hf : f.map (Int.castRingHom S) = ∏ j, (X - C (r j)))
    {T : Type*} [CommRing T] [Nontrivial T] (φ : S →+* T)
    (hsep : (f.map (Int.castRingHom T)).Separable) :
    Function.Injective (fun i => φ (r i)) := by
  rw [map_product_integer_roots r f hf φ] at hsep
  exact hsep.injective_of_prod_X_sub_C

variable {F : Type*} [Field F]

omit [Fintype ι] in
lemma perm_pow_root (r : ι → F) (π : Equiv.Perm ι) (p : ℕ)
    (hπ : ∀ i, r (π i) = (r i) ^ p) (k : ℕ) (i : ι) :
    r ((π ^ k) i) = (r i) ^ (p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hπ, ih, ← pow_mul, Nat.pow_succ]

lemma fixed_card_eq_gcd_degree (r : ι → F) (hr : Function.Injective r)
    (π : Equiv.Perm ι) (p : ℕ) (hπ : ∀ i, r (π i) = (r i) ^ p) (k : ℕ) :
    (Finset.univ.filter (fun i => (π ^ k) i = i)).card =
      (EuclideanDomain.gcd (∏ i, (X - C (r i))) (X ^ (p ^ k) - X)).natDegree := by
  classical
  let f : F[X] := ∏ i, (X - C (r i))
  let g := EuclideanDomain.gcd f (X ^ (p ^ k) - X)
  have hf : f ≠ 0 := (monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (r i))).ne_zero
  have hgf : g ∣ f := EuclideanDomain.gcd_dvd_left _ _
  have hg : g ≠ 0 := by
    intro he
    rw [he, zero_dvd_iff] at hgf
    exact hf hgf
  have hs : f.Separable := Polynomial.separable_prod_X_sub_C_iff.mpr hr
  have hgs : g.Separable := hs.of_dvd hgf
  have hsplit : f.Splits := Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_sub_C (r i))
  have hgsplit : g.Splits := hsplit.of_dvd hf hgf
  have himage : (Finset.univ.filter (fun i => (π ^ k) i = i)).image r = g.roots.toFinset := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Multiset.mem_toFinset, Polynomial.mem_roots hg]
    change (∃ i, (π ^ k) i = i ∧ r i = x) ↔ g.IsRoot x
    rw [show g = EuclideanDomain.gcd f (X ^ (p ^ k) - X) from rfl,
      Polynomial.isRoot_gcd_iff_isRoot_left_right]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨root_of_product r i, ?_⟩
      simp only [IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero]
      rw [← perm_pow_root r π p hπ k i, hi]
    · rintro ⟨hx, hpow⟩
      obtain ⟨i, hi⟩ := exists_index_of_product_root r x hx
      refine ⟨i, hr ?_, hi.symm⟩
      rw [perm_pow_root r π p hπ k i, ← hi]
      simpa only [IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero] using hpow
  calc
    _ = ((Finset.univ.filter (fun i => (π ^ k) i = i)).image r).card :=
      (Finset.card_image_of_injective _ hr).symm
    _ = g.roots.toFinset.card := congrArg Finset.card himage
    _ = g.natDegree := by
      rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hgs), ← hgsplit.natDegree_eq_card_roots]

open NumberField
open scoped NumberField

lemma frobenius_permutation
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (r : ι → 𝓞 K) (hr : Function.Injective r) (f : ℤ[X])
    (hf : f.map (Int.castRingHom (𝓞 K)) = ∏ i, (X - C (r i)))
    (p : ℕ) [Fact p.Prime]
    (hsep : (f.map (Int.castRingHom (ZMod p))).Separable) :
    ∃ (σ : K ≃ₐ[ℚ] K) (π : Equiv.Perm ι),
      (∀ i, σ (r i : K) = (r (π i) : K)) ∧
      ∀ k : ℕ, (Finset.univ.filter (fun i => (π ^ k) i = i)).card =
        (EuclideanDomain.gcd (f.map (Int.castRingHom (ZMod p)))
          (X ^ (p ^ k) - X)).natDegree := by
  classical
  let S := 𝓞 K
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  let := IsIntegralClosure.MulSemiringAction ℤ ℚ K S
  let := Algebra.isInvariant_of_isGalois ℤ ℚ K S
  obtain ⟨Q, hQmax, hQ⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S) P
  let := hQmax
  let := hQ
  let F := S ⧸ Q
  let : Field F := Ideal.Quotient.field Q
  have hu : Q.under ℤ = P := (Ideal.over_def Q P).symm
  let ψ : S →+* F := Ideal.Quotient.mk Q
  let φ : ZMod p →+* F :=
    (Ideal.quotientMap Q (algebraMap ℤ S) (show P ≤ Q.comap (algebraMap ℤ S) from hu.symm.le)).comp
      (Int.quotientSpanNatEquivZMod p).symm.toRingHom
  have hφ : φ.comp (Int.castRingHom (ZMod p)) = Int.castRingHom F := by
    ext; simp
  have hfmap : (f.map (Int.castRingHom (ZMod p))).map φ =
      f.map (Int.castRingHom F) := by rw [Polynomial.map_map, hφ]
  have hred : Function.Injective (fun i => ψ (r i)) := by
    apply reduction_injective r f hf ψ
    rw [← hfmap]
    exact hsep.map (f := φ)
  let : Finite (S ⧸ Q) :=
    (Ideal.absNorm_ne_zero_iff Q).mp
      (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne Q))
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (K ≃ₐ[ℚ] K) Q
  let e : S ≃+* S := (MulSemiringAction.toAlgEquiv ℤ S σ).toRingEquiv
  obtain ⟨π, hπ⟩ := perm_of_integer_roots r hr f hf e
  have hπred (i : ι) : ψ (r (π i)) = ψ (r i) ^ p := by
    rw [← hπ]
    have hh := hσ (r i)
    rw [hu, Int.card_ideal_quot] at hh
    exact (map_sub ψ _ _ ▸ (Ideal.Quotient.eq_zero_iff_mem.mpr hh)) |> sub_eq_zero.mp
  refine ⟨σ, π, ?_, ?_⟩
  · intro i
    have hh := congrArg (algebraMap S K) (hπ i)
    exact (algebraMap_galRestrict_apply ℤ σ (r i)).symm.trans hh
  · intro k
    rw [fixed_card_eq_gcd_degree _ hred π p hπred k,
      ← map_product_integer_roots r f hf ψ, ← hfmap]
    have hx : (X ^ (p ^ k) - X : F[X]) =
        (X ^ (p ^ k) - X : (ZMod p)[X]).map φ := by simp
    rw [hx, Polynomial.gcd_map, Polynomial.natDegree_map]

end CertificateGalois

open scoped BigOperators
open Equiv Equiv.Perm Function
namespace PencilGroup
attribute [local instance] Classical.propDecidable

def fixedCount (π : Equiv.Perm (Fin 20)) : ℕ :=
  (Finset.univ.filter (fun i => π i = i)).card

lemma fixed_all (π : Equiv.Perm (Fin 20)) (h : fixedCount π = 20) : π = 1 := by
  have hh : Finset.univ.filter (fun i => π i = i) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    simpa [fixedCount] using h.ge
  apply Equiv.ext
  intro i
  change π i = i
  have : i ∈ Finset.univ.filter (fun i => π i = i) := by rw [hh]; exact Finset.mem_univ i
  exact (Finset.mem_filter.mp this).2

lemma fixed_none (π : Equiv.Perm (Fin 20)) (h : fixedCount π = 0) (i : Fin 20) : π i ≠ i := by
  have hh := Finset.card_eq_zero.mp h
  intro hi
  have : i ∈ Finset.univ.filter (fun i => π i = i) := by simp [hi]
  rw [hh] at this
  exact Finset.notMem_empty i this

lemma transitive_of_frob41 (π : Equiv.Perm (Fin 20))
    (h4 : fixedCount (π ^ 4) = 0) (h10 : fixedCount (π ^ 10) = 0)
    (h20 : fixedCount (π ^ 20) = 20) :
    ∀ x y : Fin 20, ∃ k : ℕ, (π ^ k) x = y := by
  have hpow := fixed_all _ h20
  have hperiod (x : Fin 20) : Function.minimalPeriod π x = 20 := by
    have hp : Function.IsPeriodicPt π 20 x := by
      change (π^[20]) x = x
      rw [← Equiv.Perm.coe_pow, hpow]
      rfl
    have hd := hp.minimalPeriod_dvd
    have hpos := hp.minimalPeriod_pos (by decide : 0 < 20)
    have hle := hp.minimalPeriod_le (by decide : 0 < 20)
    have hn4 : ¬ Function.minimalPeriod π x ∣ 4 := by
      intro hh
      have he := Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hh
      exact fixed_none _ h4 x (by simpa only [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow] using he)
    have hn10 : ¬ Function.minimalPeriod π x ∣ 10 := by
      intro hh
      have he := Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hh
      exact fixed_none _ h10 x (by simpa only [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow] using he)
    have hd' : ∀ m : Fin 21, 0 < m.val → m.val ∣ 20 → ¬ m.val ∣ 4 →
        ¬ m.val ∣ 10 → m.val = 20 := by decide
    exact hd' ⟨Function.minimalPeriod (⇑π) x, Nat.lt_succ_of_le hle⟩ hpos hd hn4 hn10
  intro x y
  let f : Fin 20 → Fin 20 := fun k => (π ^ k.val) x
  have hi : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod (f := ⇑π) (x := x)
      (by simp [hperiod]) (by simp [hperiod])
    simpa [f, Equiv.Perm.coe_pow] using hab
  obtain ⟨k,hk⟩ := Finite.surjective_of_injective hi y
  exact ⟨k.val,hk⟩

lemma swap_of_frob131 (π : Equiv.Perm (Fin 20))
    (h : fixedCount (π ^ 17) = 18) : (π ^ 17).IsSwap := by
  rw [← Equiv.Perm.card_support_eq_two]
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i : Fin 20 => (π ^ 17) i = i)
  change (Finset.univ.filter (fun i => (π ^ 17) i = i)).card = 18 at h
  rw [h] at hcard
  have hh : 18 + (π ^ 17).support.card = 20 := by simpa [Equiv.Perm.support] using hcard
  omega

lemma cycle_of_frob139 (π : Equiv.Perm (Fin 20))
    (h1 : fixedCount π = 1) (h19 : fixedCount (π ^ 19) = 20) :
    ∃ z, π z = z ∧ (∀ x, π x = x ↔ x = z) ∧ π.IsCycle := by
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp h1
  have hz' : ∀ x, π x = x ↔ x = z := by
    intro x
    have hh := congrArg (x ∈ ·) hz
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using (iff_of_eq hh)
  have hn : π ≠ 1 := by intro hh; simp [fixedCount, hh] at h1
  have hd : orderOf π ∣ 19 := orderOf_dvd_iff_pow_eq_one.mpr (fixed_all _ h19)
  have ho : orderOf π = 19 :=
    ((by decide : Nat.Prime 19).eq_one_or_self_of_dvd _ hd).resolve_left
      (fun h => hn (orderOf_eq_one_iff.mp h))
  refine ⟨z, (hz' z).mpr rfl, hz', ?_⟩
  apply Equiv.Perm.isCycle_of_prime_order (ho ▸ (by decide : Nat.Prime 19))
  have hh := (π.support).card_le_univ
  rw [ho]
  simpa using (lt_of_le_of_lt hh (by decide : Fintype.card (Fin 20) < 2 * 19))

lemma full_symmetric (H : Subgroup (Equiv.Perm (Fin 20)))
    (htrans : ∀ x y, ∃ g ∈ H, g x = y)
    (hswap : ∃ s ∈ H, s.IsSwap)
    (hcycle : ∃ c ∈ H, ∃ z, c z = z ∧ (∀ x, c x = x ↔ x = z) ∧ c.IsCycle) : H = ⊤ := by
  have hall (a b : Fin 20) : Equiv.swap a b ∈ H := by
    by_cases hab : a = b
    · subst b; rw [Equiv.swap_self]; exact H.one_mem
    obtain ⟨s,hs,u,v,huv,rfl⟩ := hswap
    obtain ⟨c,hc,z,hz,hfix,hcy⟩ := hcycle
    obtain ⟨g,hg,hgu⟩ := htrans u a
    obtain ⟨q,hq,hqz⟩ := htrans z a
    let b' := q.symm (g v)
    let b'' := q.symm b
    have hb' : c b' ≠ b' := by
      intro he
      have he := (hfix _).mp he
      have he' := congrArg q he
      have : g v = g u := by simpa [b', hqz, hgu] using he'
      exact huv (g.injective this).symm
    have hb'' : c b'' ≠ b'' := by
      intro he
      have he := (hfix _).mp he
      have he' := congrArg q he
      exact hab (by simpa [b'', hqz] using he'.symm)
    obtain ⟨k,hk⟩ := hcy.sameCycle hb' hb''
    let w := q * c ^ k * q⁻¹ * g
    have hw : w ∈ H := H.mul_mem (H.mul_mem (H.mul_mem hq (H.zpow_mem hc k)) (H.inv_mem hq)) hg
    have hwu : w u = a := by
      simp only [w, Equiv.Perm.mul_apply, hgu, ← hqz, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      rw [Function.IsFixedPt.perm_zpow hz]
    have hwv : w v = b := by
      change q ((c ^ k) (q.symm (g v))) = b
      rw [show (c ^ k) (q.symm (g v)) = q.symm b from hk]
      simp
    have hh := H.mul_mem (H.mul_mem hw hs) (H.inv_mem hw)
    rwa [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right, hwu, hwv] at hh
  apply top_le_iff.mp
  rw [← Equiv.Perm.closure_isSwap]
  apply (Subgroup.closure_le H).mpr
  rintro s ⟨a,b,_,rfl⟩
  exact hall a b

end PencilGroup

namespace IntegralRoots
open NumberField
open scoped NumberField
attribute [local instance] Classical.propDecidable

lemma enumerate_roots {K : Type*} [Field K] (f : K[X]) (hf : f.Monic) (hs : f.Splits)
    (n : ℕ) (hn : f.natDegree = n) :
    ∃ r : Fin n → K, f = ∏ i, (X - C (r i)) := by
  classical
  let l := f.roots.toList
  have hl : l.length = n := by
    simp only [l, Multiset.length_toList, ← hs.natDegree_eq_card_roots, hn]
  let e : Fin n ≃ Fin l.length := finCongr hl.symm
  refine ⟨fun i => l[(e i).val], ?_⟩
  change f = ∏ i, (X - C l[(e i).val])
  calc
    f = (f.roots.map (fun x => X - C x)).prod := hs.eq_prod_roots_of_monic hf
    _ = ∏ i : Fin l.length, (X - C l[i.val]) := by
      symm
      calc
        _ = (l.map (fun x => X - C x)).prod := Fin.prod_univ_fun_getElem l (fun x => X - C x)
        _ = _ := by simp [l]
    _ = ∏ i, (X - C l[(e i).val]) := (e.prod_comp _).symm

lemma exists_integral_roots {K : Type*} [Field K] [NumberField K]
    (f : ℤ[X]) (hf : f.Monic) (n : ℕ) (hn : f.natDegree = n)
    (hs : (f.map (Int.castRingHom K)).Splits) :
    ∃ r : Fin n → 𝓞 K, f.map (Int.castRingHom (𝓞 K)) = ∏ i, (X - C (r i)) := by
  classical
  obtain ⟨r, hr⟩ := enumerate_roots (f.map (Int.castRingHom K)) (hf.map _) hs n
    (by rw [hf.natDegree_map]; exact hn)
  have hint (i : Fin n) : IsIntegral ℤ (r i) := by
    refine ⟨f, hf, ?_⟩
    rw [← Polynomial.eval_map]
    change (f.map (Int.castRingHom K)).eval (r i) = 0
    rw [hr]
    exact CertificateGalois.root_of_product r i
  let r' : Fin n → 𝓞 K := fun i => ⟨r i, hint i⟩
  refine ⟨r', ?_⟩
  apply Polynomial.map_injective (algebraMap (𝓞 K) K) RingOfIntegers.coe_injective
  have hcomp : (algebraMap (𝓞 K) K).comp (Int.castRingHom (𝓞 K)) = Int.castRingHom K := by
    ext; simp
  rw [Polynomial.map_map, hcomp, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact hr

lemma injective_of_squarefree_reduction {K : Type*} [Field K] [NumberField K]
    {n : ℕ} (r : Fin n → 𝓞 K) (f : ℤ[X])
    (hf : f.map (Int.castRingHom (𝓞 K)) = ∏ i, (X - C (r i)))
    (p : ℕ) [Fact p.Prime] (hs : (f.map (Int.castRingHom (ZMod p))).Separable) :
    Function.Injective r := by
  classical
  let S := 𝓞 K
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S) P
  let := hQmax
  let := hQ
  let F := S ⧸ Q
  let : Field F := Ideal.Quotient.field Q
  have hu : Q.under ℤ = P := (Ideal.over_def Q P).symm
  let ψ : S →+* F := Ideal.Quotient.mk Q
  let φ : ZMod p →+* F :=
    (Ideal.quotientMap Q (algebraMap ℤ S) (show P ≤ Q.comap (algebraMap ℤ S) from hu.symm.le)).comp
      (Int.quotientSpanNatEquivZMod p).symm.toRingHom
  have hφ : φ.comp (Int.castRingHom (ZMod p)) = Int.castRingHom F := by ext; simp
  have hfmap : (f.map (Int.castRingHom (ZMod p))).map φ = f.map (Int.castRingHom F) := by
    rw [Polynomial.map_map, hφ]
  have hi : Function.Injective (fun i => ψ (r i)) := by
    apply CertificateGalois.reduction_injective r f hf ψ
    rw [← hfmap]
    exact hs.map (f := φ)
  intro i j hij
  exact hi (congrArg ψ hij)

end IntegralRoots
namespace GaloisAction
open NumberField
open scoped NumberField
attribute [local instance] Classical.propDecidable
local instance prime41 : Fact (Nat.Prime 41) := ⟨by decide⟩
local instance prime131 : Fact (Nat.Prime 131) := ⟨by decide⟩
local instance prime139 : Fact (Nat.Prime 139) := ⟨by decide⟩
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

def permutationImage (r : Fin 20 → K) : Subgroup (Equiv.Perm (Fin 20)) where
  carrier := {π | ∃ σ : K ≃ₐ[ℚ] K, ∀ i, σ (r i) = r (π i)}
  one_mem' := ⟨1, fun _ => rfl⟩
  mul_mem' := by
    rintro π τ ⟨σ,hσ⟩ ⟨υ,hυ⟩
    refine ⟨σ * υ, ?_⟩
    intro i
    change σ (υ (r i)) = r (π (τ i))
    rw [hυ,hσ]
  inv_mem' := by
    rintro π ⟨σ,hσ⟩
    refine ⟨σ⁻¹, ?_⟩
    intro i
    apply σ.injective
    change σ (σ.symm (r i)) = σ (r (π.symm i))
    rw [AlgEquiv.apply_symm_apply, hσ, Equiv.apply_symm_apply]

lemma full_action (r : Fin 20 → 𝓞 K) (hr : Function.Injective r) (f : ℤ[X])
    (hf : f.map (Int.castRingHom (𝓞 K)) = ∏ i, (X - C (r i)))
    (hs41 : (f.map (Int.castRingHom (ZMod 41))).Separable)
    (hc4 : (EuclideanDomain.gcd (f.map (Int.castRingHom (ZMod 41))) (X ^ (41 ^ 4) - X)).natDegree = 0)
    (hc10 : (EuclideanDomain.gcd (f.map (Int.castRingHom (ZMod 41))) (X ^ (41 ^ 10) - X)).natDegree = 0)
    (hc20 : (EuclideanDomain.gcd (f.map (Int.castRingHom (ZMod 41))) (X ^ (41 ^ 20) - X)).natDegree = 20)
    (hs131 : (f.map (Int.castRingHom (ZMod 131))).Separable)
    (hc17 : (EuclideanDomain.gcd (f.map (Int.castRingHom (ZMod 131))) (X ^ (131 ^ 17) - X)).natDegree = 18)
    (hs139 : (f.map (Int.castRingHom (ZMod 139))).Separable)
    (hc1 : (EuclideanDomain.gcd (f.map (Int.castRingHom (ZMod 139))) (X ^ (139 ^ 1) - X)).natDegree = 1)
    (hc19 : (EuclideanDomain.gcd (f.map (Int.castRingHom (ZMod 139))) (X ^ (139 ^ 19) - X)).natDegree = 20) :
    ∀ π : Equiv.Perm (Fin 20), ∃ σ : K ≃ₐ[ℚ] K, ∀ i, σ (r i : K) = (r (π i) : K) := by
  classical
  obtain ⟨σ41,π41,hσ41,hπ41⟩ := CertificateGalois.frobenius_permutation r hr f hf 41 hs41
  obtain ⟨σ131,π131,hσ131,hπ131⟩ := CertificateGalois.frobenius_permutation r hr f hf 131 hs131
  obtain ⟨σ139,π139,hσ139,hπ139⟩ := CertificateGalois.frobenius_permutation r hr f hf 139 hs139
  let H := permutationImage (fun i => (r i : K))
  have hm41 : π41 ∈ H := ⟨σ41,hσ41⟩
  have hm131 : π131 ∈ H := ⟨σ131,hσ131⟩
  have hm139 : π139 ∈ H := ⟨σ139,hσ139⟩
  have h4 : PencilGroup.fixedCount (π41 ^ 4) = 0 := by
    convert (hπ41 4).trans hc4 using 1; simp only [PencilGroup.fixedCount]
    all_goals
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h10 : PencilGroup.fixedCount (π41 ^ 10) = 0 := by
    convert (hπ41 10).trans hc10 using 1; simp only [PencilGroup.fixedCount]
    all_goals
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h20 : PencilGroup.fixedCount (π41 ^ 20) = 20 := by
    convert (hπ41 20).trans hc20 using 1; simp only [PencilGroup.fixedCount]
    all_goals
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h17 : PencilGroup.fixedCount (π131 ^ 17) = 18 := by
    convert (hπ131 17).trans hc17 using 1; simp only [PencilGroup.fixedCount]
    all_goals
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : PencilGroup.fixedCount π139 = 1 := by
    convert (hπ139 1).trans hc1 using 1; simp only [PencilGroup.fixedCount]
    all_goals
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  have h19 : PencilGroup.fixedCount (π139 ^ 19) = 20 := by
    convert (hπ139 19).trans hc19 using 1; simp only [PencilGroup.fixedCount]
    all_goals
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hH : H = ⊤ := by
    apply PencilGroup.full_symmetric
    · intro x y
      obtain ⟨k,hk⟩ := PencilGroup.transitive_of_frob41 π41 h4 h10 h20 x y
      exact ⟨π41 ^ k, H.pow_mem hm41 k, hk⟩
    · exact ⟨π131 ^ 17, H.pow_mem hm131 17, PencilGroup.swap_of_frob131 π131 h17⟩
    · exact ⟨π139, hm139, PencilGroup.cycle_of_frob139 π139 h1 h19⟩
  intro π
  have hm : π ∈ H := hH ▸ Subgroup.mem_top π
  exact hm
end GaloisAction

end

end OAI
