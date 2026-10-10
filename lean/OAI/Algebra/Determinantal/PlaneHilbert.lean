import OAI.Algebra.Determinantal.BranchConductor

namespace OAI

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

abbrev Plane := MvPolynomial (Fin 2) K
abbrev weight : Fin 2 → ℤ := fun _ => 1
abbrev H (d : ℤ) := Piece (K := K) weight d

noncomputable def pieceCoordinates (d : ℤ) : H (K := K) d ≃ₗ[K] (DegreeIndex (Fin 2) d → K) where
  toFun p s := p.val.coeff s.val
  invFun b := ⟨∑ s : DegreeIndex (Fin 2) d, monomial s.val (b s), sum_degree_homogeneous d b⟩
  left_inv p := Subtype.ext (homogeneous_sum_degree p.property).symm
  right_inv b := funext (coeff_sum_degree d b)
  map_add' p q := by ext s; rfl
  map_smul' c p := by ext s; exact coeff_smul s.val c p.val

instance piece_finite (d : ℤ) : Module.Finite K (H (K := K) d) :=
  Module.Finite.of_injective (pieceCoordinates d).toLinearMap (pieceCoordinates d).injective

lemma degree_fin_two (s : Fin 2 →₀ ℕ) : s.degree = s 0+s 1 := by
  rw [Finsupp.degree_eq_sum]
  exact Fin.sum_univ_two s

noncomputable def degreeIndexEquiv (n : ℕ) : DegreeIndex (Fin 2) (n : ℤ) ≃ Fin (n+1) where
  toFun s := ⟨s.val 0, by
    have hs : s.val 0+s.val 1 = n := by exact_mod_cast degree_fin_two s.val ▸ s.property
    omega⟩
  invFun i := ⟨Finsupp.equivFunOnFinite.symm (fun j => if j=0 then i.val else n-i.val), by
    rw [degree_fin_two]
    simp only [Finsupp.coe_equivFunOnFinite_symm, ↓reduceIte, Fin.isValue]
    have hh : (1 : Fin 2) ≠ 0 := by decide
    simp only [hh, ↓reduceIte]
    omega⟩
  left_inv s := by
    apply Subtype.ext
    ext i
    have hs : s.val 0+s.val 1 = n := by exact_mod_cast degree_fin_two s.val ▸ s.property
    fin_cases i
    · simp
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
      change (if (1 : Fin 2) = 0 then s.val 0 else n - s.val 0) = s.val 1
      simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
      omega
  right_inv i := by
    apply Fin.ext
    simp

lemma finrank_piece (d : ℤ) : Module.finrank K (H (K := K) d) = (d+1).toNat := by
  rw [(pieceCoordinates d).finrank_eq, Module.finrank_pi]
  by_cases hd : 0 ≤ d
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [Fintype.card_congr (degreeIndexEquiv n), Fintype.card_fin]
    omega
  · have : IsEmpty (DegreeIndex (Fin 2) d) := ⟨fun s => by
      have hs : (0 : ℤ) ≤ s.val.degree := by positivity
      exact hd (s.property ▸ hs)⟩
    have hc : Fintype.card (DegreeIndex (Fin 2) d) = 0 := Fintype.card_eq_zero
    rw [hc]
    omega

end PermanentBorder.PlaneHilbert

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

noncomputable def varMul (i : Fin 2) (n : ℕ) :
    H (K := K) (n : ℤ) →ₗ[K] H (K := K) ((n+1 : ℕ) : ℤ) where
  toFun p := ⟨X i * p.val, by
    have hh := (homogeneous_intWeight (isHomogeneous_X K i)).mul p.property
    change (X i * p.val).IsWeightedHomogeneous weight ((n+1 : ℕ) : ℤ)
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hh⟩
  map_add' p q := Subtype.ext (mul_add _ _ _)
  map_smul' c p := Subtype.ext (mul_smul_comm _ _ _)

lemma varMul_injective (i : Fin 2) (n : ℕ) :
    Function.Injective (varMul (K := K) i n) := by
  intro p q h
  apply Subtype.ext
  exact mul_left_cancel₀ (X_ne_zero i) (congrArg Subtype.val h)

lemma piece_degreeOf_le {n : ℕ} (p : H (K := K) (n : ℤ)) (i : Fin 2) :
    p.val.degreeOf i ≤ n :=
  (degreeOf_le_totalDegree _ _).trans (intWeight_homogeneous p.property).totalDegree_le

theorem exists_varMul_outside {n : ℕ} (W : Submodule K (H (K := K) (n : ℤ)))
    (hW : W ≠ ⊥) :
    ∃ p ∈ W, varMul 0 n p ∉ W.map (varMul 1 n) := by
  classical
  obtain ⟨p,hp,hp0⟩ := W.ne_bot_iff.mp hW
  have hpv : p.val ≠ 0 := fun h => hp0 (Subtype.ext h)
  let P : ℕ → Prop := fun j => ∃ v ∈ W, v.val ≠ 0 ∧ v.val.degreeOf 0 = j
  have he : P (p.val.degreeOf 0) := ⟨p,hp,hpv,rfl⟩
  have hb := piece_degreeOf_le p 0
  obtain ⟨q,hq,hq0,hqm⟩ := Nat.findGreatest_spec hb he
  refine ⟨q,hq,?_⟩
  rintro ⟨z,hz,heq⟩
  have hz0 : z.val ≠ 0 := by
    intro h
    have hh := congrArg Subtype.val heq
    change X 1 * z.val = X 0 * q.val at hh
    rw [h,mul_zero] at hh
    exact (mul_ne_zero (X_ne_zero 0) hq0) hh.symm
  have hzm : z.val.degreeOf 0 ≤ Nat.findGreatest P n :=
    Nat.le_findGreatest (piece_degreeOf_le z 0) ⟨z,hz,hz0,rfl⟩
  have hh := congrArg (fun v : H (K := K) ((n+1 : ℕ) : ℤ) => v.val.degreeOf 0) heq
  change (X 1 * z.val).degreeOf 0 = (X 0 * q.val).degreeOf 0 at hh
  rw [mul_comm (X 1), degreeOf_mul_X_of_ne _ (by decide : (0 : Fin 2) ≠ 1),
    mul_comm (X 0), (degreeOf_mul_X_eq_degreeOf_add_one_iff 0 q.val).mpr hq0] at hh
  omega

lemma finrank_varMul_sup {n : ℕ} (W : Submodule K (H (K := K) (n : ℤ)))
    (hW : W ≠ ⊥) :
    Module.finrank K W + 1 ≤
      Module.finrank K ↥(W.map (varMul 0 n) ⊔ W.map (varMul 1 n)) := by
  obtain ⟨p,hp,hnot⟩ := exists_varMul_outside W hW
  have hlt : W.map (varMul 1 n) < W.map (varMul 0 n) ⊔ W.map (varMul 1 n) := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    apply hnot
    rw [heq]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hp)
  have hf := Submodule.finrank_strictMono hlt
  dsimp only at hf
  rw [← (Submodule.equivMapOfInjective (varMul 1 n) (varMul_injective 1 n) W).finrank_eq] at hf
  omega

noncomputable abbrev idealComponent (I : Ideal (Plane (K := K))) (n : ℕ) :
    Submodule K (H (K := K) (n : ℤ)) :=
  (I.restrictScalars K).comap (H (K := K) (n : ℤ)).subtype

noncomputable def hVector (I : Ideal (Plane (K := K))) (n : ℕ) : ℕ :=
  Module.finrank K (H (K := K) (n : ℤ) ⧸ idealComponent I n)

lemma hVector_add_component (I : Ideal (Plane (K := K))) (n : ℕ) :
    hVector I n + Module.finrank K (idealComponent I n) = n+1 := by
  rw [hVector, Submodule.finrank_quotient_add_finrank, finrank_piece]
  omega

lemma hVector_le (I : Ideal (Plane (K := K))) (n : ℕ) : hVector I n ≤ n+1 := by
  have := hVector_add_component I n
  omega

lemma varMul_component_le (I : Ideal (Plane (K := K))) (i : Fin 2) (n : ℕ) :
    (idealComponent I n).map (varMul i n) ≤ idealComponent I (n+1) := by
  rintro _ ⟨p,hp,rfl⟩
  exact I.mul_mem_left _ hp

lemma hVector_succ_le (I : Ideal (Plane (K := K))) (n : ℕ) :
    hVector I (n+1) ≤ hVector I n + 1 := by
  have hmono := Submodule.finrank_mono (varMul_component_le I 0 n)
  rw [← (Submodule.equivMapOfInjective (varMul 0 n) (varMul_injective 0 n)
    (idealComponent I n)).finrank_eq] at hmono
  have h1 := hVector_add_component I n
  have h2 := hVector_add_component I (n+1)
  omega

lemma hVector_succ_le_of_deficit (I : Ideal (Plane (K := K))) {n : ℕ}
    (hn : hVector I n < n+1) : hVector I (n+1) ≤ hVector I n := by
  have hW : idealComponent I n ≠ ⊥ := by
    intro h
    have hh := hVector_add_component I n
    rw [h, finrank_bot] at hh
    omega
  have hh := finrank_varMul_sup (idealComponent I n) hW
  have hl := Submodule.finrank_mono
    (sup_le (varMul_component_le I 0 n) (varMul_component_le I 1 n))
  have h1 := hVector_add_component I n
  have h2 := hVector_add_component I (n+1)
  omega

lemma hVector_le_of_deficit (I : Ideal (Plane (K := K))) {n m : ℕ}
    (hn : hVector I n < n+1) (hnm : n ≤ m) : hVector I m ≤ hVector I n := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
    exact (hVector_succ_le_of_deficit I (by omega : hVector I m < m+1)).trans ih

lemma hVector_normalized_succ (I : Ideal (Plane (K := K))) (n : ℕ) :
    (n+1) * hVector I (n+1) ≤ (n+2) * hVector I n := by
  have hb := hVector_le I n
  rcases hb.eq_or_lt with he|hl
  · rw [he]
    have hh := hVector_le I (n+1)
    nlinarith
  · have hh := hVector_succ_le_of_deficit I hl
    nlinarith

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

lemma homogeneous_factor_right {a b : Plane (K := K)} {e t : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (h0 : a ≠ 0)
    (hab : (a*b).IsWeightedHomogeneous weight t) :
    b.IsWeightedHomogeneous weight (t-e) := by
  have hh := weightedHomogeneousComponent_eq_self hab
  rw [project_mul weight ha] at hh
  have hb : weightedHomogeneousComponent weight (t-e) b = b := mul_left_cancel₀ h0 hh
  rw [← hb]
  exact weightedHomogeneousComponent_mem weight b (t-e)

lemma mulPiece_injective {a : Plane (K := K)} {e : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (ha0 : a ≠ 0) (t : ℤ) :
    Function.Injective (mulPiece weight ha t) := by
  intro p q h
  apply Subtype.ext
  exact mul_left_cancel₀ ha0 (congrArg Subtype.val h)

noncomputable abbrev multiplicationRange {a : Plane (K := K)} {e : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (t : ℤ) :=
  LinearMap.range (mulPiece weight ha t)

lemma finrank_multiplicationRange {a : Plane (K := K)} {e : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (ha0 : a ≠ 0) (t : ℤ) :
    Module.finrank K (multiplicationRange ha t) = (t-e+1).toNat := by
  rw [LinearMap.finrank_range_of_inj (mulPiece_injective ha ha0 t), finrank_piece]

lemma multiplicationRange_inf {a b : Plane (K := K)} {e f : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (hb : b.IsWeightedHomogeneous weight f)
    (hb0 : b ≠ 0) (hab : IsRelPrime a b) (t : ℤ) :
    multiplicationRange ha t ⊓ multiplicationRange hb t =
      multiplicationRange (ha.mul hb) t := by
  ext p
  constructor
  · rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    have huv : a*u.val = b*v.val := congrArg Subtype.val (hu.trans hv.symm)
    have hd : b ∣ u.val := hab.symm.dvd_of_dvd_mul_left ⟨v,huv⟩
    obtain ⟨w,hw⟩ := hd
    have hbw : (b*w).IsWeightedHomogeneous weight (t-e) := hw ▸ u.property
    have hwh := homogeneous_factor_right hb hb0 hbw
    have hh : (t-e)-f = t-(e+f) := by ring
    rw [hh] at hwh
    refine ⟨⟨w,hwh⟩,?_⟩
    apply Subtype.ext
    change (a*b)*w = p.val
    rw [mul_assoc, ← hw]
    exact congrArg Subtype.val hu
  · rintro ⟨w,hw⟩
    have hbw : (b*w.val).IsWeightedHomogeneous weight (t-e) := by
      convert hb.mul w.property using 1; ring
    have haw : (a*w.val).IsWeightedHomogeneous weight (t-f) := by
      convert ha.mul w.property using 1; ring
    constructor
    · refine ⟨⟨b*w.val,hbw⟩,?_⟩
      apply Subtype.ext
      change a*(b*w.val) = p.val
      rw [← mul_assoc]
      exact congrArg Subtype.val hw
    · refine ⟨⟨a*w.val,haw⟩,?_⟩
      apply Subtype.ext
      change b*(a*w.val) = p.val
      rw [← mul_assoc, mul_comm b a]
      exact congrArg Subtype.val hw

lemma multiplicationRange_le_component (I : Ideal (Plane (K := K)))
    {a : Plane (K := K)} {e : ℤ} (ha : a.IsWeightedHomogeneous weight e)
    (haI : a ∈ I) (n : ℕ) : multiplicationRange ha (n : ℤ) ≤ idealComponent I n := by
  rintro _ ⟨p,rfl⟩
  exact I.mul_mem_right _ haI

theorem hVector_coprime_bound (I : Ideal (Plane (K := K)))
    {a b : Plane (K := K)} {e f : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (hb : b.IsWeightedHomogeneous weight f)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : IsRelPrime a b)
    (haI : a ∈ I) (hbI : b ∈ I) (n : ℕ) :
    hVector I n + ((n : ℤ)-e+1).toNat + ((n : ℤ)-f+1).toNat ≤
      n+1 + ((n : ℤ)-(e+f)+1).toNat := by
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (multiplicationRange ha (n : ℤ)) (multiplicationRange hb (n : ℤ))
  rw [multiplicationRange_inf ha hb hb0 hab,
    finrank_multiplicationRange ha ha0, finrank_multiplicationRange hb hb0,
    finrank_multiplicationRange (ha.mul hb) (mul_ne_zero ha0 hb0)] at hh
  have hl : Module.finrank K ↥(multiplicationRange ha (n : ℤ) ⊔
      multiplicationRange hb (n : ℤ)) ≤ Module.finrank K (idealComponent I n) :=
    Submodule.finrank_mono (sup_le
    (multiplicationRange_le_component I ha haI n)
    (multiplicationRange_le_component I hb hbI n))
  have heq := hVector_add_component I n
  omega

end PermanentBorder.PlaneHilbert

end OAI
