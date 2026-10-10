import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.LaurentMoments
import OAI.AlgebraicGeometry.Seshadri.Interpolation.RowCompression

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
theorem MomentJetZero.polynomials {ι : Type*} (s : Finset ι) (c x y : ι → ℂ)
    (m : ℕ) (h : MomentJetZero s c x y m) (P Q : Polynomial ℂ)
    (hdeg : P.natDegree + Q.natDegree < m) :
    ∑ i ∈ s, c i * P.eval (x i) * Q.eval (y i) = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a ha
  have hab : a + b < m := (Nat.add_le_add
    (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp ha))
    (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hb))).trans_lt hdeg
  calc
    (∑ i ∈ s, c i * (P.coeff a * x i ^ a) * (Q.coeff b * y i ^ b)) =
        (P.coeff a * Q.coeff b) * ∑ i ∈ s, c i * x i ^ a * y i ^ b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [h a b hab, mul_zero]

theorem momentJetZero_of_falling {ι : Type*} (s : Finset ι) (c x y : ι → ℂ)
    (m : ℕ) (h : ∀ a b : ℕ, a + b < m →
      ∑ i ∈ s, c i * (descPochhammer ℂ a).eval (x i) *
        (descPochhammer ℂ b).eval (y i) = 0) : MomentJetZero s c x y m := by
  intro a b hab
  let L : Polynomial ℂ →ₗ[ℂ] ℂ := ∑ i ∈ s, (c i * y i ^ b) • Polynomial.leval (x i)
  have hl (j : ℕ) (hj : j ≤ a) : L (descPochhammer ℂ j) = 0 := by
    let M : Polynomial ℂ →ₗ[ℂ] ℂ := ∑ i ∈ s,
      (c i * (descPochhammer ℂ j).eval (x i)) • Polynomial.leval (y i)
    have hm (l : ℕ) (hl : l ≤ b) : M (descPochhammer ℂ l) = 0 := by
      simpa [M] using h j l (by omega)
    have he := linearMap_zero_power_of_falling M b hm
    simpa [L, M, mul_assoc, mul_left_comm, mul_comm] using he
  have he := linearMap_zero_power_of_falling L a hl
  simpa [L, mul_assoc, mul_left_comm, mul_comm] using he

noncomputable def indexedLaurent {ι : Type*} (s : Finset ι) (e : ι → ℤ × ℤ)
    (c : ι → ℂ) (u z : ℂ) : ℂ := ∑ i ∈ s, c i * u ^ (e i).1 * z ^ (e i).2

theorem indexedLaurent_mixed_deriv {ι : Type*} (s : Finset ι) (e : ι → ℤ × ℤ)
    (c : ι → ℂ) (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) (a b : ℕ) :
    iteratedDeriv b (fun v => iteratedDeriv a (fun w => indexedLaurent s e c w v) u) z =
      ∑ i ∈ s, c i * (descPochhammer ℂ a).eval ((e i).1 : ℂ) *
        u ^ ((e i).1 - (a : ℤ)) * (descPochhammer ℂ b).eval ((e i).2 : ℂ) *
          z ^ ((e i).2 - (b : ℤ)) := by
  have hi (v : ℂ) : iteratedDeriv a (fun w => indexedLaurent s e c w v) u =
      ∑ i ∈ s, c i * (descPochhammer ℂ a).eval ((e i).1 : ℂ) *
        u ^ ((e i).1 - (a : ℤ)) * v ^ (e i).2 := by
    unfold indexedLaurent
    rw [iteratedDeriv_fun_sum (fun i _ =>
      (contDiffAt_const.mul (contDiffAt_zpow_ne_zero (e i).1 u hu a)).mul contDiffAt_const)]
    apply Finset.sum_congr rfl
    intro i _
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_eq_iterate, iter_deriv_zpow, descPochhammer_eval_eq_prod_range]
    ring
  simp_rw [hi]
  rw [iteratedDeriv_fun_sum (fun i _ =>
    contDiffAt_const.mul (contDiffAt_zpow_ne_zero (e i).2 z hz b))]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  simp_rw [descPochhammer_eval_eq_prod_range]
  ring

theorem indexedLaurent_deriv_scaled {ι : Type*} (s : Finset ι) (e : ι → ℤ × ℤ)
    (c : ι → ℂ) (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) (a b : ℕ) :
    (iteratedDeriv b (fun v => iteratedDeriv a (fun w => indexedLaurent s e c w v) u) z) *
      (u ^ a * z ^ b) =
      ∑ i ∈ s, (c i * u ^ (e i).1 * z ^ (e i).2) *
        (descPochhammer ℂ a).eval ((e i).1 : ℂ) *
        (descPochhammer ℂ b).eval ((e i).2 : ℂ) := by
  rw [indexedLaurent_mixed_deriv s e c u z hu hz, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_sub₀ hu, zpow_sub₀ hz, zpow_natCast, zpow_natCast]
  field_simp

theorem indexedLaurent_jet_iff_moments {ι : Type*} (s : Finset ι) (e : ι → ℤ × ℤ)
    (c : ι → ℂ) (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) (m : ℕ) :
    MixedJetZero (indexedLaurent s e c) u z m ↔
      MomentJetZero s (fun i => c i * u ^ (e i).1 * z ^ (e i).2)
        (fun i => ((e i).1 : ℂ)) (fun i => ((e i).2 : ℂ)) m := by
  constructor
  · intro hj
    apply momentJetZero_of_falling
    intro a b hab
    rw [← indexedLaurent_deriv_scaled s e c u z hu hz, hj a b hab, zero_mul]
  · intro hm a b hab
    have hh := hm.polynomials s _ _ _ m (descPochhammer ℂ a) (descPochhammer ℂ b)
      (by simpa only [descPochhammer_natDegree] using hab)
    rw [← indexedLaurent_deriv_scaled s e c u z hu hz] at hh
    exact (mul_eq_zero.mp hh).resolve_right (mul_ne_zero (pow_ne_zero a hu) (pow_ne_zero b hz))

theorem finiteJetColumn_indexedLaurent {ι : Type*} (s : Finset ι)
    (e : ι → ℤ × ℤ) (c : ι → ℂ) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (hnz : ∀ i, (points i).1 ≠ 0 ∧ (points i).2 ≠ 0) :
    finiteJetColumn r m points (indexedLaurent s e c) =
      ∑ i ∈ s, c i • finiteJetColumn r m points
        (fun u z => u ^ (e i).1 * z ^ (e i).2) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, finiteJetColumn]
  split_ifs with hab
  · rw [indexedLaurent_mixed_deriv s e c _ _ (hnz j.1).1 (hnz j.1).2]
    apply Finset.sum_congr rfl
    intro i _
    rw [mixed_deriv_separated (fun u : ℂ => u ^ (e i).1)
      (fun z : ℂ => z ^ (e i).2)]
    simp only [iteratedDeriv_eq_iterate, iter_deriv_zpow,
      descPochhammer_eval_eq_prod_range]
    ring
  · simp

theorem finiteJetColumn_eq_zero_iff (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (f : ℂ → ℂ → ℂ) :
    finiteJetColumn r m points f = 0 ↔ ∀ i, MixedJetZero f (points i).1 (points i).2 m := by
  constructor
  · intro h i a b hab
    have ha : a < m := by omega
    have hb : b < m := by omega
    have he := congrFun h (i, ⟨a, ha⟩, ⟨b, hb⟩)
    simpa only [finiteJetColumn, hab, ite_true, Pi.zero_apply] using he
  · intro h
    funext j
    simp only [finiteJetColumn, Pi.zero_apply]
    split_ifs with hab
    · exact h j.1 j.2.1 j.2.2 hab
    · rfl

theorem shear_monomial (u v : ℂ) (hu : u ≠ 0) (a b : ℤ) :
    u ^ (a + b) * (v / u) ^ b = u ^ a * v ^ b := by
  rw [zpow_add₀ hu, div_zpow]
  field_simp

theorem shearLaurent_jet {ι : Type*} (s : Finset ι) (e : ι → ℤ × ℤ) (c : ι → ℂ)
    (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (m : ℕ)
    (h : MixedJetZero (indexedLaurent s (fun i => ((e i).1 + (e i).2, (e i).2)) c)
      u (v / u) m) : MixedJetZero (indexedLaurent s e c) u v m := by
  have hm := (indexedLaurent_jet_iff_moments s _ c u (v / u) hu
    (div_ne_zero hv hu) m).mp h
  have hc (i : ι) : c i * u ^ ((e i).1 + (e i).2) * (v / u) ^ (e i).2 =
      c i * u ^ (e i).1 * v ^ (e i).2 := by
    rw [mul_assoc, shear_monomial u v hu, ← mul_assoc]
  simp only [hc, Int.cast_add] at hm
  have hf := MomentJetZero.affine s _ _ _ m hm 1 (-1) 0 0 1 0
  apply (indexedLaurent_jet_iff_moments s e c u v hu hv m).mpr
  simpa only [one_mul, neg_one_mul, add_zero, zero_mul, zero_add, add_neg_cancel_right] using hf

theorem shear_tuple_injective {r : ℕ} (points : Fin r → ℂ × ℂ)
    (hi : Function.Injective points) (hnz : ∀ i, (points i).1 ≠ 0) :
    Function.Injective (fun i => ((points i).1, (points i).2 / (points i).1)) := by
  intro i j hij
  have h1 : (points i).1 = (points j).1 := by
    simpa only using congrArg (fun p : ℂ × ℂ => p.1) hij
  have h2 : (points i).2 / (points i).1 = (points j).2 / (points j).1 :=
    congrArg (fun p : ℂ × ℂ => p.2) hij
  rw [h1] at h2
  exact hi (Prod.ext h1 ((div_left_inj' (hnz j)).mp h2))

theorem shear_jet_rank {ι : Type*} (e : ι → ℤ × ℤ) (r m : ℕ)
    (points : Fin r → ℂ × ℂ) (hnz : ∀ i, (points i).1 ≠ 0 ∧ (points i).2 ≠ 0)
    (h : LinearIndependent ℂ (fun i => finiteJetColumn r m points
      (fun u z => u ^ (e i).1 * z ^ (e i).2))) :
    LinearIndependent ℂ (fun i => finiteJetColumn r m
      (fun l => ((points l).1, (points l).2 / (points l).1))
        (fun x z => x ^ ((e i).1 + (e i).2) * z ^ (e i).2)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  have hpn : ∀ l, (points l).1 ≠ 0 ∧ (points l).2 / (points l).1 ≠ 0 :=
    fun l => ⟨(hnz l).1, div_ne_zero (hnz l).2 (hnz l).1⟩
  have hz : finiteJetColumn r m
      (fun l => ((points l).1, (points l).2 / (points l).1))
      (indexedLaurent s (fun i => ((e i).1 + (e i).2, (e i).2)) c) = 0 := by
    rw [finiteJetColumn_indexedLaurent s _ c r m _ hpn]
    exact hc
  have hz' : finiteJetColumn r m points (indexedLaurent s e c) = 0 := by
    apply (finiteJetColumn_eq_zero_iff r m points _).mpr
    intro l
    exact shearLaurent_jet s e c _ _ (hnz l).1 (hnz l).2 m
      ((finiteJetColumn_eq_zero_iff r m _ _).mp hz l)
  rw [finiteJetColumn_indexedLaurent s e c r m points hnz] at hz'
  exact linearIndependent_iff'.mp h s c hz' i hi

theorem diagonal_row_compression {Q : Type*} [Fintype Q]
    (q : Q → ℤ) (B n : Q → ℕ) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (hi : Function.Injective points) (hnz : ∀ i, (points i).1 ≠ 0)
    (h₀ : LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m points
      (fun u z => u ^ q i.1 * z ^ (i.2 : ℕ)))) :
    ∃ p : Fin r → ℂ × ℂ, Function.Injective p ∧
      (∀ i, (p i).1 ≠ 0 ∧ (p i).2 ≠ 0) ∧
      LinearIndependent ℂ (fun i : RowIndex n => finiteJetColumn r m p
        (fun x z => x ^ (q i.1 + ((B i.1 + (i.2 : ℕ) : ℕ) : ℤ)) *
          z ^ (B i.1 + (i.2 : ℕ)))) := by
  obtain ⟨p, hpi, hpn, hp⟩ := compression_exists_tuple q B n r m points hi hnz h₀
  let e : RowIndex n → ℤ × ℤ := fun i => (q i.1, (B i.1 + (i.2 : ℕ) : ℕ))
  have hp' : LinearIndependent ℂ (fun i => finiteJetColumn r m p
      (fun u z => u ^ (e i).1 * z ^ (e i).2)) := by
    simpa only [e, zpow_natCast] using hp
  refine ⟨(fun l => ((p l).1, (p l).2 / (p l).1)),
    shear_tuple_injective p hpi (fun i => (hpn i).1), ?_, ?_⟩
  · intro i
    exact ⟨(hpn i).1, div_ne_zero (hpn i).2 (hpn i).1⟩
  · simpa only [e, zpow_natCast] using shear_jet_rank e r m p hpn hp'

theorem indexedLaurent_nonzeroSupport {ι : Type*} (s : Finset ι)
    (e : ι → ℤ × ℤ) (c : ι → ℂ) :
    indexedLaurent (s.filter (fun i => c i ≠ 0)) e c = indexedLaurent s e c := by
  classical
  funext u z
  simp only [indexedLaurent, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h <;> simp_all

theorem indexedLaurent_image {ι : Type*} [Nonempty ι] (s : Finset ι)
    (e : ι → ℤ × ℤ) (c : ι → ℂ) (he : Set.InjOn e s) :
    indexedLaurent s e c = laurentEval (s.image e) (c ∘ Function.invFunOn e s) := by
  classical
  funext u z
  rw [laurentEval_eq_sum, Finset.sum_image (fun i hi j hj hij => he hi hj hij)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Function.comp_apply, he.leftInvOn_invFunOn hi]

theorem monomial_jet_rank_of_test (Ω : Set (ℝ × ℝ)) (r m : ℕ)
    (points : Fin r → ℂ × ℂ) (hnz : ∀ l, (points l).1 ≠ 0 ∧ (points l).2 ≠ 0)
    (htest : ∀ (s : Finset (ℤ × ℤ)), s.Nonempty →
      (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ Ω) →
      ∀ c : ℤ × ℤ → ℂ, (∀ p ∈ s, c p ≠ 0) →
        ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c) (points l).1 (points l).2 m)
    {ι : Type*} (e : ι → ℤ × ℤ) (he : Function.Injective e)
    (hΩ : ∀ i, (((e i).1 : ℝ), ((e i).2 : ℝ)) ∈ Ω) :
    LinearIndependent ℂ (fun i => finiteJetColumn r m points
      (fun u z => u ^ (e i).1 * z ^ (e i).2)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  by_contra hci
  let s' := s.filter (fun i => c i ≠ 0)
  have hi' : i ∈ s' := Finset.mem_filter.mpr ⟨hi, hci⟩
  have hs' : s'.Nonempty := ⟨i, hi'⟩
  let : Nonempty ι := ⟨i⟩
  have he' : Set.InjOn e s' := he.injOn
  have hz : finiteJetColumn r m points (indexedLaurent s e c) = 0 := by
    rw [finiteJetColumn_indexedLaurent s e c r m points hnz]
    exact hc
  rw [← indexedLaurent_nonzeroSupport s e c] at hz
  change finiteJetColumn r m points (indexedLaurent s' e c) = 0 at hz
  rw [indexedLaurent_image s' e c he'] at hz
  obtain ⟨l, hl⟩ := htest (s'.image e) (hs'.image e)
    (by intro p hp; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp; exact hΩ j)
    (c ∘ Function.invFunOn e s') (by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      simpa only [Function.comp_apply, he'.leftInvOn_invFunOn hj] using
        (Finset.mem_filter.mp hj).2)
  exact hl ((finiteJetColumn_eq_zero_iff r m points _).mp hz l)


end MaximalSeshadri.Interpolation
end

end OAI
