import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularStateZero
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularBasis
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGluing

namespace OAI

/-! Every C² radial solution belongs to the regular two-column plane. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

private theorem valueDet_ne_zero_of_kernel (u v : ℂ × ℂ)
    (hk : ∀ a b : ℂ, a • u + b • v = 0 → a = 0 ∧ b = 0) :
    spectralValueDet u v ≠ 0 := by
  intro hd
  change u.1 * v.2 - u.2 * v.1 = 0 at hd
  have h1 := hk v.1 (-u.1) (by
    apply Prod.ext
    · change v.1 * u.1 + -u.1 * v.1 = 0
      ring
    · change v.1 * u.2 + -u.1 * v.2 = 0
      linear_combination -hd)
  have h2 := hk v.2 (-u.2) (by
    apply Prod.ext
    · change v.2 * u.1 + -u.2 * v.1 = 0
      linear_combination hd
    · change v.2 * u.2 + -u.2 * v.2 = 0
      ring)
  have hu : u = 0 := Prod.ext (neg_eq_zero.mp h1.2) (neg_eq_zero.mp h2.2)
  exact one_ne_zero (hk 1 0 (by simp [hu])).1

theorem homogeneousRegular_basis_complete (νp νm : ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (m : ℕ) (Q : ℝ → ℂ) (hQ : Continuous Q) (R : ℝ) (hR : 0 < R)
    (U Vp Vm : ℝ → E₄)
    (hUc : ContDiff ℝ 2 (fun r => (U r).1.1) ∧ ContDiff ℝ 2 (fun r => (U r).2.1))
    (hpc : ContDiff ℝ 2 (fun r => (Vp r).1.1) ∧ ContDiff ℝ 2 (fun r => (Vp r).2.1))
    (hmc : ContDiff ℝ 2 (fun r => (Vm r).1.1) ∧ ContDiff ℝ 2 (fun r => (Vm r).2.1))
    (hU : ∀ r ∈ Ioc 0 R, HasDerivAt U
      (spectralPhysicalCircularField νp νm (eta : ℂ) m (Q r) r (U r)) r)
    (hp : ∀ r ∈ Ioc 0 R, HasDerivAt Vp
      (spectralPhysicalCircularField νp νm (eta : ℂ) m (Q r) r (Vp r)) r)
    (hm : ∀ r ∈ Ioc 0 R, HasDerivAt Vm
      (spectralPhysicalCircularField νp νm (eta : ℂ) m (Q r) r (Vm r)) r)
    (hRank : LinearIndependent ℂ ![Vp R, Vm R]) :
    ∃ c : ℂ × ℂ, U R = c.1 • Vp R + c.2 • Vm R := by
  classical
  obtain ⟨δ, hδ, hzero⟩ := homogeneousRegular_state_zero_radius νp νm m Q hQ
  let t := min δ R / 2
  have ht : 0 < t := by dsimp only [t]; exact div_pos (lt_min hδ hR) (by norm_num)
  have htδ : t ≤ δ := by
    have hh := min_le_left δ R
    dsimp only [t]
    linarith
  have htR : t < R := by
    have hh := min_le_right δ R
    dsimp only [t]
    linarith
  let W := fun x y z : ℂ => fun r => x • U r + y • Vp r + z • Vm r
  have hWc (x y z : ℂ) :
      ContDiff ℝ 2 (fun r => (W x y z r).1.1) ∧
      ContDiff ℝ 2 (fun r => (W x y z r).2.1) := by
    constructor
    · simpa only [W, Prod.fst_add, Prod.smul_fst] using
        ((hUc.1.const_smul x).add (hpc.1.const_smul y)).add (hmc.1.const_smul z)
    · simpa only [W, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst] using
        ((hUc.2.const_smul x).add (hpc.2.const_smul y)).add (hmc.2.const_smul z)
  have hWd (x y z : ℂ) (r : ℝ) (hr : r ∈ Ioc 0 R) : HasDerivAt (W x y z)
      (spectralPhysicalCircularField νp νm (eta : ℂ) m (Q r) r (W x y z r)) r := by
    apply ((((hU r hr).const_smul x).add ((hp r hr).const_smul y)).add
      ((hm r hr).const_smul z)).congr_deriv
    dsimp only [W]
    rw [spectralPhysicalField_add, spectralPhysicalField_add,
      spectralPhysicalField_smul, spectralPhysicalField_smul, spectralPhysicalField_smul]
  have hkernel (a b : ℂ)
      (h : a • spectralPhysicalValueMap (Vp t) + b • spectralPhysicalValueMap (Vm t) = 0) :
      a = 0 ∧ b = 0 := by
    have hv : spectralPhysicalValueMap (W 0 a b t) = 0 := by
      dsimp only [W]
      rw [map_add, map_add, map_smul, map_smul, map_smul, zero_smul, zero_add]
      exact h
    have he := hzero eta R t heta ht htR htδ (W 0 a b) (hWc 0 a b).1 (hWc 0 a b).2
      (hWd 0 a b) (congrArg Prod.fst hv) (congrArg Prod.snd hv)
    have hab : a • Vp R + b • Vm R = 0 := by
      simpa only [W, zero_smul, zero_add] using he
    have hcoeff := Fintype.linearIndependent_iff.mp hRank (![a, b])
      (by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hab)
    exact ⟨by simpa using hcoeff 0, by simpa using hcoeff 1⟩
  have hdet := valueDet_ne_zero_of_kernel _ _ hkernel
  let c := spectralValueInverse (spectralPhysicalValueMap (Vp t))
    (spectralPhysicalValueMap (Vm t)) (spectralPhysicalValueMap (U t))
  have hc : c.1 • spectralPhysicalValueMap (Vp t) + c.2 • spectralPhysicalValueMap (Vm t) =
      spectralPhysicalValueMap (U t) :=
    spectralTwoColumns_apply_inverse _ _ _ hdet
  have hv : spectralPhysicalValueMap (W 1 (-c.1) (-c.2) t) = 0 := by
    dsimp only [W]
    rw [map_add, map_add, map_smul, map_smul, map_smul, one_smul, neg_smul, neg_smul]
    rw [← hc]
    abel
  have he := hzero eta R t heta ht htR htδ (W 1 (-c.1) (-c.2))
    (hWc 1 (-c.1) (-c.2)).1 (hWc 1 (-c.1) (-c.2)).2 (hWd 1 (-c.1) (-c.2))
    (congrArg Prod.fst hv) (congrArg Prod.snd hv)
  refine ⟨c, sub_eq_zero.mp ?_⟩
  simpa only [W, one_smul, neg_smul, sub_eq_add_neg, neg_add, add_assoc] using he

/-- The constructed analytic regular basis is complete for C² radial solutions.
The two positions, rather than a prescribed asymptotic expansion, are the only
origin regularity data required of the solution. -/
theorem homogeneousRegular_exists_complete_basis (ell m : ℕ) (νp νm : ℂ)
    (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L) (Q : ℝ → ℂ) (hQ : Continuous Q) :
    ∃ Vp Vm : ℂ → ℝ → E₄,
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R, HasDerivAt (Vp lam)
        (spectralPhysicalCircularField (νp - 2 * lam) (νm - 2 * lam)
          ((ell * (ell + 10) : ℕ) : ℂ) m (Q r) r (Vp lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R, HasDerivAt (Vm lam)
        (spectralPhysicalCircularField (νp - 2 * lam) (νm - 2 * lam)
          ((ell * (ell + 10) : ℕ) : ℂ) m (Q r) r (Vm lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → LinearIndependent ℂ ![Vp lam R, Vm lam R]) ∧
      (∀ lam, ‖lam‖ ≤ L → ∀ r, 0 ≤ r →
        AnalyticAt ℂ (fun z => Vp z r) lam ∧ AnalyticAt ℂ (fun z => Vm z r) lam) ∧
      (∀ lam, ‖lam‖ ≤ L → ∀ U : ℝ → E₄,
        ContDiff ℝ 2 (fun r => (U r).1.1) → ContDiff ℝ 2 (fun r => (U r).2.1) →
        (∀ r ∈ Ioc 0 R, HasDerivAt U
          (spectralPhysicalCircularField (νp - 2 * lam) (νm - 2 * lam)
            ((ell * (ell + 10) : ℕ) : ℂ) m (Q r) r (U r)) r) →
        ∃ c : ℂ × ℂ, U R = c.1 • Vp lam R + c.2 • Vm lam R) := by
  obtain ⟨Vp, Vm, hp, hm, hrank, hc, ha, _⟩ :=
    exists_regular_physical_basis_c2 ell m νp νm R L hR hL Q hQ
  refine ⟨Vp, Vm, hp, hm, hrank, ha, ?_⟩
  intro lam hlam U hU1 hU2 hU
  have hc' := hc lam
  have he : (0 : ℝ) ≤ (ell * (ell + 10) : ℕ) := by positivity
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
    homogeneousRegular_basis_complete (νp - 2 * lam) (νm - 2 * lam)
      ((ell * (ell + 10) : ℕ) : ℝ) he m Q hQ R hR U (Vp lam) (Vm lam)
      ⟨hU1, hU2⟩ ⟨hc'.1, hc'.2.1⟩ ⟨hc'.2.2.1, hc'.2.2.2⟩
      (by simpa using hU) (by simpa using hp lam hlam) (by simpa using hm lam hlam)
      (hrank lam hlam)

end DefocusingNLS

end OAI
