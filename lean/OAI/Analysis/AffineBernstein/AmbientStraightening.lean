import Mathlib
import OAI.Analysis.AffineBernstein.CapChangeOfVariables

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def ambientCoordinates (n : ℕ) : (Space n × ℝ) ≃ₗ[ℝ] (Fin n ⊕ Unit → ℝ) :=
  (graphAmbientBasis n).equivFun

@[simp] lemma ambientCoordinates_inl {n : ℕ} (z : Space n × ℝ) (i : Fin n) :
    ambientCoordinates n z (Sum.inl i) = z.1 i := by
  simp [ambientCoordinates,graphAmbientBasis]

@[simp] lemma ambientCoordinates_inr {n : ℕ} (z : Space n × ℝ) (i : Unit) :
    ambientCoordinates n z (Sum.inr i) = z.2 := by
  simp [ambientCoordinates,graphAmbientBasis]

def ambientSwap {n : ℕ} (j : Fin n ⊕ Unit) : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ) :=
  ((ambientCoordinates n).trans ((LinearEquiv.funCongrLeft ℝ ℝ
    (Equiv.swap j (Sum.inr ()))).trans (ambientCoordinates n).symm)).toContinuousLinearEquiv

lemma ambientSwap_coordinates {n : ℕ} (j : Fin n ⊕ Unit) (z : Space n × ℝ)
    (i : Fin n ⊕ Unit) :
    ambientCoordinates n (ambientSwap j z) i =
      ambientCoordinates n z (Equiv.swap j (Sum.inr ()) i) := by
  simp [ambientSwap,LinearEquiv.funCongrLeft]

lemma ambientSwap_involutive {n : ℕ} (j : Fin n ⊕ Unit) :
    Function.Involutive (ambientSwap j) := by
  intro z
  apply (ambientCoordinates n).injective
  ext i
  simp only [ambientSwap_coordinates,Equiv.swap_apply_self]

lemma abs_det_involutive {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : V ≃L[ℝ] V) (h : Function.Involutive L) :
    |L.toContinuousLinearMap.det| = 1 := by
  have he : L.toLinearEquiv.toLinearMap.comp L.toLinearEquiv.toLinearMap = LinearMap.id := by
    ext x
    exact h x
  have hd := congrArg LinearMap.det he
  rw [LinearMap.det_comp,LinearMap.det_id] at hd
  change L.toContinuousLinearMap.det*L.toContinuousLinearMap.det = 1 at hd
  have hs := sq_abs L.toContinuousLinearMap.det
  have hn := abs_nonneg L.toContinuousLinearMap.det
  nlinarith

lemma abs_det_trans {n : ℕ} (L M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) :
    |(L.trans M).toContinuousLinearMap.det| =
      |M.toContinuousLinearMap.det| * |L.toContinuousLinearMap.det| := by
  change |LinearMap.det (M.toLinearEquiv.toLinearMap.comp L.toLinearEquiv.toLinearMap)| = _
  rw [LinearMap.det_comp,abs_mul]
  rfl

/-- A determinant-one-in-absolute-value coordinate change straightens any nonzero
vector upwards, with a uniform factor two bound on coordinate boxes. No Euclidean
structure is falsely assigned to the max-norm product. -/
theorem bounded_ambient_straightening {n : ℕ} {e : Space n × ℝ} (he : e ≠ 0) :
    ∃ (A : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (c : ℝ),
      0 < c ∧ A e = (0,c) ∧ |A.toContinuousLinearMap.det| = 1 ∧
      ∀ {R : ℝ}, 0 ≤ R → ∀ z : Space n × ℝ,
        (∀ i, |z.1 i| ≤ R) → |z.2| ≤ R →
        (∀ i, |(A z).1 i| ≤ 2*R) ∧ |(A z).2| ≤ 2*R := by
  classical
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ
    (fun i => |ambientCoordinates n e i|) Finset.univ_nonempty
  have hjmax (i) : |ambientCoordinates n e i| ≤ |ambientCoordinates n e j| := hj i (Finset.mem_univ _)
  have hjn : ambientCoordinates n e j ≠ 0 := by
    intro h
    apply he
    apply (ambientCoordinates n).injective
    ext i
    have hi := hjmax i
    simp only [h,abs_zero] at hi
    simpa using (abs_nonpos_iff.mp hi)
  let P := ambientSwap j
  have hP2 : (P e).2 = ambientCoordinates n e j := by
    have h := ambientSwap_coordinates j e (Sum.inr ())
    simpa only [ambientCoordinates_inr,Equiv.swap_apply_right] using h
  have hdetP : |P.toContinuousLinearMap.det| = 1 := abs_det_involutive P (ambientSwap_involutive j)
  have hPb {R : ℝ} (z : Space n × ℝ) (hz : ∀ i, |z.1 i| ≤ R) (ht : |z.2| ≤ R) :
      ∀ i, |ambientCoordinates n (P z) i| ≤ R := by
    intro i
    rw [show P = ambientSwap j from rfl,ambientSwap_coordinates]
    cases Equiv.swap j (Sum.inr ()) i with
    | inl l => simpa using hz l
    | inr l => simpa using ht
  let N : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ) :=
    if 0 < ambientCoordinates n e j then ContinuousLinearEquiv.refl ℝ _
    else (LinearEquiv.neg ℝ).toContinuousLinearEquiv
  have hN (z : Space n × ℝ) (i : Fin n ⊕ Unit) :
      |ambientCoordinates n (N z) i| = |ambientCoordinates n z i| := by
    dsimp [N]
    split_ifs <;> simp
  have hdetN : |N.toContinuousLinearMap.det| = 1 := by
    apply abs_det_involutive
    intro z
    dsimp [N]
    split_ifs <;> simp
  let Q := P.trans N
  have hQ2 : (Q e).2 = |ambientCoordinates n e j| := by
    dsimp [Q,N]
    split_ifs with h
    · simpa [abs_of_pos h] using hP2
    · have hn : ambientCoordinates n e j < 0 := lt_of_le_of_ne (le_of_not_gt h) hjn
      simpa [abs_of_neg hn] using congrArg Neg.neg hP2
  have hQmax (i : Fin n) : |(Q e).1 i| ≤ (Q e).2 := by
    rw [hQ2]
    change |ambientCoordinates n (N (P e)) (Sum.inl i)| ≤ _
    rw [hN,show P = ambientSwap j from rfl,ambientSwap_coordinates]
    exact hjmax _
  have hc : 0 < (Q e).2 := hQ2 ▸ (abs_pos.mpr hjn)
  let p := ((Q e).2)⁻¹ • (Q e).1
  have hp (i) : |p i| ≤ 1 := by
    change |((Q e).2)⁻¹*(Q e).1 i| ≤ 1
    rw [abs_mul,abs_inv,abs_of_pos hc]
    simpa only [inv_mul_cancel₀ hc.ne'] using mul_le_mul_of_nonneg_left (hQmax i) (inv_nonneg.mpr hc.le)
  refine ⟨Q.trans (verticalShear p),(Q e).2,hc,?_,?_,?_⟩
  · exact verticalShear_straightens (Q e) hc.ne'
  · simp only [abs_det_trans,det_verticalShear,abs_one,Q,hdetP,hdetN,mul_one]
  · intro R hR z hz ht
    have hQb (i) : |ambientCoordinates n (Q z) i| ≤ R := by
      change |ambientCoordinates n (N (P z)) i| ≤ R
      rw [hN]
      exact hPb z hz ht i
    have hs : |(Q z).2| ≤ R := by simpa using hQb (Sum.inr ())
    constructor
    · intro i
      change |(Q z).1 i-(Q z).2*p i| ≤ 2*R
      calc
        _ ≤ |(Q z).1 i|+|(Q z).2*p i| := abs_sub _ _
        _ = |(Q z).1 i|+|(Q z).2| * |p i| := by rw [abs_mul]
        _ ≤ R+R*1 := add_le_add (by simpa using hQb (Sum.inl i))
          (mul_le_mul hs (hp i) (abs_nonneg _) hR)
        _ = _ := by ring
    · change |(Q z).2| ≤ 2*R
      linarith

end AffineBernstein
end

end OAI
