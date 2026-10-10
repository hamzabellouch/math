import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayFamily
import OAI.NumberTheory.Ostmann.QuadraticCenter.PoissonPhase
import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def adaptivePhaseResidue (L : ℕ) (h : ℤ) : ℕ := (h:ZMod L).val

theorem adaptivePhaseResidue_lt {L : ℕ} (hL : 0 < L) (h : ℤ) :
    adaptivePhaseResidue L h < L := by
  let : NeZero L := ⟨hL.ne'⟩
  exact ZMod.val_lt _

theorem adaptivePhaseResidue_cast {L d : ℕ} (hL : 0 < L) (hd : d ∣ L) (h : ℤ) :
    ((adaptivePhaseResidue L h:ℕ):ZMod d) = (h:ZMod d) := by
  let : NeZero L := ⟨hL.ne'⟩
  have he : ((adaptivePhaseResidue L h:ℕ):ZMod L) = (h:ZMod L) := ZMod.natCast_zmod_val _
  have hh := congrArg (ZMod.castHom hd (ZMod d)) he
  simpa using hh

theorem adaptive_mod_cast {L d M : ℕ} (hd : d ∣ L) :
    ((M%(4*L):ℕ):ZMod d) = (M:ZMod d) := by
  have hdiv : d ∣ 4*L := dvd_mul_of_dvd_right hd 4
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  exact Nat.mod_mod_of_dvd M hdiv

theorem adaptive_odd_mod {L M : ℕ} (hM : Odd M) : Odd (M%(4*L)) := by
  rw [Nat.odd_iff] at hM ⊢
  rw [Nat.mod_mod_of_dvd]
  · exact hM
  · exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 4) L

theorem adaptive_jacobi_mod {L d M : ℕ} (hd : d ∣ L) (hM : Odd M) :
    jacobiSym (d:ℤ) M = jacobiSym (d:ℤ) (M%(4*L)) := by
  have hdiv : 4*d ∣ 4*L := Nat.mul_dvd_mul_left 4 hd
  have he : rightJacobi d M = rightJacobi d (M%(4*L)) := by
    rw [rightJacobi_mod d M,rightJacobi_mod d (M%(4*L)),Nat.mod_mod_of_dvd M hdiv]
  simpa only [rightJacobi,hM,adaptive_odd_mod hM,ite_true] using he

theorem divisorQuadraticSumP_inverse_congr {d : ℕ} (hd : Squarefree d)
    (A : ∀ p : ℕ, Finset (ZMod p)) {u u' : ℤ}
    (hu : (u:ZMod d) = (u':ZMod d)) (s v P : ℕ) (R h θ : ℝ) :
    divisorQuadraticSumP d A u s v P R h θ = divisorQuadraticSumP d A u' s v P R h θ := by
  have he : (u:ZMod (∏ p : d.primeFactors,p.val)) =
      (u':ZMod (∏ p : d.primeFactors,p.val)) := by
    rw [divisor_coordinates_product hd]
    exact hu
  unfold divisorQuadraticSumP
  rw [he]

theorem divisorQuadraticSumP_phase_congr {d : ℕ} (hd : Squarefree d)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ) (s v P : ℕ) (R θ : ℝ)
    {h h' : ℤ} (hh : (d:ℤ) ∣ h-h') :
    divisorQuadraticSumP d A mInv s v P R h θ =
      divisorQuadraticSumP d A mInv s v P R h' θ := by
  obtain ⟨k,hk⟩ := hh
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne_zero
  rw [divisorQuadraticSumP_eq_normalized hd,divisorQuadraticSumP_eq_normalized hd]
  unfold normalizedSmoothQuadraticSum
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  have he : weylPhase (((h:ℝ)+θ)*((s:ℝ)*v/d)*(w:ℝ)^2) =
      weylPhase (((h':ℝ)+θ)*((s:ℝ)*v/d)*(w:ℝ)^2) := by
    apply weylPhase_eq_of_sub_int (k*s*v*w^2)
    have hkR : (h:ℝ)-(h':ℝ)=(d:ℝ)*k := by exact_mod_cast hk
    push_cast
    field_simp
    nlinarith [show ((h:ℝ)-(h':ℝ))*((s:ℝ)*v*(w:ℝ)^2) =
      ((d:ℝ)*k)*((s:ℝ)*v*(w:ℝ)^2) by rw [hkR]]
  rw [he]

end Ostmann.QuadraticCenter

end

end OAI
