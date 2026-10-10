import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardBottomBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedHubbardForm

namespace OAI

/-! The actual finite Hubbard energy, including its off-site shift and
form error, has polynomial size. No occupation-space dimension enters. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open HubbardGlobal

theorem localizedOffsiteCoulomb_nonnegative {m : ℕ} (freq : ℝ)
    (u : Fin m → PlanarPosition) (i j : Fin m) : 0 ≤ localizedOffsiteCoulomb freq u i j := by
  unfold localizedOffsiteCoulomb
  split_ifs
  · exact le_rfl
  · exact localizedCoulombCoeff_nonnegative _ _ _

theorem localizedOffsiteCoulomb_le {m : ℕ} {freq : ℝ} (hf : 0 < freq)
    (u : Fin m → PlanarPosition) (i j : Fin m) :
    localizedOffsiteCoulomb freq u i j ≤ localizedPotentialBound freq := by
  unfold localizedOffsiteCoulomb
  split_ifs
  · exact localizedPotentialBound_nonnegative _
  · exact localizedCoulombCoeff_le hf _ _

theorem localizedOffsiteCoulomb_sum_le {m : ℕ} {freq : ℝ} (hf : 0 < freq)
    (u : Fin m → PlanarPosition) :
    (∑ i, ∑ j, localizedOffsiteCoulomb freq u i j) ≤ (m:ℝ)^2*localizedPotentialBound freq := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => localizedOffsiteCoulomb_le hf u i j))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,pow_two,mul_assoc] using h

theorem localizedHubbardFormError_nonnegative (m : ℕ) (freq D : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ localizedHubbardFormError m freq D ε := by
  have hO := localizedOverlapBound_nonnegative D
  have hP := localizedPotentialBound_nonnegative freq
  have hC := localizedFourIndexConstant_nonnegative freq
  unfold localizedHubbardFormError
  positivity

theorem shifted_hubbard_abs_bound {Edge : Type*} [Fintype Edge]
    {freq D ε : ℝ} (hf : 0 < freq) (hε : 0 ≤ ε) (m : ℕ)
    (u : Fin (m+1) → PlanarPosition) (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
    (he : localizedHubbardFormError m freq D ε ≤ 1) :
    |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-localizedHubbardFormError m freq D ε| ≤
      ((m+1:ℝ)/2+(m+1:ℝ)^2)*localizedPotentialBound freq+4*(∑ e, |t e|)+1 := by
  have hP := localizedPotentialBound_nonnegative freq
  have hU0 := localizedCoulombProfile_nonnegative freq 0
  have hU : localizedCoulombProfile freq 0 ≤ localizedPotentialBound freq := by
    simpa only [localizedCoulombCoeff_distance,sub_self,norm_zero] using
      localizedCoulombCoeff_le hf (0 : PlanarPosition) 0
  have hsum0 : 0 ≤ ∑ i, ∑ j, localizedOffsiteCoulomb freq u i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => localizedOffsiteCoulomb_nonnegative freq u i j))
  have hsum := localizedOffsiteCoulomb_sum_le hf u
  have he0 := localizedHubbardFormError_nonnegative m freq D hε
  have hh := hubbardFermionBottom_abs_bound m (localizedCoulombProfile freq 0)
    (localizedOffsiteCoulomb freq u) left right t
  simp_rw [abs_of_nonneg hU0,abs_of_nonneg (localizedOffsiteCoulomb_nonnegative freq u _ _)] at hh
  have hu := mul_le_mul_of_nonneg_left hU (show 0 ≤ (m+1:ℝ)/2 by positivity)
  have ht := (abs_sub
    (hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)) (localizedHubbardFormError m freq D ε)).trans
    (add_le_add (abs_sub _ _) (le_refl |localizedHubbardFormError m freq D ε|))
  rw [abs_of_nonneg he0,abs_of_nonneg (mul_nonneg (by norm_num) hsum0)] at ht
  simp only [Nat.cast_add,Nat.cast_one] at hsum
  nlinarith only [ht,hh,hu,hsum,he]

theorem exists_shifted_hubbard_polynomial_bound {freq : ℝ} (hf : 0 < freq) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ (r v : ℕ) (N : ℝ), 2 ≤ N →
    ∀ {Edge : Type} [Fintype Edge] (m : ℕ) (u : Fin (m+1) → PlanarPosition)
      (left right : Edge → Fin (m+1)) (t : Edge → ℝ) (D ε : ℝ),
      (m+1:ℝ) ≤ N^r → (∑ e, |t e|) ≤ N^v → 0 ≤ ε →
      localizedHubbardFormError m freq D ε ≤ 1 →
      |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-localizedHubbardFormError m freq D ε| ≤
        N^(q+2*r+v) := by
  let C := (3/2:ℝ)*localizedPotentialBound freq+5
  have hP := localizedPotentialBound_nonnegative freq
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds (by norm_num : (0:ℝ)<1) C
  refine ⟨q,by omega,fun r v N hN Edge _ m u left right t D ε hm ht hε he => ?_⟩
  have hN1 : 1 ≤ N := by linarith
  have hM : 1 ≤ (m+1:ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hM2 : (m+1:ℝ) ≤ (m+1:ℝ)^2 := by nlinarith [sq_nonneg ((m+1:ℝ)-1)]
  have hpow : (m+1:ℝ)^2 ≤ N^(2*r+v) := by
    calc
      _ ≤ (N^r)^2 := pow_le_pow_left₀ (by positivity) hm 2
      _ ≤ N^(2*r+v) := by
        rw [← pow_mul]
        exact pow_le_pow_right₀ hN1 (by omega)
  have hfirst : ((m+1:ℝ)/2+(m+1:ℝ)^2)*localizedPotentialBound freq ≤
      ((3/2:ℝ)*localizedPotentialBound freq)*N^(2*r+v) := by
    calc
      _ ≤ ((3/2:ℝ)*(m+1:ℝ)^2)*localizedPotentialBound freq :=
        mul_le_mul_of_nonneg_right (by linarith only [hM2]) hP
      _ ≤ ((3/2:ℝ)*localizedPotentialBound freq)*N^(2*r+v) := by
        have h := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (3/2:ℝ)*localizedPotentialBound freq by positivity)
        convert h using 1
        ring
  have ht' : (∑ e, |t e|) ≤ N^(2*r+v) := ht.trans (pow_le_pow_right₀ hN1 (by omega))
  have hone : 1 ≤ N^(2*r+v) := one_le_pow₀ hN1
  calc
    _ ≤ ((m+1:ℝ)/2+(m+1:ℝ)^2)*localizedPotentialBound freq+4*(∑ e, |t e|)+1 :=
      shifted_hubbard_abs_bound hf hε m u left right t he
    _ ≤ C*N^(2*r+v) := by dsimp [C]; nlinarith only [hfirst,ht',hone]
    _ ≤ N^q*N^(2*r+v) := mul_le_mul_of_nonneg_right (hbound N hN).2 (by positivity)
    _ = N^(q+2*r+v) := by rw [← pow_add]; congr 1; omega

end ContinuumCoulomb

end

end OAI
