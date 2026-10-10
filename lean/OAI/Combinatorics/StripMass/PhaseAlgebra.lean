import Mathlib
import OAI.Combinatorics.StripMass.NodalNodes
import OAI.Combinatorics.StripMass.ThreeBoxSplitPolynomial
import OAI.Combinatorics.StripMass.ThreeBoxBraidPolynomial

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

theorem phase_four : phase^(4:ℕ) = Complex.I := by
  have h := phase_pow 4
  norm_num only [zpow_ofNat, Int.cast_ofNat] at h
  rw [h]
  have he : (4:ℂ)*lambda*Complex.I = (Real.pi / 2 : ℝ)*Complex.I := by
    simp [lambda]
    ring
  rw [he, Complex.exp_mul_I]
  simp

theorem constF_phase_four (n : ℕ) : constF n phase ^ 4 = constF n Complex.I := by
  rw [constF, ← map_pow, phase_four]
  rfl

theorem constF_d_eq (n : ℕ) :
    constF n d = ((constF n phase)^4+1)/(2*(constF n phase)^2) := by
  change constF n (Real.cos ((2:ℝ)*lambda)) = _
  have h := torusCos_phase_pow n 2
  norm_num only [Nat.cast_ofNat] at h
  rw [← h]
  unfold torusCos
  field_simp [constF_phase_ne_zero]


 

 


def torusCommon {n : ℕ} (z : SpectralField n) : SpectralField n :=
  (constF n phase^4*z^2-1)*(constF n phase^6*z^2-1)

theorem torusCommon_eq {n : ℕ} (z : SpectralField n) (hz : z ≠ 0) :
    torusCommon z = 4*(constF n Complex.I)^2*(constF n phase)^5*z^2*torusL z := by
  unfold torusCommon torusL torusSin
  have hq := constF_phase_ne_zero n
  have hI : constF n Complex.I ≠ 0 :=
    (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr Complex.I_ne_zero
  field_simp
  ring

theorem torusCommon_ne_zero {n : ℕ} (z : SpectralField n) (hz : z ≠ 0)
    (hL : torusL z ≠ 0) : torusCommon z ≠ 0 := by
  rw [torusCommon_eq z hz]
  have hI : constF n Complex.I ≠ 0 :=
    (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr Complex.I_ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ hI)) (pow_ne_zero _ (constF_phase_ne_zero n))) (pow_ne_zero _ hz)) hL

end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset

 

theorem torusWeights_cleared {n : ℕ} (z : SpectralField n) (hz : z ≠ 0)
    (hL : torusL z ≠ 0) (t : Tile) :
    torusCommon z * (torusWeights z).tile t =
      tileNumerator (constF n phase) (constF n phase^4) z t := by
  have hq := constF_phase_ne_zero n
  have hI : constF n Complex.I ≠ 0 :=
    (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr Complex.I_ne_zero
  cases t
  · simp [Weights.tile, tileNumerator, torusCommon]
  all_goals
    rw [torusCommon_eq z hz]
    simp only [torusWeights, Weights.tile, tileNumerator]
    try rw [constF_d_eq]
    simp only [torusSin]
    rw [← constF_phase_four n]
    field_simp [hL]
    ring


 

 


theorem coefficient_scale {K : Type*} [CommSemiring K] (a b c : Tile → K)
    (r s u : K) (k : Fin 51) :
    coefficient (fun t => r*a t) (fun t => s*b t) (fun t => u*c t) k =
      (r*s*u) * coefficient a b c k := by
  unfold coefficient
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  ring

 

theorem braid_coefficient {n : ℕ} (z w : SpectralField n)
    (hz : z ≠ 0) (hw : w ≠ 0) (hLz : torusL z ≠ 0) (hLw : torusL w ≠ 0)
    (hLzw : torusL (z*w) ≠ 0) (k : Fin 51) :
    coefficient (torusWeights z).tile (torusWeights (z*w)).tile (torusWeights w).tile k =
    coefficient (torusWeights w).tile (torusWeights (z*w)).tile (torusWeights z).tile
      (mirrorIndex k) := by
  have hN (v : SpectralField n) (hv : v ≠ 0) (hLv : torusL v ≠ 0) :
      (fun t => torusCommon v * (torusWeights v).tile t) =
        tileNumerator (constF n phase) (constF n phase^4) v :=
    funext (torusWeights_cleared v hv hLv)
  have h := braid_numerator (constF n phase) z w (constF_phase_eight n) k
  rw [← hN z hz hLz, ← hN w hw hLw, ← hN (z*w) (mul_ne_zero hz hw) hLzw,
    coefficient_scale, coefficient_scale] at h
  have hc := mul_ne_zero (mul_ne_zero (torusCommon_ne_zero z hz hLz)
    (torusCommon_ne_zero (z*w) (mul_ne_zero hz hw) hLzw)) (torusCommon_ne_zero w hw hLw)
  apply mul_left_cancel₀ hc
  calc
    _ = (torusCommon w * torusCommon (z*w) * torusCommon z) *
        coefficient (torusWeights w).tile (torusWeights (z*w)).tile (torusWeights z).tile
          (mirrorIndex k) := h
    _ = _ := by ring

end

 

 

noncomputable section
open Finset
open scoped Classical

theorem coefficient_eq_sumif {K : Type*} [CommSemiring K] (a b c : Tile → K) (k : Fin 51) :
    coefficient a b c k =
      ∑ t : Config, if profile t = some k then a t.1*b t.2.1*c t.2.2 else 0 := by
  unfold coefficient
  rw [← sum_filter]
  congr 1
  ext t
  simp only [mem_filter, mem_univ, true_and, mem_fiber_iff]

 

theorem profile_partition {K : Type*} [CommSemiring K] (a b c : Tile → K)
    (P : Fin 51 → Prop) :
    (∑ t : Config, if ∃ k, profile t = some k ∧ P k
      then a t.1*b t.2.1*c t.2.2 else 0) =
    ∑ k : Fin 51, if P k then coefficient a b c k else 0 := by
  have hk (k : Fin 51) : (if P k then coefficient a b c k else 0) =
      ∑ t : Config, if profile t = some k ∧ P k then a t.1*b t.2.1*c t.2.2 else 0 := by
    rw [coefficient_eq_sumif]
    by_cases h : P k <;> simp [h]
  simp_rw [hk]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  cases he : profile t with
  | none => simp
  | some j =>
    simp only [Option.some.injEq]
    have hs (x : Fin 51) :
        (if j = x ∧ P x then a t.1*b t.2.1*c t.2.2 else 0) =
        if x = j then (if P j then a t.1*b t.2.1*c t.2.2 else 0) else 0 := by
      by_cases h : x = j
      · subst x; simp
      · simp [h, Ne.symm h]
    simp_rw [hs]
    simp

 

theorem patch_partition {K B : Type*} [CommSemiring K] (a₀ a₁ a₂ : Tile → K)
    (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop) (out : B → Prop)
    (test : (B → B → Prop) → Prop) :
    (∑ t : Config, if patchTest s b active out test t
      then a₀ t.1*a₁ t.2.1*a₂ t.2.2 else 0) =
    ∑ k : Fin 51, if exteriorTest s b active out test k
      then coefficient a₀ a₁ a₂ k else 0 := by
  simp_rw [patchTest_iff]
  exact profile_partition a₀ a₁ a₂ _

 

theorem braid_partition {n : ℕ} (z w : SpectralField n)
    (hz : z ≠ 0) (hw : w ≠ 0) (hLz : torusL z ≠ 0) (hLw : torusL w ≠ 0)
    (hLzw : torusL (z*w) ≠ 0) (P : Fin 51 → Prop) :
    (∑ t : Config, if ∃ k, profile t = some k ∧ P k
      then (torusWeights z).tile t.1 * (torusWeights (z*w)).tile t.2.1 *
        (torusWeights w).tile t.2.2 else 0) =
    (∑ t : Config, if ∃ k, profile t = some k ∧ P (mirrorIndex k)
      then (torusWeights w).tile t.1 * (torusWeights (z*w)).tile t.2.1 *
        (torusWeights z).tile t.2.2 else 0) := by
  rw [profile_partition, profile_partition]
  simp_rw [braid_coefficient z w hz hw hLz hLw hLzw]
  let e : Fin 51 ≃ Fin 51 :=
    ⟨mirrorIndex,mirrorIndex,mirrorIndex_involutive,mirrorIndex_involutive⟩
  refine Fintype.sum_equiv e _ _ ?_
  intro k
  change (if P k then _ else 0) =
    (if P (mirrorIndex (mirrorIndex k)) then _ else 0)
  rw [mirrorIndex_involutive]
  rfl

end

 

 

noncomputable section
open scoped Classical

theorem split3_numerator {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1)
    (k : Fin 51) (h₁ : ¬ boundarySupport (diagram k) 1) (h₂ : ¬ boundarySupport (diagram k) 2) :
    coefficient deletionTile (tileNumerator q (q^4) (q^3*z)) (tileNumerator q (q^4) z) k =
      commonNumerator q (q^3*z) * commonNumerator q z * coefficient swapTile swapTile deletionTile (mirrorIndex k) := by
  fin_cases k
  · exact split3_numerator_0 q z hq
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split3_numerator_14 q z hq
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split3_numerator_22 q z hq
  · exact split3_numerator_23 q z hq
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split3_numerator_27 q z hq
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact split3_numerator_30 q z hq
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₁ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split3_numerator_48 q z hq
  · exact split3_numerator_49 q z hq
  · exact split3_numerator_50 q z hq

theorem split2_numerator {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1)
    (k : Fin 51) (h₂ : ¬ boundarySupport (diagram k) 2) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) k * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) (mirrorIndex k) := by
  fin_cases k
  · exact split2_numerator_0 q z hq
  · exact split2_numerator_1 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_7 q z hq
  · exact split2_numerator_8 q z hq
  · exact split2_numerator_9 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_14 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_17 q z hq
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_19 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_22 q z hq
  · exact split2_numerator_23 q z hq
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_25 q z hq
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_27 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_30 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_35 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_38 q z hq
  · exact split2_numerator_39 q z hq
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_41 q z hq
  · exact split2_numerator_42 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_48 q z hq
  · exact split2_numerator_49 q z hq
  · exact split2_numerator_50 q z hq

end
end CriticalStrip.Diagram.ThreeBox

 

 

namespace CriticalStrip.Diagram
noncomputable section

 
def swapWeights {K : Type*} [Zero K] [One K] : Weights K := ⟨0,1,0,0,0⟩
 

def mergeWeights {K : Type*} [Field K] (q : K) : Weights K :=
  ⟨q/(q^2+1),q/(q^2+1),q/(q^2+1),0,0⟩

@[simp] lemma swapWeights_tile {K : Type*} [Zero K] [One K] :
    (swapWeights : Weights K).tile = ThreeBox.swapTile := by funext t; cases t <;> rfl
@[simp] lemma deletionWeights_tile {K : Type*} [Zero K] [One K] :
    (deletionWeights : Weights K).tile = ThreeBox.deletionTile := by funext t; cases t <;> rfl

lemma eighthRoot_two_add_one_ne_zero {K : Type*} [Field K] [CharZero K] {q : K}
    (hq : q^8 = -1) : q^2+1≠0 := by
  intro h
  have h2 : q^2 = -1 := by linear_combination h
  have h8 : q^8 = 1 := by calc
    q^8 = (q^2)^4 := by ring
    _ = 1 := by rw [h2]; norm_num
  have : (1 : K) = -1 := h8.symm.trans hq
  norm_num at this

lemma mergeWeights_cleared {K : Type*} [Field K] (q : K) (hq : q^2+1≠0) :
    (fun t => (q^2+1)*(mergeWeights q).tile t) = ThreeBox.mergeNumerator q := by
  funext t
  cases t <;> simp [mergeWeights,Weights.tile,ThreeBox.mergeNumerator, mul_div_cancel₀, hq]

namespace ThreeBox
lemma coefficient_scale₂₃ {K : Type*} [CommSemiring K] (a b c : Tile → K)
    (r s : K) (k : Fin 51) :
    coefficient a (fun t => r*b t) (fun t => s*c t) k =
      (r*s) * coefficient a b c k := by
  simpa using coefficient_scale a b c 1 r s k

lemma coefficient_scale₁₃ {K : Type*} [CommSemiring K] (a b c : Tile → K)
    (r s : K) (k : Fin 51) :
    coefficient (fun t => r*a t) b (fun t => s*c t) k =
      (r*s) * coefficient a b c k := by
  simpa using coefficient_scale a b c r 1 s k

lemma coefficient_deletion {n : ℕ} (z : SpectralField n)
    (hz : z≠0) (hL : torusL z≠0) (hL3 : torusL (constF n phase^3*z)≠0)
    (k : Fin 51) (h₁ : ¬ boundarySupport (diagram k) 1)
    (h₂ : ¬ boundarySupport (diagram k) 2) :
    coefficient deletionWeights.tile (torusWeights (constF n phase^3*z)).tile
        (torusWeights z).tile k =
      coefficient swapWeights.tile swapWeights.tile deletionWeights.tile (mirrorIndex k) := by
  have hN (v : SpectralField n) (hv : v≠0) (hLv : torusL v≠0) :
      (fun t => torusCommon v*(torusWeights v).tile t) =
        tileNumerator (constF n phase) (constF n phase^4) v :=
    funext (torusWeights_cleared v hv hLv)
  have hz3 := mul_ne_zero (pow_ne_zero 3 (constF_phase_ne_zero n)) hz
  have h := split3_numerator (constF n phase) z (constF_phase_eight n) k h₁ h₂
  change coefficient deletionTile _ _ k =
    torusCommon (constF n phase^3*z)*torusCommon z *
      coefficient swapTile swapTile deletionTile (mirrorIndex k) at h
  rw [←hN _ hz3 hL3,←hN _ hz hL,coefficient_scale₂₃] at h
  simpa only [deletionWeights_tile,swapWeights_tile] using
    mul_left_cancel₀ (mul_ne_zero (torusCommon_ne_zero _ hz3 hL3)
      (torusCommon_ne_zero _ hz hL)) h

lemma coefficient_merge {n : ℕ} (z : SpectralField n)
    (hz : z≠0) (hL : torusL z≠0) (hL1 : torusL (constF n phase*z)≠0)
    (hL2 : torusL (constF n phase^2*z)≠0)
    (k : Fin 51) (h₂ : ¬ boundarySupport (diagram k) 2) :
    coefficient (mergeWeights (constF n phase)).tile
        (torusWeights (constF n phase^2*z)).tile (torusWeights z).tile k =
      coefficient (torusWeights (constF n phase*z)).tile swapWeights.tile
        (mergeWeights (constF n phase)).tile (mirrorIndex k) := by
  let q := constF n phase
  have hq := eighthRoot_two_add_one_ne_zero (constF_phase_eight n)
  have hN (v : SpectralField n) (hv : v≠0) (hLv : torusL v≠0) :
      (fun t => torusCommon v*(torusWeights v).tile t) =
        tileNumerator q (q^4) v := funext (torusWeights_cleared v hv hLv)
  have hz1 := mul_ne_zero (constF_phase_ne_zero n) hz
  have hz2 := mul_ne_zero (pow_ne_zero 2 (constF_phase_ne_zero n)) hz
  have h := split2_numerator q z (constF_phase_eight n) k h₂
  change coefficient (mergeNumerator q) _ _ k * torusCommon (q*z) =
    torusCommon (q^2*z)*torusCommon z *
      coefficient _ swapTile (mergeNumerator q) (mirrorIndex k) at h
  rw [←hN _ hz2 hL2,←hN _ hz hL,←hN _ hz1 hL1,
    ←mergeWeights_cleared q hq,coefficient_scale,coefficient_scale₁₃] at h
  have hc : (q^2+1)*torusCommon (q^2*z)*torusCommon z*torusCommon (q*z)≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hq (torusCommon_ne_zero _ hz2 hL2))
      (torusCommon_ne_zero _ hz hL)) (torusCommon_ne_zero _ hz1 hL1)
  apply mul_left_cancel₀ hc
  simp only [swapWeights_tile]
  calc
    _ = ((q^2+1)*torusCommon (q^2*z)*torusCommon z) *
        coefficient (mergeWeights q).tile (torusWeights (q^2*z)).tile (torusWeights z).tile k *
        torusCommon (q*z) := by ring
    _ = _ := h
    _ = _ := by ring

end ThreeBox

 

 


lemma rho_eq_inv_two_C : rho=1/(2*C) := by
  rw [rho,C,lambda,Real.cos_pi_div_eight]
  congr 1
  ring

lemma phase_div_two_add_one : phase/(phase^2+1)=(rho:ℂ) := by
  have h := phase_cosine 1
  simp only [zpow_one,Int.cast_one,one_mul] at h
  change (phase+phase⁻¹)/2=(C:ℂ) at h
  have he : 2*(C:ℂ)*phase=phase^2+1 := by
    field_simp [phase_ne_zero] at h
    linear_combination -h
  have hden : phase^2+1≠0 := eighthRoot_two_add_one_ne_zero phase_eight
  rw [rho_eq_inv_two_C]
  push_cast
  apply (div_eq_div_iff hden (by
    intro hc
    have hh:=he
    rw [hc,zero_mul] at hh
    exact hden hh.symm)).mpr
  simpa only [one_mul,mul_comm] using he

lemma mergeWeights_source_constant (n : ℕ) :
    mergeWeights (constF n phase)=
      (⟨constF n rho,constF n rho,constF n rho,0,0⟩ : Weights (SpectralField n)) := by
  have h:=congrArg (constF n) phase_div_two_add_one
  simp only [constF,map_div₀,map_add,map_pow,map_one] at h
  unfold mergeWeights
  change (⟨_,_,_,0,0⟩ : Weights (SpectralField n))=⟨_,_,_,0,0⟩
  simp only [constF,h]


 

 


@[simp] lemma torusSin_inv {n : ℕ} (z : SpectralField n) : torusSin z⁻¹ = -torusSin z := by
  simp only [torusSin,inv_inv]
  ring

@[simp] lemma torusSin_neg {n : ℕ} (z : SpectralField n) : torusSin (-z) = -torusSin z := by
  simp only [torusSin]
  ring

lemma shifted_gamma_difference {n : ℕ} (i j : Fin n) :
    spectralA j-shiftedCosine i (phase^(-9:ℤ))=
      -2*torusSin (variableF i*variableF j/constF n phase^6)*
        torusSin (constF n phase^5*(variableF i/variableF j)) := by
  have hq := constF_phase_ne_zero n
  have hi := variableF_ne_zero i
  have hj := variableF_ne_zero j
  have hp:=torusSin_product (variableF i*variableF j/constF n phase^6)
    (constF n phase^3*variableF j/variableF i)
    (div_ne_zero (mul_ne_zero hi hj) (pow_ne_zero _ hq))
    (div_ne_zero (mul_ne_zero (pow_ne_zero _ hq) hj) hi)
  have he₁ : (variableF i*variableF j/constF n phase^6)/
      (constF n phase^3*variableF j/variableF i)=constF n (phase^(-9:ℤ))*variableF i^2 := by
    simp only [constF,zpow_neg,zpow_ofNat,map_inv₀,map_pow]
    field_simp
  have he₂ : (variableF i*variableF j/constF n phase^6)*
      (constF n phase^3*variableF j/variableF i)=variableF j^2/constF n phase^3 := by
    field_simp
  have he₃ : constF n phase^3*variableF j/variableF i=
      -(constF n phase^5*(variableF i/variableF j))⁻¹ := by
    have h:=constF_phase_eight n
    field_simp
    linear_combination h
  rw [he₁,he₂,he₃,torusSin_neg,torusSin_inv] at hp
  rw [shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero)]
  change torusCos (variableF j^2/constF n phase^3)-_= _
  rw [neg_neg] at hp
  linear_combination hp

lemma shifted_sigma_difference {n : ℕ} (i j : Fin n) :
    spectralA j-shiftedCosine i (phase^(9:ℤ))=
      2*torusSin (constF n phase^3*(variableF i*variableF j))*
        torusSin (constF n phase^6*(variableF i/variableF j)) := by
  have hq := constF_phase_ne_zero n
  have hi := variableF_ne_zero i
  have hj := variableF_ne_zero j
  have hp:=torusSin_product (constF n phase^3*(variableF i*variableF j))
    (variableF j/(constF n phase^6*variableF i))
    (mul_ne_zero (pow_ne_zero _ hq) (mul_ne_zero hi hj))
    (div_ne_zero hj (mul_ne_zero (pow_ne_zero _ hq) hi))
  have he₁ : (constF n phase^3*(variableF i*variableF j))/
      (variableF j/(constF n phase^6*variableF i))=constF n (phase^(9:ℤ))*variableF i^2 := by
    simp only [constF,zpow_ofNat,map_pow]
    field_simp
  have he₂ : (constF n phase^3*(variableF i*variableF j))*
      (variableF j/(constF n phase^6*variableF i))=variableF j^2/constF n phase^3 := by
    field_simp
  have he₃ : variableF j/(constF n phase^6*variableF i)=
      (constF n phase^6*(variableF i/variableF j))⁻¹ := by
    field_simp
  rw [he₁,he₂,he₃,torusSin_inv] at hp
  rw [shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero)]
  change torusCos (variableF j^2/constF n phase^3)-_= _
  linear_combination hp

 

theorem movingBox_scalar_cancellation {n : ℕ} (i j : Fin n) :
    (spectralA j-shiftedCosine i (phase^(-9:ℤ)))*
      (spectralA j-shiftedCosine i (phase^(9:ℤ)))=
      (-4*torusSin (variableF i*variableF j/constF n phase^6)*
        torusSin (constF n phase^3*(variableF i*variableF j)))*
          torusL (constF n phase^3*(variableF i/variableF j)) := by
  rw [shifted_gamma_difference,shifted_sigma_difference]
  unfold torusL
  have h₁ : constF n phase^2*(constF n phase^3*(variableF i/variableF j))=
      constF n phase^5*(variableF i/variableF j) := by ring
  have h₂ : constF n phase^3*(constF n phase^3*(variableF i/variableF j))=
      constF n phase^6*(variableF i/variableF j) := by ring
  rw [h₁,h₂]
  ring

end
end CriticalStrip.Diagram

end OAI
