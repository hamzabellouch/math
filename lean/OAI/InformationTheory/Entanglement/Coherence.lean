import OAI.InformationTheory.Entanglement.NormalizeRepresentation
import OAI.InformationTheory.Entanglement.SpectralWeights

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {r s n m : Type} [Fintype r] [Fintype s] [Fintype n] [Fintype m]
  [DecidableEq r] [DecidableEq s] [DecidableEq n] [DecidableEq m]

lemma four_effect_commuting (L : Map r n) (M : Map s m) (χ : r × s → ℂ)
    (hL : CP L) (hLT : CP (L.comp transposeMap))
    (hM : CP M) (hMT : CP (M.comp transposeMap))
    (X : Fin 2 → Mat n) (Y : Fin 2 → Mat m)
    (hX : ∀ i, (X i).PosSemidef) (hY : ∀ i, (Y i).PosSemidef)
    (hcomm : Commute (hsAdjoint L (X 0)) (hsAdjoint L (X 1))) :
    let R := tensorMap L M (projector χ)
    let D := fun i j => X i ⊗ₖ Y j
    let p := fun i j => (Matrix.trace (D i j * R)).re
    traceNorm (CFC.sqrt (D 0 0) * R * CFC.sqrt (D 1 1)) ≤
      Real.sqrt (p 0 0 * p 0 1) + Real.sqrt (p 1 0 * p 1 1) +
        2 * Real.sqrt (p 0 1 * p 1 0) := by
  let A := fun i => hsAdjoint L (X i)
  let B := fun j => hsAdjoint M (Y j)
  have hA (i : Fin 2) : (A i).PosSemidef := cp_positive (cp_hsAdjoint hL) (hX i)
  have hB (j : Fin 2) : (B j).PosSemidef := cp_positive (cp_hsAdjoint hM) (hY j)
  let C := tensorMap L M
  let D := fun i j => X i ⊗ₖ Y j
  let p := fun i j => (Matrix.trace (D i j * C (projector χ))).re
  let wgt := fun (z : r × s → ℂ) i j => quad (A i ⊗ₖ B j) z
  have hw (z : r × s → ℂ) (i j : Fin 2) :
      (Matrix.trace (D i j * C (projector z))).re=wgt z i j := by
    rw [pullback_tensor hL hM,quad_trace]
  have hn (z : r × s → ℂ) (i j : Fin 2) : 0≤wgt z i j :=
    quad_nonneg ((hA i).kronecker (hB j)) z
  have hD (i j : Fin 2) : (D i j).PosSemidef := (hX i).kronecker (hY j)
  obtain ⟨v,w,hsum,hadd,hv,hw'⟩ := spectral_weights A B hA hB hcomm χ
  change (∀ i j, wgt χ i j=wgt v i j+wgt w i j) at hadd
  change wgt v 1 1≤wgt v 0 1 at hv
  change wgt w 0 0≤wgt w 1 0 at hw'
  have hvle (i j : Fin 2) : wgt v i j≤p i j := by
    dsimp [p]; rw [hw,hadd]; exact le_add_of_nonneg_right (hn w i j)
  have hwle (i j : Fin 2) : wgt w i j≤p i j := by
    dsimp [p]; rw [hw,hadd]; exact le_add_of_nonneg_left (hn v i j)
  let Z := fun u z => CFC.sqrt (D 0 0)*C (vecMulVec u (star z))*CFC.sqrt (D 1 1)
  have hd (u z : r × s → ℂ) : traceNorm (Z u z)≤Real.sqrt (wgt u 0 0*wgt z 1 1) := by
    have h := cp_effect_direct (cp_tensorMap hL hM) u z (hD 0 0) (hD 1 1)
    dsimp only [D] at h
    simpa only [pullback_tensor hL hM,quad_trace] using h
  have hr (u z : r × s → ℂ) : traceNorm (Z u z)≤Real.sqrt (wgt z 0 0*wgt u 1 1) := by
    have h := cp_effect_reverse (cp_tensor_input_transpose hLT hMT) u z (hD 0 0) (hD 1 1)
    dsimp only [D] at h
    simpa only [pullback_tensor hL hM,quad_trace] using h
  have hvv : traceNorm (Z v v)≤Real.sqrt (p 0 0*p 0 1) :=
    (hd v v).trans (Real.sqrt_le_sqrt (mul_le_mul (hvle 0 0) (hv.trans (hvle 0 1))
      (hn v 1 1) ((hn v 0 0).trans (hvle 0 0))))
  have hww : traceNorm (Z w w)≤Real.sqrt (p 1 0*p 1 1) :=
    (hd w w).trans (Real.sqrt_le_sqrt (mul_le_mul (hw'.trans (hwle 1 0)) (hwle 1 1)
      (hn w 1 1) ((hn w 0 0).trans (hw'.trans (hwle 1 0)))))
  have hc : Real.sqrt (wgt w 0 0*wgt v 1 1)≤Real.sqrt (p 0 1*p 1 0) := by
    rw [mul_comm (p 0 1)]
    exact Real.sqrt_le_sqrt (mul_le_mul (hw'.trans (hwle 1 0)) (hv.trans (hvle 0 1))
      (hn v 1 1) ((hn w 0 0).trans (hw'.trans (hwle 1 0))))
  have he : Z χ χ=(Z v v+Z v w)+(Z w v+Z w w) := by
    dsimp [Z]
    rw [hsum]
    simp only [star_add,Matrix.add_vecMulVec,Matrix.vecMulVec_add,map_add,
      Matrix.mul_add,Matrix.add_mul]
    abel
  change traceNorm (Z χ χ)≤_
  rw [he]
  have h1 := traceNorm_add_le (Z v v+Z v w) (Z w v+Z w w)
  have h2 := traceNorm_add_le (Z v v) (Z v w)
  have h3 := traceNorm_add_le (Z w v) (Z w w)
  have h4 := (hr v w).trans hc
  have h5 := (hd w v).trans hc
  dsimp only [p,C,D] at hvv hww h4 h5
  linarith

theorem four_effect {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (R : Mat (n × m)) (hR : Represented R)
    (X : Fin 2 → Mat n) (Y : Fin 2 → Mat m)
    (hX : ∀ i, (X i).PosSemidef) (hY : ∀ i, (Y i).PosSemidef) :
    let D := fun i j => X i ⊗ₖ Y j
    let p := fun i j => (Matrix.trace (D i j * R)).re
    traceNorm (CFC.sqrt (D 0 0) * R * CFC.sqrt (D 1 1)) ≤
      Real.sqrt (p 0 0 * p 0 1) + Real.sqrt (p 1 0 * p 1 1) +
        2 * Real.sqrt (p 0 1 * p 1 0) := by
  obtain ⟨r,s,_,_,L,M,χ,hL,hLT,hM,hMT,hR,hcomm⟩ := normalized_representation R hR X hX
  rw [hR]
  exact four_effect_commuting L M χ hL hLT hM hMT X Y hX hY hcomm

end SecretKey

end

end OAI
