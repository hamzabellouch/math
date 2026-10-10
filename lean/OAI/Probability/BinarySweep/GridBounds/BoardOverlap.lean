import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GroupedMoments
import OAI.Probability.BinarySweep.MatrixBounds.TraceDensityComparison

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A I J U W V : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
  [Fintype U] [Fintype W]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem regularized_board_overlap {n : ℕ} (e : Fin n ↪ I × J) (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (R Q : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hR : R.IsHermitian) (hQ : Q.IsHermitian) (hRR : R*R=R) (hQQ : Q*Q=Q)
    (hPQ : isotypicProjection p ρ * Q = Q * isotypicProjection p ρ)
    (hCQ : ∀ M : Matrix A A ℂ, M.PosSemidef →
      (∀ a b, p a ≠ p b → M a b = 0) → matrixTensorPower n M * Q = Q * matrixTensorPower n M)
    (r : U → I → Matrix A A ℂ) (v : W → J → Matrix A A ℂ)
    (hr : ∀ u i, (r u i).PosSemidef) (hv : ∀ w j, (v w j).PosSemidef)
    (htr : ∀ u i, (r u i).trace=1) (htv : ∀ w j, (v w j).trace=1)
    (her : ∀ u i a b, p a ≠ p b → r u i a b=0)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdr : ((a:ℂ) • ∑u, tensorMatrices (fun t : Fin n => r u (e t).1)-R).PosSemidef)
    (hdv : ((b:ℂ) • ∑w, tensorMatrices (fun t : Fin n => v w (e t).2)-Q).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Module.finrank ℂ V : ℝ) * (1-ε)^n * ‖Q * isotypicProjection p ρ * R‖^2 ≤
      a*b*Fintype.card U*Fintype.card W*
        Real.exp (Fintype.card I * Fintype.card J - (n : ℝ)) := by
  let P := isotypicProjection p ρ
  let d : ℝ := Module.finrank ℂ V
  let L : ℝ := (1-ε)^n
  let E := Real.exp (Fintype.card I * Fintype.card J - (n : ℝ))
  let T (u : U) := tensorMatrices (fun t : Fin n => r u (e t).1)
  let Z (w : W) := tensorMatrices (fun t : Fin n => v w (e t).2)
  have hL : 0 ≤ L := pow_nonneg (sub_nonneg.mpr hε1) n
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hP : P.PosSemidef := isotypicProjection_psd p ρ
  have hPP : P*P=P := projectionMatrix_idempotent _
  have hn := projection_overlap_norm_trace R Q P hR hQ hP.isHermitian hRR hQQ hPP hPQ
  have hQP := commuting_projection_product_psd P Q hP hQ hQQ hPQ
  have hrow := trace_right_density_domination R (Q*P) a T hQP hdr
  rw [← mul_assoc R Q P] at hrow
  have hlocal (u : U) : L * (d * (T u*Q*P).trace.re) ≤ b*(Fintype.card W*E) := by
    let M := regularizedMean (r u) ε
    have hM : M.PosDef := regularizedMean_posDef (r u) (hr u) hε hε1
    have heM := regularizedMean_even (r u) p (her u) ε
    obtain ⟨B,C,hB,hC,hBB,hBC,hCB,heB,heC⟩ := exists_even_whitening p M hM heM
    let H := matrixTensorPower n C
    have hH : H.PosSemidef := tensorMatrices_psd _ (fun _ => hC)
    have hcap := signed_tensor_whitening p ρ M B C hB hC hBB hBC
      (regularizedMean_trace (r u) (htr u) ε) heM heC
    change (H.conjTranspose*H-(d:ℂ)•P).PosSemidef at hcap
    rw [hH.isHermitian.eq] at hcap
    have hcomp := compress_whitening_cap P Q H (d:ℂ) hQ hQQ hPQ (hCQ C hC heC) hcap
    have htu : (T u).PosSemidef := tensorMatrices_psd _ (fun t => hr u (e t).1)
    have ht := trace_density_whitening (T u) Q P H d b Z htu hH.isHermitian hcomp hdv
    have hCMC : C * regularizedMean (r u) ε * C = 1 := by
      change C * M * C = 1
      rw [← hBB,← mul_assoc C B B,hCB,one_mul,hBC]
    have hz (w : W) : L * (H*T u*H*Z w).trace.re ≤ E := by
      have hh := whitened_board_budget e (r u) (v w) C (hr u) (hv w) (htv w)
        hε.le hε1 hC.isHermitian hCMC
      change L * (tensorMatrices (fun _ : Fin n => C) * T u *
        tensorMatrices (fun _ : Fin n => C) * Z w).trace.re ≤ E
      simpa only [T,Z,L,E,tensorMatrices_mul] using hh
    calc
      L*(d*(T u*Q*P).trace.re) ≤ L*(b*∑w, (H*T u*H*Z w).trace.re) :=
        mul_le_mul_of_nonneg_left ht hL
      _ = b*∑w, L*(H*T u*H*Z w).trace.re := by simp only [Finset.mul_sum]; congr 1; ring_nf
      _ ≤ b*∑w : W, E := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun w _ => hz w)) hb
      _ = b*(Fintype.card W*E) := by simp
  change d*L*‖Q*P*R‖^2 ≤ a*b*Fintype.card U*Fintype.card W*E
  calc
    _ ≤ d*L*(a*∑u, (T u*(Q*P)).trace.re) :=
      mul_le_mul_of_nonneg_left (hn.trans hrow) (mul_nonneg hd hL)
    _ = a*∑u, L*(d*(T u*Q*P).trace.re) := by
      simp only [← mul_assoc,Finset.mul_sum]
      ring_nf
    _ ≤ a*∑u : U, b*(Fintype.card W*E) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun u _ => hlocal u)) ha
    _ = _ := by simp; ring

omit [FiniteDimensional ℂ V] in
theorem board_overlap {n : ℕ} (e : Fin n ↪ I × J) (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (R Q : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hR : R.IsHermitian) (hQ : Q.IsHermitian) (hRR : R*R=R) (hQQ : Q*Q=Q)
    (hPQ : isotypicProjection p ρ * Q = Q * isotypicProjection p ρ)
    (hCQ : ∀ M : Matrix A A ℂ, M.PosSemidef →
      (∀ a b, p a ≠ p b → M a b = 0) → matrixTensorPower n M * Q = Q * matrixTensorPower n M)
    (r : U → I → Matrix A A ℂ) (v : W → J → Matrix A A ℂ)
    (hr : ∀ u i, (r u i).PosSemidef) (hv : ∀ w j, (v w j).PosSemidef)
    (htr : ∀ u i, (r u i).trace=1) (htv : ∀ w j, (v w j).trace=1)
    (her : ∀ u i a b, p a ≠ p b → r u i a b=0)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdr : ((a:ℂ) • ∑u, tensorMatrices (fun t : Fin n => r u (e t).1)-R).PosSemidef)
    (hdv : ((b:ℂ) • ∑w, tensorMatrices (fun t : Fin n => v w (e t).2)-Q).PosSemidef)
    : (Module.finrank ℂ V : ℝ) * ‖Q * isotypicProjection p ρ * R‖^2 ≤
      a*b*Fintype.card U*Fintype.card W*
        Real.exp (Fintype.card I * Fintype.card J - (n : ℝ)) := by
  have hε1 : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ε < 1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (Module.finrank ℂ V : ℝ) * (1-ε)^n * ‖Q*isotypicProjection p ρ*R‖^2 ≤
        a*b*Fintype.card U*Fintype.card W*
          Real.exp (Fintype.card I * Fintype.card J - (n : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin,hε1] with ε hε hε1
    exact regularized_board_overlap e p ρ R Q hR hQ hRR hQQ hPQ hCQ r v hr hv
      htr htv her a b ha hb hdr hdv hε hε1.le
  apply le_of_tendsto _ hbound
  have ht : Filter.Tendsto (fun ε : ℝ => (Module.finrank ℂ V:ℝ)*(1-ε)^n*
      ‖Q*isotypicProjection p ρ*R‖^2) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((Module.finrank ℂ V:ℝ)*(1-(0:ℝ))^n*‖Q*isotypicProjection p ρ*R‖^2)) := by
    exact (show Continuous (fun ε : ℝ => (Module.finrank ℂ V:ℝ)*(1-ε)^n*
      ‖Q*isotypicProjection p ρ*R‖^2) by fun_prop).continuousWithinAt.tendsto
  simpa using ht

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [LinearOrder I] [Nonempty I] [Fintype J] [LinearOrder J]
  {nR : I → ℕ} {nC : J → ℕ} {N : ℕ}
  {VR : I → Type*} [∀i, NormedAddCommGroup (VR i)]
  [∀i, InnerProductSpace ℂ (VR i)] [∀i, FiniteDimensional ℂ (VR i)]
  {VC : J → Type*} [∀j, NormedAddCommGroup (VC j)]
  [∀j, InnerProductSpace ℂ (VC j)] [∀j, FiniteDimensional ℂ (VC j)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem actual_board_overlap (board : Fin N ↪ I × J) (p : A → Bool)
    (eR : (Σₗ i, Fin (nR i)) ≃o Fin N) (eC : (Σₗ j, Fin (nC j)) ≃o Fin N)
    (gR gC : Equiv.Perm (Fin N))
    (hR : ∀t, groupOf eR gR t=(board t).1) (hC : ∀t, groupOf eC gC t=(board t).2)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) [ρ.IsIrreducible]
    (α : ∀i, Representation ℂ (Equiv.Perm (Fin (nR i))) (VR i)) [∀i, (α i).IsIrreducible]
    (β : ∀j, Representation ℂ (Equiv.Perm (Fin (nC j))) (VC j)) [∀j, (β j).IsIrreducible] :
    (Module.finrank ℂ V:ℝ)*
      ‖groupedProjection eC gC p β*isotypicProjection p ρ*groupedProjection eR gR p α‖^2 ≤
    (∏i, (Module.finrank ℂ (VR i):ℝ)*(nR i+1:ℝ)^(2*(Fintype.card A)^2))*
    (∏j, (Module.finrank ℂ (VC j):ℝ)*(nC j+1:ℝ)^(2*(Fintype.card A)^2))*
    Fintype.card (∀i, LocalDensityIndex p (nR i))*Fintype.card (∀j, LocalDensityIndex p (nC j))*
    Real.exp (Fintype.card I*Fintype.card J-(N:ℝ)) := by
  apply board_overlap board p ρ _ _
    (groupedProjection_psd eR gR p α).isHermitian
    (groupedProjection_psd eC gC p β).isHermitian
    (groupedProjection_idempotent eR gR p α)
    (groupedProjection_idempotent eC gC p β)
    (groupedProjection_commutes eC gC p β _ (isotypicProjection_invariant p ρ))
    (fun M _ he => groupedProjection_commutes eC gC p β _ (even_tensor_invariant p M he))
    (fun u i => localDensity p (nR i) (u i)) (fun w j => localDensity p (nC j) (w j))
    (fun u i => localDensity_psd p _ _) (fun w j => localDensity_psd p _ _)
    (fun u i => localDensity_trace p _ _) (fun w j => localDensity_trace p _ _)
    (fun u i => localDensity_even p _ _)
  · positivity
  · positivity
  · have h := grouped_density_domination eR gR p α
    rw [show groupOf eR gR = (fun t => (board t).1) from funext hR] at h
    simpa only [hR,Complex.ofReal_prod,Complex.ofReal_mul,Complex.ofReal_natCast,
      Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_one] using h
  · have h := grouped_density_domination eC gC p β
    rw [show groupOf eC gC = (fun t => (board t).2) from funext hC] at h
    simpa only [hC,Complex.ofReal_prod,Complex.ofReal_mul,Complex.ofReal_natCast,
      Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_one] using h

end BinaryCoordinateSweeps.Signed

end

end OAI
