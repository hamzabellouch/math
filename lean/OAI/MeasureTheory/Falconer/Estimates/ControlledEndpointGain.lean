import OAI.MeasureTheory.Falconer.Slicing.DyadicSliceCosts
import OAI.MeasureTheory.Falconer.Slicing.GaussianEndpointExclusion
import OAI.MeasureTheory.Falconer.Slicing.EndpointSliceCosts
import OAI.MeasureTheory.Falconer.Slicing.GaussianRowDimension
import OAI.MeasureTheory.Falconer.Slicing.SliceCoordinates
import OAI.MeasureTheory.Falconer.Slicing.TransverseFrame

namespace OAI

/-! # Endpoint angular gain from the two actual radial slice costs

This is the finite-scale assembly step. Its cost and scalar hypotheses are
verified from the original direction law in the uniform endpoint application.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem controlled_endpoint_angular_gain {h N : ℕ} {t : ℝ}
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
    (ν₀ : Measure (Space (h+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ν₀]
    (hνeq : Measure.map gnomonicChart ν₀ = ν)
    (B : Space h →ₗᵢ[ℝ] Space (h+3)) (w₀ : Sphere (h+3))
    (E : Set (Space (h+3) × Sphere (h+3)))
    (J : Sphere (h+3) → Finset κ) (v : κ → Space (h+3))
    (G : Set (Space (h+2) × Space (h+2))) (hG : MeasurableSet G)
    {ρ Lt Lq K C₀ Nc a κ₀ C a₀ b Bpair Btriple : ℝ}
    (hρ : 0 ≤ ρ) (hδρ : 1/(2:ℝ)^N ≤ ρ)
    (hB : ∀ i, inner ℝ (w₀:Space (h+3)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
    (hν : ∀ᵐ w ∂ν, dist w w₀ ≤ ρ)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2)
    (hsmall : 2*(h:ℝ)*(1/(2:ℝ)^N) < 1)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) (hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1)
    (hμmass : μ univ ≤ 1) (hνmass : ν univ ≤ 1)
    (hLt : 0 ≤ Lt) (hLq : 0 ≤ Lq) (ht : (h:ℝ) < t)
    (hμball : ∀ x : Space (h+3), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t))
    (hνball : ∀ x : Sphere (h+3), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^(h+1:ℝ)))
    (hpair : ∀ᵐ u : Sphere (h+3) × Sphere (h+3) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+3)) (u.2:Space (h+3)))
    (hK : 1 ≤ K) (hNc : 0 < Nc)
    (hCpoint : (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C₀)
    (hCdir : (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h (h+1:ℝ) ≤ C₀)
    (hCmass : (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h (h+1:ℝ)|+1) ≤ C₀)
    (hcard : ((N+1:ℕ):ℝ)*C₀ ≤ K) (hC₀ : C₀ ≤ K)
    (hlarge : 4*(1+2*(2:ℝ)^h+1) ≤ K)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hb : 0 < b)
    (hBp : 0 < Bpair) (hBt : 0 < Btriple)
    (ha₀ : 1 ≤ a₀) (haK : 4+4*(h:ℝ) ≤ a₀)
    (hbad : ENNReal.ofReal Btriple+2*ENNReal.ofReal (K^6)*ENNReal.ofReal Bpair ≤
      ENNReal.ofReal (b^3/(4*(K^6)^3)))
    (hmass : (1/(2:ℝ)^N)^κ₀ ≤ b^3/(2*(K^6)^5))
    (hcount : K^11*(Nc*(2*((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+
      (C*(1/(2:ℝ)^N))*((h+3:ℝ)*(2*ρ)+1)))^h) ≤ (1/(2:ℝ)^N)^(-1-κ₀))
    (hcoef : K^6*(4*a₀)^(t-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-κ₀))
    (herror : 144*(h:ℝ)*(1/(2:ℝ)^N) ≤ 3*((1/(2:ℝ)^N)^a)^2)
    (hbudget : ((1/(2:ℝ)^N)^(-1-κ₀))^3*((6*C+35)/(1/(2:ℝ)^N)^a)^6*
      ((1/(2:ℝ)^N)^(-κ₀)*(6*(1/(2:ℝ)^N))^(t-(h:ℝ)))^2 < ((1/(2:ℝ)^N)^κ₀)^2)
    (hbase :
      ENNReal.ofReal b*volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N))+
      (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*
        volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
        ((∫⁻ A, endpointPairCost ν₀ (1/(2:ℝ)^N) G A
          ∂(gaussianRows (h+3) h).restrict
            (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ))))/
              ENNReal.ofReal Bpair)+
      (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*
        volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
        ((∫⁻ A, endpointTripleCost ν₀ (1/(2:ℝ)^N) (2*(1/(2:ℝ)^N)^a) G A
          ∂(gaussianRows (h+3) h).restrict
            (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ))))/
              ENNReal.ofReal Btriple) ≤ ENNReal.ofReal (1/(4*K)))
    (hE : MeasurableSet E) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (hJN : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc)
    (hEb : ∀ u ∈ E, ‖u.1‖ ≤ 1/4) (hanchors : ∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant (h+2) ρ^h)*
      (μ.prod ν) E < ENNReal.ofReal (1/K) := by
  classical
  let δ : ℝ := 1/(2:ℝ)^N
  let ε : ℝ := (h+3:ℝ)*(2*ρ)
  let Mrow : ℝ := ε+1
  let R : ℝ := δ+(2*(1/4))*δ+(C*δ)*Mrow
  let T : ℝ := K^11*(Nc*(2*R)^h)
  let rows : Fin h → Space (h+3) := fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hMrow : 0 ≤ Mrow := by dsimp [Mrow]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hrows (i : Fin h) : ‖rows i‖ ≤ 1 := by
    rw [show rows i = B (EuclideanSpace.basisFun (Fin h) ℝ i) from rfl,B.norm_map]
    exact ((EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one i).le
  have hwB : ∀ᵐ (w : Sphere (h+3)) ∂ν, ∀ i, |inner ℝ (w:Space (h+3)) (rows i)| ≤ ρ := by
    filter_upwards [hν] with w hw i
    exact transverse_frame_chart_bound B (w₀:Space (h+3)) hB hw i
  by_contra hnot
  have hmean := le_of_not_gt hnot
  have hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal ((2:ℝ)^h) := by
    simpa only [mul_one] using mul_le_mul' le_rfl hμmass
  have hcast : ((h+2:ℕ):ℝ)+1 = (h+3:ℝ) := by push_cast; ring
  obtain ⟨A,hA,z,_,hp,htc,hbig⟩ := dyadic_original_slice_costs rows hrows μ ν N
    (by norm_num : (1/4:ℝ) < 1/2) hμ hδρ hwB hLt hLq ht (by linarith : (h:ℝ) < h+1)
    hμmass hνmass hμball hνball hpair hKpos (by positivity : 0 ≤ (2:ℝ)^h) hNc hR
    hCpoint hCdir hCmass hcard hC₀ hlarge hfactor E hE J hJ v hJN hmean
    (endpointPairCost ν₀ δ G) (endpointTripleCost ν₀ δ (2*δ^a) G)
    (endpointPairCost_measurable ν₀ δ hG) (endpointTripleCost_measurable ν₀ δ (2*δ^a) hG)
    (ENNReal.ofReal Bpair) (ENNReal.ofReal Btriple) (ENNReal.ofReal b)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hBp)) (ne_of_gt (ENNReal.ofReal_pos.mpr hBt))
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (by simpa only [hcast] using hbase)
  rw [hcast] at hA
  have hdim : Module.finrank ℝ (gaussianRowMap A).ker = 3 := by
    simpa only [Nat.add_assoc,Nat.add_sub_cancel_left] using row_kernel_finrank A B hA hstable
  let e := sliceCoordinates (gaussianRowMap A).ker hdim
  have hdirMass : K^3 ≤ K^6 := pow_le_pow_right₀ hK (by norm_num)
  have hupper := gaussian_endpoint_slice_exclusion μ ν₀ hμ hν₀ A z e E hE J hJ v
    (fun g : Fin (N+1) => ENNReal.ofReal (K^3*(1/(2:ℝ)^g.val))) G hG
    (by positivity : 0 ≤ K^6) le_rfl hdirMass (by positivity : 0 < K^6) hMrow
    (by positivity) ha hC (sub_nonneg.mpr ht.le) hb ha₀ haK
    (gaussianRowNeighborhood_norm rows hrows hA) (row_kernel_projection_bound A B hA hstable)
    hsmall hEb hanchors hcover hp.le htc.le hbad hmass hcount hcoef herror hbudget
  rw [← hνeq] at hbig
  have hq : (h+1:ℝ)-(h:ℝ) = 1 := by ring
  simp only [gaussianPruningWeight_eq,hq,Real.rpow_one] at hbig
  exact (not_lt_of_ge hupper.le) hbig

end Falconer

end OAI
