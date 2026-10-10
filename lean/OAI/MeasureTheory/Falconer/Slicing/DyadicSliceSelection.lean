import OAI.MeasureTheory.Falconer.Slicing.GaussianPolynomialSlice
import OAI.MeasureTheory.Falconer.Slicing.GaussianMomentWeights

namespace OAI

/-! # Selecting a slice directly from the two original finite-scale ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def gaussianPruningRadius {N : ℕ} (g : Fin (N+1)) : ℝ :=
  (1/(2:ℝ)^g.val)/2

noncomputable def gaussianPruningWeight (h : ℕ) (s : ℝ) {N : ℕ} (g : Fin (N+1)) : ℝ :=
  ((2:ℝ)^g.val)^((h:ℝ)-s)

theorem gaussianPruningWeight_eq (h : ℕ) (s : ℝ) {N : ℕ} (g : Fin (N+1)) :
    gaussianPruningWeight h s g = (1/(2:ℝ)^g.val)^(s-(h:ℝ)) := by
  unfold gaussianPruningWeight
  rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
  congr 1
  ring

theorem dyadic_original_slice_selection
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N : ℕ)
    {D ρ Lt Lq t q : ℝ} (hD : D < 1/2) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hδρ : 1/(2:ℝ)^N ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (hLt : 0 ≤ Lt) (hLq : 0 ≤ Lq) (ht : (h:ℝ) < t) (hq : (h:ℝ) < q)
    (hμmass : μ univ ≤ 1) (hνmass : ν univ ≤ 1)
    (hμball : ∀ x : Space (n+1), ∀ j : ℕ, j ≤ N →
      μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t))
    (hνball : ∀ x : Sphere (n+1), ∀ j : ℕ, j ≤ N →
      ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q))
    (hchart : ∀ᵐ z : Sphere (n+1) × Sphere (n+1) ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space (n+1)) (z.2:Space (n+1)))
    {K C S Nc R : ℝ} (hK : 0 < K) (hS : 0 ≤ S) (hNc : 0 < Nc) (hR : 0 < R)
    (hCpoint : (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C)
    (hCdir : (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C)
    (hCmass : (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C)
    (hcard : ((N+1:ℕ):ℝ)*C ≤ K) (hC : C ≤ K) (hlarge : 4*(1+2*S+1) ≤ K)
    (hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal S)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space (n+1)) (hJN : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc)
    (hmean : ENNReal.ofReal (1/K) ≤ ENNReal.ofReal ((2:ℝ)^h)*
      ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E)
    {b : ℝ≥0∞}
    (hbase : b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)) ≤
      ENNReal.ofReal (1/(4*K))) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N),
      b < gaussianPrunedPairMass μ ν (1/(2:ℝ)^N) (gaussianPruningRadius (N := N))
        (fun i => ENNReal.ofReal (K^6*gaussianPruningWeight h t i))
        (fun i => ENNReal.ofReal (K^3*gaussianPruningWeight h q i)) (ENNReal.ofReal (K^3))
        (gaussianActiveRelation E J a R (ENNReal.ofReal (K^11*(Nc*(2*R)^h))) true) (A,z) := by
  let r : Fin (N+1) → ℝ := gaussianPruningRadius
  let w : Fin (N+1) → ℝ := gaussianPruningWeight h t
  let v : Fin (N+1) → ℝ := gaussianPruningWeight h q
  let CP : Fin (N+1) → ℝ≥0∞ := fun i => ENNReal.ofReal (C*w i)
  let CD : Fin (N+1) → ℝ≥0∞ := fun i => ENNReal.ofReal (C*v i)
  have hp (i : Fin (N+1)) := gaussian_point_moment_weight μ hLt ht i.val N
    (Nat.le_of_lt_succ i.isLt) hμmass hμball hCpoint
  have hd (i : Fin (N+1)) := gaussian_direction_moment_weight ν hLq hq i.val N
    (Nat.le_of_lt_succ i.isLt) hνmass hνball hchart hCdir
  have hm := gaussian_direction_total_moment_bound ν hLq hq N hνmass hνball hchart hCmass
  have hi₀ : D < r 0 := by simpa only [r,gaussianPruningRadius,Fin.val_zero,pow_zero,div_one] using hD
  have hh := gaussian_select_polynomial_slice B hB μ ν hμ (by positivity) hδρ hwB r w v
    (fun i => by dsimp [w,gaussianPruningWeight]; positivity)
    (fun i => by dsimp [v,gaussianPruningWeight]; positivity)
    CP CD (ENNReal.ofReal C) hK hS hNc hR
    (by simpa only [Fintype.card_fin] using hcard) hC hlarge
    (fun _ => le_rfl) (fun _ => le_rfl) le_rfl hfactor 0 hi₀ hp hd hm
    E hE J hJ a hJN hmean hbase
  simpa only [w,v,r,gaussianPruningWeight,Fin.val_zero,pow_zero,Real.one_rpow,one_mul] using hh

end Falconer

end OAI
