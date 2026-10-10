import OAI.MeasureTheory.Falconer.Angular.StationaryProductKernel
import OAI.MeasureTheory.Falconer.Estimates.ActualTwoPointDerivatives
import OAI.MeasureTheory.Falconer.Angular.AngularStationarySpatial
import OAI.MeasureTheory.Falconer.Angular.StationaryPairGain
import OAI.MeasureTheory.Falconer.Angular.AngularFarStationaryScale

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_actual_stationary_product_kernel {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ) (x y : Fin 2 → Plane),
    (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
    ∀ v bdepth : ℝ, (∀ l, (2:ℝ)^(-bdepth) ≤ ‖x l-y l‖) →
    (∀ l, sourceSymbolScale N sig L^2 ≤ (2:ℝ)^v*‖x l-y l‖) →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    ‖angularStationarySpatialKernel (β 0) (β 1) n v Ψ ![x 0,y 0,x 1,y 1]‖ ≤
      H*(2:ℝ)^(-(v-bdepth))/(1+(2:ℝ)^v*|‖x 0-y 0‖-‖x 1-y 1‖|)^2 := by
  obtain ⟨H,hH,hkernel⟩ := stationary_product_radial_bound hΨ hs n
  obtain ⟨C,hC,N₀,h₀⟩ := uniform_actual_pair_derivatives hsig K (2*n)
  refine ⟨H*C*C,by positivity,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i hsp x y hx hy v bdepth hd hD
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N (lam l) sig (J l) (i l) (hsp l)
  let f := fun l t => β l (x l) (sourceUnitDirection t)*conj (β l (y l) (sourceUnitDirection t))
  have hp (l : Fin 2) := h₀ N hN (S l) (b l) (k l) (hcard l) (hK l) L (hL l)
    (Q l) (hQ l) (ρ l) (m l) (lam l) (J l) (i l) (hsp l) (x l) (y l) (hx l) (hy l)
  have hfs (l : Fin 2) : ContDiff ℝ ∞ (fun t => f l (t+angularPairAngle (x l) (y l))) :=
    (hp l).1.comp (contDiff_id.add contDiff_const)
  have hbs (l : Fin 2) (j : ℕ) (hj : j ≤ 2*n) (t : ℝ) :
      ‖iteratedDeriv j (fun u => f l (u+angularPairAngle (x l) (y l))) t‖ ≤ C*sourceSymbolScale N sig L^j := by
    rw [iteratedDeriv_comp_add_const]
    exact (hp l).2 j hj _
  have hpos (l : Fin 2) : 0 < ‖x l-y l‖ := (by positivity : (0:ℝ) < (2:ℝ)^(-bdepth)).trans_le (hd l)
  have he := hkernel (hfs 0) (hfs 1) hC hC (sourceSymbolScale_one_le N hsig.le L)
    (by positivity : (0:ℝ) < (2:ℝ)^v) (hpos 0) (hpos 1) (hD 0) (hD 1) (hbs 0) (hbs 1)
  apply he.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (stationary_pair_dyadic_gain (hd 0) (hd 1)) (by positivity)

theorem sourceSymbolScale_far_frequency_le {sig : ℝ} (hsig : 0 ≤ sig)
    (N L : ℕ) {v h L₀ d : ℝ} (hv : v-h = 2*L₀)
    (hLL : (L:ℝ) ≤ L₀) (hL₀ : 10*sig*(N:ℝ) ≤ L₀)
    (hd : 4*(2:ℝ)^(-h) ≤ d) : sourceSymbolScale N sig L^2 ≤ (2:ℝ)^v*d := by
  have hfreq : (2:ℝ)^(2*L₀) ≤ (2:ℝ)^v*d := by
    simpa only [mul_one] using far_bump_frequency hv hd (by norm_num : (1/4:ℝ) ≤ 1)
  have hp : 0 < (2:ℝ)^v*d := (by positivity : (0:ℝ) < (2:ℝ)^(2*L₀)).trans_le hfreq
  have he := (actual_far_stationary_slack hsig N L hLL hL₀ hfreq).2
  have hpow : ((2:ℝ)^N)^(-18*sig) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by linarith)
  simpa only [one_mul] using (div_le_iff₀ hp).mp (he.trans hpow)

end PlanarFalconer

end OAI
