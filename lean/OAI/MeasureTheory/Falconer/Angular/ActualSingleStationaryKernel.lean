import OAI.MeasureTheory.Falconer.Angular.SingleStationaryAngular
import OAI.MeasureTheory.Falconer.Angular.ActualStationaryProductKernel

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def angularSingleStationaryKernel (β γ : Plane → UnitCircle → ℂ)
    (n : ℕ) (v : ℝ) (Ψ : ℝ → ℝ) (x : Fin 4 → Plane) : ℂ :=
  ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
    (angularPairStationary β n (x 0) (x 1) r *
      angularPairCircleIntegral γ (x 2) (x 3) r))

theorem unit_direction_inner_bound (u : UnitCircle) (z : Plane) :
    |inner ℝ (u:Plane) z| ≤ ‖z‖ := by
  simpa only [u.property,one_mul] using abs_real_inner_le_norm (u:Plane) z

theorem uniform_actual_single_stationary_kernel {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K n q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ) (x y : Fin 2 → Plane),
    (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
    ∀ v : ℝ, 0 < ‖x 0-y 0‖ → 2*‖x 1-y 1‖ ≤ ‖x 0-y 0‖ →
    sourceSymbolScale N sig L^2 ≤ (2:ℝ)^v*‖x 0-y 0‖ →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    ‖angularSingleStationaryKernel (β 0) (β 1) n v Ψ ![x 0,y 0,x 1,y 1]‖ ≤
      H*((2:ℝ)^v*‖x 0-y 0‖)^(-1/2:ℝ)/((2:ℝ)^v*‖x 0-y 0‖/2)^q := by
  obtain ⟨H,hH,hkernel⟩ := stationary_single_angular_bound hΨ hs n q
  obtain ⟨C,hC,N₀,h₀⟩ := uniform_actual_pair_derivatives hsig K (2*n)
  let B := symbolDerivativeConstant K^K
  have hB : 0 ≤ B := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  refine ⟨H*C*B^2,by positivity,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i hsp x y hx hy v hl hsep hD
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N (lam l) sig (J l) (i l) (hsp l)
  let f := fun t => β 0 (x 0) (sourceUnitDirection t)*conj (β 0 (y 0) (sourceUnitDirection t))
  have hp := h₀ N hN (S 0) (b 0) (k 0) (hcard 0) (hK 0) L (hL 0)
    (Q 0) (hQ 0) (ρ 0) (m 0) (lam 0) (J 0) (i 0) (hsp 0) (x 0) (y 0) (hx 0) (hy 0)
  have hfs : ContDiff ℝ ∞ (fun t => f (t+angularPairAngle (x 0) (y 0))) :=
    hp.1.comp (contDiff_id.add contDiff_const)
  have hbs (j : ℕ) (hj : j ≤ 2*n) (t : ℝ) :
      ‖iteratedDeriv j (fun u => f (u+angularPairAngle (x 0) (y 0))) t‖ ≤ C*sourceSymbolScale N sig L^j := by
    rw [iteratedDeriv_comp_add_const]
    exact hp.2 j hj _
  let g := fun u => β 1 (x 1) u*conj (β 1 (y 1) u)
  have hg : Measurable g := by
    have hc (z : Plane) : Continuous (β 1 z) :=
      inheritedCircleSymbol_continuous _ _ _ _ (hQ 1) _ _ _ _ _ _ _ _ z
    exact ((hc (x 1)).mul (Complex.continuous_conj.comp (hc (y 1)))).measurable
  have hbg (u : UnitCircle) : ‖g u‖ ≤ B^2 := by
    have hbx := inheritedCircleSymbol_norm_le (S 1) (b 1) (k 1) (Q 1) (hQ 1)
      (ρ 1) (m 1) N (lam 1) sig (J 1) (i 1) (hsp 1) K (hK 1) (x 1) (hx 1) u
    have hby := inheritedCircleSymbol_norm_le (S 1) (b 1) (k 1) (Q 1) (hQ 1)
      (ρ 1) (m 1) N (lam 1) sig (J 1) (i 1) (hsp 1) K (hK 1) (y 1) (hy 1) u
    simpa only [g,norm_mul,Complex.norm_conj,pow_two] using
      mul_le_mul hbx hby (norm_nonneg _) hB
  exact hkernel hfs hC (sourceSymbolScale_one_le N hsig.le L)
    (by positivity : (0:ℝ) < (2:ℝ)^v) hl hsep hD hbs g hg (sq_nonneg B) hbg
    (fun u : UnitCircle => inner ℝ (u:Plane) (x 1-y 1)) (by fun_prop)
    (fun u => unit_direction_inner_bound u _)

end PlanarFalconer

end OAI
