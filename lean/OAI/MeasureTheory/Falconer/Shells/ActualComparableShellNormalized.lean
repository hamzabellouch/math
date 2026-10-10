import OAI.MeasureTheory.Falconer.Shells.ActualComparableShellDistance
import OAI.MeasureTheory.Falconer.Measures.ComparableNormalization

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_comparable_shell_normalized {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a d n v : ℕ),
    0 < q → a₀ ≤ a+n → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (B₀ : ℕ) (δ lam : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) → a+n ≤ N →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m)
      N (lam) sig J (i l) (hsp l)
    let D : Fin 2 → PositiveDistanceData := fun l =>
      ⟨Q l,ρ l,m,N,q,a+n,v,lam,sig,J,i l+1,[],[]⟩
    ‖((2:ℝ)^(2*((v:ℝ)-a))/(((2:ℝ)^N)^(-m a))^4) •
      (∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
      ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
        if ¬ angularNear (Q 0) (Q 1) (a+d) row col then
          ∫ x in angularLengthShell (a+n), angularStationarySpatialKernel (β 0) (β 1) o v Ψ x
            ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
        else 0)‖ ≤
    H * ((2:ℝ)^N)^(-2*(m (a+n)-(a+n:ℕ)/N-(m a-(a:ℝ)/N))+12*lam) *
      ((D 0).separatedMaximum (D 1) (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) (a+n)).toReal := by
  obtain ⟨H,hH,N₀,h₀⟩ := uniform_actual_comparable_shell_distance hΨ hsΨ hsig K o hJ
  let C : ℝ≥0∞ := ENNReal.ofReal H*binKernelConstant*257025537024256*4096
  have hC : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top binKernelConstant_ne_top) (by norm_num))
      (by norm_num)
  refine ⟨C.toReal,ENNReal.toReal_nonneg,max 1 N₀,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a d n v hq ha₀ ht hv S k hS hcard hK L hL
    L₀ hvh hLL hL₀ B₀ δ lam hd hp i hsp hspb A B hA hB
  let D : Fin 2 → PositiveDistanceData := fun l =>
    ⟨Q l,ρ l,m,N,q,a+n,v,lam,sig,J,i l+1,[],[]⟩
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num : 0 < 1) ((le_max_left _ _).trans hN)
  have he := h₀ N ((le_max_right _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a d n v hq ha₀ ht hv
    S k hS hcard hK L hL L₀ hvh hLL hL₀ lam i hsp hspb A B hA hB
  have hc := sourceProductVertices_profile_count (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1)
    N B₀ δ lam m m (hd 0) (hd 1) A B a n hA hB hp
  have hcc : ((sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n).card:ℝ) ≤
      4096*((2:ℝ)^N)^(2*(m (a+n)-m a)+12*lam) := by
    convert hc using 1
    congr 2
    ring
  have hn := comparable_normalized_bound N hNp m a (a+n:ℕ) v lam
    (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n).card
    (ENNReal.ofReal H*binKernelConstant)
    ((D 0).separatedMaximum (D 1) (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) (a+n))
    _ (by simpa only [Nat.cast_add] using hcc) (by simpa only [Nat.cast_add] using he)
  have hmax := PositiveDistanceData.separatedMaximum_ne_top (D 0) (D 1)
    (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) (a+n)
  have hfin : C * ENNReal.ofReal (((2:ℝ)^N)^(-2*(m (a+n)-(a+n:ℕ)/N-(m a-(a:ℝ)/N))+12*lam)) *
      (D 0).separatedMaximum (D 1) (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) (a+n) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hmax
  simp only [Nat.cast_add] at hfin hn
  have ht := ENNReal.toReal_mono hfin hn
  have hrpow : 0 ≤ ((2:ℝ)^N)^(-2*(m ((a:ℝ)+n)-((a:ℝ)+n)/N-(m a-(a:ℝ)/N))+12*lam) := by positivity
  simpa only [← ofReal_norm,ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hrpow,C,D,Nat.cast_add] using ht

end PlanarFalconer

end OAI
