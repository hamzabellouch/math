import OAI.MeasureTheory.Falconer.Angular.AngularMeanAssembly
import OAI.MeasureTheory.Falconer.Angular.AngularUniformAbsorption
import OAI.MeasureTheory.Falconer.Estimates.ActualRegularizedClasses

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem regularized_parallel_inverse_scaled (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {m : ℝ → ℝ} {N B : ℕ} {δ lam : ℝ}
    (hr : RegularizedProfileData Q ρ N B δ lam m) (hN : 0 < N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath} (hP : P.length = p) :
    (∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
      1/dist (Q.descendant c).center (Q.descendant P).center)/(2:ℝ)^p ≤
      484*(1+2*(N:ℝ))*((2:ℝ)^N)^
        (height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+6*lam) := by
  have hpack := hr.packing
  simp only [hQ,div_one] at hpack
  have hi := parallel_inverse_distance_profile Q hQ ρ m N lam hpack hgp hpN hP
  have hs := angular_profile_dyadic_sum m hN lam hgp
  have hn : ((p-g:ℕ):ℝ) ≤ N := by exact_mod_cast (show p-g ≤ N by omega)
  have hp : 0 < (2:ℝ)^p := by positivity
  apply (div_le_div_of_nonneg_right hi hp.le).trans
  rw [mul_div_assoc]
  calc
    _ ≤ 484*((1+2*(p-g:ℕ))*((2:ℝ)^N)^
        (height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+6*lam)) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ _ := by rw [← mul_assoc]; gcongr

theorem regularized_parallel_strip_sum (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {m : ℝ → ℝ} {N B : ℕ} {δ lam sig : ℝ}
    (hr : RegularizedProfileData Q ρ N B δ lam m) (hN : 0 < N)
    (hlam : 0 < lam) (hsig : 0 < sig)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath} (hP : P.length = p) :
    ∑ c ∈ parallelTestCells Q ρ g p P,
      stripHitBound (2/(2:ℝ)^p*((2:ℝ)^N)^(1000*sig))
        (quarterTurn ((Q.descendant c).center-(Q.descendant P).center)) ≤
      ENNReal.ofReal ((3874*Real.pi)*(1+2*(N:ℝ))*((2:ℝ)^N)^
        (height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+1000*sig+6*lam)) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  apply (parallel_strip_sum_inverse Q hside ρ g p hP (by positivity)).trans
  apply ENNReal.ofReal_le_ofReal
  let K := height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p
  have hi := regularized_parallel_inverse_scaled Q hQ ρ hr hN hgp hpN hP
  change _ ≤ 484*(1+2*(N:ℝ))*((2:ℝ)^N)^(K+6*lam) at hi
  have hRp : 0 < (2:ℝ)^N := by positivity
  have he : ((2:ℝ)^N)^(1000*sig)*((2:ℝ)^N)^(K+6*lam) =
      ((2:ℝ)^N)^(K+1000*sig+6*lam) := by rw [← Real.rpow_add hRp]; congr 1; ring
  have hK : 0 ≤ K := height_nonneg _ hgp
  have hz : 1 ≤ ((2:ℝ)^N)^(K+1000*sig+6*lam) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
  have hn : 1 ≤ 1+2*(N:ℝ) := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hb := mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ 8*Real.pi*((2:ℝ)^N)^(1000*sig))
  have hid : 8*Real.pi*((2:ℝ)^N)^(1000*sig)*
      (484*(1+2*(N:ℝ))*((2:ℝ)^N)^(K+6*lam)) =
      3872*Real.pi*(1+2*(N:ℝ))*((2:ℝ)^N)^(K+1000*sig+6*lam) := by
    calc
      _ = 3872*Real.pi*(1+2*(N:ℝ))*
        (((2:ℝ)^N)^(1000*sig)*((2:ℝ)^N)^(K+6*lam)) := by ring
      _ = _ := by rw [he]
  rw [hid] at hb
  have hdiag : 2*Real.pi ≤ 2*Real.pi*(1+2*(N:ℝ))*((2:ℝ)^N)^(K+1000*sig+6*lam) := by
    calc
      _ ≤ 2*Real.pi*(1+2*(N:ℝ)) := le_mul_of_one_le_right (by positivity) hn
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hz
  change _ ≤ (3874*Real.pi)*(1+2*(N:ℝ))*((2:ℝ)^N)^(K+1000*sig+6*lam)
  calc
    _ = 2*Real.pi+8*Real.pi*((2:ℝ)^N)^(1000*sig)*
      ((∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
        1/dist (Q.descendant c).center (Q.descendant P).center)/(2:ℝ)^p) := by ring
    _ ≤ _ := by linarith

theorem uniform_parallel_exceptional {lam sig : ℝ} (hlam : 0 < lam) (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
      ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (B : ℕ) (δ : ℝ),
      RegularizedProfileData Q ρ N B δ lam m →
      ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ P : CellPath, P.length = p →
      sourceArcLength (parallelGoodSet Q ρ g p P
        (2/(2:ℝ)^p*((2:ℝ)^N)^(1000*sig))
        (((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+2000*(lam+sig))))ᶜ ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  obtain ⟨N₁,hN₁⟩ := fixed_linear_subpower (3874*Real.pi) (by positivity) (add_pos hlam hsig)
  refine ⟨max 1 N₁,?_⟩
  intro N hN Q hQ ρ m B δ hr g p hgp hpN P hP
  have hNpos : 0 < N := by omega
  let K := height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p
  have hb := regularized_parallel_strip_sum Q hQ ρ hr hNpos hlam hsig hgp hpN hP
  apply (parallelGoodSet_compl_bound Q ρ g p P (by positivity) (by positivity)).trans
  apply (ENNReal.div_le_div_right hb _).trans
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hc := hN₁ N ((le_max_right _ _).trans hN)
  apply le_trans _ (angular_ratio_absorption (K := K) hlam hsig hc)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  dsimp [K]; linarith

end PlanarFalconer

end OAI
