import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.ScaleTiling

namespace OAI

/-! Strict subvolume exponent from uniform square-scale recurrence. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open Set Filter Complex Complex.HadamardThreeLines
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.SubvolumeArithmetic

theorem power_bound (B : ℕ) (hB : 1<B) (T A : ℝ)
    (hBT : (B:ℝ)<T) (hTB : T<(B:ℝ)^2) (hA : 0≤A)
    (f : ℕ → ℝ) (hf : ∀ k n : ℕ, n≤B^k → f n≤A*T^k) :
    let e := Real.logb (B:ℝ) T-1
    0<e ∧ e<1 ∧ ∀ n : ℕ, 0<n → f n≤(A*T)*Real.rpow n (1+e) := by
  have hBr : (1:ℝ)<B := by exact_mod_cast hB
  have hB0 : (0:ℝ)<B := lt_trans zero_lt_one hBr
  have hT0 : 0<T := hB0.trans hBT
  let a := Real.logb (B:ℝ) T
  have ha1 : 1<a := by
    apply (Real.lt_logb_iff_rpow_lt hBr hT0).mpr
    simpa only [Real.rpow_one] using hBT
  have ha2 : a<2 := by
    apply (Real.logb_lt_iff_lt_rpow hBr hT0).mpr
    simpa only [Real.rpow_two] using hTB
  change 0<a-1 ∧ a-1<1 ∧ _
  refine ⟨by linarith only [ha1],by linarith only [ha2],?_⟩
  intro n hn
  let k := Nat.log B n
  have hlow : B^k≤n := Nat.pow_log_le_self B (ne_of_gt hn)
  have hhigh : n≤B^(k+1) := le_of_lt (Nat.lt_pow_succ_log_self hB n)
  have hh := hf (k+1) n hhigh
  have he : Real.rpow ((B^k:ℕ):ℝ) a=T^k := by
    rw [Nat.cast_pow,Real.rpow_eq_pow,← Real.rpow_pow_comm (le_of_lt hB0)]
    dsimp only [a]
    rw [Real.rpow_logb hB0 (ne_of_gt hBr) hT0]
  have hpower : T^k≤Real.rpow (n:ℝ) a := by
    rw [← he]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hlow)
      (le_trans zero_le_one (le_of_lt ha1))
  have hstep := mul_le_mul_of_nonneg_left hpower (mul_nonneg hA (le_of_lt hT0))
  have haa : 1+(a-1)=a := by ring
  change f n≤(A*T)*Real.rpow n (1+(a-1))
  rw [haa]
  calc
    f n≤A*T^(k+1) := hh
    _=(A*T)*T^k := by rw [pow_succ]; ring
    _≤(A*T)*Real.rpow n a := hstep

end PolynomialPEPS.Subvolume.SubvolumeArithmetic

namespace PolynomialPEPS.Subvolume.RectangleTiling
open scoped BigOperators
open PolynomialPEPS.Subvolume.HarmonicWeights PolynomialPEPS.Subvolume.GeometricLower

theorem uniform_subvolume_square (q : ℕ) (hq : 2≤q) (J Δ : ℝ)
    (hJ : 0<J) (hΔ : 0<Δ) :
    ∃ C e : ℝ, 0<C ∧ 0<e ∧ e<1 ∧
      ∀ (L : ℕ) (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
        (Ω : State L q) (E₀ : ℝ),
        ‖Ω‖=1 → IsGridHamiltonian J hv he →
        asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω →
        FullSystemGap (Hamiltonian hv he) Ω E₀ Δ →
        ∀ (lo₁ lo₂ : ℤ) (n : ℕ), 0<n →
        vonNeumannEntropy Ω (box lo₁ lo₂ 1 n)≤C*Real.rpow n (1+e) := by
  let M : ℕ := 4*(2^(blocks q J Δ)+1)
  let B : ℕ := M^2
  let T : ℝ := (M:ℝ)^2*((M:ℝ)^2-2)
  let A : ℝ := 3*Real.log q+4*bufferConstant q J Δ
  let e : ℝ := Real.logb (B:ℝ) T-1
  have hM : (4:ℝ)≤M := by
    dsimp only [M]
    exact_mod_cast (Nat.mul_le_mul_left 4 (Nat.succ_le_succ (Nat.zero_le (2^(blocks q J Δ)))))
  have hM2 : (16:ℝ)≤(M:ℝ)^2 := by nlinarith only [hM]
  have hBr : (1:ℝ)<B := by dsimp only [B]; push_cast; linarith only [hM2]
  have hBn : 1<B := by exact_mod_cast hBr
  have hB0 : (0:ℝ)<B := zero_lt_one.trans hBr
  have hBT : (B:ℝ)<T := by
    dsimp only [B,T]
    push_cast
    nlinarith only [hM2]
  have hTB : T<(B:ℝ)^2 := by
    dsimp only [B,T]
    push_cast
    nlinarith only [hM2]
  have hT : 0<T := hB0.trans hBT
  have hQ : 0<Real.log q := Real.log_pos (by exact_mod_cast (show 1<q by omega))
  have hbuf : 0≤bufferConstant q J Δ := by dsimp only [bufferConstant]; positivity
  have hA : 0<A := by dsimp only [A]; positivity
  have he0 : 0<e := by
    have hh := (Real.lt_logb_iff_rpow_lt hBr hT).mpr
      (show (B:ℝ)^(1:ℝ)<T by simpa only [Real.rpow_one] using hBT)
    dsimp only [e]
    linarith only [hh]
  have he1 : e<1 := by
    have hh := (Real.logb_lt_iff_lt_rpow hBr hT).mpr
      (show T<(B:ℝ)^(2:ℝ) by simpa only [Real.rpow_two] using hTB)
    dsimp only [e]
    linarith only [hh]
  refine ⟨A*T,e,mul_pos hA hT,he0,he1,?_⟩
  intro L hv he Ω E₀ hΩ hH hg hgap lo₁ lo₂ n hn
  have hf : ∀ k n : ℕ, n≤B^k →
      vonNeumannEntropy Ω (box lo₁ lo₂ 1 n)≤A*T^k := by
    intro k m hm
    have hm' : m≤M^(2*k) := by
      simpa only [B,pow_mul] using hm
    exact square_entropy_below_scale (by omega) J Δ E₀ (le_of_lt hJ) hΔ
      hv he Ω hΩ hH hg hgap k m lo₁ lo₂ hm'
  exact (SubvolumeArithmetic.power_bound B hBn T A hBT hTB (le_of_lt hA)
    (fun m => vonNeumannEntropy Ω (box lo₁ lo₂ 1 m)) hf).2.2 n hn

end PolynomialPEPS.Subvolume.RectangleTiling

end

end OAI
