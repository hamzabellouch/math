import OAI.NumberTheory.Ostmann.QuadraticSieveCutoffScalesAlgebra
import OAI.NumberTheory.Ostmann.QuadraticSieveCutoffScalesChoice

namespace OAI

namespace Ostmann.QuadraticSieve

theorem smoothingCutoff_scalar_bound {M N : ℕ} {η ξ : ℝ}
    (hM : 0<M) (hN : 0<N) (hη : 0<η) (hξ1 : 1<ξ) (hξ2 : ξ≤2)
    (hscale : 4*(N:ℝ)*((M:ℝ)*N)^η ≤ M) :
    Real.sqrt (M:ℝ)*(smoothingCutoff M N η:ℝ)^(ξ-1/2) ≤
      16*((M:ℝ)*N)^(2*η)*((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)) := by
  have hM1 : (1:ℝ)≤M := by exact_mod_cast hM
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hP1 : (1:ℝ)≤(M:ℝ)*N := by nlinarith
  have hT1 : 1≤((M:ℝ)*N)^η := Real.one_le_rpow hP1 hη.le
  have hbound := cutoff_scale_scalar_bound hM1 (by exact_mod_cast hN) hT1
    (Nat.cast_nonneg (smoothingCutoff M N η))
    (smoothingCutoff_size hM hN hη hscale).2.2.2.2 hξ1 hξ2
  have he : (((M:ℝ)*N)^η)^2 = ((M:ℝ)*N)^(2*η) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity : (0:ℝ)≤(M:ℝ)*N)]
    congr 1
    ring
  simpa only [he] using hbound

theorem exists_smoothing_cutoff_scales {M N : ℕ} {η ξ : ℝ}
    (hM : 0<M) (hN : 0<N) (hη : 0<η) (hξ1 : 1<ξ) (hξ2 : ξ≤2)
    (hscale : 4*(N:ℝ)*((M:ℝ)*N)^η ≤ M) :
    ∃ K : ℕ, K=smoothingCutoff M N η ∧ 0<K ∧ K≤M ∧
      (2*(N:ℝ)^2/M)*((M:ℝ)*N)^η ≤ (K:ℝ) ∧
      (K:ℝ)≤((M:ℝ)*N)^3 ∧
      Real.sqrt (M:ℝ)*(K:ℝ)^(ξ-1/2) ≤
        16*((M:ℝ)*N)^(2*η)*((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1)) ∧
      Real.sqrt ((M:ℝ)/(K:ℝ))*N ≤ M := by
  have h := smoothingCutoff_size hM hN hη hscale
  exact ⟨smoothingCutoff M N η,rfl,h.1,h.2.1,h.2.2.1,h.2.2.2.1,
    smoothingCutoff_scalar_bound hM hN hη hξ1 hξ2 hscale,
    smoothingCutoff_sqrt_bound hM hN hη hscale⟩

end Ostmann.QuadraticSieve

end OAI
