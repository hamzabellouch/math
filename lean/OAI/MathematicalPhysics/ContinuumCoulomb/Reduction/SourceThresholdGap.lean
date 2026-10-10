import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePositiveCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceGridGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ScalarScaleBudgets

namespace OAI

/-! The actual rational output gap is at least one at a fixed polynomial
amplification. The same scale also dominates the numerical error budget. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_source_gap_offset {a : ℝ} (ha : 0 < a) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ s B k : ℕ, q+2*B+s ≤ k →
      ∀ N M : ℝ, 2 ≤ N → 0 ≤ M → M ≤ N →
      2*M^s ≤ (a*(N^k)^30)*((N^(30*B))⁻¹)^2 := by
  obtain ⟨q,hq,hbounds⟩ := exists_polynomial_constant_bounds (by positivity : 0 < a/2) 1
  refine ⟨q,by omega,fun s B k hk N M hN hM hMN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hratio := (hbounds N hN).1
  have hconst : 2 ≤ a*N^q := by
    have he := (inv_le_iff_one_le_mul₀ (pow_pos hN0 q)).mp hratio
    nlinarith
  rw [inv_pow]
  apply (le_mul_inv_iff₀ (sq_pos_of_pos (pow_pos hN0 (30*B)))).mpr
  calc
    2*M^s*(N^(30*B))^2 ≤ (a*N^q)*N^s*(N^(30*B))^2 := by
      gcongr
    _ = a*N^(q+s+60*B) := by
      rw [pow_add N (q+s) (60*B),pow_add N q s,
        show 60*B=(30*B)*2 by omega,pow_mul]
      ring
    _ ≤ a*(N^k)^30 := by
      rw [← pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 (by omega)) ha.le

namespace SourcePhysicalThreshold

theorem gap_ge_one (rho C : ℕ) (eps c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) (hp : d.PolynomialPromise s)
    (hscale : 2*((SourceMetadataProgram.size d:ℝ)^s) ≤
      (SourceNuclearProgram.amplification rho k d:ℝ)*
        (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2) :
    (1:ℚ) ≤ (value rho C eps c s p h k A B q d).2-
      (value rho C eps c s p h k A B q d).1 := by
  have hsource := SourcePositiveProgram.output_gap s d hd hp
  have hgap := SourceMetadataProgram.polynomialPromise_gap s d hp
  have hG0 : (0:ℚ) < (SourceMetadataProgram.size d:ℚ)^s :=
    pow_pos (by exact_mod_cast SourceMetadataProgram.size_pos d) s
  have hpos : (0:ℝ) < (SourceMetadataProgram.size d:ℝ)^s := by exact_mod_cast hG0
  have hlow : (63:ℝ)/(64*((SourceMetadataProgram.size d:ℝ)^s)) ≤
      ((SourcePositiveProgram.output s d).upper:ℝ)-(SourcePositiveProgram.output s d).lower := by
    have hh : (63:ℚ)/64*(1/(SourceMetadataProgram.size d:ℚ)^s) ≤
        (SourcePositiveProgram.output s d).upper-(SourcePositiveProgram.output s d).lower := by
      simpa only [Nat.cast_pow] using
        (mul_le_mul_of_nonneg_left hgap (by norm_num : (0:ℚ) ≤ 63/64)).trans hsource
    have hhR : (63:ℝ)/64*(1/(SourceMetadataProgram.size d:ℝ)^s) ≤
        ((SourcePositiveProgram.output s d).upper:ℝ)-(SourcePositiveProgram.output s d).lower := by
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_pow,
        Rat.cast_natCast,Rat.cast_sub] using (Rat.cast_le (K := ℝ)).mpr hh
    convert hhR using 1; ring
  let scale := (SourceNuclearProgram.amplification rho k d:ℝ)*
    (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2
  have hs : 0 ≤ scale := (by positivity : (0:ℝ) ≤ 2*(SourceMetadataProgram.size d:ℝ)^s).trans hscale
  have hprod := mul_le_mul hscale hlow (by positivity : (0:ℝ) ≤ 63/(64*(SourceMetadataProgram.size d:ℝ)^s)) hs
  have hone : (1:ℝ) ≤ scale*
      (((SourcePositiveProgram.output s d).upper:ℝ)-(SourcePositiveProgram.output s d).lower) := by
    have he : 2*(SourceMetadataProgram.size d:ℝ)^s*(63/(64*(SourceMetadataProgram.size d:ℝ)^s)) = 63/32 := by
      field_simp [hpos.ne']
      ring
    rw [he] at hprod
    linarith
  rw [gap]
  change (1:ℚ) ≤ SourceNuclearProgram.amplification rho k d *
    (((SourceContactProgram.size d^(30*B):ℕ):ℚ)⁻¹)^2 *
      ((SourcePositiveProgram.output s d).upper-(SourcePositiveProgram.output s d).lower)
  dsimp only [scale] at hone
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_one,Rat.cast_mul,Rat.cast_inv,Rat.cast_pow,Rat.cast_natCast,Rat.cast_sub] using hone

end SourcePhysicalThreshold
end ContinuumCoulomb

end

end OAI
