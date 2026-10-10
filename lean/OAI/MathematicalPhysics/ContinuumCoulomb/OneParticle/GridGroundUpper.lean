import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ShiftedHubbardBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabSections
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CenteredGaussLabels

namespace OAI

/-! Polynomial size bounds used to choose the precision of the literal
nuclear-coordinate program. The negative slab offset is retained. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open HubbardGlobal

theorem shifted_hubbard_upper {Edge : Type*} [Fintype Edge]
    {freq : ℝ} (hf : 0 < freq) (m : ℕ) (u : Fin (m+1) → PlanarPosition)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j) ≤
      (m+1:ℝ)/2*localizedPotentialBound freq+4*(∑ e, |t e|) := by
  have hU0 := localizedCoulombProfile_nonnegative freq 0
  have hU : localizedCoulombProfile freq 0 ≤ localizedPotentialBound freq := by
    simpa only [localizedCoulombCoeff_distance,sub_self,norm_zero] using
      localizedCoulombCoeff_le hf (0 : PlanarPosition) 0
  have h := (le_abs_self _).trans (hubbardFermionBottom_abs_bound m
    (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t)
  simp_rw [abs_of_nonneg hU0,abs_of_nonneg (localizedOffsiteCoulomb_nonnegative freq u _ _)] at h
  have hmul := mul_le_mul_of_nonneg_left hU (show 0 ≤ (m+1:ℝ)/2 by positivity)
  linarith only [h,hmul]

theorem exists_grid_ground_upper_exponent {freq rho a : ℝ}
    (hf : 1 ≤ freq) (hrho : 0 ≤ rho) (ha : 0 < a) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r v p k : ℕ, ∀ N H S : ℝ, 2 ≤ N →
    ∀ {Edge : Type} [Fintype Edge] (m : ℕ) (u : Fin (m+1) → PlanarPosition)
      (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (m+1:ℝ) ≤ N^r → (∑ e, |t e|) ≤ N^v →
    let scale := a*(N^k)^30
    scale^2*(m+1:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
      scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq u) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j))+
      scale*(N^p)⁻¹ ≤ N^(q+60*k+r+v) := by
  let E0 := (-1/2:ℝ)+freq/2
  let C := a^2*E0+a*localizedPotentialBound freq/2+5*a
  have hE0 : 0 ≤ E0 := by dsimp [E0]; linarith
  have hP := localizedPotentialBound_nonnegative freq
  have hfp : 0 < freq := lt_of_lt_of_le zero_lt_one hf
  obtain ⟨q,hq,hconst⟩ := exists_polynomial_constant_bounds (by norm_num : (0:ℝ)<1) C
  refine ⟨q,by omega,?_⟩
  intro r v p k N H S hN Edge _ m u left right t hm ht
  dsimp only
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  let Z := N^(60*k+r+v)
  have hfirst : (a*(N^k)^30)^2*(m+1:ℝ)*E0 ≤ (a^2*E0)*Z := by
    calc
      _ = (a^2*E0)*((N^k)^60*(m+1:ℝ)) := by ring
      _ ≤ (a^2*E0)*((N^k)^60*N^r) := by gcongr
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [Z]
        rw [← pow_mul,← pow_add]
        exact pow_le_pow_right₀ hN1 (by omega)
  have hMr : (N^k)^30*(m+1:ℝ) ≤ Z := by
    calc
      _ ≤ (N^k)^30*N^r := by gcongr
      _ ≤ _ := by
        dsimp [Z]
        rw [← pow_mul,← pow_add]
        exact pow_le_pow_right₀ hN1 (by omega)
  have hTr : (N^k)^30*(∑ e, |t e|) ≤ Z := by
    calc
      _ ≤ (N^k)^30*N^v := by gcongr
      _ ≤ _ := by
        dsimp [Z]
        rw [← pow_mul,← pow_add]
        exact pow_le_pow_right₀ hN1 (by omega)
  have hLast : (N^k)^30*(N^p)⁻¹ ≤ Z := by
    calc
      _ ≤ (N^k)^30*1 := mul_le_mul_of_nonneg_left
        (inv_le_one_of_one_le₀ (one_le_pow₀ hN1)) (by positivity)
      _ ≤ _ := by dsimp [Z]; rw [mul_one,← pow_mul]; exact pow_le_pow_right₀ hN1 (by omega)
  have hneg := slabPotential_nonpositive hrho H S 0
  have hslab := mul_le_mul_of_nonneg_left (show slabPotential rho H S 0+E0 ≤ E0 by linarith)
    (show 0 ≤ (a*(N^k)^30)^2*(m+1:ℝ) by positivity)
  have hhub := mul_le_mul_of_nonneg_left (shifted_hubbard_upper hfp m u left right t)
    (show 0 ≤ a*(N^k)^30 by positivity)
  have hmid := mul_le_mul_of_nonneg_left hMr (show 0 ≤ a*localizedPotentialBound freq/2 by positivity)
  have ht' := mul_le_mul_of_nonneg_left hTr (show 0 ≤ 4*a by positivity)
  have hend := mul_le_mul_of_nonneg_left hLast ha.le
  calc
    _ ≤ C*Z := by dsimp only [C,E0] at *; nlinarith only [hslab,hhub,hfirst,hmid,ht',hend]
    _ ≤ N^q*Z := mul_le_mul_of_nonneg_right (hconst N hN).2 (by dsimp [Z]; positivity)
    _ = _ := by dsimp [Z]; rw [← pow_add]; congr 1; omega

theorem centered_grid_count_power {N : ℝ} (hN : 2 ≤ N) (k : ℕ)
    {r : CenteredGaussLabels.Radii}
    (h0 : (r.1:ℝ) ≤ N^(60*k)) (h1 : (r.2.1:ℝ) ≤ N^(60*k))
    (h2 : (r.2.2:ℝ) ≤ N^(15*k)) :
    ((CenteredGaussLabels.labels r).length:ℝ) ≤ N^(135*k+8) := by
  have hN1 : 1 ≤ N := by linarith
  have hp60 : 1 ≤ N^(60*k) := one_le_pow₀ hN1
  have hp15 : 1 ≤ N^(15*k) := one_le_pow₀ hN1
  have ha : 2*(r.1:ℝ)+1 ≤ 3*N^(60*k) := by linarith
  have hb : 2*(r.2.1:ℝ)+1 ≤ 3*N^(60*k) := by linarith
  have hc : 2*(r.2.2:ℝ)+1 ≤ 3*N^(15*k) := by linarith
  have h216 : (216:ℝ) ≤ N^8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 8
    norm_num at h
    linarith
  rw [CenteredGaussLabels.labels_length]
  push_cast
  calc
    _ ≤ 8*((3*N^(60*k))*(3*N^(60*k))*(3*N^(15*k))) := by gcongr
    _ = 216*N^(135*k) := by rw [show 135*k=(60*k+60*k)+15*k by omega,pow_add,pow_add]; ring
    _ ≤ _ := by rw [pow_add N (135*k) 8]; nlinarith [pow_nonneg (by linarith : 0 ≤ N) (135*k)]

end ContinuumCoulomb

end

end OAI
