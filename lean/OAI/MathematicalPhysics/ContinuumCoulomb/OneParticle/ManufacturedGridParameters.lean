import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedGridWitness
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ActualOneBodyParameters
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ActualResidualParameters

namespace OAI

/-! One actual nuclear cloud simultaneously satisfies the full-domain form,
finite matrix, and differential-residual estimates at fixed polynomial scales. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem manufactured_grid_parameters (hp : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧ ∃ B : ℝ, 1 ≤ B ∧
    ∀ freq : ℝ, 0 < freq → ∃ q : ℕ, 1 ≤ q ∧
    ∀ r s p k : ℕ, q+7*r+72*s+p ≤ k →
    ∀ N H S D : ℝ, 2 ≤ N →
      (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
      (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 25*(k:ℝ)*Real.log N ≤ D →
    ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ N^r →
      (∀ i, ‖u i‖ ≤ N^s) → (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
    ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      (⋃ i, positionCube (gaussCellCenter (1/(N^k)^10) (index i)) (1/(N^k)^10)) = slabDomain H S →
    let scale := (8/(rho:ℝ))*(N^k)^30
    let η := localizedCountertermBound freq*N^r/scale
    (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) ∧
    0 ≤ η ∧ η ≤ 1 ∧
    4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D ((N^k)^5) u j) ≤
      ((N^k)^19)⁻¹^2 ∧
    ∃ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
      Function.Bijective (fun x => G x 1) ∧
      LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) ∧
      let F : Position → ℝ := fun y => gridNuclearPotential index (fun x => G x 1) rho (1/(N^k)^10) y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y)
      (∀ (n : ℕ) (w : Coulomb.H1Vector n) (t : SpinConfiguration n) (i : Fin n),
        Integrable (fun x => |F (Coulomb.position x i)| * ‖w.value t x‖^2) ∧
        (∫ x, |F (Coulomb.position x i)| * ‖w.value t x‖^2) ≤
          (B/(N^k)^20)*((∫ x, ‖w.value t x‖^2)+∑ j : Fin 3, ∫ x, ‖w.gradient t (i,j) x‖^2)) ∧
      (∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x)) ∧
      (∀ i j, |scale*correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
        localizedOneBodyTarget scale freq u i j| ≤ (N^p)⁻¹) := by
  obtain ⟨rho,hrho,L,K,hL,hK,B,hB,hfamily⟩ := manufactured_grid_witness hp
  refine ⟨rho,hrho,L,K,hL,hK,B,hB,?_⟩
  intro freq hf
  obtain ⟨E,hE,hgrid⟩ := hfamily freq hf
  have hrhoR : (0:ℝ) < rho := by exact_mod_cast hrho
  have ha : (0:ℝ) < 8/(rho:ℝ) := by positivity
  obtain ⟨qR,hqR,hres⟩ := exists_actual_manufactured_residual_parameters hf hrhoR.le ha
  obtain ⟨qM,hqM,hmat⟩ := exists_actual_oneBody_parameters hrhoR.le hf ha (zero_le_one.trans hE)
  obtain ⟨qD,hqD,hsepD⟩ := exists_logarithmic_scale_threshold 3
  refine ⟨qR+qM+qD+1,by omega,?_⟩
  intro r s p k hk N H S D hN hHlo hHhi hSlo hShi hD m u hm hu hsep ι _ index hi hcover
  dsimp only
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR : 2 ≤ N^k := hN.trans (le_self_pow₀ hN1 (by omega))
  have hR0 : 0 < N^k := by positivity
  have hS : 0 < S := (pow_pos hR0 5).trans_le hSlo
  have hH : 0 ≤ H := (pow_nonneg hR0.le 50).trans hHlo
  have hscale : 0 < (8/(rho:ℝ))*(N^k)^30 := by positivity
  obtain ⟨hcoeff,hη,hη1,herr⟩ := hres r s k (by omega) N hN H S D
    hHlo hHhi hSlo hShi hD m u hm hu
  refine ⟨hcoeff,hη,hη1,herr,?_⟩
  have hmR : (m:ℝ) ≤ (N^k)^14 := hm.trans (by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hN1 (by omega))
  have h3 : 3 ≤ D := (hsepD k (by omega) N hN).trans hD
  have hcounter (i : Fin m) : localizedCounterterm freq u i ≤ (8/(rho:ℝ))*(N^k)^30 :=
    (div_le_one hscale).mp ((hcoeff i).2.trans hη1)
  have hbox : N^s+1 ≤ H := by
    calc
      _ ≤ 2*N^s := by linarith [one_le_pow₀ hN1 (n := s)]
      _ ≤ N^(s+1) := by rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_right hN (pow_nonneg hN0.le s)]
      _ ≤ (N^k)^50 := by rw [← pow_mul]; exact pow_le_pow_right₀ hN1 (by omega)
      _ ≤ H := hHlo
  have hsupp := manufacturedWellField_support_slab freq ((8/(rho:ℝ))*(N^k)^30) hS hbox u hu
  obtain ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,hfull,hentries⟩ :=
    hgrid (N^k) ((8/(rho:ℝ))*(N^k)^30) S H hR hscale hSlo hShi hH m u hmR
      (fun i j hij => h3.trans (hsep i j hij)) hcounter hsupp index hi hcover
  refine ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,hfull,?_,?_⟩
  · exact fun i j => (hentries (u i) (u j)).1
  · exact hmat r s p k (by omega) N H S D hN hHlo hHhi hSlo hShi hD m u hm hu hsep _
      (fun i j => (hentries (u i) (u j)).1) (fun i j => (hentries (u i) (u j)).2)

end ContinuumCoulomb

end

end OAI
