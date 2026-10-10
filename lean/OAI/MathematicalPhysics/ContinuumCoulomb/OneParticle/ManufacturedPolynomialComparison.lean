import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedGridGroundComparison
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedGridParameters
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedScalarParameters
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedFrequency

namespace OAI

/-! Uniform polynomial accuracy for the actual unit-charge cloud. All
infinite-dimensional estimates are derived from the cited published inputs. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb
open HubbardGlobal

theorem manufactured_polynomial_comparison
    (hflow : PublishedC4FlowInput)
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
    ∃ (rho : ℕ) (hrho : 0 < rho), ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧
    let freq := GaussianFrequency.frequency rho
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r s v p k : ℕ, q+9*r+72*s+v+p ≤ k →
    ∀ N H S D : ℝ, ∀ hN : 2 ≤ N,
      (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
      (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 25*(k:ℝ)*Real.log N ≤ D →
    ∀ (m n : ℕ) (u : Fin (m+1) → PlanarPosition), n+2=m+1 →
      (m+1:ℝ) ≤ N^r → (∀ i, ‖u i‖ ≤ N^s) →
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
    ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (∑ e, |t e|) ≤ N^v →
      (∀ i j, ‖((((8/(rho:ℝ))*(N^k)^30)*planarHoppingMatrix u i j:ℝ):ℂ)-
        graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤ (N^(2*r+p+6))⁻¹) →
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] (index : ι → Fin 3 → ℤ)
      (hindex : Function.Injective index),
      (⋃ i, positionCube (gaussCellCenter (1/(N^k)^10) (index i)) (1/(N^k)^10)) = slabDomain H S →
    let scale := (8/(rho:ℝ))*(N^k)^30
    let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
      scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq u) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j))
    ∃ (G : Position → ℝ → Position) (hbij : Function.Bijective (fun x => G x 1)),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
      LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ j (fun y => G y 1) x‖ ≤ L) ∧
      (∀ i, localizedCounterterm freq u i ≤ scale) ∧
      ((center-scale*(N^p)⁻¹:ℝ):EReal) ≤
        formGroundEnergy (dilatedNuclei
          (gridNuclei index hindex (fun x => G x 1) hbij.injective (manufactured_mesh_positive hN k))
          scale (manufactured_scale_positive hrho hN k).ne') (n+2) ∧
      formGroundEnergy (dilatedNuclei
          (gridNuclei index hindex (fun x => G x 1) hbij.injective (manufactured_mesh_positive hN k))
          scale (manufactured_scale_positive hrho hN k).ne') (n+2) ≤
        ((center+scale*(N^p)⁻¹:ℝ):EReal) := by
  obtain ⟨rho,hrho,L,K,hL,hK,B,hB,hgrid⟩ := manufactured_grid_parameters hflow
  let freq := GaussianFrequency.frequency rho
  have hf : 1 ≤ freq := manufactured_frequency_ge_one hrho
  have hfp : 0 < freq := lt_of_lt_of_le zero_lt_one hf
  have hr : (0:ℝ) < rho := by exact_mod_cast hrho
  have ha : (0:ℝ) < 8/(rho:ℝ) := by positivity
  obtain ⟨qW,hqW,hwitness⟩ := hgrid freq hfp
  obtain ⟨γ,R,S₀,δ,C,hγ,hγ1,hR,hS₀,hδ,hC,hground⟩ :=
    manufactured_grid_ground_bounds hp hv hdensity hf hr.le (manufactured_frequency_relation rho)
  obtain ⟨qT,qG,hqT,_hqG,hscalar⟩ := manufactured_scalar_parameters hf hr.le ha hγ hγ1 hδ (zero_le_one.trans hB)
  obtain ⟨qD,hqD,hsepD⟩ := exists_logarithmic_scale_threshold R
  obtain ⟨qS,hqS,hslab⟩ := exists_centered_slab_threshold C S₀
  refine ⟨rho,hrho,L,K,hL,hK,qW+qT+qD+qS+7,by omega,?_⟩
  intro r s v p k hk N H S D hN hHlo hHhi hSlo hShi hD m n u hNe hm hu hsep
    Edge _ left right t ht hgraph ι _ _ index hindex hcover
  dsimp only
  let scale := (8/(rho:ℝ))*(N^k)^30
  let η := localizedCountertermBound freq*N^r/scale
  let ε := ((N^k)^19)⁻¹
  let tol := (N^(2*r+p+6))⁻¹
  let Eform := localizedHubbardFormError m freq D (tol+tol)
  let A := hubbardFermionBottom m (localizedCoulombProfile freq 0)
    (localizedOffsiteCoulomb freq u) left right t-
    (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-Eform
  let kin := (m+1:ℝ)*(((m+1:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
    ((-1/2:ℝ)+freq/2))+2*(m+1:ℝ)*ε
  let g := (N^(qG+2*r))⁻¹
  let I := 3*((2*(m+1:ℝ)*ε)^2+scale⁻¹^2*(8*(m+1:ℝ)^3*kin)+
    (B/(N^k)^20)^2*((m+1:ℝ)+2*kin)*(m+1:ℝ))/g
  let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
    scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
      (localizedOffsiteCoulomb freq u) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j))
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hscale : 0 < scale := manufactured_scale_positive hrho hN k
  have hh : 0 < 1/(N^k)^10 := manufactured_mesh_positive hN k
  have he : 0 ≤ ε := by dsimp [ε]; positivity
  have htol : 0 ≤ tol := by dsimp [tol]; positivity
  have hmatch : (rho:ℝ)*(1/(N^k)^10)^3/8=scale⁻¹ := by
    dsimp [scale]
    field_simp
  obtain ⟨hcoeff,_hη0,_hη1,hres,G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,hfull,hraw,hmatrix⟩ :=
    hwitness r s (2*r+p+6) k (by omega) N H S D hN hHlo hHhi hSlo hShi hD
      (m+1) u (by simpa only [Nat.cast_add,Nat.cast_one] using hm) hu hsep index hindex hcover
  obtain ⟨hη0,_hη1,hηδ,hresSmall,hE,hg,hsmall,hI⟩ :=
    hscalar r v p k (by omega) N D hN hD m u left right t hm ht
  obtain ⟨hS,hH,hCH,hrH⟩ := hslab k (by omega) N hN H S hHlo hSlo hShi
  have hsepR : R ≤ D := (hsepD k (by omega) N hN).trans hD
  have hcount : (m+1:ℝ) ≤ Real.exp ((19/320:ℝ)*D) :=
    hm.trans (polynomial_count_le_exp_separation hN (by omega : r ≤ k) hD)
  have hNeR : (n+2:ℝ)=(m+1:ℝ) := by exact_mod_cast hNe
  have hresSmall' : (n+1:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 := by
    have hn : (n+1:ℝ) ≤ (m+1:ℝ) := by linarith only [hNeR]
    exact (mul_le_mul_of_nonneg_right hn (by positivity)).trans hresSmall
  have hB0 : 0 ≤ B/(N^k)^20 := div_nonneg (zero_le_one.trans hB) (by positivity)
  have hground' := hground m n D S H scale ((N^k)^5) ε η tol tol hsepR
    (by simpa only [Nat.cast_add,Nat.cast_one] using hcount) hS hH hCH hscale
    (by positivity) hrH hSlo he hη0 hηδ htol htol u hsep hcoeff hres hresSmall'
    index hindex (fun x => G x 1) hbij.injective (1/(N^k)^10) hh hmatch
    (B/(N^k)^20) hB0 (fun w s i => hfull (n+2) w s i) hraw hmatrix left right t (by simpa only [scale,tol,Complex.ofReal_mul] using hgraph) hNe g hg
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hNeR] at hground'
  have hbnds := hground' hsmall
  have hcenter : scale^2*(m+1:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
      scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq u) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)) = center := by
    dsimp only [center]
    rw [hNeR]
  rw [hcenter] at hbnds
  change ((center-scale*Eform-scale^2*I:ℝ):EReal) ≤ _ ∧ _ ≤ ((center+scale*Eform:ℝ):EReal) at hbnds
  have hpow : (N^(p+2))⁻¹+(N^(p+2))⁻¹ ≤ (N^p)⁻¹ := by
    apply (double_inverse_power_le hN (p+1)).trans
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hN1 (by omega : p ≤ p+1))
  have htotal : scale*Eform+scale^2*I ≤ scale*(N^p)⁻¹ := by
    have hEI := add_le_add hE hI
    have hmul := mul_le_mul_of_nonneg_left (hEI.trans hpow) hscale.le
    change scale*(Eform+scale*I) ≤ _ at hmul
    nlinarith only [hmul]
  have hEonly : scale*Eform ≤ scale*(N^p)⁻¹ := by
    apply mul_le_mul_of_nonneg_left (hE.trans ?_) hscale.le
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hN1 (by omega : p ≤ p+2))
  have hcounter (i : Fin (m+1)) : localizedCounterterm freq u i ≤ scale :=
    (div_le_one hscale).mp ((hcoeff i).2.trans _hη1)
  refine ⟨G,hbij,hflow,hLip,hAnti,hfix,hcharge,hreg,hjets,hcounter,?_,?_⟩
  · have hlo : center-scale*(N^p)⁻¹ ≤ center-scale*Eform-scale^2*I := by linarith only [htotal]
    exact (EReal.coe_le_coe_iff.mpr hlo).trans hbnds.1
  · have hup : center+scale*Eform ≤ center+scale*(N^p)⁻¹ := by linarith only [hEonly]
    exact hbnds.2.trans (EReal.coe_le_coe_iff.mpr hup)

end ContinuumCoulomb

end

end OAI
