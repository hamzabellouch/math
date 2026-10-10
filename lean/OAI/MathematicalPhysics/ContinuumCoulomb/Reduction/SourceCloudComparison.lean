import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedPolynomialComparison
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedScaleThreshold
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceGridGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceUnitCoulomb
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.UnitProgramGroundInterval

namespace OAI

/-! The actual source nuclear program has the manufactured Hubbard ground
interval. The remaining premises concern only its finite calibrated sites
and hopping matrix, not any continuum energy comparison. -/

noncomputable section
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb
open HubbardGlobal

theorem source_cloud_comparison
    (hflow : PublishedC4FlowInput)
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
    ∃ (rho : ℕ) (_hrho : 0 < rho) (U F K q : ℕ), 1 ≤ q ∧
    ∀ (r s v p k ap calC srcS pc h A B qt : ℕ) (eps c : ℚ) (d : BinaryHeisenberg),
      q+9*r+72*s+v+p ≤ k → q+465*k+2*r+v+p+34 ≤ ap →
    ∀ (m n : ℕ) (u : Fin (m+1) → ℚ×ℚ), n+2=m+1 →
      (SourcePositiveProgram.output srcS d).vertices=n+2 →
      SourceNuclearProgram.sites rho calC eps c srcS pc h k A B d=List.ofFn u →
      (m+1:ℝ) ≤ (SourceContactProgram.size d:ℝ)^r →
      (∀ i, ‖PlanarForcingProgram.position (u i)‖ ≤ (SourceContactProgram.size d:ℝ)^s) →
    ∀ D : ℝ, 25*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ D →
      (∀ i j, i ≠ j → D ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖) →
    ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (∑ e, |t e|) ≤ (SourceContactProgram.size d:ℝ)^v →
      (∀ i j, ‖((SourceNuclearProgram.amplification rho k d:ℝ):ℂ)*
          (planarHoppingMatrix (fun a => PlanarForcingProgram.position (u a)) i j:ℂ)-
        graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤
          ((SourceContactProgram.size d:ℝ)^(2*r+p+7))⁻¹) →
      (1:ℚ) ≤ (SourcePhysicalThreshold.value rho calC eps c srcS pc h k A B qt d).2-
        (SourcePhysicalThreshold.value rho calC eps c srcS pc h k A B qt d).1 →
    let freq := GaussianFrequency.frequency rho
    let scale := (SourceNuclearProgram.amplification rho k d:ℝ)
    let center := scale^2*(n+2:ℝ)*
      (slabPotential rho (SourcePhysicalThreshold.slabHorizontal k d)
        (SourcePhysicalThreshold.slabVertical k d) 0+((-1/2:ℝ)+freq/2))+
      scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq (fun a => PlanarForcingProgram.position (u a))) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq (fun a => PlanarForcingProgram.position (u a)) i j))
    let output := SourceUnitCoulomb.value rho calC U F K eps c srcS pc h k A B qt ap d
    ∃ ho : output.Valid,
      ((center-scale*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) ≤ unitGroundEnergy (output.toData ho) ∧
      unitGroundEnergy (output.toData ho) ≤ ((center+scale*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) := by
  obtain ⟨rho,hrho,L,J,hL,hJ,q₀,hq₀,hpoly⟩ := manufactured_polynomial_comparison hflow hp hv hdensity
  let freq := GaussianFrequency.frequency rho
  have hf : 1 ≤ freq := manufactured_frequency_ge_one hrho
  have hr : (0:ℝ) < rho := by exact_mod_cast hrho
  have ha : (0:ℝ) < 8/(rho:ℝ) := by positivity
  obtain ⟨U,F,_hU,_hF,hnum⟩ := TransformedGauss.exists_uniform_constants rho hrho
  obtain ⟨K,hK⟩ := exists_nat_ge (L:ℝ)
  obtain ⟨qS,_hqS,hscale⟩ := exists_manufactured_scale_threshold ha
  obtain ⟨qU,_hqU,hupper⟩ := exists_grid_ground_upper_exponent hf hr.le ha
  obtain ⟨qJ,_hqJ,hprecision⟩ := exists_grid_node_separation_offset J
  obtain ⟨qD,_hqD,hthree⟩ := exists_logarithmic_scale_threshold 3
  refine ⟨rho,hrho,U,F,K,q₀+qS+qU+qJ+qD+4,by omega,?_⟩
  intro r s v p k ap calC srcS pc h A B qt eps c d hk hap m n u hNe helectrons hsites hm hu D hD hsep
    Edge _ left right t ht hgraph hgap
  dsimp only
  let N := SourceContactProgram.size d
  let uu := fun i => PlanarForcingProgram.position (u i)
  let scale := (SourceNuclearProgram.amplification rho k d:ℝ)
  let H := (SourcePhysicalThreshold.slabHorizontal k d:ℝ)
  let S := (SourcePhysicalThreshold.slabVertical k d:ℝ)
  let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
    scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq uu) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq uu i j))
  have hN : (2:ℝ) ≤ N := by exact_mod_cast SourceContactProgram.size_ge_two d
  have hN0 : (0:ℝ) < N := by linarith
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hscaleEq : scale=(8/(rho:ℝ))*((N:ℝ)^k)^30 := SourceNuclearProgram.amplification_real rho k d
  have hs1 : 1 ≤ scale := by rw [hscaleEq]; exact hscale k (by omega) N hN
  have hs : 0 < scale := lt_of_lt_of_le zero_lt_one hs1
  have hmesh := SourcePhysicalThreshold.mesh_positive k d
  have hH := SourceNuclearProgram.horizontal_bounds k d
  have hS := SourceNuclearProgram.vertical_bounds k d
  let rad := SourceNuclearProgram.radii k d
  let index := fun j : {j // j ∈ centeredGridIndices (CenteredGaussLabels.radiiVector rad)} => j.val
  have hgraph' : ∀ i j, ‖((((8/(rho:ℝ))*((N:ℝ)^k)^30)*planarHoppingMatrix uu i j:ℝ):ℂ)-
      graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤ ((N:ℝ)^(2*r+(p+1)+6))⁻¹ := by
    simpa only [← hscaleEq,Complex.ofReal_mul,uu,scale,N,show 2*r+(p+1)+6=2*r+p+7 by omega] using hgraph
  obtain ⟨G,hbij,hGflow,hLip,hAnti,hfix,hcharge,hreg,hjets,hcounter,hlo,hhi⟩ :=
    hpoly r s v (p+1) k (by omega) N H S D hN hH.1 hH.2 hS.1 hS.2 hD
      m n uu hNe hm hu hsep left right t ht hgraph' index Subtype.val_injective
      (SourceNuclearProgram.grid_cover k d)
  have hthreeD : 3 ≤ D := (hthree k (by omega) N hN).trans hD
  have huinj : Function.Injective u := by
    intro i j hij
    by_contra hne
    have hh := hthreeD.trans (hsep i j hne)
    rw [hij,sub_self,norm_zero] at hh
    norm_num at hh
  have hSp : 1 ≤ S := (one_le_pow₀ (one_le_pow₀ hN1 : (1:ℝ) ≤ (N:ℝ)^k)).trans hS.1
  have hnum' := hnum K (N^ap) (SourcePhysicalThreshold.mesh k d) hmesh
    (SourceNuclearProgram.amplification rho k d) (SourcePhysicalThreshold.slabVertical k d)
    hs1 hSp (m+1) u huinj (fun i j hij => hthreeD.trans (hsep i j hij))
    (by simpa only [uu,← hscaleEq] using hcounter) (by simpa only [uu,← hscaleEq] using hcharge)
    G (by simpa only [uu,← hscaleEq] using hGflow) L hLip hK
  have hNpow : (N:ℝ)^ap ≤ (N^ap:ℕ) := by simp only [Nat.cast_pow]; exact le_rfl
  have hprec := hprecision k ap (by omega) N (N^ap) hN hNpow
  rw [← SourceNuclearProgram.inverse_mesh_real k d] at hprec
  have hNeR : (n+2:ℝ)=(m+1:ℝ) := by exact_mod_cast hNe
  have hupper' : center+scale*((N:ℝ)^(p+1))⁻¹ ≤ (N:ℝ)^(qU+60*k+r+v) := by
    have hh := hupper r v (p+1) k N H S hN m uu left right t hm ht
    simpa only [center,hNeR,hscaleEq] using hh
  have hcount := SourceNuclearProgram.grid_count k d
  have hbudget := grid_node_rounding_budget hN hs1 (q := qU) (r := r) (v := v) (p := p+1)
    (k := k) (a := ap) (P := N^ap) (by omega) hNpow (Q := (CenteredGaussLabels.labels rad).length)
    (by positivity) hcount (M := (n+2:ℝ)) (by positivity) (by simpa only [hNeR] using hm) hupper'
  have hhlo : ((center-scale*((N:ℝ)^(p+1))⁻¹:ℝ):EReal) ≤ formGroundEnergy
      (dilatedNuclei (CenteredGaussLabels.nuclei rad (fun x => G x 1) hbij.injective
        (by positivity : 0 < (SourcePhysicalThreshold.mesh k d:ℝ)⁻¹)) scale hs.ne') (n+2) := by
    rw [CenteredGaussLabels.dilated_nuclei_ground (hs := hs)]
    simpa only [SourceNuclearProgram.inverse_mesh_real,center,hscaleEq,H,S,N,uu,index,rad] using hlo
  have hhhi : formGroundEnergy
      (dilatedNuclei (CenteredGaussLabels.nuclei rad (fun x => G x 1) hbij.injective
        (by positivity : 0 < (SourcePhysicalThreshold.mesh k d:ℝ)⁻¹)) scale hs.ne') (n+2) ≤
      ((center+scale*((N:ℝ)^(p+1))⁻¹:ℝ):EReal) := by
    rw [CenteredGaussLabels.dilated_nuclei_ground (hs := hs)]
    simpa only [SourceNuclearProgram.inverse_mesh_real,center,hscaleEq,H,S,N,uu,index,rad] using hhi
  let x := AffinePhysicalOutput.argument rho (SourceUnitCoulomb.input rho calC eps c srcS pc h k A B qt ap d)
  have hn : 0 < x.2.1 := by change 0 < (SourcePositiveProgram.output srcS d).vertices; omega
  have hNx : 0 < x.1.1.1.2 := hmesh
  have hnumx : ∀ l : TransformedGauss.Label,
      ‖CappedKernelProgram.position (TransformedGauss.value rho U F K x.1.1.1.1 x.1.1.1.2
        x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2 l.1 l.2)-
        G (gaussLatticePoint (x.1.1.1.2:ℝ)⁻¹ (RationalGaussNodes.index l.1 l.2)) 1‖ ≤
          ((x.1.1.1.1:ℝ)+1)⁻¹ := by
    intro l
    simpa only [x,AffinePhysicalOutput.argument,SourceUnitCoulomb.input,SourceNuclearProgram.input,hsites,N] using hnum' l.1 l.2
  have hxs : x.2.1=n+2 := helectrons
  obtain ⟨ho,hl,hh⟩ := UnitCoulombProgram.ground_interval (center := center) (error := scale*((N:ℝ)^(p+1))⁻¹) (roundError := ((N:ℝ)^(p+1))⁻¹) rho U F K hrho x hNx hn hgap
    (fun x => G x 1) hbij.injective hAnti hnumx hprec hs (SourceNuclearProgram.factor_amplification hrho k d)
    (by simpa only [hxs,x,AffinePhysicalOutput.argument,SourceUnitCoulomb.input,
      SourceNuclearProgram.input,SourcePhysicalThreshold.input,helectrons,rad,SourceNuclearProgram.radii] using hhlo)
    (by simpa only [hxs,x,AffinePhysicalOutput.argument,SourceUnitCoulomb.input,
      SourceNuclearProgram.input,SourcePhysicalThreshold.input,helectrons,rad,SourceNuclearProgram.radii] using hhhi)
    hbudget.1 (by simpa only [hxs,x,AffinePhysicalOutput.argument,SourceUnitCoulomb.input,
      SourceNuclearProgram.input,SourcePhysicalThreshold.input,helectrons,rad,SourceNuclearProgram.radii,Nat.cast_add,Nat.cast_ofNat] using hbudget.2)
  have hsum : scale*((N:ℝ)^(p+1))⁻¹+((N:ℝ)^(p+1))⁻¹ ≤ scale*((N:ℝ)^p)⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right hs1 (by positivity : 0 ≤ ((N:ℝ)^(p+1))⁻¹)
    have hdouble := mul_le_mul_of_nonneg_left (double_inverse_power_le hN p) hs.le
    nlinarith only [hmul,hdouble]
  refine ⟨ho,?_,?_⟩
  · have he : center-scale*((N:ℝ)^p)⁻¹ ≤ center-scale*((N:ℝ)^(p+1))⁻¹-((N:ℝ)^(p+1))⁻¹ := by linarith only [hsum]
    exact (EReal.coe_le_coe_iff.mpr he).trans hl
  · have he : center+scale*((N:ℝ)^(p+1))⁻¹+((N:ℝ)^(p+1))⁻¹ ≤ center+scale*((N:ℝ)^p)⁻¹ := by linarith only [hsum]
    exact hh.trans (EReal.coe_le_coe_iff.mpr he)

end ContinuumCoulomb

end

end OAI
