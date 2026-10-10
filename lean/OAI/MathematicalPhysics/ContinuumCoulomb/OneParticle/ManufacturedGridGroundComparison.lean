import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedHubbardComparison
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedGroundUpper
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GridNuclei

namespace OAI

/-! The actual transported unit-charge cloud has two-sided physical ground
bounds obtained from the full-domain lower estimate and localized trials. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

def manufacturedGridError {ι : Type*} [Fintype ι] (index : ι → Fin 3 → ℤ)
    (G : Position → Position) (rho H S freq scale h : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (y : Position) : ℝ :=
  gridNuclearPotential index G rho h y-(slabPotential rho H S y+manufacturedWellField freq scale S u y)

theorem manufactured_grid_ground_bounds
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2=4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 1 ≤ C ∧
    ∀ (m n : ℕ) (D S H scale r ε η εM εG : ℝ), R ≤ D →
      (m+1:ℕ) ≤ Real.exp ((19/320:ℝ)*D) → S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H →
      ∀ hscale : 0 < scale, 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε → 0 ≤ η → η ≤ δ →
      0 ≤ εM → 0 ≤ εG →
    ∀ (u : Fin (m+1) → PlanarPosition), (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) →
      4*(m+1:ℕ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ ε^2 →
      (n+1:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 →
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
      (G : Position → Position) (hG : Function.Injective G) (h : ℝ) (hh : 0 < h), rho*h^3/8=scale⁻¹ →
    ∀ B : ℝ, 0 ≤ B →
      (∀ (w : Coulomb.H1Vector (n+2)) s i,
        Integrable (fun x => |manufacturedGridError index G rho H S freq scale h u (Coulomb.position x i)| * ‖w.value s x‖^2) ∧
        (∫ x, |manufacturedGridError index G rho H S freq scale h u (Coulomb.position x i)| * ‖w.value s x‖^2) ≤
          B*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2)) →
      (∀ i j, Integrable (fun x => manufacturedGridError index G rho H S freq scale h u x*
        continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x)) →
      (∀ i j, |scale*correctedNuclearOneBodyMatrix rho H S freq scale u
        (manufacturedGridError index G rho H S freq scale h u) i j-localizedOneBodyTarget scale freq u i j| ≤ εM) →
    ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (∀ i j, ‖(scale*planarHoppingMatrix u i j:ℂ)-graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤ εG) →
      n+2=m+1 →
      let Hb := hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t
      let Vsum := (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)
      let Eform := localizedHubbardFormError m freq D (εM+εG)
      let A := Hb-Vsum-Eform
      let e := 2*(n+2:ℝ)*ε
      let K := (n+2:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+((-1/2:ℝ)+freq/2))+e
      let g₀ := (γ/8)/(2*((n+2:ℕ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+
        6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1))
      let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+scale*(Hb-Vsum)
      ∀ g : ℝ, 0 < g → B*(n+2)+|A/scale|+g ≤ g₀ →
      let I := 3*(e^2+(scale⁻¹)^2*(8*(n+2:ℝ)^3*K)+B^2*((n+2:ℝ)+2*K)*(n+2))/g
      ((center-scale*Eform-scale^2*I:ℝ):EReal) ≤
        formGroundEnergy (dilatedNuclei (gridNuclei index hindex G hG hh) scale hscale.ne') (n+2) ∧
      formGroundEnergy (dilatedNuclei (gridNuclei index hindex G hG hh) scale hscale.ne') (n+2) ≤
        ((center+scale*Eform:ℝ):EReal) := by
  obtain ⟨γ,R,S₀,δ,C,hγ,hγ1,hR,hS₀,hδ,hC,hlower⟩ :=
    manufacturedSlab_uniform_hubbard_lower hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,_hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,C,hγ,hγ1,hR.trans (le_max_left _ _),hS₀,hδ,hC,?_⟩
  intro m n D S H scale r ε η εM εG hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ hεM hεG
    u hsep hcoeff herr hsmall ι _ _ index hindex G hG h hh hmatch B hB hfull hraw hmatrix Edge _ left right t hgraph hNe
  dsimp only
  intro g hg hsmallB
  let F := manufacturedGridError index G rho H S freq scale h u
  let Hb := hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t
  let Vsum := (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)
  let Eform := localizedHubbardFormError m freq D (εM+εG)
  let A := Hb-Vsum-Eform
  let e := 2*(n+2:ℝ)*ε
  let K := (n+2:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+((-1/2:ℝ)+freq/2))+e
  let I := 3*(e^2+(scale⁻¹)^2*(8*(n+2:ℝ)^3*K)+B^2*((n+2:ℝ)+2*K)*(n+2))/g
  let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+scale*(Hb-Vsum)
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  have hs := hover D ((le_max_right _ _).trans hD) (m+1) hm
  have hcorr (i j : Fin (m+1)) : Integrable (fun x => F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x) :=
    localizedLinearOrbital_weighted_integrable freq u F hraw _ _
  have hN := localizedSpin_nuclear_integrable u F hcorr
  have hK := localizedSpin_hubbard_oneBody_error hrho hHp.le hSp.le hf u hη hcoeff F hcorr
    left right t hεM hεG hmatrix hgraph
  have hF : Measurable F := (gridNuclearPotential_measurable index G rho h).sub
    (((slabPotential_continuous hrho hHp.le hSp.le).add (manufacturedWellField_C7 freq scale S u).continuous).measurable)
  have hI (w : Coulomb.H1Vector (n+2)) : nuclearFormIntegrable F w :=
    nuclearFormIntegrable_of_absolute F hF w (fun s i => (hfull w s i).1)
  have hsplit := manufactured_grid_split index hindex G hG hh rho H S freq scale u hmatch
  have hl (w : Coulomb.H1Vector (n+2)) (hw : Coulomb.Antisymmetric w) :
      ((n+2:ℝ)*((-1/2:ℝ)+freq/2)+A/scale-I)*Coulomb.mass w ≤
      nuclearPerturbedForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)) F w+
        scale⁻¹*Coulomb.pairEnergy w :=
    hlower m n D S H scale r ε η ((le_max_left _ _).trans hD) hm hS hH hCH hscale hr hrH hrS hε hη hηδ
      u hsep hcoeff herr hsmall F hF B hB hfull left right t (εM+εG) hN hK hNe w hw g hg hsmallB
  have hlphys := formGroundEnergy_dilated_lower (gridNuclei index hindex G hG hh)
    (manufacturedSlabPotential rho H S freq scale u) F hscale (slabPotential rho H S 0) hsplit hI
    ((n+2:ℝ)*((-1/2:ℝ)+freq/2)+A/scale-I) hl
  have huphys := localized_hubbard_physical_upper hdensity hrho hHp hSp hf hrelation hscale u hsep hs hη hcoeff
    F hN left right t hK hI hNe (gridNuclei index hindex G hG hh) (slabPotential rho H S 0) hsplit
  simp only [Nat.cast_add,Nat.cast_ofNat] at hlphys huphys
  constructor
  · have hid : scale^2*(((n+2:ℝ)*((-1/2:ℝ)+freq/2)+A/scale-I)+(n+2:ℝ)*slabPotential rho H S 0) =
        center-scale*Eform-scale^2*I := by dsimp [center,A]; field_simp [ne_of_gt hscale]; ring
    rw [hid] at hlphys
    exact hlphys
  · have hid : scale^2*(n+2:ℝ)*(((-1/2:ℝ)+freq/2)+slabPotential rho H S 0)+
        scale*(Hb-Vsum+Eform) = center+scale*Eform := by dsimp [center]; ring
    change formGroundEnergy (dilatedNuclei (gridNuclei index hindex G hG hh) scale hscale.ne') (n+2) ≤
      ((scale^2*(n+2:ℝ)*(((-1/2:ℝ)+freq/2)+slabPotential rho H S 0)+
        scale*(Hb-Vsum+Eform):ℝ):EReal) at huphys
    rw [hid] at huphys
    exact huphys

end ContinuumCoulomb

end

end OAI
