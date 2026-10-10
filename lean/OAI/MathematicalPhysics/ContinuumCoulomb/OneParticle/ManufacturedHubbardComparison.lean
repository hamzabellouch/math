import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedHubbardForm
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedNuclearComparison

namespace OAI

/-! The actual Hubbard lower bound passes through the full continuum
complement estimate. The only spectral and domain inputs here are the
explicit published planar, oscillator, and smooth-density propositions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

theorem manufacturedSlab_uniform_hubbard_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    {freq rho : ℝ} (hfreq : 1 ≤ freq) (hrho : 0 ≤ rho) (hrelation : freq^2 = 4*Real.pi*rho) :
    ∃ γ R S₀ δ C : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧ 1 ≤ S₀ ∧ 0 < δ ∧ 1 ≤ C ∧
    ∀ (m n : ℕ) (D S H scale r ε η : ℝ), R ≤ D →
      (m+1:ℕ) ≤ Real.exp ((19/320:ℝ)*D) → S₀ ≤ S → 1 ≤ H → C*S^3 ≤ H →
      0 < scale → 0 < r → r ≤ H/2 → r ≤ S → 0 ≤ ε → 0 ≤ η → η ≤ δ →
      ∀ u : Fin (m+1) → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ η) →
      4*(m+1:ℕ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq η D r u j) ≤ ε^2 →
      (n+1:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 →
      ∀ F : Position → ℝ, Measurable F → ∀ B : ℝ, 0 ≤ B →
      (∀ (z : Coulomb.H1Vector (n+2)) s i,
        Integrable (fun x => |F (Coulomb.position x i)| * ‖z.value s x‖^2) ∧
        (∫ x, |F (Coulomb.position x i)| * ‖z.value s x‖^2) ≤
          B*((∫ x, ‖z.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖z.gradient s (i,k) x‖^2)) →
      ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ) (εK : ℝ),
      (∀ a b, Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
        (star (Coulomb.flatSpinOrbital (localizedSpinMode freq u a) z)*
          Coulomb.flatSpinOrbital (localizedSpinMode freq u b) z)) Coulomb.spinSpaceMeasure) →
      (∀ a b, ‖(scale:ℂ)*(flatResidualMatrix (localizedSpinMode freq u)
          (localizedSpinResidual rho H S freq scale u) a b+
          flatNuclearMatrix (localizedSpinMode freq u) F a b)-
        hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t a b‖ ≤ εK) →
      n+2=m+1 → ∀ w : Coulomb.H1Vector (n+2), Coulomb.Antisymmetric w →
      let A := hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-
        localizedHubbardFormError m freq D εK
      let V : Configuration (n+2) → ℝ := fun x => ∑ i,
        manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
      let E : ℝ := (n+2:ℝ)*((-1/2:ℝ)+freq/2)
      let e : ℝ := 2*(n+2:ℝ)*ε
      let K : ℝ := (n+2:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+e
      let g₀ : ℝ := (γ/8)/(2*((n+2:ℕ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+
        6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1))
      ∀ g : ℝ, 0 < g → B*(n+2)+|A/scale|+g ≤ g₀ →
      (E+A/scale-3*(e^2+(scale⁻¹)^2*(8*(n+2:ℝ)^3*K)+
        B^2*((n+2:ℝ)+2*K)*(n+2))/g)*Coulomb.mass w ≤
        nuclearPerturbedForm V F w+scale⁻¹*Coulomb.pairEnergy w := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  obtain ⟨γ,R,S₀,δ,C,hγ,hγsmall,hR,hS₀,hδ,hC,hbase⟩ :=
    manufacturedSlab_uniform_nuclear_lower hp hv hdensity hfreq hrho hrelation
  obtain ⟨R₂,_hR₂,hover⟩ := localizedOverlap_row_threshold
  refine ⟨γ,max R R₂,S₀,δ,C,hγ,hγsmall,hR.trans (le_max_left _ _),hS₀,hδ,hC,?_⟩
  intro m n D S H scale r ε η hD hm hS hH hCH hscale hr hrH hrS hε hη hηδ
    u hsep hcoeff herr hsmall F hF B hB herror Edge inst left right t εK hN hK hNe w hw
  let A := hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
    left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-
      localizedHubbardFormError m freq D εK
  dsimp only
  intro g hg hsmallB
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one (hS₀.trans hS)
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hs := hover D ((le_max_right _ _).trans hD) (m+1) hm
  let p := finiteTensorProjection (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) w
  have hc : Laughlin.Antisymmetric (Coulomb.orbitalCoefficient w (localizedSpinMode freq u)) := by
    intro i j hij a
    simpa only [Equiv.Perm.sign_swap hij,Units.val_neg,Units.val_one,
      Int.cast_neg,Int.cast_one,neg_one_mul] using
      Coulomb.orbitalCoefficient_antisymmetric hw (localizedSpinMode freq u) (Equiv.swap i j) a
  have hfinite := localizedTensor_hubbard_lower hdensity hrho hHp hSp hf hrelation hscale u hsep hs
    hη hcoeff F hN left right t hK (Coulomb.orbitalCoefficient w (localizedSpinMode freq u))
    hc
    (nuclearFormIntegrable_of_absolute F hF p (fun s i => (herror p s i).1)) hNe
  have hfinite' : ((n+2:ℝ)*((-1/2:ℝ)+freq/2)+A/scale)*Coulomb.mass p ≤
      nuclearPerturbedForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) F p+scale⁻¹*Coulomb.pairEnergy p := by
    apply (mul_le_mul_iff_right₀ hscale).mp
    have hcancel : A/scale*scale=A := div_mul_cancel₀ A (ne_of_gt hscale)
    have he : scale*(((n+2:ℝ)*((-1/2:ℝ)+freq/2)+A/scale)*Coulomb.mass p) =
        (scale*(n+2:ℝ)*((-1/2:ℝ)+freq/2)+A)*Coulomb.mass p := by
      calc
        _ = (scale*(n+2:ℝ)*((-1/2:ℝ)+freq/2)+(A/scale*scale))*Coulomb.mass p := by ring
        _ = _ := by rw [hcancel]
    rw [he]
    dsimp only [A, p, finiteTensorProjection]
    convert hfinite using 1
    ring
  have hncast : ((n:ℝ)+1)+1=(n:ℝ)+2 := by ring
  have hout := hbase m (n+1) D S H scale r ε η ((le_max_left _ _).trans hD)
    hm hS hH hCH hscale.le hr hrH hrS hε hη hηδ u hsep hcoeff herr
    (by simpa only [Nat.cast_add,Nat.cast_one] using hsmall) F hF B hB herror w hw
    (A/scale) g scale⁻¹ hg (inv_nonneg.mpr hscale.le)
    (by simpa only [A,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hncast] using hsmallB)
    (by simpa only [A,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hncast] using hfinite')
  simpa only [A,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hncast] using hout

end ContinuumCoulomb

end

end OAI
