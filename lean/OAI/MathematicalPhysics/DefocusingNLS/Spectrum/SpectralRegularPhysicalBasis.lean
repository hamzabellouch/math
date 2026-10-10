import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularStateFamily
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAngularRank
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAngularAnalytic

namespace OAI

/-! The regular physical basis for the actual continuous profile on a finite ball. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_regular_physical_basis_normalized (ell m : ℕ) (νp νm : ℂ)
    (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L) (Q : ℝ → ℂ) (hQ : Continuous Q) :
    ∃ Vp Vm : ℂ → ℝ → E₄,
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R, HasDerivAt (Vp lam)
        (spectralPhysicalCircularField (νp-2*lam) (νm-2*lam)
          ((ell*(ell+10) : ℕ) : ℂ) m (Q r) r (Vp lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R, HasDerivAt (Vm lam)
        (spectralPhysicalCircularField (νp-2*lam) (νm-2*lam)
          ((ell*(ell+10) : ℕ) : ℂ) m (Q r) r (Vm lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → LinearIndependent ℂ ![Vp lam R,Vm lam R]) ∧
      (∀ z, ‖z‖ ≤ L → ∀ r, 0 ≤ r → AnalyticAt ℂ (fun lam => Vp lam r) z ∧
        AnalyticAt ℂ (fun lam => Vm lam r) z) ∧
      (∃ Wp Wm : ℂ → ℝ → E₄,
        (∀ lam, Continuous (Wp lam) ∧ Continuous (Wm lam) ∧
          Wp lam 0=((1,0),(0,0)) ∧ Wm lam 0=((0,0),(1,0))) ∧
        (∀ lam r, Vp lam r=spectralAngularPair ell (Wp lam) r ∧
          Vm lam r=spectralAngularPair ell (Wm lam) r)) := by
  let q := spectralClampedProfile R hR.le Q hQ
  let A := spectralRegularDiagonal m q
  let B := spectralRegularCross m q
  let cp := -Complex.I*νp/2+Complex.I*(ell : ℂ)/2
  let cm := Complex.I*νm/2-Complex.I*(ell : ℂ)/2
  obtain ⟨W,hinit,hODE,hrank,ha⟩ :=
    exists_regular_state_family (2*ell+11) R L hR hL A B cp cm
  have hcp (lam : ℂ) : cp+Complex.I*lam=
      -Complex.I*(νp-2*lam)/2+Complex.I*(ell : ℂ)/2 := by dsimp only [cp]; ring
  have hcm (lam : ℂ) : cm-Complex.I*lam=
      Complex.I*(νm-2*lam)/2-Complex.I*(ell : ℂ)/2 := by dsimp only [cm]; ring
  have hphysical (c : ℂ × ℂ) (lam : ℂ) (hlam : ‖lam‖ ≤ L) (r : ℝ) (hr : r ∈ Ioc 0 R) :
      HasDerivAt (spectralAngularPair ell (W c lam))
        (spectralPhysicalCircularField (νp-2*lam) (νm-2*lam)
          ((ell*(ell+10) : ℕ) : ℂ) m (Q r) r (spectralAngularPair ell (W c lam) r)) r := by
    apply spectralRegularPhysical_hasDerivAt ell m _ _ _ _ r hr.1
    have he := hODE c lam hlam r hr
    have hq : q r=Q r := spectralClampedProfile_eq R hR.le Q hQ r ⟨hr.1.le,hr.2⟩
    have hA : A r=spectralDiagonalCoefficient m (Q r) := by
      dsimp only [A]
      rw [spectralRegularDiagonal_apply,hq]
    have hB : B r=spectralCrossCoefficient m (Q r) := by
      dsimp only [B]
      rw [spectralRegularCross_apply,hq]
    rw [hA,hB,hcp,hcm] at he
    exact he
  refine ⟨(fun lam => spectralAngularPair ell (W (1,0) lam)),
    (fun lam => spectralAngularPair ell (W (0,1) lam)),hphysical (1,0),hphysical (0,1),?_,?_,?_⟩
  · intro lam hlam
    exact spectralAngularPair_rank ell _ _ R hR.ne' (hrank lam hlam)
  · intro z hz r hr
    exact ⟨spectralAngularPair_analyticAt ell _ z r (ha (1,0) z hz r hr),
      spectralAngularPair_analyticAt ell _ z r (ha (0,1) z hz r hr)⟩
  · exact ⟨W (1,0),W (0,1),
      (fun lam => ⟨(hinit (1,0) lam).2,(hinit (0,1) lam).2,
        (hinit (1,0) lam).1,(hinit (0,1) lam).1⟩),fun _ _ => ⟨rfl,rfl⟩⟩

theorem exists_regular_physical_basis (ell m : ℕ) (νp νm : ℂ)
    (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L) (Q : ℝ → ℂ) (hQ : Continuous Q) :
    ∃ Vp Vm : ℂ → ℝ → E₄,
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R, HasDerivAt (Vp lam)
        (spectralPhysicalCircularField (νp-2*lam) (νm-2*lam)
          ((ell*(ell+10) : ℕ) : ℂ) m (Q r) r (Vp lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R, HasDerivAt (Vm lam)
        (spectralPhysicalCircularField (νp-2*lam) (νm-2*lam)
          ((ell*(ell+10) : ℕ) : ℂ) m (Q r) r (Vm lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → LinearIndependent ℂ ![Vp lam R,Vm lam R]) ∧
      (∀ z, ‖z‖ ≤ L → ∀ r, 0 ≤ r → AnalyticAt ℂ (fun lam => Vp lam r) z ∧
        AnalyticAt ℂ (fun lam => Vm lam r) z) := by
  obtain ⟨Vp,Vm,hp,hm,hr,ha,_⟩ :=
    exists_regular_physical_basis_normalized ell m νp νm R L hR hL Q hQ
  exact ⟨Vp,Vm,hp,hm,hr,ha⟩

end DefocusingNLS

end OAI
