import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularPrimitive

namespace OAI

/-! The normalized regular basis, retaining its C² physical values at the origin. -/

open Set
open scoped BoundedContinuousFunction ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_regular_state_family_c2 (ell d : ℕ) (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) :
    ∃ W : (ℂ × ℂ) → ℂ → ℝ → E₄,
      (∀ c lam, W c lam 0=((c.1,0),(c.2,0)) ∧ Continuous (W c lam)) ∧
      (∀ c lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R,
        HasDerivAt (W c lam)
          (spectralRegularField d (A r) (B r) (cp+Complex.I*lam)
            (cm-Complex.I*lam) r (W c lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → LinearIndependent ℂ ![W (1,0) lam R,W (0,1) lam R]) ∧
      (∀ c z, ‖z‖ ≤ L → ∀ r, 0 ≤ r → AnalyticAt ℂ (fun lam => W c lam r) z) ∧
      (∀ c lam, ContDiff ℝ 2 (fun r => (spectralAngularPair ell (W c lam) r).1.1) ∧
        ContDiff ℝ 2 (fun r => (spectralAngularPair ell (W c lam) r).2.1)) := by
  let α := spectralRegularSourceBound A B cp cm+2*L+1
  have hC := spectralRegularSourceBound_nonneg A B cp cm
  have hα : 0 < α := by dsimp only [α]; linarith
  have hgap (lam : ℂ) (hlam : ‖lam‖ ≤ L) :
      spectralRegularSourceBound A B (cp+Complex.I*lam) (cm-Complex.I*lam)<2*α := by
    have h := spectralRegularSourceBound_parameter A B cp cm lam
    dsimp only [α]
    linarith
  let W := fun c lam => spectralRegularState d α c
    (spectralRegularSolutionSource d R α hR.le hα A B cp cm c lam)
  have hinit (c : ℂ × ℂ) (lam : ℂ) :
      W c lam 0=((c.1,0),(c.2,0)) ∧ Continuous (W c lam) :=
    ⟨spectralRegularState_initial d α c _,spectralRegularState_continuous d α c _⟩
  have hODE (c : ℂ × ℂ) (lam : ℂ) (hlam : ‖lam‖ ≤ L) (r : ℝ) (hr : r ∈ Ioc 0 R) :
      HasDerivAt (W c lam) (spectralRegularField d (A r) (B r)
        (cp+Complex.I*lam) (cm-Complex.I*lam) r (W c lam r)) r :=
    spectralRegularState_hasDerivAt d R α hR.le hα A B _ _ c _ _
      (spectralRegularVector_equation d R α hR.le hα A B cp cm c lam (hgap lam hlam))
      rfl r hr
  refine ⟨W,hinit,hODE,?_,?_,?_⟩
  · intro lam hlam
    exact spectralRegular_at_linearIndependent d A B _ _ (W (1,0) lam) (W (0,1) lam) R hR
      (hinit _ _).2 (hinit _ _).2 (hODE _ _ hlam) (hODE _ _ hlam)
      (hinit _ _).1 (hinit _ _).1
  · intro c z hz r hr
    exact spectralRegularState_analyticAt d α hα c _ z r hr
      (spectralRegularSolutionSource_analyticAt d R α hR.le hα A B cp cm c z (hgap z hz))

  · intro c lam
    exact homogeneousRegularPhysical_contDiff_two ell d α c _

theorem exists_regular_physical_basis_c2 (ell m : ℕ) (νp νm : ℂ)
    (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L) (Q : ℝ → ℂ) (hQ : Continuous Q) :
    ∃ Vp Vm : ℂ → ℝ → E₄,
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R, HasDerivAt (Vp lam)
        (spectralPhysicalCircularField (νp-2*lam) (νm-2*lam)
          ((ell*(ell+10) : ℕ) : ℂ) m (Q r) r (Vp lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R, HasDerivAt (Vm lam)
        (spectralPhysicalCircularField (νp-2*lam) (νm-2*lam)
          ((ell*(ell+10) : ℕ) : ℂ) m (Q r) r (Vm lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → LinearIndependent ℂ ![Vp lam R,Vm lam R]) ∧
      (∀ lam, ContDiff ℝ 2 (fun r => (Vp lam r).1.1) ∧
        ContDiff ℝ 2 (fun r => (Vp lam r).2.1) ∧
        ContDiff ℝ 2 (fun r => (Vm lam r).1.1) ∧
        ContDiff ℝ 2 (fun r => (Vm lam r).2.1)) ∧
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
  obtain ⟨W,hinit,hODE,hrank,ha,hc2⟩ :=
    exists_regular_state_family_c2 ell (2*ell+11) R L hR hL A B cp cm
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
    (fun lam => spectralAngularPair ell (W (0,1) lam)),hphysical (1,0),hphysical (0,1),?_,?_,?_,?_⟩
  · intro lam hlam
    exact spectralAngularPair_rank ell _ _ R hR.ne' (hrank lam hlam)
  · intro lam
    exact ⟨(hc2 (1,0) lam).1,(hc2 (1,0) lam).2,
      (hc2 (0,1) lam).1,(hc2 (0,1) lam).2⟩
  · intro z hz r hr
    exact ⟨spectralAngularPair_analyticAt ell _ z r (ha (1,0) z hz r hr),
      spectralAngularPair_analyticAt ell _ z r (ha (0,1) z hz r hr)⟩
  · exact ⟨W (1,0),W (0,1),
      (fun lam => ⟨(hinit (1,0) lam).2,(hinit (0,1) lam).2,
        (hinit (1,0) lam).1,(hinit (0,1) lam).1⟩),fun _ _ => ⟨rfl,rfl⟩⟩

end DefocusingNLS

end OAI
