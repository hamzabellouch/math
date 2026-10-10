import OAI.Geometry.IsometricImmersion.Curvature.CurvatureParameterJets
import OAI.Geometry.IsometricImmersion.Calculus.JointDerivative

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

theorem contDiffOn_succ_of_continuous_partials
    {s : Set (ℝ × ℝ)} (hs : IsOpen s) {f fx fy : (ℝ × ℝ) → ℝ} (n : ℕ)
    (hfx : ContDiffOn ℝ n fx s) (hfy : ContDiffOn ℝ n fy s)
    (hdx : ∀ p ∈ s, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hdy : ∀ p ∈ s, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2) :
    ContDiffOn ℝ (n + 1 : ℕ) f s := by
  have hd (p : ℝ × ℝ) (hp : p ∈ s) :
      HasFDerivAt f (jointDifferential (fx p) (fy p)) p :=
    hasFDerivAt_of_continuous_partials hs hfx.continuousOn hfy.continuousOn hdx hdy hp
  have hnext : ContDiffOn ℝ ((n : ℕ∞ω) + 1) f s := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hfield : ContDiffOn ℝ n (fun p => jointDifferential (fx p) (fy p)) s :=
      (contDiffOn_const.smulRight hfx).add (contDiffOn_const.smulRight hfy)
    exact hfield.congr (fun p hp => (hd p hp).fderiv)
  simpa only [Nat.cast_add, Nat.cast_one] using hnext

theorem volterra_family_joint_smooth
    (r : ℝ) (hr : 0 < r) {s : Set ℝ} (hs : IsOpen s)
    {K F P : ℝ → IntervalFunctions r}
    (hK : ContDiffOn ℝ ∞ K s) (hF : ContDiffOn ℝ ∞ F s)
    (hP : ContDiffOn ℝ ∞ P s)
    (hKjets : ∀ j, ContDiffOn ℝ ∞ (intervalFamilyJet r hr K j) (Ioo (-r) r ×ˢ s))
    (c : ℝ)
    (hFP : ∀ y ∈ s,
      F y = ContinuousMap.const (Icc (-r) r) c + primitiveCLM r hr (P y))
    (hPQ : ∀ y ∈ s, P y = primitiveCLM r hr (-(K y * F y))) :
    ∀ j, ContDiffOn ℝ ∞ (intervalFamilyJet r hr F j) (Ioo (-r) r ×ˢ s) ∧
      ContDiffOn ℝ ∞ (intervalFamilyJet r hr P j) (Ioo (-r) r ×ˢ s) := by
  let D : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ s
  let Q : ℝ → IntervalFunctions r := fun y => -(K y * F y)
  have hD : IsOpen D := isOpen_Ioo.prod hs
  have hQ : ContDiffOn ℝ ∞ Q s := (hK.mul hF).neg
  have hdxF (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => intervalFamilyJet r hr F j (x, p.2))
        (intervalFamilyJet r hr P j p) p.1 :=
    intervalFamilyJet_hasDerivAt_x_of_primitive r hr hs hP c hFP j hp.1 hp.2
  have hdxP (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => intervalFamilyJet r hr P j (x, p.2))
        (intervalFamilyJet r hr Q j p) p.1 := by
    apply intervalFamilyJet_hasDerivAt_x_of_primitive r hr hs hQ 0 _ j hp.1 hp.2
    intro y hy
    change P y = 0 + primitiveCLM r hr (Q y)
    rw [zero_add]
    exact hPQ y hy
  have hdyF (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => intervalFamilyJet r hr F j (p.1, y))
        (intervalFamilyJet r hr F (j + 1) p) p.2 :=
    intervalFamilyJet_hasDerivAt_y r hr hs hF j p.1 hp.2
  have hdyP (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => intervalFamilyJet r hr P j (p.1, y))
        (intervalFamilyJet r hr P (j + 1) p) p.2 :=
    intervalFamilyJet_hasDerivAt_y r hr hs hP j p.1 hp.2
  have hnat : ∀ n : ℕ, ∀ j,
      ContDiffOn ℝ n (intervalFamilyJet r hr F j) D ∧
      ContDiffOn ℝ n (intervalFamilyJet r hr P j) D := by
    intro n
    induction n with
    | zero =>
        intro j
        constructor
        · simpa only [Nat.cast_zero, contDiffOn_zero] using
            (intervalFamilyJet_continuousOn r hr hs hF j).mono
              (fun p hp => ⟨mem_univ p.1, hp.2⟩)
        · simpa only [Nat.cast_zero, contDiffOn_zero] using
            (intervalFamilyJet_continuousOn r hr hs hP j).mono
              (fun p hp => ⟨mem_univ p.1, hp.2⟩)
    | succ n hn =>
        intro j
        have hQj : ContDiffOn ℝ n (intervalFamilyJet r hr Q j) D := by
          have hsum : ContDiffOn ℝ n (fun p =>
              ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
                intervalFamilyJet r hr K i p * intervalFamilyJet r hr F (j - i) p) D :=
            ContDiffOn.sum (fun i hi =>
              (contDiffOn_const.mul (contDiffOn_infty.mp (hKjets i) n)).mul (hn (j - i)).1)
          apply hsum.neg.congr
          intro p hp
          have hneg : intervalFamilyJet r hr Q j p =
              -intervalFamilyJet r hr (fun y => K y * F y) j p := by
            simp only [intervalFamilyJet, Q, iteratedDeriv_fun_neg]
            rfl
          rw [hneg, intervalFamilyJet_mul r hr hs hK hF j p.1 hp.2]
        exact ⟨contDiffOn_succ_of_continuous_partials hD n (hn j).2 (hn (j + 1)).1
            (hdxF j) (hdyF j),
          contDiffOn_succ_of_continuous_partials hD n hQj (hn (j + 1)).2
            (hdxP j) (hdyP j)⟩
  intro j
  exact ⟨contDiffOn_infty.mpr (fun n => (hnat n j).1),
    contDiffOn_infty.mpr (fun n => (hnat n j).2)⟩

def prescribedVelocityFamily (K : SmoothLocal.Geometry.Coord → ℝ)
    (r : ℝ) (hr : 0 < r) (y : ℝ) : IntervalFunctions r :=
  primitiveCLM r hr (-(coordinateCurvatureFamily K r y * prescribedVolterraFamily K r hr y))

theorem prescribedVolterraFamily_joint_contDiffOn
    {K : SmoothLocal.Geometry.Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K SmoothLocal.Geometry.square)
    (hbound : ∀ p ∈ SmoothLocal.Geometry.square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      intervalExtension r hr (prescribedVolterraFamily K r hr p.2) p.1)
      (Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1) := by
  have hKB := coordinateCurvatureFamily_contDiffOn hK r hr1
  have hFB := prescribedVolterraFamily_contDiffOn hK hbound r hr hr1
  have hPB : ContDiffOn ℝ ∞ (prescribedVelocityFamily K r hr) (Ioo (-1 : ℝ) 1) :=
    contDiffOn_const.clm_apply (hKB.mul hFB).neg
  have hFP : ∀ y ∈ Ioo (-1 : ℝ) 1, prescribedVolterraFamily K r hr y =
      ContinuousMap.const (Icc (-r) r) 1 +
        primitiveCLM r hr (prescribedVelocityFamily K r hr y) := by
    intro y hy
    have he := prescribedVolterraFamily_equation hK hbound r hr hr1 hy
    change prescribedVolterraFamily K r hr y +
      primitiveCLM r hr (primitiveCLM r hr
        (coordinateCurvatureFamily K r y * prescribedVolterraFamily K r hr y)) = 1 at he
    change prescribedVolterraFamily K r hr y = 1 +
      primitiveCLM r hr (prescribedVelocityFamily K r hr y)
    simpa only [prescribedVelocityFamily, map_neg, sub_eq_add_neg] using eq_sub_of_add_eq he
  have hj := volterra_family_joint_smooth r hr isOpen_Ioo hKB hFB hPB
    (coordinateCurvatureFamily_jet_contDiffOn hK r hr hr1) 1 hFP
    (fun y hy => rfl) 0
  apply hj.1.congr
  intro p hp
  simp only [intervalFamilyJet, iteratedDeriv_zero]

end SmoothLocal.ODE

end

end OAI
