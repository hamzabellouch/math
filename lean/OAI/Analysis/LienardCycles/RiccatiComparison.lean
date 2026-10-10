import OAI.Analysis.LienardCycles.Riccati

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuinticLienard.RiccatiJets
open PartialCalculus Riccati

lemma neg_deriv : deriv (fun x : ℝ => -x) = fun _ => -1 :=
  funext (fun x => ((hasDerivAt_id x).neg).deriv)

lemma neg_second_deriv : deriv (deriv (fun x : ℝ => -x)) = fun _ => 0 := by
  rw [neg_deriv]
  exact funext (fun x => (hasDerivAt_const x (-1:ℝ)).deriv)

lemma neg_third_deriv : deriv (deriv (deriv (fun x : ℝ => -x))) = fun _ => 0 := by
  rw [neg_second_deriv]
  exact funext (fun x => (hasDerivAt_const x (0:ℝ)).deriv)

theorem parameter_multiplier {u : ℝ × ℝ → ℝ} {m n d b : ℝ}
    (hm : 0 < m) (hn : 0 < n)
    (hc : Continuous (fun y => u (m,y)))
    (hu : ∀ y ∈ Icc (-m) n, ContDiffAt ℝ ω u (m,y))
    (he : ∀ y ∈ Icc (-m) n, ∀ᶠ q in 𝓝 (m,y),
      HasDerivAt (fun s => u (q.1,s)) (d*u q+b*(u q)^2-q.2) q.2)
    (hroot : ∀ᶠ s in 𝓝 m, u (s,-s)=0) :
    ∀ y ∈ Icc (-m) n, first u (m,y) =
      m/(multiplier (fun s => u (m,s)) b d (-m) y)^2 := by
  let V := multiplier (fun s => u (m,s)) b d (-m)
  have hmn : -m ≤ n := by linarith
  have hmI : -m ∈ Icc (-m) n := ⟨le_rfl,hmn⟩
  have hzi := root_first (hu _ hmI) contDiffAt_id.neg
    (jets_eventually (hu _ hmI) (he _ hmI)).1.self_of_nhds hroot
  have hz0 : first u (m,-m)=m := by
    simpa only [neg_deriv,mul_neg_one,neg_neg] using hzi
  let g : ℝ → ℝ := fun y => (V y)^2*first u (m,y)
  have hgd (y : ℝ) (hy : y ∈ Icc (-m) n) : HasDerivAt g 0 y := by
    have hz := second_hasDerivAt ((first_contDiffAt (hu y hy)).differentiableAt (by simp))
    rw [(jets_eventually (hu y hy) (he y hy)).2.1.self_of_nhds] at hz
    have hd := ((multiplier_deriv hc b d (-m) y).pow 2).mul hz
    convert! hd using 1
    dsimp [V]
    ring
  have hgc : ContinuousOn g (Icc (-m) n) :=
    fun y hy => (hgd y hy).continuousAt.continuousWithinAt
  have hconstant := eq_of_hasDerivAt_eq_on_Icc hgc continuousOn_const hgd
    (fun y _ => hasDerivAt_const y m) hmI (by simp [g,V,hz0])
  intro y hy
  have h := hconstant hy
  change (V y)^2*first u (m,y)=m at h
  exact (eq_div_iff (pow_ne_zero 2 (ne_of_gt (multiplier_pos _ _ _ _ _)))).mpr
    (by simpa [V,mul_comm] using h)

theorem endpoint_formulas {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {m d b : ℝ}
    (hm : 0 < m) (hn : 0 < Y m) (hl : 0 < deriv Y m)
    (hc : Continuous (fun y => u (m,y)))
    (hu : ∀ y ∈ Icc (-m) (Y m), ContDiffAt ℝ ω u (m,y))
    (he : ∀ y ∈ Icc (-m) (Y m), ∀ᶠ q in 𝓝 (m,y),
      HasDerivAt (fun s => u (q.1,s)) (d*u q+b*(u q)^2-q.2) q.2)
    (hY : ContDiffAt ℝ ω Y m)
    (hrootL : ∀ᶠ s in 𝓝 m, u (s,-s)=0)
    (hrootR : ∀ᶠ s in 𝓝 m, u (s,Y s)=0) :
    schwarzian Y m =
      2*b*(m+Y m*(deriv Y m)^2)+(d^2/2)*((deriv Y m)^2-1)
      -d*(1/m+(deriv Y m)^2/Y m)
      +(3/2)*((deriv Y m)^2/(Y m)^2-1/m^2) ∧
    deriv (deriv Y) m/deriv Y m =
      1/m-deriv Y m/Y m+d*(1+deriv Y m)+
      2*b*m*(∫ y in (-m)..(Y m), 1/(multiplier (fun s => u (m,s)) b d (-m) y)^2) ∧
    deriv Y m = m/(Y m*(multiplier (fun s => u (m,s)) b d (-m) (Y m))^2) := by
  let V := multiplier (fun s => u (m,s)) b d (-m)
  have hmn : -m ≤ Y m := by linarith
  have hmI : -m ∈ Icc (-m) (Y m) := ⟨le_rfl,hmn⟩
  have hnI : Y m ∈ Icc (-m) (Y m) := ⟨hmn,le_rfl⟩
  have hz := parameter_multiplier hm hn hc hu he hrootL
  have hzpos (y : ℝ) (hy : y ∈ Icc (-m) (Y m)) : 0 < first u (m,y) := by
    rw [hz y hy]
    exact div_pos hm (sq_pos_of_pos (multiplier_pos _ _ _ _ _))
  have hId (y : ℝ) (hy : y ∈ Icc (-m) (Y m)) :=
    invariant_derivatives (hu y hy) (he y hy) (ne_of_gt (hzpos y hy))
  have hBc : ContinuousOn (fun y => schwarzJet u (m,y)) (Icc (-m) (Y m)) :=
    fun y hy => (hId y hy).2.continuousAt.continuousWithinAt
  have hB := eq_of_hasDerivAt_eq_on_Icc hBc continuousOn_const
    (fun y hy => (hId y hy).2) (fun y _ => hasDerivAt_const y (schwarzJet u (m,-m)))
    hmI rfl hnI
  have hinvL := root_invariants (hu _ hmI) (contDiffAt_id.neg)
    (he _ hmI) hrootL (neg_ne_zero.mpr (ne_of_gt hm))
    (show deriv (fun x : ℝ => -x) m ≠ 0 by rw [neg_deriv]; norm_num)
  have hinvR := root_invariants (hu _ hnI) hY (he _ hnI) hrootR
    (ne_of_gt hn) (ne_of_gt hl)
  have hAL : logJet u (m,-m) = 1/m+d := by
    have h := hinvL.1
    rw [neg_second_deriv,neg_deriv] at h
    dsimp only at h
    convert h using 1
    field_simp
    ring
  have hBL : schwarzJet u (m,-m) = 2*b*m-d^2/2-d/m-3/(2*m^2) := by
    have h := hinvL.2
    dsimp [schwarzian] at h
    rw [neg_third_deriv,neg_second_deriv,neg_deriv] at h
    dsimp only at h
    convert h using 1
    field_simp
    ring
  have hS : schwarzian Y m =
      2*b*(m+Y m*(deriv Y m)^2)+(d^2/2)*((deriv Y m)^2-1)
      -d*(1/m+(deriv Y m)^2/Y m)
      +(3/2)*((deriv Y m)^2/(Y m)^2-1/m^2) := by
    dsimp only at hB
    rw [hinvR.2,hBL] at hB
    field_simp at hB ⊢
    nlinarith
  let f : ℝ → ℝ := fun y => 1/(V y)^2
  have hVc : Continuous V := continuous_iff_continuousAt.mpr
    (fun y => (multiplier_deriv hc b d (-m) y).continuousAt)
  have hfc : Continuous f := continuous_const.div (hVc.pow 2)
    (fun y => pow_ne_zero 2 (ne_of_gt (multiplier_pos _ _ _ _ _)))
  let A : ℝ → ℝ := fun y => logJet u (m,y)-2*b*m*(∫ s in (-m)..y, f s)
  have hAd (y : ℝ) (hy : y ∈ Icc (-m) (Y m)) : HasDerivAt A 0 y := by
    have hd := (hId y hy).1.sub ((hfc.integral_hasStrictDerivAt (-m) y).hasDerivAt.const_mul (2*b*m))
    rw [hz y hy] at hd
    convert! hd using 1
    dsimp [f,V]
    ring
  have hAc : ContinuousOn A (Icc (-m) (Y m)) :=
    fun y hy => (hAd y hy).continuousAt.continuousWithinAt
  have hA := eq_of_hasDerivAt_eq_on_Icc hAc continuousOn_const hAd
    (fun y _ => hasDerivAt_const y (logJet u (m,-m))) hmI
    (by simp [A]) hnI
  have hW : deriv (deriv Y) m/deriv Y m =
      1/m-deriv Y m/Y m+d*(1+deriv Y m)+
      2*b*m*(∫ y in (-m)..Y m,1/(V y)^2) := by
    change logJet u (m,Y m)-2*b*m*(∫ s in (-m)..Y m, f s)=logJet u (m,-m) at hA
    rw [hinvR.1,hAL] at hA
    dsimp [f] at hA
    linarith
  refine ⟨hS,hW,?_⟩
  have hzn := (root_first_eventually (hu _ hnI) hY
    (jets_eventually (hu _ hnI) (he _ hnI)).1 hrootR).self_of_nhds
  dsimp only at hzn
  rw [hz _ hnI] at hzn
  have hvn : V (Y m) ≠ 0 := ne_of_gt (multiplier_pos _ _ _ _ _)
  change deriv Y m = m/(Y m*(V (Y m))^2)
  change m/(V (Y m))^2=Y m*deriv Y m at hzn
  field_simp at hzn ⊢
  nlinarith

end QuinticLienard.RiccatiJets

end OAI
