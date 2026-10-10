import OAI.Geometry.NodalSets.Elliptic.RealDifferenceQuotientTest

namespace OAI

noncomputable section

namespace Yau

open Set Metric

theorem real_closedBall_subset_cube {n : ℕ} (r : ℝ) :
    closedBall (0 : Coord n) r ⊆ realCenteredCube n r := by
  intro x hx i hi
  have hx' : ‖x‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
  exact abs_le.mp ((norm_le_pi_norm x i).trans hx')

theorem real_closedBall_subset_cube_interior {n : ℕ} {r R : ℝ} (h : r < R) :
    closedBall (0 : Coord n) r ⊆ interior (realCenteredCube n R) := by
  intro x hx
  rw [realCenteredCube,interior_pi_set finite_univ]
  intro i hi
  rw [interior_Icc]
  have hb := (real_closedBall_subset_cube r hx) i hi
  exact ⟨(neg_lt_neg h).trans_le hb.1,hb.2.trans_lt h⟩

open Filter
open scoped Topology

theorem realDifferenceQuotient_mul {n : ℕ} (i : Fin n) (h : ℝ)
    (a u : Coord n → ℝ) (x : Coord n) :
    realDifferenceQuotient i h (fun y ↦ a y*u y) x =
      a (x+Pi.single i h)*realDifferenceQuotient i h u x+
      realDifferenceQuotient i h a x*u x := by
  unfold realDifferenceQuotient
  ring

theorem realDifferenceQuotient_sum {n m : ℕ} (i : Fin n) (h : ℝ)
    (u : Fin m → Coord n → ℝ) (x : Coord n) :
    realDifferenceQuotient i h (fun y ↦ ∑ j, u j y) x =
      ∑ j, realDifferenceQuotient i h (u j) x := by
  simp only [realDifferenceQuotient,mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]

theorem real_coordPartial_eq_zero_of_one {n : ℕ} (eta : Coord n → ℝ) (x : Coord n)
    (he : eta =ᶠ[𝓝 x] (fun _ ↦ 1)) (j : Fin n) : coordPartial eta x j=0 := by
  unfold coordPartial
  rw [he.fderiv_eq]
  simp

theorem real_cutoff_difference_of_one {n : ℕ} (eta u : Coord n → ℝ)
    (i : Fin n) (h : ℝ) (x : Coord n)
    (he : eta =ᶠ[𝓝 x] (fun _ ↦ 1))
    (ht : eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)) :
    realDifferenceQuotient i h (fun y ↦ eta y*u y) x = realDifferenceQuotient i h u x := by
  simp only [realDifferenceQuotient,he.eq_of_nhds,ht.eq_of_nhds,one_mul]

theorem real_cutoff_gradient_difference_of_one {n : ℕ} (eta u U : Coord n → ℝ)
    (i j : Fin n) (h : ℝ) (x : Coord n)
    (he : eta =ᶠ[𝓝 x] (fun _ ↦ 1))
    (ht : eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)) :
    realDifferenceQuotient i h (fun y ↦ eta y*U y+coordPartial eta y j*u y) x =
      realDifferenceQuotient i h U x := by
  simp only [realDifferenceQuotient,he.eq_of_nhds,ht.eq_of_nhds,
    real_coordPartial_eq_zero_of_one eta x he j,
    real_coordPartial_eq_zero_of_one eta _ ht j,one_mul,zero_mul,add_zero]

open MeasureTheory Set
open scoped ContDiff

theorem real_divergence_forcing_difference_equation {n : ℕ}
    (A G : Fin n → Coord n → ℝ) (F : Coord n → ℝ)
    (hA : ∀ j, MemLp (A j) 2 volume) (hG : ∀ j, MemLp (G j) 2 volume)
    (hF : MemLp F 2 volume) (R r : ℝ) (hr : r ≤ R)
    (heq : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∑ j, ∫ x, A j x*coordPartial psi x j) =
        (∫ x, F x*psi x)-(∑ j, ∫ x, G j x*coordPartial psi x j))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r)
    (phi : Coord n → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ realCenteredCube n r) :
    (∀ j, Integrable (fun x ↦ realDifferenceQuotient i h (A j) x*coordPartial phi x j) ∧
      Integrable (fun x ↦ realDifferenceQuotient i h (G j) x*coordPartial phi x j)) ∧
    Integrable (fun x ↦ F x*realDifferenceQuotient i (-h) phi x) ∧
    (∑ j, ∫ x, realDifferenceQuotient i h (A j) x*coordPartial phi x j) =
      -(∫ x, F x*realDifferenceQuotient i (-h) phi x)-
        (∑ j, ∫ x, realDifferenceQuotient i h (G j) x*coordPartial phi x j) := by
  have ht := heq (realDifferenceQuotient i (-h) phi)
    (realDifferenceQuotient_smooth i (-h) phi hp)
    (realDifferenceQuotient_compact i (-h) phi hc)
    (realDifferenceQuotient_tsupport i (-h) phi (realCenteredCube_isCompact n R).isClosed
      (hs.trans (realCenteredCube_mono hr))
      (fun x hx ↦ realCenteredCube_shift i (by simpa only [abs_neg] using hh) (hs hx)))
  have hd (j : Fin n) := real_compact_continuous_memLp _ (real_coordPartial_smooth phi hp j).continuous
    (hc.fderiv_apply ℝ (Pi.single j 1))
  have hda (j : Fin n) := real_differenceQuotient_pairing i h (A j) _ (hA j) (hd j)
  have hdg (j : Fin n) := real_differenceQuotient_pairing i h (G j) _ (hG j) (hd j)
  have hi : Integrable (fun x ↦ F x*realDifferenceQuotient i (-h) phi x) :=
    hF.integrable_mul (realDifferenceQuotient_memLp i (-h) phi
      (real_compact_continuous_memLp phi hp.continuous hc))
  refine ⟨fun j ↦ ⟨(hda j).1,(hdg j).1⟩,hi,?_⟩
  simp only [realDifferenceQuotient_partial i _ (-h) phi hp] at ht
  simp only [(hda _).2.2,(hdg _).2.2,Finset.sum_neg_distrib]
  linarith only [ht]

theorem real_ae_translation_endpoints {n : ℕ} {S : Set (Coord n)}
    (hS : MeasurableSet S) (P : Coord n → Prop)
    (hP : ∀ᵐ x ∂volume.restrict S, P x) (v : Coord n) :
    ∀ᵐ x ∂volume, (x ∈ S → P x) ∧ (x+v ∈ S → P (x+v)) := by
  have hbase : ∀ᵐ x ∂volume, x ∈ S → P x := (ae_restrict_iff' hS).mp hP
  have hshift := (measurePreserving_add_right (G := Coord n) volume v).quasiMeasurePreserving.ae hbase
  filter_upwards [hbase,hshift] with x hx hy
  exact ⟨hx,hy⟩

theorem realCenteredCube_subset_interior {n : ℕ} {r R : ℝ} (hr : r < R) :
    realCenteredCube n r ⊆ interior (realCenteredCube n R) := by
  let U : Set (Coord n) := univ.pi (fun _ ↦ Ioo (-R) R)
  have ho : IsOpen U := isOpen_set_pi finite_univ (fun _ _ ↦ isOpen_Ioo)
  have hi : U ⊆ realCenteredCube n R := by
    intro x hx j hj
    exact ⟨(hx j hj).1.le,(hx j hj).2.le⟩
  intro x hx
  apply (interior_maximal hi ho)
  intro j hj
  exact ⟨lt_of_lt_of_le (neg_lt_neg hr) (hx j hj).1,lt_of_le_of_lt (hx j hj).2 hr⟩

theorem real_local_difference_weak_derivative {n : ℕ} (u g : Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) (R r : ℝ) (hr : r ≤ R)
    (j : Fin n)
    (hw : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∫ x, u x*coordPartial psi x j)=-(∫ x, g x*psi x))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r)
    (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆ realCenteredCube n r) :
    (∫ x, realDifferenceQuotient i h u x*coordPartial psi x j) =
      -(∫ x, realDifferenceQuotient i h g x*psi x) := by
  have hd := real_compact_continuous_memLp _ (real_coordPartial_smooth psi hp j).continuous
    (hc.fderiv_apply ℝ (Pi.single j 1))
  have hv := real_compact_continuous_memLp psi hp.continuous hc
  have ht := hw (realDifferenceQuotient i (-h) psi)
    (realDifferenceQuotient_smooth i (-h) psi hp)
    (realDifferenceQuotient_compact i (-h) psi hc)
    (realDifferenceQuotient_tsupport i (-h) psi (realCenteredCube_isCompact n R).isClosed
      (hs.trans (realCenteredCube_mono hr))
      (fun x hx ↦ realCenteredCube_shift i (by simpa only [abs_neg] using hh) (hs hx)))
  simp only [realDifferenceQuotient_partial i j (-h) psi hp] at ht
  rw [(real_differenceQuotient_pairing i h u _ hu hd).2.2,
    (real_differenceQuotient_pairing i h g psi hg hv).2.2]
  linarith only [ht]

end Yau

end

end OAI
