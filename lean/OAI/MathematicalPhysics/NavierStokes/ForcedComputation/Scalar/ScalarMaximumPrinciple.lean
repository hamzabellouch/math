import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMaximumCalculus

namespace OAI

/-! The weak maximum principle on the two-torus, proved on a compact
fundamental square. No parabolic existence theorem is used in this argument. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set Filter
open scoped Topology ContDiff

def unitRepresentative (x : Plane) : Plane := fun j => Int.fract (x j)

theorem unitRepresentative_mem (x : Plane) :
    unitRepresentative x ∈ Icc (0 : Plane) (fun _ => 1) := by
  exact ⟨fun j => Int.fract_nonneg _, fun j => (Int.fract_lt_one _).le⟩

theorem periodic_unitRepresentative {f : Plane → ℝ} (hf : ForcedComputation.PlanePeriodic f)
    (x : Plane) : f (unitRepresentative x) = f x := by
  have he : unitRepresentative x = x + fun j => ((-⌊x j⌋ : ℤ) : ℝ) := by
    funext j
    simp [unitRepresentative, Int.fract, sub_eq_add_neg]
  rw [he]
  exact hf _ _

theorem periodic_cylinder_max {w : ℝ → Plane → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ univ))
    (hp : ∀ t ∈ Icc 0 T, ForcedComputation.PlanePeriodic (w t)) :
    ∃ t ∈ Icc 0 T, ∃ x : Plane, ∀ s ∈ Icc 0 T, ∀ y, w s y ≤ w t x := by
  have hK : IsCompact (Icc (0 : ℝ) T ×ˢ Icc (0 : Plane) (fun _ => 1)) :=
    isCompact_Icc.prod isCompact_Icc
  have hne : (Icc (0 : ℝ) T ×ˢ Icc (0 : Plane) (fun _ => 1)).Nonempty :=
    ⟨(0, 0), ⟨⟨le_rfl, hT⟩, ⟨le_rfl, fun _ => zero_le_one⟩⟩⟩
  obtain ⟨p, hpK, hmax⟩ := hK.exists_isMaxOn hne
    (hc.mono (fun _ h => ⟨h.1, mem_univ _⟩))
  refine ⟨p.1, hpK.1, p.2, fun s hs y => ?_⟩
  rw [← periodic_unitRepresentative (hp s hs) y]
  exact hmax (show (s, unitRepresentative y) ∈
    Icc (0 : ℝ) T ×ˢ Icc (0 : Plane) (fun _ => 1) from ⟨hs, unitRepresentative_mem y⟩)

theorem spatialD_sub_const (f : Plane → ℝ) (c : ℝ) (j : Fin 2) :
    spatialD j (fun x => f x - c) = spatialD j f := by
  funext x
  simp only [spatialD, fderiv_sub_const]

theorem scalarGenerator_sub_const (ν : ℝ) (a : Plane → Plane)
    (f : Plane → ℝ) (c : ℝ) (x : Plane) :
    scalarGenerator ν a (fun y => f y - c) x = scalarGenerator ν a f x := by
  simp only [scalarGenerator, scalarLaplacian, spatialD_sub_const, fderiv_sub_const]

theorem timeDerivative_nonneg_at_max {f : ℝ → ℝ} {d t : ℝ} (ht : 0 < t)
    (hm : IsMaxOn f (Icc 0 t) t) (hd : HasDerivWithinAt f d (Icc 0 t) t) : 0 ≤ d := by
  have hv : 0 - t ∈ posTangentConeAt (Icc 0 t) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      (by rw [segment_symm, segment_eq_Icc ht.le])
  have h := hm.isLocalMaxOn.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt hv
  have hmul : d * (0 - t) ≤ 0 := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      mul_comm] using h
  nlinarith

theorem scalar_maximum_principle {w d : ℝ → Plane → ℝ}
    {a : ℝ → Plane → Plane} {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (hc : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ univ))
    (hp : ∀ t ∈ Icc 0 T, ForcedComputation.PlanePeriodic (w t))
    (hs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (w t))
    (hd : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => w s x) (d t x) (Icc 0 T) t)
    (he : ∀ t ∈ Ioc 0 T, ∀ x, d t x ≤ scalarGenerator ν (a t) (w t) x)
    (h₀ : ∀ x, w 0 x ≤ 0) : ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ 0 := by
  intro t ht x
  by_contra! hpos
  let ε := w t x / (2 * (T + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let v : ℝ → Plane → ℝ := fun s y => w s y - ε * s
  have hvc : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ) :=
    hc.sub ((continuous_const.mul continuous_fst).continuousOn)
  have hvp : ∀ s ∈ Icc 0 T, ForcedComputation.PlanePeriodic (v s) := by
    intro s hs y n
    dsimp [v]
    rw [hp s hs y n]
  obtain ⟨s, hsK, y, hmax⟩ := periodic_cylinder_max hT hvc hvp
  have hvtx : 0 < v t x := by
    dsimp [v]
    have hmul : ε * (2 * (T + 1)) = w t x := by
      dsimp [ε]
      exact div_mul_cancel₀ _ (by positivity)
    have htimele := mul_le_mul_of_nonneg_left ht.2 hε.le
    nlinarith
  have hvsy : 0 < v s y := hvtx.trans_le (hmax t ht x)
  have hspos : 0 < s := by
    by_contra hn
    have hz : s = 0 := le_antisymm (le_of_not_gt hn) hsK.1
    subst s
    have h := h₀ y
    dsimp [v] at hvsy
    linarith
  have hst : s ∈ Ioc (0 : ℝ) T := ⟨hspos, hsK.2⟩
  have htime : 0 ≤ d s y - ε := by
    apply timeDerivative_nonneg_at_max hspos
      (fun r hr => hmax r ⟨hr.1, hr.2.trans hsK.2⟩ y)
    simpa only [v, Pi.sub_def, id_eq, mul_one] using
      (((hd s hst y).sub ((hasDerivWithinAt_id s _).const_mul ε)).mono
        (Icc_subset_Icc le_rfl hsK.2))
  have hspace : IsLocalMax (v s) y := Filter.Eventually.of_forall (fun z => hmax s hsK z)
  have hgen := scalarGenerator_nonpos ((hs s hsK).sub contDiff_const) hspace hν (a s)
  rw [scalarGenerator_sub_const] at hgen
  have hle := (he s hst y).trans hgen
  linarith

end ForcedComputation.VelocityDetector

end

end OAI
