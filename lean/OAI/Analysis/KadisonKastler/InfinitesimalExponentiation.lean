import OAI.Analysis.KadisonKastler.SelfAdjointApproximation
import OAI.Analysis.KadisonKastler.UnitaryExponentialBounds
import OAI.Analysis.KadisonKastler.Normalizer

namespace OAI

/-! # Exponentiating the infinitesimal normalizer estimate -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Products of an algebra unitary and a commutant unitary. -/
def separateUnitaryProducts (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {T | ∃ a b : unitary (H →L[ℂ] H), (a : H →L[ℂ] H) ∈ M ∧
    (b : H →L[ℂ] H) ∈ M.commutant ∧ T = (a * b : unitary (H →L[ℂ] H))}

theorem one_mem_separateUnitaryProducts (M : VonNeumannAlgebra H) :
    1 ∈ separateUnitaryProducts M := by
  exact ⟨1, 1, M.one_mem, M.commutant.one_mem, by simp⟩

theorem separateUnitaryProducts_mul (M : VonNeumannAlgebra H)
    {s t : H →L[ℂ] H} (hs : s ∈ separateUnitaryProducts M)
    (ht : t ∈ separateUnitaryProducts M) : s * t ∈ separateUnitaryProducts M := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hs
  obtain ⟨c, d, hc, hd, rfl⟩ := ht
  refine ⟨a * c, b * d, M.mul_mem ha hc, M.commutant.mul_mem hb hd, ?_⟩
  change ((a : H →L[ℂ] H) * b) * ((c : H →L[ℂ] H) * d) =
    ((a : H →L[ℂ] H) * c) * ((b : H →L[ℂ] H) * d)
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb c hc
  calc
    _ = (a : H →L[ℂ] H) * ((b : H →L[ℂ] H) * c) * d := by noncomm_ring
    _ = (a : H →L[ℂ] H) * ((c : H →L[ℂ] H) * b) * d := by rw [← hcomm]
    _ = _ := by noncomm_ring

theorem separateUnitaryProducts_star (M : VonNeumannAlgebra H)
    {s : H →L[ℂ] H} (hs : s ∈ separateUnitaryProducts M) :
    star s ∈ separateUnitaryProducts M := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hs
  refine ⟨star a, star b, star_mem ha, star_mem hb, ?_⟩
  change star ((a : H →L[ℂ] H) * b) = star (a : H →L[ℂ] H) * star (b : H →L[ℂ] H)
  rw [star_mul]
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb a ha
  simpa only [star_mul] using congrArg star hcomm

theorem conjugates_of_mem_separateUnitaryProducts (M : VonNeumannAlgebra H)
    {u : unitary (H →L[ℂ] H)} (hu : (u : H →L[ℂ] H) ∈ separateUnitaryProducts M) :
    Conjugates u M M := by
  obtain ⟨a, b, ha, hb, he⟩ := hu
  have hue : u = a * b := Subtype.ext he
  rw [hue]
  exact conjugates_self_of_separate_factors ha hb

theorem infDist_separateUnitaryProducts_left (M : VonNeumannAlgebra H)
    (p : unitary (H →L[ℂ] H)) (hp : (p : H →L[ℂ] H) ∈ separateUnitaryProducts M)
    (T : H →L[ℂ] H) :
    Metric.infDist (star (p : H →L[ℂ] H) * T) (separateUnitaryProducts M) =
      Metric.infDist T (separateUnitaryProducts M) := by
  let f (x : H →L[ℂ] H) := star (p : H →L[ℂ] H) * x
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro x y
    simp only [dist_eq_norm]
    change ‖star (p : H →L[ℂ] H) * x - star (p : H →L[ℂ] H) * y‖ = ‖x - y‖
    rw [← mul_sub, ← Unitary.coe_star, CStarRing.norm_coe_unitary_mul]
  have himage : f '' separateUnitaryProducts M = separateUnitaryProducts M := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact separateUnitaryProducts_mul M (separateUnitaryProducts_star M hp) hx
    · intro hy
      refine ⟨(p : H →L[ℂ] H) * y, separateUnitaryProducts_mul M hp hy, ?_⟩
      dsimp [f]
      rw [← mul_assoc, Unitary.star_mul_self_of_mem p.property, one_mul]
  simpa only [himage] using Metric.infDist_image (x := T) (t := separateUnitaryProducts M) hf

theorem infDist_unitaryConj_normalizer (M : VonNeumannAlgebra H)
    (p : unitary (H →L[ℂ] H)) (hp : Conjugates p M M) (T : H →L[ℂ] H) :
    Metric.infDist (unitaryConj p T) (M : Set (H →L[ℂ] H)) =
      Metric.infDist T (M : Set (H →L[ℂ] H)) := by
  change unitaryConj p '' (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H)) at hp
  simpa only [hp] using Metric.infDist_image (x := T) (t := (M : Set (H →L[ℂ] H)))
    (isometry_unitaryConj p)

theorem expUnitary_mem_vonNeumann (M : VonNeumannAlgebra H)
    (a : selfAdjoint (H →L[ℂ] H)) (ha : (a : H →L[ℂ] H) ∈ M) :
    (selfAdjoint.expUnitary a : H →L[ℂ] H) ∈ M := by
  let : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  change NormedSpace.exp (Complex.I • (a : H →L[ℂ] H)) ∈ M.toStarSubalgebra
  exact NormedSpace.exp_mem (R := ℂ) (S := StarSubalgebra ℂ (H →L[ℂ] H))
    (s := M.toStarSubalgebra) (isClosed_algebra M) (M.smul_mem ha _)

theorem expUnitary_mem_separateUnitaryProducts (M : VonNeumannAlgebra H)
    (h : selfAdjoint (H →L[ℂ] H))
    (hh : (h : H →L[ℂ] H) ∈ selfAdjointAlgebraCommutantSum M) :
    (selfAdjoint.expUnitary h : H →L[ℂ] H) ∈ separateUnitaryProducts M := by
  obtain ⟨a, b, ha, hb, hsa, hsb, he⟩ := hh
  let sa : selfAdjoint (H →L[ℂ] H) := ⟨a, hsa⟩
  let sb : selfAdjoint (H →L[ℂ] H) := ⟨b, hsb⟩
  have hsum : h = sa + sb := Subtype.ext he
  have hcomm : Commute (sa : H →L[ℂ] H) (sb : H →L[ℂ] H) :=
    VonNeumannAlgebra.mem_commutant_iff.mp hb a ha
  refine ⟨selfAdjoint.expUnitary sa, selfAdjoint.expUnitary sb,
    expUnitary_mem_vonNeumann M sa ha, expUnitary_mem_vonNeumann M.commutant sb hb, ?_⟩
  rw [hsum, hcomm.expUnitary_add]

theorem infDist_expUnitary_le_infDist_selfAdjointSum (M : VonNeumannAlgebra H)
    (h : selfAdjoint (H →L[ℂ] H)) :
    Metric.infDist (selfAdjoint.expUnitary h : H →L[ℂ] H) (separateUnitaryProducts M) ≤
      Metric.infDist (h : H →L[ℂ] H) (selfAdjointAlgebraCommutantSum M) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  obtain ⟨s, hs, hnear⟩ := (Metric.infDist_lt_iff
    (show (selfAdjointAlgebraCommutantSum M).Nonempty from
      ⟨0, selfAdjointAlgebraCommutantSum_zero M⟩)).mp hr
  let k : selfAdjoint (H →L[ℂ] H) := ⟨s, selfAdjoint_of_mem_algebraCommutantSum M hs⟩
  calc
    _ ≤ dist (selfAdjoint.expUnitary h : H →L[ℂ] H) (selfAdjoint.expUnitary k) :=
      Metric.infDist_le_dist_of_mem (expUnitary_mem_separateUnitaryProducts M k hs)
    _ = ‖(selfAdjoint.expUnitary h : H →L[ℂ] H) - selfAdjoint.expUnitary k‖ := dist_eq_norm _ _
    _ ≤ ‖(h : H →L[ℂ] H) - (k : H →L[ℂ] H)‖ := norm_expUnitary_sub_expUnitary_le h k
    _ ≤ r := by simpa only [dist_eq_norm] using hnear.le

end

end KadisonKastler

end OAI
