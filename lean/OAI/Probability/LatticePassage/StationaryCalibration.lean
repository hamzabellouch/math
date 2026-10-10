import OAI.Probability.LatticePassage.WeakCalibration
import OAI.Probability.LatticePassage.LocalCovariance

namespace OAI

namespace CompanionFPP
open MeasureTheory Filter Topology

lemma environmentTranslation_zero (ω : Environment) : environmentTranslation 0 ω = ω := by
  funext e
  unfold environmentTranslation
  congr 1
  apply Subtype.ext
  change Sym2.map (fun x : Vertex => 0+x) e.val = e.val
  simp

lemma translationL2_zero (f : CalibrationL2) : translationL2 0 f = f := by
  apply Lp.ext
  filter_upwards [coe_translationL2 0 f] with ω hω
  simpa only [environmentTranslation_zero] using hω

lemma translationL2_add (a b : Vertex) (f : CalibrationL2) :
    translationL2 (a+b) f = translationL2 a (translationL2 b f) := by
  apply Lp.ext
  have hc := (environmentTranslation_preserving a).quasiMeasurePreserving.ae (coe_translationL2 b f)
  filter_upwards [coe_translationL2 (a+b) f, coe_translationL2 a (translationL2 b f), hc]
    with ω h₁ h₂ h₃
  rw [h₁,h₂,h₃,environmentTranslation_add]

lemma translationL2_injective (a : Vertex) : Function.Injective (translationL2 a) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (E := ℝ) (p := 2) (environmentTranslation a)
    (environmentTranslation_preserving a)).injective

noncomputable def calibrationCovarianceSubgroup (B : Vertex → Vertex → CalibrationL2) :
    AddSubgroup Vertex where
  carrier := {a | ∀ x y, translationL2 a (B x y) = B (a+x) (a+y)}
  zero_mem' := by intro x y; simp only [translationL2_zero, zero_add]
  add_mem' := by
    intro a b ha hb x y
    rw [translationL2_add, hb, ha]
    simp only [add_assoc]
  neg_mem' := by
    intro a ha x y
    apply translationL2_injective a
    rw [← translationL2_add, add_neg_cancel, translationL2_zero, ha]
    simp only [add_neg_cancel_left]

lemma covariance_of_generators (B : Vertex → Vertex → CalibrationL2)
    (h₁ : ∀ x y, translationL2 (1,0) (B x y) = B ((1,0)+x) ((1,0)+y))
    (h₂ : ∀ x y, translationL2 (0,1) (B x y) = B ((0,1)+x) ((0,1)+y)) :
    ∀ a x y, translationL2 a (B x y) = B (a+x) (a+y) := by
  intro a
  have hmem : a ∈ calibrationCovarianceSubgroup B := by
    have he : a = a.1 • ((1,0) : Vertex) + a.2 • ((0,1) : Vertex) := by ext <;> simp
    rw [he]
    exact (calibrationCovarianceSubgroup B).add_mem
      ((calibrationCovarianceSubgroup B).zsmul_mem h₁ a.1)
      ((calibrationCovarianceSubgroup B).zsmul_mem h₂ a.2)
  exact hmem

structure DirectionalCalibration (d : Vertex) where
  value : Environment → Vertex → Vertex → ℝ
  measurable : ∀ x y, Measurable (fun ω => value ω x y)
  memLp : ∀ x y, MemLp (fun ω => value ω x y) 2 environmentLaw
  dominated : ∀ᵐ ω ∂environmentLaw, ∀ x y, |value ω x y| ≤ passageTime ω x y
  additive : ∀ᵐ ω ∂environmentLaw, ∀ x y z, value ω x z = value ω x y+value ω y z
  covariant : ∀ᵐ ω ∂environmentLaw, ∀ a x y,
    value (environmentTranslation a ω) x y = value ω (a+x) (a+y)
  directional_mean : (∫ ω, value ω 0 d ∂environmentLaw) = directionalMeanConstant d

theorem exists_directionalCalibration (d : Vertex) : Nonempty (DirectionalCalibration d) := by
  obtain ⟨B,hdom,hadd,hmean,h₁,h₂⟩ := exists_directional_calibrationL2 d (1,0) (0,1)
  have hcov := covariance_of_generators B h₁ h₂
  refine ⟨{ value := fun ω x y => B x y ω
            measurable := fun x y => (Lp.stronglyMeasurable (B x y)).measurable
            memLp := fun x y => Lp.memLp (B x y)
            dominated := ?_
            additive := ?_
            covariant := ?_
            directional_mean := ?_ }⟩
  · apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    have hlow := (Lp.coeFn_le _ _).mpr (hdom x y).1
    have hupp := (Lp.coeFn_le _ _).mpr (hdom x y).2
    filter_upwards [hlow,hupp,coe_passageL2 x y,Lp.coeFn_neg (passageL2 x y)]
      with ω hl hu hp hn
    apply abs_le.mpr
    rw [hn,Pi.neg_apply,hp] at hl
    rw [hp] at hu
    exact ⟨hl,hu⟩
  · apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    apply ae_all_iff.mpr
    intro z
    have h := Lp.coeFn_add (B x y) (B y z)
    rw [← hadd] at h
    exact h
  · apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    have h := coe_translationL2 a (B x y)
    rw [hcov] at h
    exact h.symm
  · rwa [meanL2_eq_integral] at hmean

end CompanionFPP

end OAI
