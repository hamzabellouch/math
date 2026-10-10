import OAI.Analysis.KadisonKastler.BilateralCocycle
import OAI.Analysis.KadisonKastler.FiniteCoordinateL2

namespace OAI

/-! Coordinate measurability and independence for the bilateral product law. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem bilateralCoordinateSigma_independent {I J : Set ℤ} (hIJ : Disjoint I J) :
    Indep (cylinderEvents (X := fun _ : ℤ => G) I)
      (cylinderEvents (X := fun _ : ℤ => G) J) (bilateralWalkLaw G) := by
  let m : ℤ → MeasurableSpace (BilateralWalkPath G) := fun n =>
    MeasurableSpace.comap (fun ω => ω n) inferInstance
  have hi : iIndep m (bilateralWalkLaw G) :=
    iIndepFun_infinitePi (X := fun _ (g : G) => g) (fun _ => measurable_id)
  have hm (n : ℤ) : m n ≤ (inferInstance : MeasurableSpace (BilateralWalkPath G)) :=
    (measurable_pi_apply n).comap_le
  exact indep_iSup_of_disjoint hm hi hIJ

variable {G}

theorem bilateralCoordinate_indepFun {I J : Set ℤ} (hIJ : Disjoint I J)
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {f f' : BilateralWalkPath G → E} {g g' : BilateralWalkPath G → F}
    (hf : Measurable[cylinderEvents (X := fun _ : ℤ => G) I] f')
    (hg : Measurable[cylinderEvents (X := fun _ : ℤ => G) J] g')
    (hff' : f =ᵐ[bilateralWalkLaw G] f') (hgg' : g =ᵐ[bilateralWalkLaw G] g') :
    IndepFun f g (bilateralWalkLaw G) := by
  have hi : IndepFun f' g' (bilateralWalkLaw G) :=
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (bilateralCoordinateSigma_independent G hIJ) hf.comap_le)
      hg.comap_le
  exact hi.congr hff'.symm hgg'.symm

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
theorem bilateralTranslate_coordinate_measurable {I J : Set ℤ} (k : ℤ)
    (hIJ : ∀ j ∈ I, j + k ∈ J) :
    @Measurable (BilateralWalkPath G) (BilateralWalkPath G)
      (cylinderEvents (X := fun _ : ℤ => G) J)
      (cylinderEvents (X := fun _ : ℤ => G) I) (bilateralTranslate G k) := by
  rw [measurable_cylinderEvents_iff]
  intro j hj
  exact measurable_cylinderEvent_apply (hIJ j hj)

theorem bilateralIncrementProduct_coordinate_measurable {I : Set ℤ} (n : ℕ)
    (hI : ∀ j : ℕ, j < n → (j : ℤ) ∈ I) :
    Measurable[cylinderEvents (X := fun _ : ℤ => G) I] (bilateralIncrementProduct G n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun p : G × G => p.1⁻¹ * p.2)).comp
      ((measurable_cylinderEvent_apply (hI n (Nat.lt_succ_self n))).prodMk
        (ih (fun j hj => hI j (hj.trans (Nat.lt_succ_self n)))))

variable {K : Type*} [NormedAddCommGroup K]

theorem bilateralTranslate_coordinate_aestronglyMeasurable {I J : Set ℤ} (k : ℤ)
    (hIJ : ∀ j ∈ I, j + k ∈ J) {f : BilateralWalkPath G → K}
    (hf : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) I] f (bilateralWalkLaw G)) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) J]
      (f ∘ bilateralTranslate G k) (bilateralWalkLaw G) := by
  refine ⟨(hf.mk f) ∘ bilateralTranslate G k, ?_, ?_⟩
  · exact hf.stronglyMeasurable_mk.comp_measurable (bilateralTranslate_coordinate_measurable k hIJ)
  · exact (bilateralTranslate_measurePreserving G k).quasiMeasurePreserving.ae hf.ae_eq_mk

end

end KadisonKastler

end OAI
