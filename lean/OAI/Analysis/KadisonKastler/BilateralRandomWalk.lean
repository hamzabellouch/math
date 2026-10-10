import OAI.Analysis.KadisonKastler.RandomWalkIdentityBoundary

namespace OAI

/-! # Independent forward and reflected backward random walks -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

abbrev BilateralWalkPath := ℤ → G

def bilateralWalkLaw : Measure (BilateralWalkPath G) :=
  Measure.infinitePi (fun _ : ℤ => symmetricRandomWalkLaw G)

instance : IsProbabilityMeasure (bilateralWalkLaw G) := by
  unfold bilateralWalkLaw
  infer_instance

def bilateralFuture (ω : BilateralWalkPath G) (n : ℕ) : G := ω (n : ℤ)

def bilateralPast (ω : BilateralWalkPath G) (n : ℕ) : G := ω (-(n : ℤ) - 1)

def bilateralReflectedPast (ω : BilateralWalkPath G) (n : ℕ) : G := (bilateralPast G ω n)⁻¹

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
theorem bilateralFuture_measurable : Measurable (bilateralFuture G) :=
  Measurable.of_eval (fun n => measurable_pi_apply (n : ℤ))

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
theorem bilateralPast_measurable : Measurable (bilateralPast G) :=
  Measurable.of_eval (fun n => measurable_pi_apply (-(n : ℤ) - 1))

theorem bilateralReflectedPast_measurable : Measurable (bilateralReflectedPast G) :=
  Measurable.of_eval (fun n => (measurable_of_countable (Inv.inv : G → G)).comp
    (measurable_pi_apply (-(n : ℤ) - 1)))

theorem bilateralFuture_law : (bilateralWalkLaw G).map (bilateralFuture G) =
    Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G) :=
  Measure.map_infinitePi_infinitePi_of_inj Int.ofNat_injective

theorem bilateralPast_law : (bilateralWalkLaw G).map (bilateralPast G) =
    Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G) := by
  have hi : Function.Injective (fun n : ℕ => -(n : ℤ) - 1) := by
    intro a b hab
    dsimp only at hab
    omega
  exact Measure.map_infinitePi_infinitePi_of_inj hi

theorem bilateralReflectedPast_law : (bilateralWalkLaw G).map (bilateralReflectedPast G) =
    Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G) := by
  let I : (ℕ → G) → (ℕ → G) := fun ω n => (ω n)⁻¹
  have hm : Measurable I := Measurable.of_eval (fun n =>
    (measurable_of_countable (Inv.inv : G → G)).comp (measurable_pi_apply n))
  change (bilateralWalkLaw G).map (I ∘ bilateralPast G) = _
  rw [← Measure.map_map hm (bilateralPast_measurable G), bilateralPast_law]
  simpa only [symmetricRandomWalkLaw_inv] using
    (Measure.infinitePi_map_pi (fun _ : ℕ => symmetricRandomWalkLaw G)
      (fun _ : ℕ => measurable_of_countable (Inv.inv : G → G)))

theorem bilateral_halves_independent :
    IndepFun (bilateralFuture G) (bilateralPast G) (bilateralWalkLaw G) := by
  let m : ℤ → MeasurableSpace (BilateralWalkPath G) := fun n =>
    MeasurableSpace.comap (fun ω => ω n) inferInstance
  have hi : iIndep m (bilateralWalkLaw G) :=
    iIndepFun_infinitePi (X := fun _ (g : G) => g) (fun _ => measurable_id)
  have hm (n : ℤ) : m n ≤ (inferInstance : MeasurableSpace (BilateralWalkPath G)) :=
    (measurable_pi_apply n).comap_le
  have hd : Disjoint {n : ℤ | 0 ≤ n} {n : ℤ | n < 0} := by
    apply Set.disjoint_left.mpr
    intro n hn hp
    change 0 ≤ n at hn
    change n < 0 at hp
    omega
  have hh := indep_iSup_of_disjoint hm hi hd
  have hfuture : MeasurableSpace.comap (bilateralFuture G) inferInstance ≤
      ⨆ n ∈ {n : ℤ | 0 ≤ n}, m n := by
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro n
    exact le_iSup_of_le (n : ℤ) (le_iSup_of_le (Int.natCast_nonneg n) le_rfl)
  have hpast : MeasurableSpace.comap (bilateralPast G) inferInstance ≤
      ⨆ n ∈ {n : ℤ | n < 0}, m n := by
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro n
    exact le_iSup_of_le (-(n : ℤ) - 1) (le_iSup_of_le (by change -(n : ℤ) - 1 < 0; omega) le_rfl)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hh hfuture) hpast

theorem bilateral_reflected_halves_independent :
    IndepFun (bilateralFuture G) (bilateralReflectedPast G) (bilateralWalkLaw G) := by
  exact (bilateral_halves_independent G).comp measurable_id
    (Measurable.of_eval (fun n => (measurable_of_countable (Inv.inv : G → G)).comp
      (measurable_pi_apply n)))

end

end KadisonKastler

end OAI
