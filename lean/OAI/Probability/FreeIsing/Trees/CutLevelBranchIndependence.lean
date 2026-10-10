import OAI.Probability.FreeIsing.Trees.BroadcastConeLocality
import OAI.Probability.FreeIsing.Trees.FreeIsingBranchFamily
import OAI.Probability.FreeIsing.Trees.Shells

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

local instance (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  infer_instance

theorem strictDescendant_length_gt {d n : ℕ} (c : TreeShell d n)
    (v : StrictDescendantVertex c.1) : n < v.1.1.length := by
  have hle := v.2.1.length_le
  have hne : c.1.1.length ≠ v.1.1.length := by
    intro h
    exact v.2.2 (Subtype.ext (v.2.1.eq_of_length h).symm)
  rw [c.2] at hle hne
  omega

theorem cutLevel_descendants_disjoint {d n : ℕ} :
    Pairwise (fun c e : TreeShell d n =>
      Disjoint {v : TreeVertex d | c.1.1 <+: v.1}
        {v : TreeVertex d | e.1.1 <+: v.1}) := by
  intro c e hce
  apply Set.disjoint_left.mpr
  intro v hc he
  have hpre : c.1.1 <+: e.1.1 :=
    List.prefix_of_prefix_length_le hc he (by simp only [c.2, e.2, le_refl])
  exact hce (Subtype.ext (Subtype.ext (hpre.eq_of_length (c.2.trans e.2.symm))))

theorem cutLevel_strictDescendants_disjoint {d n : ℕ} :
    Pairwise (fun c e : TreeShell d n =>
      Disjoint {v : TreeVertex d | c.1.1 <+: v.1 ∧ v ≠ c.1}
        {v : TreeVertex d | e.1.1 <+: v.1 ∧ v ≠ e.1}) := by
  intro c e hce
  exact (cutLevel_descendants_disjoint hce).mono
    (fun _ h => h.1) (fun _ h => h.1)

def cutUpperExtension {d n : ℕ} (U : TreeBall d n → ℝ) : TreeVertex d → ℝ :=
  fun v => if hv : v.1.length ≤ n then U ⟨v, hv⟩ else 0

theorem measurable_cutUpperExtension (d n : ℕ) :
    Measurable (@cutUpperExtension d n) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v.1.length ≤ n
  · simpa only [cutUpperExtension, dite_eq_left hv] using
      (measurable_pi_apply (X := fun _ : TreeBall d n => ℝ) ⟨v, hv⟩)
  · simpa only [cutUpperExtension, dite_eq_right hv] using
      (measurable_const : Measurable (fun _ : TreeBall d n → ℝ => (0 : ℝ)))

def cutSpins {d : ℕ} (theta : ℝ) (n : ℕ)
    (U : TreeVertex d → ℝ) : TreeShell d n → IsingSpin :=
  fun c => factor theta U c.1

theorem measurable_cutSpins (d : ℕ) (theta : ℝ) (n : ℕ) :
    Measurable (@cutSpins d theta n) := by
  exact Measurable.of_eval (fun vertex =>
    (measurable_pi_apply vertex.1).comp (measurable_factor d theta))

theorem cutSpins_upper_extension {d : ℕ} (theta : ℝ) (n : ℕ)
    (U : TreeVertex d → ℝ) :
    cutSpins theta n (cutUpperExtension (fun v : TreeBall d n => U v.1)) =
      cutSpins theta n U := by
  funext c
  apply factor_congr_prefix
  intro w hw
  have hlen : w.1.length ≤ n := hw.length_le.trans_eq c.2
  simp only [cutUpperExtension, dite_eq_left hlen]

def cutLabels {d n : ℕ} (U : TreeVertex d → ℝ) :
    (c : TreeShell d n) → StrictDescendantVertex c.1 → ℝ :=
  fun _ v => U v.1

theorem measurable_cutLabels (d n : ℕ) : Measurable (@cutLabels d n) := by
  unfold cutLabels
  fun_prop

theorem indepFun_cutSpins_cutLabels (d : ℕ) (theta : ℝ) (n : ℕ) :
    IndepFun (cutSpins theta n) (@cutLabels d n) (labelMeasure d) := by
  let F : (TreeBall d n → ℝ) → (TreeShell d n → IsingSpin) :=
    fun U => cutSpins theta n (cutUpperExtension U)
  let G : ({v : TreeVertex d // n < v.1.length} → ℝ) →
      ((c : TreeShell d n) → StrictDescendantVertex c.1 → ℝ) :=
    fun U c v => U ⟨v.1, strictDescendant_length_gt c v⟩
  have hF : Measurable F :=
    (measurable_cutSpins d theta n).comp (measurable_cutUpperExtension d n)
  have hG : Measurable G := by fun_prop
  have hdisj : Disjoint {v : TreeVertex d | v.1.length ≤ n}
      {v : TreeVertex d | n < v.1.length} := by
    apply Set.disjoint_left.mpr
    intro v hle hlt
    exact (not_lt_of_ge (show v.1.length ≤ n from hle))
      (show n < v.1.length from hlt)
  have h := indepFun_infinitePi_disjoint_blocks (fun _ : TreeVertex d => uniform01)
    {v : TreeVertex d | v.1.length ≤ n} {v : TreeVertex d | n < v.1.length}
    hdisj F G hF hG
  have heq : (fun U : TreeVertex d → ℝ => F (fun v : TreeBall d n => U v.1)) =
      cutSpins theta n := by
    funext U
    exact cutSpins_upper_extension theta n U
  change IndepFun (fun U => F (fun v : TreeBall d n => U v.1))
    (@cutLabels d n) (labelMeasure d) at h
  rw [heq] at h
  exact h

theorem map_cutSpins_cutLabels (d : ℕ) (theta : ℝ) (n : ℕ) :
    (labelMeasure d).map (fun U => (cutSpins theta n U, cutLabels U)) =
      ((labelMeasure d).map (cutSpins theta n)).prod
        (Measure.infinitePi (fun c : TreeShell d n =>
          Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01))) := by
  rw [(indepFun_cutSpins_cutLabels d theta n).map_prod_eq_prod_map_map
    (measurable_cutSpins d theta n).aemeasurable (measurable_cutLabels d n).aemeasurable]
  congr 1
  exact infinitePi_map_disjoint_family (fun _ : TreeVertex d => uniform01)
    (fun c : TreeShell d n => {v : TreeVertex d | c.1.1 <+: v.1 ∧ v ≠ c.1})
    cutLevel_strictDescendants_disjoint

theorem iCondIndepFun_factor_cutLevel (d : ℕ) (theta : ℝ) (n : ℕ) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (cutSpins theta n)) (measurable_cutSpins d theta n).comap_le
      (fun (c : TreeShell d n) (U : TreeVertex d → ℝ) =>
        fun v : DescendantVertex c.1 => factor theta U v.1)
      (labelMeasure d) := by
  let S := TreeShell d n → IsingSpin
  let A := (c : TreeShell d n) → StrictDescendantVertex c.1 → ℝ
  let rho := (labelMeasure d).map (cutSpins theta n)
  let nu := Measure.infinitePi (fun c : TreeShell d n =>
    Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01))
  let e : (TreeVertex d → ℝ) → S × A :=
    fun U => (cutSpins theta n U, cutLabels U)
  have he : MeasurePreserving e (labelMeasure d) (rho.prod nu) :=
    ⟨(measurable_cutSpins d theta n).prodMk (measurable_cutLabels d n),
      map_cutSpins_cutLabels d theta n⟩
  let F := fun (c : TreeShell d n) (p : S × (StrictDescendantVertex c.1 → ℝ)) =>
    coneFactor theta c.1 (p.1 c, p.2)
  have hF : ∀ c, Measurable (F c) := by
    intro c
    exact (measurable_coneFactor theta c.1).comp
      (((measurable_pi_apply c).comp measurable_fst).prodMk measurable_snd)
  have hbase := iCondIndepFun_latent_infinitePi rho
    (fun c : TreeShell d n => Measure.infinitePi
      (fun _ : StrictDescendantVertex c.1 => uniform01)) F hF
  have hpull := iCondIndepFun_comp_measurePreserving (labelMeasure d) (rho.prod nu)
    e he ((inferInstance : MeasurableSpace S).comap Prod.fst) measurable_fst.comap_le
    (fun c => show Measurable (fun p : S × A => F c (p.1, p.2 c)) from
      (hF c).comp (measurable_fst.prodMk
        ((measurable_pi_apply c).comp measurable_snd))) hbase
  have hfun : (fun c => (fun p : S × A => F c (p.1, p.2 c)) ∘ e) =
      (fun (c : TreeShell d n) (U : TreeVertex d → ℝ) =>
        fun v : DescendantVertex c.1 => factor theta U v.1) := by
    funext c U
    exact (factor_cone_representation theta c.1 U).symm
  rw [hfun] at hpull
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e] using hpull

end Problem367.RootedBroadcast

namespace Problem367

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem freeIsingMeasure_iCondIndepFun_cutLevel (d : ℕ) (theta : ℝ) (n : ℕ) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun x : TreeVertex d → IsingSpin => fun c : TreeShell d n => x c.1))
      (by fun_prop : Measurable
        (fun x : TreeVertex d → IsingSpin => fun c : TreeShell d n => x c.1)).comap_le
      (fun (c : TreeShell d n) (x : TreeVertex d → IsingSpin) =>
        fun v : RootedBroadcast.DescendantVertex c.1 => x v.1)
      (freeIsingMeasure d theta) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  have he : MeasurePreserving (RootedBroadcast.factor theta)
      (labelMeasure d) (freeIsingMeasure d theta) :=
    ⟨RootedBroadcast.measurable_factor d theta, rfl⟩
  apply iCondIndepFun_of_comp_measurePreserving (labelMeasure d)
    (freeIsingMeasure d theta) (RootedBroadcast.factor theta) he
    ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
      (fun x : TreeVertex d → IsingSpin => fun c : TreeShell d n => x c.1))
    (by fun_prop : Measurable
      (fun x : TreeVertex d → IsingSpin => fun c : TreeShell d n => x c.1)).comap_le
    (fun _ => by fun_prop)
  simp only [MeasurableSpace.comap_comp, Function.comp_def]
  exact RootedBroadcast.iCondIndepFun_factor_cutLevel d theta n

theorem HasFreeIsingLaw.iCondIndepFun_cutLevel {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun x : TreeVertex d → IsingSpin => fun c : TreeShell d n => x c.1))
      (by fun_prop : Measurable
        (fun x : TreeVertex d → IsingSpin => fun c : TreeShell d n => x c.1)).comap_le
      (fun (c : TreeShell d n) (x : TreeVertex d → IsingSpin) =>
        fun v : RootedBroadcast.DescendantVertex c.1 => x v.1) μ := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_iCondIndepFun_cutLevel d theta n

end Problem367

end

end OAI
