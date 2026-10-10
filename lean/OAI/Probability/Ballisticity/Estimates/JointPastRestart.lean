import Mathlib
import OAI.Probability.Ballisticity.Estimates.CommonBoundaryRestart

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def BoundaryData (d : ℕ) := Σ q : ℕ × ℕ,
  (((i : Finset.Iic q.1) → Lattice d) × ((i : Finset.Iic q.2) → Lattice d))

instance {d : ℕ} : Countable (BoundaryData d) := by unfold BoundaryData; infer_instance
instance {d : ℕ} : MeasurableSpace (BoundaryData d) := ⊤
instance {d : ℕ} : DiscreteMeasurableSpace (BoundaryData d) := ⟨fun _ => trivial⟩

noncomputable def boundaryData {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) :
    BoundaryData d := ⟨boundaryTimes ℓ H P,
      pairPrefix (boundaryTimes ℓ H P).1 (boundaryTimes ℓ H P).2 P⟩

lemma boundaryData_fiber {d : ℕ} (ℓ : Vector d) (H : ℝ) (F : BoundaryData d) :
    boundaryData ℓ H ⁻¹' {F} =
      (boundaryTimes ℓ H ⁻¹' {F.1}) ∩ (pairPrefix F.1.1 F.1.2 ⁻¹' {F.2}) := by
  ext P
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_inter_iff]
  constructor
  · intro he
    have ht : boundaryTimes ℓ H P = F.1 := congrArg Sigma.fst he
    refine ⟨ht,?_⟩
    cases F with
    | mk q f =>
      dsimp only at ht ⊢
      unfold boundaryData at he
      cases ht
      exact Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq
  · rintro ⟨ht,hf⟩
    cases F with
    | mk q f =>
      dsimp only at ht hf ⊢
      unfold boundaryData
      cases ht
      exact congrArg (Sigma.mk _) hf

lemma measurable_boundaryData {d : ℕ} (ℓ : Vector d) (H : ℝ) :
    Measurable (boundaryData ℓ H) := by
  apply measurable_to_countable'
  intro F
  rw [boundaryData_fiber]
  exact ((measurable_boundaryTimes ℓ H) (measurableSet_singleton _)).inter
    ((measurable_pairPrefix _ _) (measurableSet_singleton _))

noncomputable def boundarySuffix {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) :
    Path d × Path d := commonPairSuffix (boundaryTimes ℓ H P).1 (boundaryTimes ℓ H P).2 P

lemma measurable_boundarySuffix {d : ℕ} (ℓ : Vector d) (H : ℝ) :
    Measurable (boundarySuffix ℓ H) := by
  have hm : Measurable (fun Z : (Path d × Path d) × (ℕ × ℕ) =>
      commonPairSuffix Z.2.1 Z.2.2 Z.1) :=
    measurable_from_prod_countable_left fun q => measurable_commonPairSuffix q.1 q.2
  exact hm.comp (measurable_id.prodMk (measurable_boundaryTimes ℓ H))

lemma boundaryData_times {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    (F : BoundaryData d) (hF : boundaryData ℓ H P = F) :
    boundaryTimes ℓ H P = F.1 := congrArg Sigma.fst hF

lemma boundaryAtom_fiber_ae {d : ℕ} (μ : Measure (Path d × Path d))
    (ℓ : Vector d) (H : ℝ) (x y : Lattice d)
    (hD : ∀ᵐ P ∂μ, P.1 ∈ NoDrop ℓ x ∧ P.2 ∈ NoDrop ℓ y)
    (hS : ∀ᵐ P ∂μ, BoundaryAt ℓ H P (boundaryTimes ℓ H P).1 (boundaryTimes ℓ H P).2)
    (F : BoundaryData d) :
    (boundaryData ℓ H ⁻¹' {F}) =ᵐ[μ]
      boundaryAtom ℓ H x y (extendPrefix F.1.1 F.2.1) (extendPrefix F.1.2 F.2.2) F.1.1 F.1.2 := by
  filter_upwards [hD,hS] with P hDP hSP
  rw [boundaryData_fiber,pairPrefix_fiber]
  apply propext
  change (boundaryTimes ℓ H P = F.1 ∧ _) ↔ _
  constructor
  · rintro ⟨ht,hpre⟩
    refine ⟨hpre,hDP,?_⟩
    change BoundaryAt ℓ H P F.1.1 F.1.2
    simpa only [ht] using hSP
  · rintro ⟨hpre,hno,hB⟩
    exact ⟨boundaryTimes_eq ℓ H P hB,hpre⟩

lemma shared_boundaryData_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (hxy : height x = height y) (H : ℕ) (hH : 0 < H)
    (F : BoundaryData d) :
    ((sharedConditionedPairLaw ν ℓ x y).restrict
       (boundaryData ℓ ((height x+H : ℤ) : ℝ) ⁻¹' {F})).map
       (boundarySuffix ℓ ((height x+H : ℤ) : ℝ)) =
      sharedConditionedPairLaw ν ℓ x y
        (boundaryData ℓ ((height x+H : ℤ) : ℝ) ⁻¹' {F}) •
      sharedConditionedPairLaw ν ℓ
        (extendPrefix F.1.1 F.2.1 F.1.1) (extendPrefix F.1.2 F.2.2 F.1.2) := by
  let μ := sharedConditionedPairLaw ν ℓ x y
  let h : ℝ := ((height x+H : ℤ) : ℝ)
  have hae := boundaryAtom_fiber_ae μ ℓ h x y (sharedConditionedPairLaw_noDrop ν ℓ x y)
    (shared_boundaryTimes_spec ν hue ℓ hℓ htrans height hproj hstep x y hxy H hH) F
  have hmap : (μ.restrict (boundaryData ℓ h ⁻¹' {F})).map (boundarySuffix ℓ h) =
      (μ.restrict (boundaryData ℓ h ⁻¹' {F})).map (commonPairSuffix F.1.1 F.1.2) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem ((measurable_boundaryData ℓ h) (measurableSet_singleton F))] with P hP
    have ht := boundaryData_times ℓ h P F hP
    simp only [boundarySuffix,ht]
  change (μ.restrict (boundaryData ℓ h ⁻¹' {F})).map _ = _
  rw [hmap,Measure.restrict_congr_set hae,measure_congr hae]
  exact shared_boundaryAtom_map ν hue ℓ hℓ htrans h x y _ _ _ _

lemma lintegral_partition_countable {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] (μ : Measure Ω) (D : Ω → I) (hD : Measurable D)
    (f : Ω → ℝ≥0∞) : (∫⁻ a, f a ∂μ) = ∑' i, ∫⁻ a in D ⁻¹' {i}, f a ∂μ := by
  have hu : (⋃ i, D ⁻¹' {i}) = Set.univ := by ext a; simp
  have hd : Pairwise (fun i j : I => Disjoint (D ⁻¹' {i}) (D ⁻¹' {j})) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro a hi hj
    exact hij (hi.symm.trans hj)
  have hh := lintegral_iUnion (μ := μ) (fun i => hD (measurableSet_singleton i)) hd f
  simpa only [hu,Measure.restrict_univ] using hh

lemma lintegral_countable_restart {Ω I S : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSpace S] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) (D : Ω → I) (Y : Ω → S) (κ : I → Measure S)
    (hD : Measurable D) (hY : Measurable Y)
    (hrestart : ∀ i, (μ.restrict (D ⁻¹' {i})).map Y = μ (D ⁻¹' {i}) • κ i)
    (f : I → ℝ≥0∞) (g : S → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ a, f (D a) * g (Y a) ∂μ) =
      ∫⁻ a, f (D a) * (∫⁻ z, g z ∂κ (D a)) ∂μ := by
  rw [lintegral_partition_countable μ D hD,lintegral_partition_countable μ D hD]
  apply tsum_congr
  intro i
  have ha : ∀ᵐ a ∂μ.restrict (D ⁻¹' {i}), D a = i :=
    ae_restrict_mem (hD (measurableSet_singleton i))
  calc
    (∫⁻ a in D ⁻¹' {i}, f (D a) * g (Y a) ∂μ) =
        ∫⁻ a in D ⁻¹' {i}, f i * g (Y a) ∂μ :=
      lintegral_congr_ae (ha.mono fun a ha => by dsimp only; rw [ha])
    _ = f i * ∫⁻ a in D ⁻¹' {i}, g (Y a) ∂μ :=
      lintegral_const_mul _ (hg.comp hY)
    _ = f i * ∫⁻ z, g z ∂(μ.restrict (D ⁻¹' {i})).map Y := by
      rw [lintegral_map hg hY]
    _ = f i * (μ (D ⁻¹' {i}) * ∫⁻ z, g z ∂κ i) := by
      rw [hrestart i,lintegral_smul_measure,smul_eq_mul]
    _ = ∫⁻ a in D ⁻¹' {i}, f i * (∫⁻ z, g z ∂κ i) ∂μ := by
      rw [lintegral_const,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
      ac_rfl
    _ = ∫⁻ a in D ⁻¹' {i}, f (D a) * (∫⁻ z, g z ∂κ (D a)) ∂μ :=
      lintegral_congr_ae (ha.mono fun a ha => by dsimp only; rw [ha])

theorem shared_jointPast_restart {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (hxy : height x = height y) (H : ℕ) (hH : 0 < H)
    (f : BoundaryData d → ℝ≥0∞) (g : (Path d × Path d) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ P, f (boundaryData ℓ ((height x+H : ℤ) : ℝ) P) *
        g (boundarySuffix ℓ ((height x+H : ℤ) : ℝ) P) ∂sharedConditionedPairLaw ν ℓ x y) =
      ∫⁻ P, f (boundaryData ℓ ((height x+H : ℤ) : ℝ) P) *
        (∫⁻ Q, g Q ∂sharedConditionedPairLaw ν ℓ
          (extendPrefix (boundaryData ℓ ((height x+H : ℤ) : ℝ) P).1.1
            (boundaryData ℓ ((height x+H : ℤ) : ℝ) P).2.1
            (boundaryData ℓ ((height x+H : ℤ) : ℝ) P).1.1)
          (extendPrefix (boundaryData ℓ ((height x+H : ℤ) : ℝ) P).1.2
            (boundaryData ℓ ((height x+H : ℤ) : ℝ) P).2.2
            (boundaryData ℓ ((height x+H : ℤ) : ℝ) P).1.2))
        ∂sharedConditionedPairLaw ν ℓ x y := by
  exact lintegral_countable_restart _ _ _ _ (measurable_boundaryData ℓ _)
    (measurable_boundarySuffix ℓ _)
    (shared_boundaryData_map ν hue ℓ hℓ htrans height hproj hstep x y hxy H hH) f g hg

end DirectionalTransience

end

end

end OAI
