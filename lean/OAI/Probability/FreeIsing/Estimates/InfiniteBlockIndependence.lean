import Mathlib

namespace OAI

namespace Problem367

open MeasureTheory ProbabilityTheory

section Unconditional

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : Measure Ω} {f : ∀ i, Ω → X i}

theorem indepFun_disjoint_blocks (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S T : Set ι) (hst : Disjoint S T) :
    IndepFun (fun ω (i : S) => f i ω) (fun ω (i : T) => f i ω) μ := by
  change Indep (MeasurableSpace.comap (fun ω (i : S) => f i ω) inferInstance)
    (MeasurableSpace.comap (fun ω (i : T) => f i ω) inferInstance) μ
  simp only [MeasurableSpace.comap_process_pi, iSup_subtype]
  exact indep_iSup_of_disjoint (fun i => (hm i).comap_le) hf hst

theorem indepFun_of_disjoint_blocks (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S T : Set ι) (hst : Disjoint S T)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : (∀ i : S, X i) → A) (G : (∀ i : T, X i) → B)
    (hF : Measurable F) (hG : Measurable G) :
    IndepFun (fun ω => F (fun i => f i ω))
      (fun ω => G (fun i => f i ω)) μ :=
  (indepFun_disjoint_blocks hf hm S T hst).comp hF hG

theorem indepFun_infinitePi_disjoint_blocks
    (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (S T : Set ι) (hst : Disjoint S T)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : (∀ i : S, X i) → A) (G : (∀ i : T, X i) → B)
    (hF : Measurable F) (hG : Measurable G) :
    IndepFun (fun U : ∀ i, X i => F (fun i => U i))
      (fun U : ∀ i, X i => G (fun i => U i)) (Measure.infinitePi ν) :=
  indepFun_of_disjoint_blocks (iIndepFun_infinitePi (fun _ => measurable_id))
    (fun i => measurable_pi_apply i) S T hst F G hF hG

theorem infinitePi_map_disjoint_blocks
    (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (S T : Set ι) (hst : Disjoint S T) :
    (Measure.infinitePi ν).map (fun labels => (S.domRestrict labels, T.domRestrict labels)) =
      (Measure.infinitePi fun i : S => ν i).prod
        (Measure.infinitePi fun i : T => ν i) := by
  have h := indepFun_disjoint_blocks (iIndepFun_infinitePi (fun _ => measurable_id))
    (fun i => measurable_pi_apply i) S T hst (μ := Measure.infinitePi ν)
  change IndepFun S.domRestrict T.domRestrict (Measure.infinitePi ν) at h
  calc
    _ = ((Measure.infinitePi ν).map S.domRestrict).prod
        ((Measure.infinitePi ν).map T.domRestrict) :=
      h.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
    _ = _ := by rw [Measure.infinitePi_map_restrict', Measure.infinitePi_map_restrict']

theorem iIndepFun_disjoint_blocks {κ : Type*} (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S : κ → Set ι)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepFun (fun j ω (i : S j) => f i ω) μ := by
  have := hf.isProbabilityMeasure
  have : ∀ index, IsProbabilityMeasure (μ.map (f index)) :=
    fun _ => inferInstance
  have hinj : Function.Injective (fun p : (j : κ) × S j => (p.2 : ι)) := by
    rintro ⟨i, u⟩ ⟨j, v⟩ huv
    change (u : ι) = (v : ι) at huv
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.1 (hS hne) u.property (huv.symm ▸ v.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext huv)
  have hgroup := hf.precomp hinj
  have hmap := hgroup.map_fun_eq_infinitePi_map (fun p => hm p.2)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  calc
    μ.map (fun ω j (i : S j) => f i ω) =
        (μ.map (fun ω (p : (j : κ) × S j) => f p.2 ω)).map
          (MeasurableEquiv.piCurry (fun j (i : S j) => X i)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.infinitePi (fun j =>
        Measure.infinitePi (fun i : S j => μ.map (f i))) := by
      rw [hmap]
      exact Measure.infinitePi_map_piCurry (fun (j : κ) (i : S j) => μ.map (f i))
    _ = Measure.infinitePi (fun j => μ.map (fun ω (i : S j) => f i ω)) := by
      congr 1
      funext j
      exact (hf.precomp (g := fun i : S j => (i : ι)) Subtype.val_injective
        |>.map_fun_eq_infinitePi_map (fun i : S j => hm (i : ι))).symm

theorem iIndepFun_of_disjoint_blocks {κ : Type*} (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S : κ → Set ι)
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    {A : κ → Type*} [∀ j, MeasurableSpace (A j)]
    (F : ∀ j, (∀ i : S j, X i) → A j) (hF : ∀ j, Measurable (F j)) :
    iIndepFun (fun j ω => F j (fun i => f i ω)) μ :=
  (iIndepFun_disjoint_blocks hf hm S hS).comp F hF

theorem infinitePi_map_disjoint_family {κ : Type*}
    (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (S : κ → Set ι) (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    (Measure.infinitePi ν).map (fun labels index => (S index).domRestrict labels) =
      Measure.infinitePi (fun j => Measure.infinitePi (fun i : S j => ν i)) := by
  have h := iIndepFun_disjoint_blocks (iIndepFun_infinitePi (fun _ => measurable_id))
    (fun i => measurable_pi_apply i) S hS (μ := Measure.infinitePi ν)
  change iIndepFun (fun index labels => (S index).domRestrict labels)
    (Measure.infinitePi ν) at h
  calc
    _ = Measure.infinitePi (fun index => (Measure.infinitePi ν).map (S index).domRestrict) :=
      h.map_fun_eq_infinitePi_map (by fun_prop)
    _ = _ := by
      congr 1
      funext j
      exact Measure.infinitePi_map_restrict' ν

end Unconditional

section Conditional

variable {ι Ω : Type*} (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
variable [StandardBorelSpace Ω] (hm : m ≤ mΩ)
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : Measure Ω} [IsFiniteMeasure μ] {f : ∀ i, Ω → X i}

theorem condIndepFun_disjoint_blocks (hf : iCondIndepFun m hm f μ)
    (hfmeas : ∀ i, Measurable (f i)) (S T : Set ι) (hst : Disjoint S T) :
    CondIndepFun m hm (fun ω (i : S) => f i ω)
      (fun ω (i : T) => f i ω) μ := by
  change CondIndep m
    (MeasurableSpace.comap (fun ω (i : S) => f i ω) inferInstance)
    (MeasurableSpace.comap (fun ω (i : T) => f i ω) inferInstance) hm μ
  simp only [MeasurableSpace.comap_process_pi, iSup_subtype]
  exact condIndep_iSup_of_disjoint (fun i => (hfmeas i).comap_le) hf hst

theorem condIndepFun_of_disjoint_blocks (hf : iCondIndepFun m hm f μ)
    (hfmeas : ∀ i, Measurable (f i)) (S T : Set ι) (hst : Disjoint S T)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : (∀ i : S, X i) → A) (G : (∀ i : T, X i) → B)
    (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun m hm (fun ω => F (fun i => f i ω))
      (fun ω => G (fun i => f i ω)) μ :=
  (condIndepFun_disjoint_blocks m hm hf hfmeas S T hst).comp hF hG

end Conditional

end Problem367

end OAI
