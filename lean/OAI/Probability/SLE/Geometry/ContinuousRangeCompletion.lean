import Mathlib

namespace OAI

/-! Continuous images of Baire space are measurable in the completion of a
finite measure. This supplies the uncountable-time projection step for SLE. -/
noncomputable section
open Set Filter MeasureTheory Function PiNat Metric
open scoped Topology ENNReal

namespace SLEExactGauge

def prefixCylinder (s : List ℕ) : Set (ℕ → ℕ) :=
  {b | res b s.length=s}

lemma prefixCylinder_nil : prefixCylinder []=univ := by
  ext b
  simp [prefixCylinder]

lemma prefixCylinder_children (s : List ℕ) :
    prefixCylinder s=⋃ k : ℕ, prefixCylinder (k::s) := by
  ext b
  simp only [prefixCylinder,mem_ofPred_eq,mem_iUnion,List.length_cons,res_succ,List.cons.injEq]
  constructor
  · intro h
    exact ⟨b s.length,rfl,h⟩
  · rintro ⟨k,_,h⟩
    exact h

lemma prefixCylinder_res (b : ℕ → ℕ) (n : ℕ) :
    prefixCylinder (res b n)=cylinder b n := by
  rw [prefixCylinder,res_length,cylinder_eq_res]

theorem nullMeasurableSet_continuous_baire_range
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) :
    NullMeasurableSet (range f) μ := by
  classical
  let A (s : List ℕ) := f '' prefixCylinder s
  let E (s : List ℕ) := toMeasurable μ (A s) ∩ closure (A s)
  have hE (s : List ℕ) : MeasurableSet (E s) :=
    (measurableSet_toMeasurable μ (A s)).inter isClosed_closure.measurableSet
  have hAE (s : List ℕ) : A s ⊆ E s :=
    fun _ h => ⟨subset_toMeasurable μ (A s) h,subset_closure h⟩
  have hAchildren (s : List ℕ) : A s=⋃ k, A (k::s) := by
    dsimp only [A]
    rw [prefixCylinder_children,image_iUnion]
  have hzero (s : List ℕ) : μ (E s \ ⋃ k, E (k::s))=0 := by
    have hU : MeasurableSet (⋃ k, E (k::s)) := MeasurableSet.iUnion fun k => hE (k::s)
    have hsub : A s ⊆ ⋃ k, E (k::s) := by
      rw [hAchildren]
      exact iUnion_mono fun k => hAE (k::s)
    have hempty : A s ∩ (⋃ k, E (k::s))ᶜ=∅ := by
      exact eq_empty_iff_forall_notMem.mpr (fun x hx => hx.2 (hsub hx.1))
    apply measure_mono_null (show E s \ ⋃ k, E (k::s) ⊆
      toMeasurable μ (A s) ∩ (⋃ k, E (k::s))ᶜ from fun _ h => ⟨h.1.1,h.2⟩)
    rw [μ.measure_toMeasurable_inter hU.compl (measure_ne_top μ (A s)),hempty,measure_empty]
  let N := ⋃ s : List ℕ, E s \ ⋃ k, E (k::s)
  have hN : μ N=0 := measure_iUnion_null hzero
  have hcover : range f ⊆ E [] := by
    have h := hAE []
    simpa only [A,prefixCylinder_nil,image_univ] using h
  have hinside (x : X) (hx : x ∈ E []) (hxN : x ∉ N) : x ∈ range f := by
    have hchild (s : List ℕ) (hs : x ∈ E s) : ∃ k, x ∈ E (k::s) := by
      by_contra h
      apply hxN
      exact mem_iUnion.mpr ⟨s,hs,by simpa only [mem_iUnion,not_exists] using h⟩
    let S := {s : List ℕ // x ∈ E s}
    let F (s : S) : S := ⟨(hchild s.1 s.2).choose::s.1,(hchild s.1 s.2).choose_spec⟩
    let p (n : ℕ) : S := F^[n] ⟨[],hx⟩
    have hp (n : ℕ) : p (n+1)=F (p n) := by simp only [p,iterate_succ',comp_apply]
    let b (n : ℕ) := (hchild (p n).1 (p n).2).choose
    have hres (n : ℕ) : (p n).1=res b n := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [hp]
        change b n::(p n).1=res b (n+1)
        rw [res_succ,ih]
    have hclosure (n : ℕ) : x ∈ closure (f '' cylinder b n) := by
      have h := (p n).2.2
      simpa only [hres,A,prefixCylinder_res] using h
    have heq : x=f b := by
      apply eq_of_forall_dist_le
      intro ε hε
      obtain ⟨v,⟨c,n,rfl⟩,hb,hv⟩ :=
        (isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open
          (show b ∈ f ⁻¹' ball (f b) ε from mem_ball_self hε)
          (isOpen_ball.preimage hf)
      have hsub : f '' cylinder b n ⊆ closedBall (f b) ε := by
        rw [← mem_cylinder_iff_eq.mp hb] at hv
        exact (image_subset_iff.mpr hv).trans ball_subset_closedBall
      have hc := closure_minimal hsub isClosed_closedBall (hclosure n)
      exact hc
    exact ⟨b,heq.symm⟩
  apply (hE []).nullMeasurableSet.congr
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN] with x hxN
  exact propext ⟨fun hx => hinside x hx hxN,fun hx => hcover hx⟩

theorem nullMeasurableSet_of_analytic_finite
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {s : Set X} (hs : AnalyticSet s) :
    NullMeasurableSet s μ := by
  rw [AnalyticSet] at hs
  rcases hs with rfl | ⟨f,hf,rfl⟩
  · exact MeasurableSet.empty.nullMeasurableSet
  · exact nullMeasurableSet_continuous_baire_range μ f hf

end SLEExactGauge

end

end OAI
