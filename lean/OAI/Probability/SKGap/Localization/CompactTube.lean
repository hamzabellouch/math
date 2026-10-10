import Mathlib
import OAI.Probability.SKGap.Localization.ConditionalModelAlgebra

namespace OAI

section
noncomputable section
namespace SKGap
open Set Filter Topology

theorem compact_perturbation_tube {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (E : Set (X × ℝ))
    (hE : ∀ x ∈ K, E ∈ 𝓝 (x,0)) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ ∃ δ > 0,
      ∀ x ∈ U, ∀ r : ℝ, |r| ≤ δ → (x,r) ∈ E := by
  have hc : K ×ˢ ({0} : Set ℝ) ⊆ interior E := by
    rintro ⟨x,r⟩ ⟨hx,hr⟩
    have hr0 : r=0 := mem_singleton_iff.mp hr
    subst r
    exact mem_interior_iff_mem_nhds.mpr (hE x hx)
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma hK isCompact_singleton isOpen_interior hc
  have hV0 : V ∈ 𝓝 (0:ℝ) := hV.mem_nhds (h0V (mem_singleton 0))
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp hV0
  refine ⟨U,hU,hKU,r/2,half_pos hr,?_⟩
  intro x hx a ha
  apply interior_subset (hUV ⟨hx,?_⟩)
  apply hrV
  rw [Metric.mem_ball,Real.dist_eq,sub_zero]
  linarith
end SKGap
namespace SKGap
open Set Filter Topology
lemma compact_perturbation_tube_norm {X Y : Type*} [TopologicalSpace X]
    [NormedAddCommGroup Y] {K : Set X} (hK : IsCompact K) (E : Set (X × Y))
    (hE : ∀ x ∈ K, E ∈ 𝓝 (x,0)) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ ∃ δ > 0,
      ∀ x ∈ U, ∀ r : Y, ‖r‖ ≤ δ → (x,r) ∈ E := by
  have hc : K ×ˢ ({0} : Set Y) ⊆ interior E := by
    rintro ⟨x,r⟩ ⟨hx,hr⟩
    have hr0 : r=0 := mem_singleton_iff.mp hr
    subst r
    exact mem_interior_iff_mem_nhds.mpr (hE x hx)
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma hK isCompact_singleton isOpen_interior hc
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton 0)))
  refine ⟨U,hU,hKU,r/2,half_pos hr,?_⟩
  intro x hx a ha
  apply interior_subset (hUV ⟨hx,hrV ?_⟩)
  rw [Metric.mem_ball,dist_zero_right]
  linarith
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators Matrix.Norms.Frobenius

def conditionalScalarSize (j : ℝ) (p : ScalarPoint) (r : ℝ) : ℝ :=
  (1+|scalarD j p|)/scalarS j p+1/scalarQMoment p.1+1/scalarS j p+
    1/(j*scalarBMoment p.1+r)+(j*scalarBMoment p.1+r)+‖conditionalScalarData j p‖

lemma continuousAt_conditionalSize {X : Type*} [TopologicalSpace X]
    {R j : ℝ} (hR : 0 ≤ R) (f : X → ScalarPoint) (hf : Continuous f)
    (hdom : ∀ x,f x ∈ scalarMomentDomain R) (r : X → ℝ) (hr : Continuous r)
    {x : X} (hq : 0 < scalarQMoment (f x).1) (hs : 0 < scalarS j (f x))
    (hS : 0 < scalarS j (f x)+j*scalarQMoment (f x).1)
    (hB : 0 < j*scalarBMoment (f x).1+r x) :
    ContinuousAt (fun x=>conditionalScalarSize j (f x) (r x)) x := by
  have hq' := (continuous_scalarQMoment.comp (continuous_fst.comp hf)).continuousAt (x := x)
  have hs' := ((continuous_scalarS j).comp hf).continuousAt (x := x)
  have hd' := ((continuous_scalarD j).comp hf).continuousAt (x := x)
  have hb' := (((continuous_const : Continuous (fun _ : X=>j)).mul (continuous_scalarBMoment.comp (continuous_fst.comp hf))).add hr).continuousAt (x := x)
  have he' := (continuousAt_conditionalData hR f hf hdom r hr hq hs hS).2.norm
  exact (((((continuousAt_const.add hd'.abs).div hs' hs.ne').add
    (continuousAt_const.div hq' hq.ne')).add (continuousAt_const.div hs' hs.ne')).add
    (continuousAt_const.div hb' hB.ne')).add hb' |>.add he'

lemma continuousAt_augmentedGram {X : Type*} [TopologicalSpace X]
    {H : X → Matrix (Fin 3) (Fin 3) ℝ} {x : X} (hH : ContinuousAt H x) :
    ContinuousAt (fun x=>augmentedGram (ν := Unit) (H x)) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  cases i with
  | inl i => cases k with
    | inl k => exact (continuousAt_pi.mp (continuousAt_pi.mp hH i) k)
    | inr k => exact continuousAt_const
  | inr i => cases k <;> exact continuousAt_const

abbrev ScalarTimeDomain (R t0 T : ℝ) := (momentBall R) × (Icc t0 T)

def scalarEqualitySet (j R t0 T : ℝ) : Set (ScalarTimeDomain R t0 T) :=
  {x | (x.1 : ProbabilityMeasure ℝ)=scalarCurve j x.2}

def scalarPerturbedPoint {R t0 T : ℝ} (z : ScalarTimeDomain R t0 T × (ℝ × ℝ)) : ScalarPoint :=
  ((z.1.1 : ProbabilityMeasure ℝ),(z.1.2 : ℝ),z.2.1)

lemma continuous_scalarPerturbedPoint {R t0 T : ℝ} :
    Continuous (@scalarPerturbedPoint R t0 T) := by
  unfold scalarPerturbedPoint
  fun_prop

lemma scalarPerturbedPoint_domain {R t0 T : ℝ} (z : ScalarTimeDomain R t0 T × (ℝ × ℝ)) :
    scalarPerturbedPoint z ∈ scalarMomentDomain R := ⟨z.1.1.2,mem_univ _⟩

lemma isCompact_scalarEqualitySet {j R t0 T : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht0 : 0 < t0) :
    IsCompact (scalarEqualitySet j R t0 T) := by
  let : CompactSpace (momentBall R) := isCompact_iff_compactSpace.mp (isCompact_momentBall R)
  have hcurve : Continuous (fun t : Icc t0 T=>scalarCurve j t) :=
    (continuous_scalarCurve_nonneg hj hj1).comp (continuous_subtype_val.subtype_mk (fun t=>ht0.le.trans t.2.1))
  exact (isClosed_eq (continuous_subtype_val.comp continuous_fst) (hcurve.comp continuous_snd)).isCompact

theorem scalar_conditional_neighborhood {j R t0 T ρ : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R) (ht0 : 0 < t0) (hρ : 0 < ρ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧
      scalarEqualitySet j R t0 T ⊆ U ∧ ∃ δ > 0,
      ∀ x ∈ U,∀ σ r : ℝ, |σ| ≤ δ → |r| ≤ δ →
      let p : ScalarPoint := ((x.1 : ProbabilityMeasure ℝ),(x.2 : ℝ),σ)
      0 < scalarQMoment p.1 ∧ 0 < scalarS j p ∧ 0 < j*scalarBMoment p.1+r ∧
      conditionalScalarSize j p r < L ∧
      ‖augmentedGram (ν := Unit) (scalarMomentGram p.1 (scalarD j p) (scalarS j p))-
        augmentedGram (ν := Unit) (limitingGram (scalarBMoment (scalarCurve j x.2))
          (scalarEMoment (scalarCurve j x.2)) (scalarFixedPoint j x.2))‖ < ρ ∧
      ‖conditionalMeanData j p r-curveCoefficient j x.2‖ < ρ := by
  let X := ScalarTimeDomain R t0 T
  let K := scalarEqualitySet j R t0 T
  let f : X × (ℝ × ℝ) → ScalarPoint := scalarPerturbedPoint
  let r : X × (ℝ × ℝ) → ℝ := fun z=>z.2.2
  have hf : Continuous f := continuous_scalarPerturbedPoint
  have hr : Continuous r := continuous_snd.comp continuous_snd
  have hd : ∀ z,f z ∈ scalarMomentDomain R := scalarPerturbedPoint_domain
  have hK : IsCompact K := isCompact_scalarEqualitySet hj hj1 ht0
  have heq (x : X) (hx : x ∈ K) : f (x,0)=(scalarCurve j x.2,(x.2:ℝ),0) := by
    change ((x.1:ProbabilityMeasure ℝ),(x.2:ℝ),0)=_
    rw [show (x.1:ProbabilityMeasure ℝ)=scalarCurve j x.2 from hx]
  have hpoint (x : X) (hx : x ∈ K) :
      0 < scalarQMoment (f (x,0)).1 ∧ 0 < scalarS j (f (x,0)) ∧
      0 < scalarS j (f (x,0))+j*scalarQMoment (f (x,0)).1 ∧
      0 < j*scalarBMoment (f (x,0)).1+r (x,0) := by
    rw [heq x hx,scalarQMoment_curve hj hj1 (ht0.le.trans x.2.2.1),scalarS_curve hj hj1 (ht0.le.trans x.2.2.1)]
    have hp := scalar_fixed_pos hj hj1 (ht0.trans_le x.2.2.1)
    exact ⟨hp.2,hp.1,add_pos hp.1 (mul_pos hj hp.2),by simpa [r] using mul_pos hj (scalarBMoment_pos (scalarCurve j x.2))⟩
  have hsize (x : X) (hx : x ∈ K) :
      ContinuousAt (fun z=>conditionalScalarSize j (f z) (r z)) (x,0) :=
    continuousAt_conditionalSize hR f hf hd r hr (hpoint x hx).1 (hpoint x hx).2.1
      (hpoint x hx).2.2.1 (hpoint x hx).2.2.2
  have hsizeK : ContinuousOn (fun x : X=>conditionalScalarSize j (f (x,0)) (r (x,0))) K := by
    intro x hx
    exact ((hsize x hx).comp (x := x) (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.bddAbove_image hsizeK
  let L := max 1 (M+1)
  have hL : 1 ≤ L := le_max_left _ _
  have hsmall (x : X) (hx : x ∈ K) : conditionalScalarSize j (f (x,0)) (r (x,0)) < L :=
    (lt_of_le_of_lt (hM (mem_image_of_mem _ hx)) (by linarith : M < M+1)).trans_le (le_max_right _ _)
  obtain ⟨hs,hq,hb,he,hkap,hc⟩ := continuous_curve_statistics (T := T) hj hj1 ht0
  let G : X × (ℝ × ℝ) → Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ := fun z=>
    augmentedGram (ν := Unit) (scalarMomentGram (f z).1 (scalarD j (f z)) (scalarS j (f z)))
  let G0 : X × (ℝ × ℝ) → Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ := fun z=>
    augmentedGram (ν := Unit) (limitingGram (scalarBMoment (scalarCurve j z.1.2))
      (scalarEMoment (scalarCurve j z.1.2)) (scalarFixedPoint j z.1.2))
  have hG0 : Continuous G0 := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply continuousAt_augmentedGram
    unfold limitingGram
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro k
    have hb' := (hb.comp (continuous_snd.comp continuous_fst)).continuousAt (x := z)
    have he' := (he.comp (continuous_snd.comp continuous_fst)).continuousAt (x := z)
    have hs' := (hs.comp (continuous_snd.comp continuous_fst)).continuousAt (x := z)
    fin_cases i <;> fin_cases k <;> simp only [Matrix.of_apply,Matrix.cons_val,Fin.reduceFinMk] <;>
      fun_prop (disch := exact (scalar_fixed_pos hj hj1 (ht0.trans_le z.1.2.2.1)).1.ne')
  let E : Set (X × (ℝ × ℝ)) := {z |
    0 < scalarQMoment (f z).1 ∧ 0 < scalarS j (f z) ∧ 0 < j*scalarBMoment (f z).1+r z ∧
    conditionalScalarSize j (f z) (r z) < L ∧ ‖G z-G0 z‖ < ρ ∧
    ‖conditionalMeanData j (f z) (r z)-curveCoefficient j z.1.2‖ < ρ}
  have hE (x : X) (hx : x ∈ K) : E ∈ 𝓝 (x,0) := by
    have hpt := hpoint x hx
    have hqc := (continuous_scalarQMoment.comp (continuous_fst.comp hf)).continuousAt (x := (x,0))
    have hsc := ((continuous_scalarS j).comp hf).continuousAt (x := (x,0))
    have hbc := (((continuous_const : Continuous (fun _ : X × (ℝ × ℝ)=>j)).mul (continuous_scalarBMoment.comp (continuous_fst.comp hf))).add hr).continuousAt (x := (x,0))
    have cg : ContinuousAt G (x,0) := by
      apply continuousAt_augmentedGram
      exact (continuousAt_scalarMomentGram (p := ((f (x,0)).1,scalarD j (f (x,0)),scalarS j (f (x,0)))) hpt.2.1.ne').comp
        (x := (x,0)) ((continuous_fst.comp hf).continuousAt.prodMk
        (((continuous_scalarD j).comp hf).continuousAt.prodMk hsc))
    have cm := (continuousAt_conditionalData hR f hf hd r hr hpt.1 hpt.2.1 hpt.2.2.1).1
    have hgzero : G (x,0)-G0 (x,0)=0 := by
      dsimp only [G,G0]
      rw [heq x hx,scalarD_curve hj hj1 (ht0.le.trans x.2.2.1),scalarS_curve hj hj1 (ht0.le.trans x.2.2.1),
        scalarMomentGram_curve hj hj1 (ht0.trans_le x.2.2.1)]
      exact sub_self _
    have hczero : conditionalMeanData j (f (x,0)) (r (x,0))-curveCoefficient j x.2=0 := by
      rw [heq x hx]
      change conditionalMeanData j (scalarCurve j x.2,(x.2:ℝ),0) 0-curveCoefficient j x.2=0
      rw [conditionalMeanData_curve hj hj1 (ht0.trans_le x.2.2.1),sub_self]
    have e1 := hqc.eventually_const_lt hpt.1
    have e2 := hsc.eventually_const_lt hpt.2.1
    have e3 := hbc.eventually_const_lt hpt.2.2.2
    have e4 := (hsize x hx).eventually_lt_const (hsmall x hx)
    have e5 := (cg.sub hG0.continuousAt).norm.eventually_lt_const (by change ‖G (x,0)-G0 (x,0)‖ < ρ; simpa only [hgzero,norm_zero] using hρ)
    have e6 := (cm.sub (hc.comp (continuous_snd.comp continuous_fst)).continuousAt).norm.eventually_lt_const (by change ‖conditionalMeanData j (f (x,0)) (r (x,0))-curveCoefficient j x.2‖ < ρ; simpa only [hczero,norm_zero] using hρ)
    exact e1.and (e2.and (e3.and (e4.and (e5.and e6))))
  obtain ⟨U,hU,hKU,δ,hδ,hδE⟩ := compact_perturbation_tube_norm hK E hE
  refine ⟨L,hL,U,hU,hKU,δ,hδ,?_⟩
  intro x hx σ r hσ hr
  exact hδE x hx (σ,r) (by simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff] using And.intro hσ hr)
end SKGap
end
end

end OAI
