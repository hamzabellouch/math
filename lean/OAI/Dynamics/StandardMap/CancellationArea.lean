import OAI.Dynamics.StandardMap.CancellationVector

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_complex_mk {α : Type*} [TopologicalSpace α] (f g : α → ℝ)
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => (⟨f x,g x⟩:ℂ)) :=
  Complex.equivRealProdCLM.symm.continuous.comp (hf.prodMk hg)
lemma isClosed_torusSmallEndpoints (k : ℝ) (Np Nm : ℕ) (R : ℝ) :
    IsClosed {z : Torus | torusSmallEndpoints k Np Nm R z} := by
  let S : Set (Torus × ℝ) := {p | p.2 ∈ Icc (-growthBase k) (growthBase k) ∧
    ‖torusSegmentTransfer k p.1.swap 0 (Nm-1) ⟨p.2,1⟩‖ ≤ R ∧
    ‖torusSegmentTransfer k p.1 0 Np ⟨1,p.2⟩‖ ≤ R}
  have h1 : Continuous (fun p : Torus × ℝ =>
      ‖torusSegmentTransfer k p.1.swap 0 (Nm-1) ⟨p.2,1⟩‖) := by
    exact (((continuous_torusSegmentTransfer k 0 (Nm-1)).comp (continuous_swap.comp continuous_fst)).clm_apply
      (continuous_complex_mk _ _ continuous_snd continuous_const)).norm
  have h2 : Continuous (fun p : Torus × ℝ =>
      ‖torusSegmentTransfer k p.1 0 Np ⟨1,p.2⟩‖) := by
    exact (((continuous_torusSegmentTransfer k 0 Np).comp continuous_fst).clm_apply
      (continuous_complex_mk _ _ continuous_const continuous_snd)).norm
  have hS : IsCompact S := by
    have hc := (isCompact_univ : IsCompact (univ : Set Torus)).prod
      (isCompact_Icc : IsCompact (Icc (-growthBase k) (growthBase k)))
    convert hc.inter_right ((isClosed_le h1 (continuous_const (y:=R))).inter (isClosed_le h2 (continuous_const (y:=R)))) using 1
    ext p
    simp only [S,mem_inter_iff,mem_prod,mem_univ,true_and,mem_ofPred_eq]
  have he : {z : Torus | torusSmallEndpoints k Np Nm R z}=Prod.fst '' S := by
    ext z
    constructor
    · rintro ⟨b,hb,hm,hp⟩
      exact ⟨(z,b),⟨hb,hm,hp⟩,rfl⟩
    · rintro ⟨⟨w,b⟩,hs,hw⟩
      subst z
      exact ⟨b,hs⟩
  rw [he]
  exact (hS.image continuous_fst).isClosed
lemma scalar_pairMagnitude_le_norm (v : ℕ → ℝ) (b : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    pairMagnitude (linearSolution v 1 b) N ≤ ‖transferProduct v (N-1) ⟨b,1⟩‖ := by
  rw [transferProduct_pair,Nat.sub_add_cancel hN]
  exact max_le (Complex.abs_re_le_norm ⟨_,_⟩) (Complex.abs_im_le_norm ⟨_,_⟩)
lemma torusSmallEndpoints_lift_sub (k q a R : ℝ) (Np Nm : ℕ) (hNp : 1 ≤ Np) (hNm : 1 ≤ Nm)
    (h : torusSmallEndpoints k Np Nm R (liftProjection (q,a))) :
    ∃ b : ℝ,
      pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤ R ∧
      pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤ R := by
  obtain ⟨b,_,hm,hp⟩ := h
  refine ⟨b,?_,?_⟩
  · have he : torusSegmentTransfer k (liftProjection (q,a)).swap 0 (Nm-1)=
        transferProduct (orbitCoefficient k q a) (Nm-1) := by
      change torusSegmentTransfer k (liftProjection (a,q)) 0 (Nm-1)=_
      rw [torusSegmentTransfer_lift,liftSegmentTransfer_eq,liftIter_zero]
    rw [he] at hm
    exact (scalar_pairMagnitude_le_norm _ b Nm hNm).trans hm
  · have he : torusSegmentTransfer k (liftProjection (q,a)) 0 Np ⟨1,b⟩=
        transferProduct (orbitCoefficient k q (phi k q-a)) (Np-1) ⟨potential k q-b,1⟩ := by
      conv_lhs => rw [← Nat.sub_add_cancel hNp,torusSegmentTransfer_first,ContinuousLinearMap.comp_apply,
        ← liftProjection_step,torusSegmentTransfer_lift,liftSegmentTransfer_eq,liftIter_zero]
      simp only [liftStep_apply]
      congr 1
      apply Complex.ext <;> simp [liftProjection,torusPotential_coe]
    rw [he] at hp
    exact (scalar_pairMagnitude_le_norm _ _ Np hNp).trans hp
lemma area_small_endpoints_of_slices (k : ℝ) (Np Nm : ℕ) (hNp : 1 ≤ Np) (hNm : 1 ≤ Nm)
    (R : ℝ) (K : ℝ≥0∞)
    (hs : ∀ q : ℝ, volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
      pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤ R ∧
      pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤ R} ≤ K) :
    area {z | torusSmallEndpoints k Np Nm R z} ≤ K := by
  let E := {z | torusSmallEndpoints k Np Nm R z}
  have hE : MeasurableSet E := (isClosed_torusSmallEndpoints k Np Nm R).measurableSet
  have hproj : Measurable liftProjection :=
    (((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
      ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd)).measurable
  have hmp := (AddCircle.measurePreserving_mk (1:ℝ) (0:ℝ)).prod
    (AddCircle.measurePreserving_mk (1:ℝ) (0:ℝ))
  have hm : ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1)))
      (liftProjection ⁻¹' E)=area E := by
    convert! hmp.measure_preimage hE.nullMeasurableSet using 1
    simp only [zero_add]; rfl
  rw [← hm,Measure.prod_apply (hE.preimage hproj)]
  calc
    _ ≤ ∫⁻ _q : ℝ, K ∂(volume.restrict (Ioc (0:ℝ) 1)) := by
      apply lintegral_mono
      intro q
      change (volume.restrict (Ioc (0:ℝ) 1)) (Prod.mk q ⁻¹' (liftProjection ⁻¹' E)) ≤ K
      have hmsec : MeasurableSet (Prod.mk q ⁻¹' (liftProjection ⁻¹' E)) := by
        exact (hE.preimage hproj).preimage (measurable_const.prodMk measurable_id)
      rw [Measure.restrict_apply hmsec]
      apply (measure_mono (show (Prod.mk q ⁻¹' (liftProjection ⁻¹' E)) ∩ Ioc 0 1 ⊆
          {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
            pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤ R ∧
            pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤ R} from ?_)).trans (hs q)
      intro a ha
      exact ⟨⟨ha.2.1.le,ha.2.2⟩,torusSmallEndpoints_lift_sub k q a R Np Nm hNp hNm ha.1⟩
    _ = K := by simp
lemma eventually_small_endpoints_area :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0 < k → M₀ ≤ growthBase k →
      ∀ n Np Nm : ℕ, 10000000 ≤ n → n ≤ Np ∧ Np ≤ n+1 → n ≤ Nm ∧ Nm ≤ n+1 →
      area {z | torusSmallEndpoints k Np Nm
        (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} ≤ ENNReal.ofReal ((1/4:ℝ)^n) := by
  obtain ⟨M₀,hM⟩ := eventually_small_endpoints_slice
  refine ⟨M₀,?_⟩
  intro k hk hMk n Np Nm hn hNp hNm
  exact area_small_endpoints_of_slices k Np Nm (by omega) (by omega) _ _
    (fun q => hM k hk hMk q n Np Nm hn hNp hNm)
end StandardMapEntropy

end OAI
