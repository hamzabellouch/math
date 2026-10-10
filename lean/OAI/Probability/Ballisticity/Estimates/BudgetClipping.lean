import Mathlib
import OAI.Probability.Ballisticity.Estimates.TupleClipping
import OAI.Probability.Ballisticity.Estimates.RelativeBudget

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma signedHeight_sub' {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedHeight e (x-y) = signedHeight e x-signedHeight e y := by
  simp only [signedHeight,Pi.sub_apply]
  split <;> ring

lemma recordOrZeroPrefix_wordFirstHit {d : ℕ} (e : Direction d) (x : Lattice d)
    (X : Path d) (h0 : X 0 = x) (hnn : ∀ n, ∃ f, X (n+1)=X n+step f)
    (w : List (Direction d)) (hw : X ∈ wordCylinder x w) (s a : ℕ)
    (ha : a ≤ w.length)
    (hrec : (fun n => X n-x) ∈ RecordOrZeroPrefix (realPosition (step e)) s a) :
    wordFirstHitTime e x s w = a := by
  by_cases hs : s=0
  · subst s
    have ha0 : a=0 := by simpa [RecordOrZeroPrefix] using hrec
    rw [ha0,wordFirstHitTime_zero]
  · have hr : (fun n => X n-x) ∈ RecordIndexPrefix (realPosition (step e)) s a := by
      simpa only [RecordOrZeroPrefix,ite_eq_right hs] using hrec
    have hstep (n : ℕ) : signedHeight e (X (n+1)-x) ≤ signedHeight e (X n-x)+1 := by
      obtain ⟨g,hg⟩ := hnn n
      rw [signedHeight_sub',signedHeight_sub',hg]
      have hh := signedHeight_step_le e (X n) g
      omega
    have ht := recordCount_eq_height_at_record (realPosition (step e)) (signedHeight e)
      (signedHeight_projection e) (fun n => X n-x) hstep hr.2.1
    have hheight : signedHeight e (X a) = signedHeight e x+s := by
      rw [hr.2.2.1,h0,sub_self] at ht
      simp only [signedHeight_sub'] at ht
      have hz : signedHeight e (0 : Lattice d)=0 := by simp [signedHeight]
      rw [hz] at ht
      omega
    have hwa : signedHeight e x+s ≤ signedHeight e (wordPath x w a) := by
      rw [← hw a ha,hheight]
    apply le_antisymm (wordFirstHitTime_le e x s w hwa)
    by_contra hn
    have hn' : wordFirstHitTime e x s w < a := by omega
    have hlt := hr.2.1 _ hn'
    simp only [signedHeight_projection,signedHeight_sub'] at hlt
    have hlt' : signedHeight e (X (wordFirstHitTime e x s w)) < signedHeight e (X a) := by
      have hh : signedHeight e (X (wordFirstHitTime e x s w))-signedHeight e x <
          signedHeight e (X a)-signedHeight e x := by exact_mod_cast hlt
      omega
    rw [hw _ (hn'.le.trans ha),hheight] at hlt'
    exact hlt'.not_ge (wordFirstHitTime_spec e x s w ⟨a,hwa⟩)

def CentralWordBudget {d : ℕ} (e f : Direction d) (x : Lattice d)
    (H : ℕ) (θ z : ℝ) (w : List (Direction d)) : Prop :=
  ∀ s ≤ H, |relativeWordDisplacement e f x s w-(s:ℝ)*θ| ≤ z

lemma tubePrefix_word_budget {d : ℕ} (e f : Direction d) (x : Lattice d)
    (X : Path d) (h0 : X 0=x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g)
    (H : ℕ) (θ z : ℝ)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H))
    (hw : X ∈ wordCylinder x w.val)
    (ht : X ∈ TubePrefix (realPosition (step e)) f x θ z H) :
    CentralWordBudget e f x H θ z w.val := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ht
  have hp := hitWord_prefix x _ _ w hw
  have hlen : n=w.val.length := by
    by_contra hne
    exact Set.disjoint_left.mp (hitAt_pairwise_disjoint (disjoint_strip_upper _ _ _) hne) hn.1 hp
  intro s hs
  obtain ⟨a,ha,hrec,hgood⟩ := hn.2 s hs
  rw [hlen] at ha
  have he := recordOrZeroPrefix_wordFirstHit e x X h0 hnn w.val hw s a ha hrec
  simpa only [relativeWordDisplacement,wordFirstHitPosition,he,← hw a ha] using hgood

lemma tubePrefix_le_centralWordBudget {d : ℕ} (e f : Direction d) (x : Lattice d)
    (ω : Environment d) (H : ℕ) (θ z : ℝ) :
    quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ z H) ≤
      rawWordLaw (realPosition (step e)) H ω x {w | CentralWordBudget e f x H θ z w} := by
  rw [rawWordLaw,Measure.map_apply measurable_subtype_coe (Set.to_countable _).measurableSet,
    successfulWordLaw_event ω x _ _ (disjoint_strip_upper _ _ _)]
  apply measure_mono_ae
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  intro ht
  have hh : X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) := by
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ht
    exact Set.mem_iUnion.mpr ⟨n,hn.1⟩
  obtain ⟨w,hw⟩ := (hitWord_cover x _ _ X h0 hnn).mp hh
  exact Set.mem_iUnion.mpr ⟨⟨w,tubePrefix_word_budget e f x X h0 hnn H θ z w hw ht⟩,hw⟩

lemma tupleCentral_budget {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (H : ℕ) (θ z : ℝ) (w : Fin k → List (Direction d))
    (hw : ∀ j, CentralWordBudget e f (x j) H θ z (w j)) :
    TupleRelativeBudget e f x H (2*z) w := by
  intro s hs i j
  calc
    _ = |(relativeWordDisplacement e f (x i) s (w i)-(s:ℝ)*θ)-
      (relativeWordDisplacement e f (x j) s (w j)-(s:ℝ)*θ)| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (by linarith [hw i s hs,hw j s hs])

lemma tupleTubeMass_le_relativeBudget {d k : ℕ} (e f : Direction d)
    (H : ℕ) (θ z : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    (∏ j, quenchedKernel (ω,x j) (TubePrefix (realPosition (step e)) f (x j) θ z H)) ≤
      relativeBudgetWordLaw e f H (2*z) ω x Set.univ := by
  rw [relativeBudgetWordLaw,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  calc
    _ ≤ ∏ j, rawWordLaw (realPosition (step e)) H ω (x j)
        {w | CentralWordBudget e f (x j) H θ z w} := by
      exact Finset.prod_le_prod fun j _ => tubePrefix_le_centralWordBudget e f (x j) ω H θ z
    _ = rawTupleWordLaw (realPosition (step e)) H ω x
        {w | ∀ j, CentralWordBudget e f (x j) H θ z (w j)} := by
      symm
      simpa only [rawTupleWordLaw,Set.pi,Set.mem_univ,forall_true_left,Set.mem_ofPred_eq] using
        Measure.pi_pi (fun j => rawWordLaw (realPosition (step e)) H ω (x j))
          (fun j => {w | CentralWordBudget e f (x j) H θ z w})
    _ ≤ _ := measure_mono fun _ hw => tupleCentral_budget e f x H θ z _ hw

lemma rawWordLaw_le_one {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) : rawWordLaw ℓ H ω x Set.univ ≤ 1 := by
  rw [rawWordLaw, Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]
  exact successfulWordLaw_le_one ω x _ _ (disjoint_strip_upper _ _ _)

lemma relativeBudgetWordLaw_le_one {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    relativeBudgetWordLaw e f H r ω x Set.univ ≤ 1 := by
  calc
    _ ≤ rawTupleWordLaw (realPosition (step e)) H ω x Set.univ := Measure.restrict_le_self _
    _ = ∏ j, rawWordLaw (realPosition (step e)) H ω (x j) Set.univ := Measure.pi_univ _
    _ ≤ 1 := Finset.prod_le_one (fun j _ => rawWordLaw_le_one _ _ _ _)

noncomputable def relativeBudgetMass {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) (ω : Environment d) : ℝ :=
  ∫ x, (relativeBudgetWordLaw e f H r ω x).real Set.univ ∂π

lemma tupleTubeMass_le_relativeBudgetMass {d k : ℕ} (e f : Direction d)
    (H : ℕ) (θ z : ℝ) (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π]
    (ω : Environment d) :
    tupleTubeMass (realPosition (step e)) f θ z H π ω ≤ relativeBudgetMass e f H (2*z) π ω := by
  apply integral_mono
  · apply (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg fun _ _ => measureReal_nonneg)]
    exact Finset.prod_le_one₀ (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_le_one)
  · apply (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (relativeBudgetWordLaw_le_one e f H (2*z) ω x)).trans_eq ENNReal.toReal_one
  · intro x
    have hh := ENNReal.toReal_mono (measure_ne_top (relativeBudgetWordLaw e f H (2*z) ω x) _)
      (tupleTubeMass_le_relativeBudget e f H θ z ω x)
    simpa only [ENNReal.toReal_prod,Measure.real] using hh

theorem initial_relativeBudget_clipping {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      ∀ (H : ℕ) (π : Measure (Fin k → Lattice d)), IsProbabilityMeasure π →
      (H:ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      (environmentLaw ν).real {ω | relativeBudgetMass e f H (η*r) π ω < c} < ε := by
  obtain ⟨c,hc,R,hR,hh⟩ := initial_tuple_clipping ν hue e f hef htrans k hT
    (show 0<η/2 by positivity) hε
  refine ⟨c,hc,R,hR,fun r hr H π hπ hH => ?_⟩
  let := hπ
  obtain ⟨θ,hθ⟩ := hh r hr
  have he : 2*(η/2*r)=η*r := by ring
  apply lt_of_le_of_lt (measureReal_mono (μ := environmentLaw ν) ?_) (hθ H π hπ hH)
  intro ω hω
  exact (he ▸ tupleTubeMass_le_relativeBudgetMass e f H θ (η/2*r) π ω).trans_lt hω

end DirectionalTransience

end

end OAI
