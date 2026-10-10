import Mathlib
import OAI.Probability.Ballisticity.Coupling.SeedOrder

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma exists_atom_probability {A : Type*} [MeasurableSpace A] [Countable A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsProbabilityMeasure μ] : ∃ x, μ {x} ≠ 0 := by
  by_contra! hn
  have hz : μ=0 := Measure.ext_of_singleton fun x => by simp [hn x]
  have h := measure_univ (μ:=μ)
  simp only [hz,Measure.coe_zero,Pi.zero_apply] at h
  exact zero_ne_one h

lemma seedOrdered_trans {d : ℕ} (f : Direction d) (s : ℤ) (g h : ℝ)
    (μ ρ σ : Measure (Lattice d)) [IsProbabilityMeasure ρ]
    (h₁ : SeedOrdered f s g μ ρ) (h₂ : SeedOrdered f s h ρ σ) : SeedOrdered f s (g+h) μ σ := by
  obtain ⟨y,hy⟩ := exists_atom_probability ρ
  intro x hx z hz
  have hxy := h₁ x hx y hy
  have hyz := h₂ y hy z hz
  nlinarith

lemma seedStateStep_ordered {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j c g g' : ℝ) (q : SeedState e a) (ω : Environment d)
    (hs : s=1 ∨ s= -1) (hq : 0<q.1) (hj : 0<j) (hc : 0<c)
    (hg' : 0≤g') (hgg' : g'≤g-2*z) (hbg' : g'≤b-z)
    (ho : SeedStateOrdered f s g q)
    (hp : SeedPreserved e f a s k H θ z c q ω) :
    SeedStateOrdered f s g' (seedStateStep e f a s k H θ z b j q ω) := by
  let P := fun i => seedAdvance e a H (SeedCentral f H θ z) (seedCentralInput e f a s k q i) ω
  have hm (i : ℕ) (hi : i<q.1) : seedEndpointRaw e H (SeedCentral f H θ z)
      (seedCentralInput e f a s k q i).measure ω Set.univ ≠ 0 := by
    intro hz
    have hh := hp i hi
    rw [hz,ENNReal.toReal_zero] at hh
    linarith
  have hop (i t : ℕ) (hit : i<t) (ht : t<q.1) : SeedOrdered f s g' (P i).measure (P t).measure := by
    apply seedOrdered_mono f s (g:=g-2*z) _ hgg'
    apply seedOrdered_central e f a s H θ z g hs _ _ ω (hm i (hit.trans ht)) (hm t ht)
    intro x hx y hy
    exact ho i t hit ht x (seedCentralInput_atom e f a s k q i hx) y (seedCentralInput_atom e f a s k q t hy)
  intro i t hit ht
  by_cases hsplit : q.1<k ∧ seedSplitTest e f a s H θ b j q ω
  · have htt : t<q.1+1 := by simpa [seedStateStep,hsplit] using ht
    have hi : i<q.1 := by omega
    have hqi : i≠q.1 := by omega
    by_cases hqt : t=q.1
    · let J := seedAdvance e a H (SeedJump f H s θ b) (seedJumpInput e f a s q) ω
      have hjm : seedEndpointRaw e H (SeedJump f H s θ b) (seedJumpInput e f a s q).measure ω Set.univ ≠ 0 := by
        intro hz
        have hh := hsplit.2
        change j ≤ _ at hh
        rw [hz,ENNReal.toReal_zero] at hh
        linarith
      have hlast : SeedOrdered f s g' (P (q.1-1)).measure J.measure := by
        have he : seedCentralInput e f a s k q (q.1-1)=seedHalfProfile e f a s false (q.2 (q.1-1)) := by
          simp [seedCentralInput,hsplit.1]
        have hh := seedOrdered_split e f a s H θ z b hs (q.2 (q.1-1)) ω
          (by simpa only [←he] using hm (q.1-1) (by omega)) hjm
        apply seedOrdered_mono f s _ hbg'
        simpa only [P,J,seedJumpInput,he] using hh
      have hip : SeedOrdered f s g' (P i).measure J.measure := by
        by_cases he : i=q.1-1
        · simpa only [he] using hlast
        · have hh := seedOrdered_trans f s g' g' (P i).measure (P (q.1-1)).measure J.measure
            (hop i (q.1-1) (by omega) (by omega)) hlast
          exact seedOrdered_mono f s hh (by linarith)
      simpa [seedStateStep,hsplit,hqt,hqi,P,J] using hip
    · have htt' : t<q.1 := by omega
      simpa [seedStateStep,hsplit,hqt,hqi,P] using hop i t hit htt'
  · have htt : t<q.1 := by simpa [seedStateStep,hsplit] using ht
    simpa [seedStateStep,hsplit,P] using hop i t hit htt

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedProfileRaw_joint_rows {d : ℕ} (e : Direction d) (a : ℤ) {H : ℕ} (hH : 0<H)
    (R : Lattice d → Lattice d → Prop) (S : Set (Lattice d))
    (hS : ∀ x, signedHeight e x=a → Strip (realPosition (step e)) x H ⊆ S) :
    @Measurable (SeedProfile e a × Environment d) ℝ
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => (seedEndpointRaw e H R p.1.measure p.2 Set.univ).toReal) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  exact ((Measure.measurable_coe MeasurableSet.univ).comp
    ((seedEndpointRaw_joint_rows e hH R {x | signedHeight e x=a} S hS).comp
      (((SeedProfile.measurable_supported e a).comp measurable_fst).prodMk measurable_snd))).ennreal_toReal

lemma seedSplitTest_joint_rows {d : ℕ} (e f : Direction d) (a s : ℤ) {H : ℕ} (hH : 0<H)
    (θ b j : ℝ) (S : Set (Lattice d))
    (hS : ∀ x, signedHeight e x=a → Strip (realPosition (step e)) x H ⊆ S) :
    @MeasurableSet (SeedState e a × Environment d)
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S))
      {p | seedSplitTest e f a s H θ b j p.1 p.2} := by
  let : MeasurableSpace (Environment d) := rowSigma S
  change MeasurableSet {p : SeedState e a × Environment d | j ≤
    (seedEndpointRaw e H (SeedJump f H s θ b) (seedJumpInput e f a s p.1).measure p.2 Set.univ).toReal}
  have hm := (seedProfileRaw_joint_rows e a hH (SeedJump f H s θ b) S hS).comp
    (((measurable_seedJumpInput e f a s).comp measurable_fst).prodMk measurable_snd)
  exact measurableSet_le measurable_const hm

lemma seedStateStep_joint_rows {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z b j : ℝ) (S : Set (Lattice d))
    (hS : ∀ x, signedHeight e x=a → Strip (realPosition (step e)) x H ⊆ S) :
    @Measurable (SeedState e a × Environment d) (SeedState e (a+H))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => seedStateStep e f a s k H θ z b j p.1 p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  have ht : MeasurableSet {p : SeedState e a × Environment d | p.1.1<k ∧ seedSplitTest e f a s H θ b j p.1 p.2} := (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_const).inter
    (seedSplitTest_joint_rows e f a s hH θ b j S hS)
  apply Measurable.prodMk
  · exact ((measurable_fst.comp measurable_fst).add_const 1).ite ht (measurable_fst.comp measurable_fst)
  · apply measurable_pi_iff.mpr
    intro i
    have hjump := (seedAdvance_joint_rows e a hH (SeedJump f H s θ b) S hS).comp
      (((measurable_seedJumpInput e f a s).comp measurable_fst).prodMk measurable_snd)
    have hcentral := (seedAdvance_joint_rows e a hH (SeedCentral f H θ z) S hS).comp
      (((measurable_seedCentralInput e f a s k i).comp measurable_fst).prodMk measurable_snd)
    exact hjump.ite (ht.inter (measurableSet_eq_fun measurable_const (measurable_fst.comp measurable_fst))) hcentral

lemma seedPreserved_joint_rows {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z c : ℝ) (S : Set (Lattice d))
    (hS : ∀ x, signedHeight e x=a → Strip (realPosition (step e)) x H ⊆ S) :
    @MeasurableSet (SeedState e a × Environment d)
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S))
      {p | SeedPreserved e f a s k H θ z c p.1 p.2} := by
  let : MeasurableSpace (Environment d) := rowSigma S
  simp only [SeedPreserved,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hc := (seedProfileRaw_joint_rows e a hH (SeedCentral f H θ z) S hS).comp
      (((measurable_seedCentralInput e f a s k i).comp measurable_fst).prodMk measurable_snd)
  have hi : MeasurableSet {p : SeedState e a × Environment d | i<p.1.1} :=
    measurableSet_lt measurable_const (measurable_fst.comp measurable_fst)
  have hmass : MeasurableSet {p : SeedState e a × Environment d | c ≤
      (seedEndpointRaw e H (SeedCentral f H θ z) (seedCentralInput e f a s k p.1 i).measure p.2 Set.univ).toReal} :=
    measurableSet_le measurable_const hc
  convert hi.compl.union hmass using 1
  ext p
  simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_compl_iff,imp_iff_not_or]

def seedBelow {d : ℕ} (e : Direction d) (a : ℤ) := {x : Lattice d | signedHeight e x<a}
def seedAbove {d : ℕ} (e : Direction d) (a : ℤ) := {x : Lattice d | a ≤ signedHeight e x}

lemma seedBelow_disjoint_above {d : ℕ} (e : Direction d) (a : ℤ) : Disjoint (seedBelow e a) (seedAbove e a) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  change signedHeight e x < a at hx
  change a ≤ signedHeight e x at hy
  omega

lemma strip_subset_seedAbove {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (x : Lattice d) (hx : signedHeight e x=a) : Strip (realPosition (step e)) x H ⊆ seedAbove e a := by
  intro y hy
  have hh := hy.1
  simp only [signedHeight_projection,hx] at hh
  exact_mod_cast hh

lemma strip_subset_seedBelow {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (x : Lattice d) (hx : signedHeight e x=a) : Strip (realPosition (step e)) x H ⊆ seedBelow e (a+H) := by
  intro y hy
  have hh := hy.2
  simp only [signedHeight_projection,hx] at hh
  change signedHeight e y<a+(H:ℤ)
  exact_mod_cast hh

lemma seed_fresh_test_bound {d : ℕ} {A : Type*} [MeasurableSpace A]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (e : Direction d) (a : ℤ)
    (U : Environment d → A) (hU : @Measurable _ _ (rowSigma (seedBelow e a)) _ U)
    (E : Set (Environment d)) (hE : MeasurableSet[rowSigma (seedBelow e a)] E)
    (G : Set (A × Environment d))
    (hG : @MeasurableSet _ (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma (seedAbove e a))) G)
    (c : ℝ≥0∞) (hb : ∀ η ∈ E, environmentLaw ν {ω | (U η,ω)∈G}≤c) :
    environmentLaw ν {ω | ω∈E ∧ (U ω,ω)∈G} ≤ c*environmentLaw ν E := by
  let S := seedBelow e a
  let T := seedAbove e a
  let K : Set (Environment d × Environment d) := {p | (U p.1,p.2)∈G}
  have hK : @MeasurableSet _ (MeasurableSpace.prod (rowSigma S) (rowSigma T)) K :=
    hG.preimage ((hU.comp measurable_fst).prodMk measurable_snd)
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb' (η : Environment d) (hη : η∈E) :
      (@Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν))
        {ω | (η,ω)∈K} ≤ c := by
    rw [show {ω | (η,ω)∈K}=Prod.mk η ⁻¹' K from rfl,
      Measure.map_apply hV (hK.preimage measurable_prodMk_left)]
    exact hb η hη
  exact @fresh_rows_random_test_bound d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
    ν _ S T (seedBelow_disjoint_above e a) id id measurable_id measurable_id E hE K hK c hb'

end DirectionalTransience

end

end OAI
