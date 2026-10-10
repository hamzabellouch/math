import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicy
import OAI.Probability.Ballisticity.Crossings.BadCrossingLaw
import OAI.Probability.Ballisticity.Geometry.SpatialConfinement
import OAI.Probability.Ballisticity.Estimates.DescendingTrials

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def CrossingGap {d : ℕ} (e : Direction d) (N : ℕ) : Set (Path d) :=
  Cross (realPosition (step e)) 0 N \ Cross (realPosition (step e)) 0 (N+1)

lemma measurableSet_crossingGap {d : ℕ} (e : Direction d) (N : ℕ) :
    MeasurableSet (CrossingGap e N) := (measurableSet_cross _ _ _).diff (measurableSet_cross _ _ _)

lemma signedHeight_zero {d : ℕ} (e : Direction d) : signedHeight e (0 : Lattice d) = 0 := by
  simp [signedHeight]

lemma confined_crossingGap_split {d : ℕ} (e : Direction d) (N : ℕ) (hN : 0 < N)
    (R : ℝ) (B : Set (Lattice d))
    (hB : ∀ y, (∀ u : Direction d, signedCoordinate u y ≤ R) → y ∈ B)
    (X : Path d) (h0 : X 0=0) (hNN : ∀ n, ∃ f, X (n+1)=X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e)))
    (hgap : X ∈ CrossingGap e N)
    (hconf : X ∉ StripExcursion (realPosition (step e)) N R) :
    X ∈ ⋃ n, HitAt (BoxStrip e N B \ {y | signedHeight e y=(N:ℤ)})
      {y | y ∈ B ∧ signedHeight e y=(N:ℤ)} n ∩
      FutureEvent (fun _ => Hit (BoxStrip e N B) {y | signedHeight e y < 0}) n := by
  have hzero : dot (realPosition (0 : Lattice d)) (realPosition (step e))=0 := by
    rw [signedHeight_projection,signedHeight_zero,Int.cast_zero]
  have hex : ∃ j, signedHeight e (X j) < 0 := by
    by_contra hh
    push Not at hh
    apply hgap.2
    have hg := ht.eventually (eventually_ge_atTop ((N:ℝ)+1))
    obtain ⟨m,hm⟩ := hg.exists
    refine ⟨m,by rwa [hzero,zero_add],?_⟩
    intro i _
    rw [hzero,signedHeight_projection]
    exact_mod_cast hh i
  let j := Nat.find hex
  have hj : signedHeight e (X j) < 0 := Nat.find_spec hex
  have hp : ∀ i < j, 0 ≤ signedHeight e (X i) := fun i hi => le_of_not_gt (Nat.find_min hex hi)
  have htop : ∀ i < j, signedHeight e (X i) ≤ (N:ℤ) := by
    intro i hi
    by_contra hn
    have hn' : (N:ℤ)+1 ≤ signedHeight e (X i) := by omega
    apply hgap.2
    refine ⟨i,?_,?_⟩
    · rw [hzero,zero_add,signedHeight_projection]
      exact_mod_cast hn'
    · intro k hk
      rw [hzero,signedHeight_projection]
      exact_mod_cast hp k (hk.trans hi)
  have hbox : ∀ i < j, X i ∈ B := by
    intro i hi
    apply hB
    intro u
    by_contra hu
    apply hconf
    refine ⟨i,?_,u,lt_of_not_ge hu⟩
    intro k hk
    rw [signedHeight_projection]
    constructor
    · exact_mod_cast hp k (hk.trans_lt hi)
    · exact_mod_cast htop k (hk.trans_lt hi)
  obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e X h0 hNN ht hN
  obtain ⟨m,hm,hmD⟩ := hgap.1
  have hnm : n ≤ m := by
    by_contra hh
    have hb := hn.2 m (by omega)
    rw [hzero,zero_add,signedHeight_projection] at hm
    have hb' : (signedHeight e (X m):ℝ) < (N:ℝ) := by exact_mod_cast hb
    linarith
  have hmj : m < j := by
    by_contra hh
    by_cases hjm : j < m
    · have hh := hmD j hjm
      rw [hzero,signedHeight_projection] at hh
      have hh' : (signedHeight e (X j):ℝ) < 0 := by exact_mod_cast hj
      linarith
    · have heq : m=j := by omega
      rw [heq,hzero,zero_add,signedHeight_projection] at hm
      have hh' : (signedHeight e (X j):ℝ) < 0 := by exact_mod_cast hj
      have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg _
      linarith
  have hnj := hnm.trans_lt hmj
  refine Set.mem_iUnion.mpr ⟨n,⟨⟨hbox n hnj,hn.1⟩,?_⟩,?_⟩
  · intro k hk
    exact ⟨⟨hbox k (hk.trans hnj),hp k (hk.trans hnj),htop k (hk.trans hnj)⟩,
      ne_of_lt (hn.2 k hk)⟩
  · change (fun k => X (n+k)) ∈ Hit (BoxStrip e N B) {y | signedHeight e y < 0}
    refine Set.mem_iUnion.mpr ⟨j-n,?_,?_⟩
    · simpa [Nat.add_sub_of_le hnj.le] using hj
    · intro k hk
      have hkj : n+k < j := by omega
      exact ⟨hbox (n+k) hkj,hp (n+k) hkj,htop (n+k) hkj⟩

lemma quenched_crossingGap_confined {d : ℕ} (ω : Environment d) (e : Direction d)
    (N : ℕ) (hN : 0 < N) (R : ℝ) (B : Set (Lattice d))
    (hB : ∀ y, (∀ u : Direction d, signedCoordinate u y ≤ R) → y ∈ B)
    (ht : ∀ᵐ X ∂quenchedKernel (ω,0), X ∈ TransientPaths (realPosition (step e)))
    (δ : ℝ≥0∞) (hgood : ∀ y ∈ BoxStrip e N B,
      δ ≤ crossingQuenched (realPosition (step e)) y (N+1) ω) :
    quenchedKernel (ω,0) (CrossingGap e N \ StripExcursion (realPosition (step e)) N R) ≤
      (1-δ)^(N+1) := by
  let S := BoxStrip e N B \ {y | signedHeight e y=(N:ℤ)}
  let T : Set (Lattice d) := {y | y ∈ B ∧ signedHeight e y=(N:ℤ)}
  have hST : Disjoint S T := Set.disjoint_left.mpr (fun _ hs ht => hs.2 ht.2)
  calc
    _ ≤ quenchedKernel (ω,0) (⋃ n, HitAt S T n ∩
        FutureEvent (fun _ => Hit (BoxStrip e N B) {y | signedHeight e y < 0}) n) := by
      apply measure_mono_ae
      filter_upwards [quenched_initial_ae (ω,0),quenched_nearest_neighbor (ω,0),ht] with X h0 hNN ht hX
      exact confined_crossingGap_split e N hN R B hB X h0 hNN ht hX.1 hX.2
    _ ≤ (1-δ)^(N+1)*quenchedKernel (ω,0) (Hit S T) :=
      quenched_hit_future_bound ω 0 hST _ (fun _ => measurableSet_hit _ _) _
        (fun y hy => quenched_descending_trials ω e N B δ hgood N y hy.1 hy.2 le_rfl)
    _ ≤ _ := by simpa using mul_le_mul_right (prob_le_one (μ := quenchedKernel (ω,0)) (s := Hit S T)) ((1-δ)^(N+1))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def latticeBox {d : ℕ} (M : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M:ℤ)) M)

lemma mem_latticeBox {d : ℕ} (M : ℕ) (x : Lattice d) :
    x ∈ latticeBox M ↔ ∀ i, -(M:ℤ) ≤ x i ∧ x i ≤ M := by
  simp [latticeBox,Fintype.mem_piFinset]

lemma card_latticeBox {d : ℕ} (M : ℕ) : (latticeBox (d := d) M).card=(2*M+1)^d := by
  have h : ((M:ℤ)+1+(M:ℤ)).toNat=2*M+1 := by omega
  simp [latticeBox,Fintype.card_piFinset,Int.card_Icc,h]

lemma latticeBox_of_signed_bound {d : ℕ} (R : ℝ) (x : Lattice d)
    (hx : ∀ u : Direction d, signedCoordinate u x ≤ R) : x ∈ latticeBox ⌈R⌉₊ := by
  rw [mem_latticeBox]
  intro i
  have hp := hx (i,true)
  have hn := hx (i,false)
  simp [signedCoordinate] at hp hn
  have hc := Nat.le_ceil R
  constructor
  · have hh : -(⌈R⌉₊:ℝ) ≤ (x i:ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (x i:ℝ) ≤ (⌈R⌉₊:ℝ) := by linarith
    exact_mod_cast hh

def badBoxEvent {d : ℕ} (e : Direction d) (N : ℕ) (β : ℝ) (S : Finset (Lattice d)) :
    Set (Environment d) :=
  ⋃ x ∈ S, {ω | (crossingQuenched (realPosition (step e)) x N ω).toReal < (N:ℝ)^(-β)}

lemma measurableSet_badBoxEvent {d : ℕ} (e : Direction d) (N : ℕ) (β : ℝ)
    (S : Finset (Lattice d)) : MeasurableSet (badBoxEvent e N β S) := by
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
    measurableSet_lt (measurable_crossingQuenched _ _ _).ennreal_toReal measurable_const

lemma badBox_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (N : ℕ) (β : ℝ) (S : Finset (Lattice d)) :
    (environmentLaw ν).real (badBoxEvent e N β S) ≤
      S.card*(environmentLaw ν).real (badCrossingEvent e N β) := by
  have htr (x : Lattice d) :
      (environmentLaw ν).real {ω | (crossingQuenched (realPosition (step e)) x N ω).toReal < (N:ℝ)^(-β)} =
      (environmentLaw ν).real (badCrossingEvent e N β) := by
    simp_rw [crossingQuenched_translation _ x]
    have hh := congrArg (fun μ : Measure (Environment d) => μ (badCrossingEvent e N β))
      (environment_translation ν x)
    rw [Measure.map_apply (by fun_prop) (badCrossingEvent_measurable e N β)] at hh
    exact congrArg ENNReal.toReal hh
  calc
    _ ≤ ∑ x ∈ S, (environmentLaw ν).real
        {ω | (crossingQuenched (realPosition (step e)) x N ω).toReal < (N:ℝ)^(-β)} :=
      measureReal_biUnion_finset_le _ _
    _ = _ := by simp [htr]

lemma good_box_crossing {d : ℕ} (e : Direction d) (N : ℕ) (β : ℝ)
    (S : Finset (Lattice d)) (ω : Environment d) (hω : ω ∉ badBoxEvent e N β S) :
    ∀ x ∈ S, ENNReal.ofReal ((N:ℝ)^(-β)) ≤ crossingQuenched (realPosition (step e)) x N ω := by
  intro x hx
  have hh : (N:ℝ)^(-β) ≤ (crossingQuenched (realPosition (step e)) x N ω).toReal := by
    by_contra hh
    exact hω (Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,lt_of_not_ge hh⟩⟩)
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top (quenchedKernel (ω,x)) _)).mpr hh

lemma annealed_bound_bad_environment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (A : Set (Path d)) (hA : MeasurableSet A) (E : Set (Environment d)) (hE : MeasurableSet E)
    (c : ℝ≥0∞) (hc : ∀ᵐ ω ∂environmentLaw ν, ω ∉ E → quenchedKernel (ω,0) A ≤ c) :
    annealedLaw ν A ≤ environmentLaw ν E+c := by
  rw [annealed_apply ν hA]
  calc
    _ ≤ ∫⁻ ω, E.indicator (fun _ => (1:ℝ≥0∞)) ω+c ∂environmentLaw ν := by
      apply lintegral_mono_ae
      filter_upwards [hc] with ω hω
      by_cases he : ω ∈ E
      · simpa [he] using (prob_le_one (μ := quenchedKernel (ω,0)) (s := A)).trans (le_add_right le_rfl)
      · simpa [he] using hω he
    _ = _ := by rw [lintegral_add_left (measurable_const.indicator hE),lintegral_indicator hE]; simp

lemma annealed_crossingGap_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (N : ℕ) (hN : 0<N) (R : ℝ) :
    (annealedLaw ν).real (CrossingGap e N) ≤
      (annealedLaw ν).real (StripExcursion (realPosition (step e)) N R)+
      (2*⌈R⌉₊+1)^d*(environmentLaw ν).real (badCrossingEvent e (N+1) (1/2))+
      (1-((N+1:ℕ):ℝ)^(-(1/2:ℝ)))^(N+1) := by
  let δ := ENNReal.ofReal (((N+1:ℕ):ℝ)^(-(1/2:ℝ)))
  have hNr : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hd1 : ((N+1:ℕ):ℝ)^(-(1/2:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr (by norm_num)
  have hd0 : 0 ≤ ((N+1:ℕ):ℝ)^(-(1/2:ℝ)) := Real.rpow_nonneg (by positivity) _
  have hδ : δ ≤ 1 := by simpa [δ] using ENNReal.ofReal_le_ofReal hd1
  have hb := annealed_bound_bad_environment ν
    (CrossingGap e N \ StripExcursion (realPosition (step e)) N R)
    ((measurableSet_crossingGap e N).diff (measurableSet_stripExcursion _ _ _))
    (badBoxEvent e (N+1) (1/2) (latticeBox ⌈R⌉₊)) (measurableSet_badBoxEvent _ _ _ _)
    ((1-δ)^(N+1)) ?_
  · have hbr := ENNReal.toReal_mono (by finiteness) hb
    rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness),ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hδ (by norm_num),ENNReal.toReal_one,ENNReal.toReal_ofReal hd0] at hbr
    have hpart : (annealedLaw ν).real (CrossingGap e N) ≤
        (annealedLaw ν).real (StripExcursion (realPosition (step e)) N R)+
        (annealedLaw ν).real (CrossingGap e N \ StripExcursion (realPosition (step e)) N R) := by
      apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (show CrossingGap e N ⊆ StripExcursion (realPosition (step e)) N R ∪
          (CrossingGap e N \ StripExcursion (realPosition (step e)) N R) from fun X hx => by
          by_cases hh : X ∈ StripExcursion (realPosition (step e)) N R
          · exact Or.inl hh
          · exact Or.inr ⟨hx,hh⟩)))
      exact measureReal_union_le _ _
    have hbox := badBox_bound ν e (N+1) (1/2) (latticeBox (d := d) ⌈R⌉₊)
    rw [card_latticeBox] at hbox
    push_cast at hbox
    change (annealedLaw ν).real _ ≤ (environmentLaw ν).real _+_ at hbr
    linarith
  · filter_upwards [quenched_directionallyTransient_ae ν _ htrans] with ω ht hω
    apply quenched_crossingGap_confined ω e N hN R (↑(latticeBox (d := d) ⌈R⌉₊) : Set (Lattice d)) (fun y hy => latticeBox_of_signed_bound R y hy) (ht 0) δ
    intro y hy
    simpa only [δ,Nat.cast_add,Nat.cast_one] using good_box_crossing e _ _ _ ω hω y hy.1

end DirectionalTransience

end

end OAI
