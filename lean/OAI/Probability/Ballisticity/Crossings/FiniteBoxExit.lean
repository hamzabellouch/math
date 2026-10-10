import Mathlib
import OAI.Probability.Ballisticity.Estimates.DirectBridge
import OAI.Probability.Ballisticity.Estimates.VisitTrials

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma sum_visitCount {d : ℕ} (X : Path d) (B : Finset (Lattice d)) (n : ℕ)
    (hB : ∀ j < n, X j∈B) : ∑ y ∈ B, visitCount X y n=n := by
  simp only [visitCount]
  rw [Finset.sum_comm]
  have hh (j : ℕ) (hj : j∈Finset.range n) : (∑ y ∈ B, if X j=y then 1 else 0)=1 := by
    rw [Finset.sum_eq_single (X j)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · exact fun h => False.elim (h (hB j (Finset.mem_range.mp hj)))
  simp_rw [Finset.sum_congr rfl hh]
  simp

lemma visitCount_pigeonhole {d : ℕ} (X : Path d) (B : Finset (Lattice d)) (K T : ℕ)
    (hT : B.card*K ≤ T) (hB : ∀ j ≤ T, X j∈B) :
    ∃ y∈B, K < visitCount X y (T+1) := by
  by_contra hh
  push Not at hh
  have hc : (∑ y ∈ B, visitCount X y (T+1)) ≤ B.card*K := by
    simpa using Finset.sum_le_sum (s := B) (fun y hy => hh y hy)
  rw [sum_visitCount X B (T+1) (fun j hj => hB j (by omega))] at hc
  omega

def ConfinedUntil {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (T : ℕ) : Set (Path d) :=
  {X | X 0=x ∧ ∀ j ≤ T, X j∈S}

lemma measurableSet_confinedUntil {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (T : ℕ) :
    MeasurableSet (ConfinedUntil x S T) := by
  unfold ConfinedUntil
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (measurable_pi_apply j) (Set.to_countable S).measurableSet)

lemma confinedUntil_subset_visits {d : ℕ} (x : Lattice d) (S : Set (Lattice d))
    (B : Finset (Lattice d)) (hS : S⊆(B:Set (Lattice d))) (T K : ℕ) (hT : B.card*K ≤ T) :
    ConfinedUntil x S T ⊆ ⋃ y∈B, VisitReached x S y K := by
  intro X hX
  obtain ⟨y,hy,hc⟩ := visitCount_pigeonhole X B K T hT (fun j hj => hS (hX.2 j hj))
  obtain ⟨j,hj,hjy,hc⟩ := visitCount_exists X y (T+1) K hc
  refine Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨hy,Set.mem_iUnion.mpr ⟨j,?_⟩⟩⟩
  exact ⟨hX.1,hjy,fun i hi => hX.2 i (by omega),hc⟩

lemma visitReached_empty {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d)
    (hy : y∉S) (K : ℕ) : VisitReached x S y K=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro X hX
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
  have hh := hn.2.2.1 n le_rfl
  rw [hn.2.1] at hh
  exact hy hh

lemma quenched_confinedUntil_bound {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S : Set (Lattice d)) (B : Finset (Lattice d)) (hS : S⊆(B:Set (Lattice d)))
    (T K : ℕ) (hT : B.card*K ≤ T) (δ : ℝ) (hδ : δ ≤ 1)
    (hsuccess : ∀ y∈S, ∃ A : Set (Path d), MeasurableSet A ∧ Disjoint A (ReturnIn S y) ∧
      δ ≤ (quenchedKernel (ω,y)).real A) :
    (quenchedKernel (ω,x)).real (ConfinedUntil x S T)  ≤  B.card*(1-δ)^K := by
  calc
    _  ≤  (quenchedKernel (ω,x)).real (⋃ y∈B,VisitReached x S y K) :=
      measureReal_mono (confinedUntil_subset_visits x S B hS T K hT) (measure_ne_top _ _)
    _  ≤  ∑ y ∈ B,(quenchedKernel (ω,x)).real (VisitReached x S y K) := measureReal_biUnion_finset_le _ _
    _  ≤  _ := by
      apply (Finset.sum_le_sum (s := B) (fun y _ => ?_)).trans_eq
        (by simp : (∑ _ ∈ B,(1-δ)^K)=B.card*(1-δ)^K)
      by_cases hy : y∈S
      · obtain ⟨A,hA,hd,hp⟩ := hsuccess y hy
        exact visitReached_geometric ω x S y K A hA hd δ hp
      · rw [visitReached_empty x S y hy,measureReal_empty]
        exact pow_nonneg (by linarith) _

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def UpwardCross {d : ℕ} (e : Direction d) (y : Lattice d) (H : ℕ) : Set (Path d) :=
  (fun X : Path d => fun j => X (1+j)) ⁻¹' Cross (realPosition (step e)) (y+step e) H ∩
    wordCylinder y [e]

lemma measurableSet_upwardCross {d : ℕ} (e : Direction d) (y : Lattice d) (H : ℕ) :
    MeasurableSet (UpwardCross e y H) :=
  ((measurableSet_cross _ _ _).preimage (by fun_prop)).inter (measurableSet_wordCylinder _ _)

lemma quenched_upwardCross {d : ℕ} (ω : Environment d) (e : Direction d) (y : Lattice d) (H : ℕ) :
    quenchedKernel (ω,y) (UpwardCross e y H)= (ω y).1 e * crossingQuenched (realPosition (step e)) (y+step e) H ω := by
  have hh := quenched_prefix_future ω y (wordPath y [e]) (wordPath_zero y [e]) 1 (measurableSet_cross (realPosition (step e)) (y+step e) H)
  change quenchedKernel (ω,y) (UpwardCross e y H)=quenchedKernel (ω,y) (wordCylinder y [e]) *
    quenchedKernel (ω,y+step e) (Cross (realPosition (step e)) (y+step e) H) at hh
  rw [quenched_wordCylinder] at hh
  simpa [wordWeight,crossingQuenched] using hh

lemma upwardCross_no_return {d : ℕ} (e : Direction d) (y : Lattice d) (H : ℕ)
    (S : Set (Lattice d)) (hy : 0 ≤ signedHeight e y)
    (hS : ∀ z∈S, signedHeight e z < (H:ℤ)) :
    Disjoint (UpwardCross e y H) (ReturnIn S y) := by
  apply Set.disjoint_left.mpr
  intro X hX hr
  obtain ⟨n,hn,hny,hpre⟩ := hr
  obtain ⟨m,hmH,hmD⟩ := hX.1
  have hup : X 1=y+step e := by simpa only [wordPath] using hX.2 1 (by simp)
  have hn1 : 1 < n := by
    by_contra hh
    have he : n=1 := by omega
    have hh' := congrArg (signedHeight e) (hup.symm.trans (he ▸ hny))
    rw [signedHeight_add_step_self] at hh'
    omega
  simp only [signedHeight_projection,signedHeight_add_step_self] at hmH hmD
  push_cast at hmH hmD
  by_cases hmn : 1+m ≤ n
  · have hh := hS (X (1+m)) (hpre (1+m) hmn)
    have hh' : (signedHeight e (X (1+m)):ℝ) < H := by exact_mod_cast hh
    have hy' : (0:ℝ) ≤ signedHeight e y := by exact_mod_cast hy
    linarith
  · have hd := hmD (n-1) (by omega)
    rw [Nat.add_sub_of_le hn1.le,hny] at hd
    linarith

lemma upwardCross_success {d : ℕ} (ω : Environment d) (e : Direction d) (y : Lattice d)
    (H : ℕ) (κ : ℝ≥0) (hκ : κ ≤ (ω y).1 e) (a : ℝ)
    (ha : a ≤ (crossingQuenched (realPosition (step e)) (y+step e) H ω).toReal)
    (ha0 : 0 ≤ a) :
    (κ:ℝ)*a ≤ (quenchedKernel (ω,y)).real (UpwardCross e y H) := by
  rw [measureReal_def,quenched_upwardCross,ENNReal.toReal_mul,ENNReal.coe_toReal]
  exact mul_le_mul (by exact_mod_cast hκ) ha ha0 (by positivity)

lemma quenched_stripBox_exit_bound {d : ℕ} (ω : Environment d) (e : Direction d)
    (H : ℕ) (B : Finset (Lattice d)) (T K : ℕ) (hT : B.card*K ≤ T)
    (κ : ℝ≥0) (hκ : ∀ y f, κ ≤ (ω y).1 f) (a : ℝ) (ha0 : 0 ≤ a)
    (hδ : (κ:ℝ)*a ≤ 1)
    (hgood : ∀ y∈B, a ≤ (crossingQuenched (realPosition (step e)) (y+step e) H ω).toReal) :
    (quenchedKernel (ω,0)).real (ConfinedUntil 0 {y | y∈B ∧ 0 ≤ signedHeight e y ∧ signedHeight e y < (H:ℤ)} T)  ≤
      B.card*(1-(κ:ℝ)*a)^K := by
  apply quenched_confinedUntil_bound ω 0 _ B (fun _ h => h.1) T K hT _ hδ
  intro y hy
  exact ⟨UpwardCross e y H,measurableSet_upwardCross e y H,
    upwardCross_no_return e y H _ hy.2.1 (fun _ hz => hz.2.2),
    upwardCross_success ω e y H κ (hκ y e) a (hgood y hy.1) ha0⟩

end DirectionalTransience

end

end OAI
