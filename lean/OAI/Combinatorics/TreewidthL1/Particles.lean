import OAI.Combinatorics.TreewidthL1.Cuts

namespace OAI

universe treewidthLevel1 treewidthLevel2 treewidthLevel3

namespace BoundedTreewidthL1

section ParticleInvariant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pairUpdate (a : ι → ℝ) (i j : ι) (e : ℝ) (x : ι) : ℝ :=
  a x + (if x = i then (a i + a j) / 2 + e - a i else 0) +
    (if x = j then (a i + a j) / 2 - e - a j else 0)

/-- Finite update histories; there is no bound on the number of updates. -/
inductive ParticleReachable : (ι → ℝ) → Prop
  | zero : ParticleReachable (fun _ => 0)
  | step {a : ι → ℝ} (ha : ParticleReachable a)
      (i j : ι) (hij : i ≠ j) (e : ℝ) (he : |e| ≤ 1) :
      ParticleReachable (pairUpdate a i j e)

/-- The quadratic subset-sum invariant controlling particle bounds.
Subtractions are real. In particular the bound at the full set is exactly zero. -/
def ParticleInvariant (a : ι → ℝ) : Prop :=
  (∑ i, a i) = 0 ∧ ∀ I : Finset ι,
    (∑ i ∈ I, a i) ≤ (I.card : ℝ) * ((Fintype.card ι : ℝ) - I.card)

end ParticleInvariant

end BoundedTreewidthL1

namespace BoundedTreewidthL1

section ParticleInvariantProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_pairUpdate
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (i j : ι) (e : ℝ) (I : Finset ι) :
    (∑ x ∈ I, pairUpdate a i j e x) =
      (∑ x ∈ I, a x) +
        (if i ∈ I then (a i + a j) / 2 + e - a i else 0) +
        (if j ∈ I then (a i + a j) / 2 - e - a j else 0) := by
  simp [pairUpdate, Finset.sum_add_distrib]

lemma pairUpdate_swap
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (i j : ι) (e : ℝ) :
    pairUpdate a i j e = pairUpdate a j i (-e) := by
  funext x
  simp only [pairUpdate]
  split_ifs <;> ring

lemma ParticleInvariant.zero
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι] : ParticleInvariant (fun _ : ι => 0) := by
  constructor
  · simp
  · intro I
    simp only [Finset.sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (sub_nonneg.mpr (by exact_mod_cast Finset.card_le_univ I))

lemma ParticleInvariant.update_one {a : ι → ℝ} (ha : ParticleInvariant a)
    (i j : ι) (e : ℝ) (he : e ≤ 1) (I : Finset ι)
    (hi : i ∈ I) (hj : j ∉ I) :
    (∑ x ∈ I, pairUpdate a i j e x) ≤
      (I.card : ℝ) * ((Fintype.card ι : ℝ) - I.card) := by
  have hsmall := ha.2 (I.erase i)
  have hlarge := ha.2 (insert j I)
  have hsumsmall := Finset.sum_erase_add I a hi
  have hsumlarge := Finset.sum_insert (f := a) hj
  have hcsmall : ((I.erase i).card : ℝ) = (I.card : ℝ) - 1 := by
    have hc := Finset.card_erase_add_one hi
    have hcast : ((I.erase i).card : ℝ) + 1 = (I.card : ℝ) := by exact_mod_cast hc
    linarith
  have hclarge : ((insert j I).card : ℝ) = (I.card : ℝ) + 1 := by
    rw [Finset.card_insert_of_notMem hj]
    norm_cast
  rw [hcsmall] at hsmall
  rw [hclarge] at hlarge
  rw [sum_pairUpdate, ite_eq_left hi, ite_eq_right hj]
  nlinarith

lemma ParticleInvariant.update {a : ι → ℝ} (ha : ParticleInvariant a)
    (i j : ι) (_ : i ≠ j) (e : ℝ) (he : |e| ≤ 1) :
    ParticleInvariant (pairUpdate a i j e) := by
  constructor
  · rw [sum_pairUpdate]
    simp only [Finset.mem_univ, ↓reduceIte, ha.1]
    ring
  · intro I
    by_cases hi : i ∈ I
    · by_cases hj : j ∈ I
      · rw [sum_pairUpdate, ite_eq_left hi, ite_eq_left hj]
        have hI := ha.2 I
        linarith
      · exact ha.update_one i j e (abs_le.mp he).2 I hi hj
    · by_cases hj : j ∈ I
      · rw [pairUpdate_swap]
        exact ha.update_one j i (-e) (by have := (abs_le.mp he).1; linarith) I hj hi
      · simpa [sum_pairUpdate, hi, hj] using ha.2 I

theorem particle_reachable_invariant {a : ι → ℝ} (ha : ParticleReachable a) :
    ParticleInvariant a := by
  induction ha with
  | zero => exact ParticleInvariant.zero
  | step ha i j hij e he ih => exact ih.update i j hij e he

/-- Exact scalar bound used for the slopes AND absolute heights of particles. -/
theorem particle_reachable_abs_le {a : ι → ℝ} (ha : ParticleReachable a) (i : ι) :
    |a i| ≤ (Fintype.card ι : ℝ) - 1 := by
  have h := particle_reachable_invariant ha
  have hi := h.2 {i}
  have hc := h.2 (Finset.univ.erase i)
  have hsum := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
  have hcard : ((Finset.univ.erase i).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    have ht := Finset.card_erase_add_one (Finset.mem_univ i)
    simp only [Finset.card_univ] at ht
    have hcast : ((Finset.univ.erase i).card : ℝ) + 1 = (Fintype.card ι : ℝ) := by
      exact_mod_cast ht
    linarith
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at hi
  rw [hcard] at hc
  rw [h.1] at hsum
  exact abs_le.mpr ⟨by nlinarith, hi⟩

end ParticleInvariantProof

end BoundedTreewidthL1

namespace BoundedTreewidthL1

section FunctionParticles

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def functionPairUpdate (F : ι → V → ℝ) (i j : ι) (g : V → ℝ) :
    ι → V → ℝ :=
  fun x v => pairUpdate (fun t => F t v) i j (g v) x

inductive FunctionParticleReachable (d : V → V → ℝ) (L H : ℝ) :
    (ι → V → ℝ) → Prop
  | zero : FunctionParticleReachable d L H (fun _ _ => 0)
  | step {F : ι → V → ℝ} (hF : FunctionParticleReachable d L H F)
      (i j : ι) (hij : i ≠ j) (g : V → ℝ)
      (hLip : ∀ u v, |g u - g v| ≤ L * d u v)
      (hHeight : ∀ v, |g v| ≤ H) :
      FunctionParticleReachable d L H (functionPairUpdate F i j g)

lemma functionPairUpdate_left
    {ι : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype ι] [DecidableEq ι]
    (F : ι → V → ℝ) (i j : ι) (hij : i ≠ j)
    (g : V → ℝ) (v : V) :
    functionPairUpdate F i j g i v = (F i v + F j v) / 2 + g v := by
  simp [functionPairUpdate, pairUpdate, hij]

lemma functionPairUpdate_right
    {ι : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype ι] [DecidableEq ι]
    (F : ι → V → ℝ) (i j : ι) (hij : i ≠ j)
    (g : V → ℝ) (v : V) :
    functionPairUpdate F i j g j v = (F i v + F j v) / 2 - g v := by
  simp [functionPairUpdate, pairUpdate, Ne.symm hij]

lemma functionPairUpdate_other
    {ι : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype ι] [DecidableEq ι]
    (F : ι → V → ℝ) (i j x : ι)
    (hxi : x ≠ i) (hxj : x ≠ j) (g : V → ℝ) (v : V) :
    functionPairUpdate F i j g x v = F x v := by
  simp [functionPairUpdate, pairUpdate, hxi, hxj]

lemma functionPairUpdate_value_normalized
    {ι : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype ι] [DecidableEq ι]
    (F : ι → V → ℝ) (i j : ι)
    (g : V → ℝ) (v : V) (R : ℝ) :
    (fun x => functionPairUpdate F i j g x v / R) =
      pairUpdate (fun x => F x v / R) i j (g v / R) := by
  funext x
  simp only [functionPairUpdate, pairUpdate]
  split_ifs <;> ring

lemma functionPairUpdate_difference_normalized
    {ι : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype ι] [DecidableEq ι]
    (F : ι → V → ℝ) (i j : ι)
    (g : V → ℝ) (u v : V) (R : ℝ) :
    (fun x => (functionPairUpdate F i j g x u -
      functionPairUpdate F i j g x v) / R) =
      pairUpdate (fun x => (F x u - F x v) / R) i j ((g u - g v) / R) := by
  funext x
  simp only [functionPairUpdate, pairUpdate]
  split_ifs <;> ring

lemma function_particles_normalized_values {d : V → V → ℝ} {L H : ℝ}
    (hH : 0 < H) {F : ι → V → ℝ} (hF : FunctionParticleReachable d L H F)
    (v : V) : ParticleReachable (fun x => F x v / H) := by
  induction hF with
  | zero => simpa using (ParticleReachable.zero (ι := ι))
  | step hF i j hij g hLip hHeight ih =>
    rw [functionPairUpdate_value_normalized]
    apply ParticleReachable.step ih i j hij
    rw [abs_div, abs_of_pos hH]
    exact (div_le_one hH).mpr (hHeight v)

lemma function_particles_normalized_differences {d : V → V → ℝ} {L H : ℝ}
    {F : ι → V → ℝ} (hF : FunctionParticleReachable d L H F)
    (u v : V) (hR : 0 < L * d u v) :
    ParticleReachable (fun x => (F x u - F x v) / (L * d u v)) := by
  induction hF with
  | zero => simpa using (ParticleReachable.zero (ι := ι))
  | step hF i j hij g hLip hHeight ih =>
    rw [functionPairUpdate_difference_normalized]
    apply ParticleReachable.step ih i j hij
    rw [abs_div, abs_of_pos hR]
    exact (div_le_one hR).mpr (hLip u v)

theorem function_particles_height_bound {d : V → V → ℝ} {L H : ℝ}
    (hH : 0 < H) {F : ι → V → ℝ} (hF : FunctionParticleReachable d L H F)
    (i : ι) (v : V) : |F i v| ≤ H * ((Fintype.card ι : ℝ) - 1) := by
  have hb := particle_reachable_abs_le (function_particles_normalized_values hH hF v) i
  rw [abs_div, abs_of_pos hH] at hb
  simpa [mul_comm] using (div_le_iff₀ hH).mp hb

theorem function_particles_difference_bound {d : V → V → ℝ} {L H : ℝ}
    (hL : 0 < L) {F : ι → V → ℝ} (hF : FunctionParticleReachable d L H F)
    (i : ι) (u v : V) (hd : 0 < d u v) :
    |F i u - F i v| ≤ L * ((Fintype.card ι : ℝ) - 1) * d u v := by
  have hR := mul_pos hL hd
  have hb := particle_reachable_abs_le (function_particles_normalized_differences hF u v hR) i
  rw [abs_div, abs_of_pos hR] at hb
  simpa [mul_assoc, mul_comm, mul_left_comm] using (div_le_iff₀ hR).mp hb

theorem function_particles_metric_bound [MetricSpace V] {L H : ℝ}
    (hL : 0 < L) {F : ι → V → ℝ} (hF : FunctionParticleReachable dist L H F)
    (i : ι) (u v : V) :
    |F i u - F i v| ≤ L * ((Fintype.card ι : ℝ) - 1) * dist u v := by
  by_cases huv : u = v
  · simp [huv]
  · exact function_particles_difference_bound hL hF i u v (dist_pos.mpr huv)

end FunctionParticles

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory
open scoped ENNReal
variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- The exact zero-error combined symmetric trace carried by a particle list. -/
noncomputable def particleTrace (M : ℝ) (F : ι → V → ℝ) (P : Finset V) :
    Measure (P → Bool) := ∑ i, cutTrace (symmetrizeCut (sweep M (F i))) P

/-- Any reservation set of size at most `2q`
leaves two particles with a common weak order, and the actual affine update
preserves the complete bag law and every reserved function. The pair is chosen
before the perturbation; the universal quantifier on g expresses that fact. -/
lemma exists_weak_order
    {V : Type treewidthLevel1} [Fintype V]
    (P : Finset V) (F : V → ℝ) :
    ∃ e : Fin P.card ≃ P, Monotone (fun i => F (e i)) := by
  classical
  let code := Fintype.equivFin P
  let enc : P → Lex (ℝ × Fin (Fintype.card P)) := fun p => toLex (F p, code p)
  have hinj : Function.Injective enc := by
    intro p q h
    exact code.injective (congrArg (fun z : Lex (ℝ × Fin (Fintype.card P)) => (ofLex z).2) h)
  let : LinearOrder P := LinearOrder.lift' enc hinj
  let e := Fintype.orderIsoFinOfCardEq P (by simp : Fintype.card P = P.card)
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  have h := e.monotone hij
  change enc (e i) ≤ enc (e j) at h
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

lemma free_common_order (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : Finset V) (hP : P.card ≤ k) (R : Finset ι) (hR : R.card ≤ 2*q)
    (F : ι → V → ℝ) :
    ∃ i j : ι, i ∉ R ∧ j ∉ R ∧ i ≠ j ∧ CommonWeakOrder P (F i) (F j) := by
  classical
  let S := Finset.univ \ R
  have hc : k.factorial < S.card := by
    have hs : S.card + R.card = Fintype.card ι := by
      simpa [S] using Finset.card_sdiff_add_card_inter Finset.univ R
    omega
  choose order horder using fun i : S => exists_weak_order P (F i)
  have hcard : Fintype.card (Fin P.card ≃ P) < Fintype.card S := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp) : Fin P.card ≃ P)]
    simpa using (Nat.factorial_le hP).trans_lt hc
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt order hcard
  refine ⟨i, j, (Finset.mem_sdiff.mp i.property).2,
    (Finset.mem_sdiff.mp j.property).2, ?_, order i, horder i, ?_⟩
  · exact fun h => hij (Subtype.ext h)
  · rw [heq]
    exact horder j

lemma cutTrace_symmetrize (μ : Measure (V → Bool)) (P : Finset V) :
    cutTrace (symmetrizeCut μ) P = symmetrizeCut (cutTrace μ P) := by
  classical
  unfold cutTrace symmetrizeCut
  rw [Measure.map_smul _ (measurable_of_finite _).aemeasurable, Measure.map_add _ _ (measurable_of_finite _),
    Measure.map_map (measurable_of_finite _) measurable_complementCut,
    Measure.map_map measurable_complementCut (measurable_of_finite _)]
  rfl

lemma symmetrize_add (μ ν : Measure (V → Bool)) :
    symmetrizeCut (μ + ν) = symmetrizeCut μ + symmetrizeCut ν := by
  unfold symmetrizeCut
  rw [Measure.map_add _ _ measurable_complementCut]
  simp [smul_add, add_assoc, add_left_comm]

lemma sum_eq_of_pair {A : Type*} [AddCommMonoid A] (a b : ι → A)
    (i j : ι) (hij : i ≠ j) (hpair : a i + a j = b i + b j)
    (hother : ∀ r, r ≠ i → r ≠ j → a r = b r) : (∑ r, a r) = ∑ r, b r := by
  classical
  let S : Finset ι := {i,j}
  have hs : (∑ r ∈ S, a r) = ∑ r ∈ S, b r := by
    simpa [S, hij] using hpair
  have ht : (∑ r ∈ Sᶜ, a r) = ∑ r ∈ Sᶜ, b r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r ≠ i ∧ r ≠ j := by simpa [S] using hr
    exact hother r hr'.1 hr'.2
  rw [← Finset.sum_add_sum_compl S a, ←Finset.sum_add_sum_compl S b, hs, ht]

lemma particleTrace_update (M : ℝ) (hM : 0 < M) (F : ι → V → ℝ)
    (i j : ι) (hij : i ≠ j) (g : V → ℝ) (P : Finset V)
    (horder : CommonWeakOrder P (F i) (F j)) (hg : ∀ s ∈ P, g s = 0)
    (hF : ∀ r v, |F r v| ≤ M)
    (hF' : ∀ r v, |functionPairUpdate F i j g r v| ≤ M) :
    particleTrace M F P = particleTrace M (functionPairUpdate F i j g) P := by
  apply sum_eq_of_pair _ _ i j hij
  · simp only [cutTrace_symmetrize, ←symmetrize_add, ←cutTrace_add]
    apply congrArg symmetrizeCut
    have hi : functionPairUpdate F i j g i = fun v => (F i v + F j v)/2 + g v := by
      funext v; exact functionPairUpdate_left F i j hij g v
    have hj : functionPairUpdate F i j g j = fun v => (F i v + F j v)/2 - g v := by
      funext v; exact functionPairUpdate_right F i j hij g v
    rw [hi, hj]
    exact sweep_trace_update M hM (F i) (F j) g P horder hg (hF i) (hF j)
      (by simpa only [hi] using hF' i) (by simpa only [hj] using hF' j)
  · intro r hri hrj
    have hr : functionPairUpdate F i j g r = F r := by
      funext v; exact functionPairUpdate_other F i j r hri hrj g v
    rw [hr]

theorem particle_step_realization (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : Finset V) (hP : P.card ≤ k) (R : Finset ι) (hR : R.card ≤ 2*q)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (F : ι → V → ℝ) (hF : FunctionParticleReachable d L H F) :
    ∃ i j : ι, i ∉ R ∧ j ∉ R ∧ i ≠ j ∧ CommonWeakOrder P (F i) (F j) ∧
      ∀ g : V → ℝ, (∀ u v, |g u - g v| ≤ L * d u v) →
        (∀ v, |g v| ≤ H) → (∀ s ∈ P, g s = 0) →
        let F' := functionPairUpdate F i j g
        let M := H * ((Fintype.card ι : ℝ)-1) + 2*Δ
        FunctionParticleReachable d L H F' ∧
        (∀ r ∈ R, F' r = F r) ∧
        particleTrace M F P = particleTrace M F' P ∧
        (∀ r v, |F' r v| + 2*Δ ≤ M) := by
  classical
  obtain ⟨i, j, hi, hj, hij, ho⟩ := free_common_order k q hN P hP R hR F
  refine ⟨i, j, hi, hj, hij, ho, ?_⟩
  intro g hLip hHeight hg
  dsimp only
  have hF' := FunctionParticleReachable.step hF i j hij g hLip hHeight
  have hmarg : ∀ r v, |functionPairUpdate F i j g r v| + 2*Δ ≤
      H * ((Fintype.card ι : ℝ)-1) + 2*Δ := by
    intro r v
    have := function_particles_height_bound hH hF' r v
    linarith
  refine ⟨hF', ?_, ?_, hmarg⟩
  · intro r hr
    funext v
    exact functionPairUpdate_other F i j r (fun h => hi (h ▸ hr))
      (fun h => hj (h ▸ hr)) g v
  · have hcard : (1 : ℝ) ≤ Fintype.card ι := by
      have hn : 1 ≤ Fintype.card ι := by omega
      exact_mod_cast hn
    have hM : 0 < H * ((Fintype.card ι : ℝ)-1) + 2*Δ := by
      have := mul_nonneg hH.le (sub_nonneg.mpr hcard)
      linarith
    apply particleTrace_update _ hM F i j hij g P ho hg
    · intro r v
      have := function_particles_height_bound hH hF r v
      linarith
    · intro r v
      have := function_particles_height_bound hH hF' r v
      linarith
end BoundedTreewidthL1

namespace BoundedTreewidthL1

structure ReservationPath where
  last : ℕ
  finish : ℕ → ℕ
  launch_le_finish : ∀ a, a ≤ last → a ≤ finish a
  finish_le_last : ∀ a, a ≤ last → finish a ≤ last
  one_release : ∀ a b t, a ≤ t → b ≤ t → t < last →
    finish a = t → finish b = t → a = b
  root_permanent : finish 0 = last
namespace ReservationPath
noncomputable def inclusive (P : ReservationPath) (t : ℕ) : Finset ℕ := by
  classical
  exact if t ≤ P.last then (Finset.range (t + 1)).filter (fun a => t ≤ P.finish a) else ∅
end ReservationPath
end BoundedTreewidthL1

namespace BoundedTreewidthL1.ParticleSchedule
open MeasureTheory
variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def before (R : ReservationPath) (t : ℕ) : Finset ℕ :=
  (R.inclusive t).filter (fun a => a < t)

noncomputable def occupied (C : Finset ℕ) (p : ℕ → ι × ι) : Finset ι := by
  classical
  exact C.image (fun a => (p a).1) ∪ C.image (fun a => (p a).2)

/-- A deterministic pair selection using only pre-launch data. Classical choice
here is a fixed function of the finite eligible-pair set, not of the fresh noise. -/
noncomputable def pickPair (P : Finset V) (C : Finset ι) (F : ι → V → ℝ) : ι × ι := by
  classical
  exact if h : ∃ p : ι × ι, p.1 ∉ C ∧ p.2 ∉ C ∧ p.1 ≠ p.2 ∧
      CommonWeakOrder P (F p.1) (F p.2) then h.choose
    else (Classical.choice inferInstance, Classical.choice inferInstance)

def RunEquations (R : ReservationPath) (P : ℕ → Finset V) (g : ℕ → V → ℝ)
    (n : ℕ) (F : ℕ → ι → V → ℝ) (p : ℕ → ι × ι) : Prop :=
  F 0 = (fun _ _ => 0) ∧ ∀ t < n,
    p t = pickPair (P t) (occupied (before R t) p) (F t) ∧
    F (t+1) = functionPairUpdate (F t) (p t).1 (p t).2 (g t)

lemma occupied_card
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C : Finset ℕ) (p : ℕ → ι × ι) :
    (occupied C p).card ≤ 2*C.card := by
  classical
  exact (Finset.card_union_le _ _).trans (by
    have h1 := Finset.card_image_le (s := C) (f := fun a => (p a).1)
    have h2 := Finset.card_image_le (s := C) (f := fun a => (p a).2)
    omega)

lemma occupied_update
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {C : Finset ℕ} (p : ℕ → ι × ι) (n : ℕ) (z : ι × ι)
    (hn : ∀ a ∈ C, a < n) : occupied C (Function.update p n z) = occupied C p := by
  classical
  unfold occupied
  congr 1 <;> apply Finset.image_congr <;> intro a ha <;>
    simp [Function.update_of_ne (ne_of_lt (hn a ha))]

lemma pickPair_spec (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : Finset V) (hP : P.card ≤ k) (C : Finset ι) (hC : C.card ≤ 2*q)
    (F : ι → V → ℝ) :
    let z := pickPair P C F
    z.1 ∉ C ∧ z.2 ∉ C ∧ z.1 ≠ z.2 ∧ CommonWeakOrder P (F z.1) (F z.2) := by
  classical
  obtain ⟨i,j,hi,hj,hij,ho⟩ := free_common_order k q hN P hP C hC F
  have hex : ∃ p : ι × ι, p.1 ∉ C ∧ p.2 ∉ C ∧ p.1 ≠ p.2 ∧
      CommonWeakOrder P (F p.1) (F p.2) := ⟨(i,j),hi,hj,hij,ho⟩
  simpa only [pickPair,dite_eq_left hex] using hex.choose_spec

lemma finite_run
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    (R : ReservationPath) (P : ℕ → Finset V) (g : ℕ → V → ℝ) (n : ℕ) :
    ∃ F : ℕ → ι → V → ℝ, ∃ p : ℕ → ι × ι, RunEquations R P g n F p := by
  classical
  induction n with
  | zero =>
    exact ⟨fun _ _ _ => 0, fun _ => (Classical.choice inferInstance,Classical.choice inferInstance),
      rfl,fun t ht => (Nat.not_lt_zero t ht).elim⟩
  | succ n ih =>
    obtain ⟨F,p,hzero,hsteps⟩ := ih
    let z := pickPair (P n) (occupied (before R n) p) (F n)
    let p' := Function.update p n z
    let F' := Function.update F (n+1) (functionPairUpdate (F n) z.1 z.2 (g n))
    refine ⟨F',p',?_,?_⟩
    · simpa [F'] using hzero
    · intro t ht
      have htn : t ≤ n := Nat.le_of_lt_succ ht
      have hoc : occupied (before R t) p' = occupied (before R t) p := by
        apply occupied_update
        intro a ha
        exact (Finset.mem_filter.mp ha).2.trans_le htn
      rw [hoc]
      by_cases hte : t = n
      · subst t
        simp [p',F',z]
      · have htn' : t < n := lt_of_le_of_ne htn hte
        have hne₁ : t ≠ n+1 := by omega
        have hne₂ : t+1 ≠ n+1 := by omega
        simpa only [p',F',Function.update_of_ne hte,Function.update_of_ne hne₁,
          Function.update_of_ne hne₂] using hsteps t htn'

theorem scheduled_particle_realization (R : ReservationPath)
    (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : ℕ → Finset V) (hP : ∀ t ≤ R.last, (P t).card ≤ k)
    (hsize : ∀ t, (R.inclusive t).card ≤ q)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : ℕ → V → ℝ)
    (hLip : ∀ t ≤ R.last, ∀ u v, |g t u - g t v| ≤ L * d u v)
    (hHeight : ∀ t ≤ R.last, ∀ v, |g t v| ≤ H)
    (hvanish : ∀ t ≤ R.last, ∀ v ∈ P t, g t v = 0) :
    ∃ F : ℕ → ι → V → ℝ, ∃ p : ℕ → ι × ι,
      RunEquations R P g (R.last+1) F p ∧
      (∀ t ≤ R.last+1, FunctionParticleReachable d L H (F t)) ∧
      (∀ t ≤ R.last, (p t).1 ≠ (p t).2 ∧
        particleTrace (H * ((Fintype.card ι : ℝ)-1) + 2*Δ) (F t) (P t) =
        particleTrace (H * ((Fintype.card ι : ℝ)-1) + 2*Δ) (F (t+1)) (P t)) ∧
      (∀ t ≤ R.last, ∀ a ∈ R.inclusive t,
        F (t+1) (p a).1 = F (a+1) (p a).1 ∧
        F (t+1) (p a).2 = F (a+1) (p a).2) := by
  classical
  obtain ⟨F,p,hrun⟩ := finite_run (ι := ι) R P g (R.last+1)
  have hs (t : ℕ) (ht : t ≤ R.last) :
      (p t).1 ∉ occupied (before R t) p ∧ (p t).2 ∉ occupied (before R t) p ∧
      (p t).1 ≠ (p t).2 ∧ CommonWeakOrder (P t) (F t (p t).1) (F t (p t).2) := by
    have hc : (occupied (before R t) p).card ≤ 2*q := by
      have h1 := occupied_card (before R t) p
      have h2 : (before R t).card ≤ (R.inclusive t).card := Finset.card_filter_le _ _
      have h3 := hsize t
      omega
    have hh := pickPair_spec k q hN (P t) (hP t ht) (occupied (before R t) p) hc (F t)
    dsimp only at hh
    rw [← (hrun.2 t (by omega)).1] at hh
    exact hh
  have hreach : ∀ t ≤ R.last+1, FunctionParticleReachable d L H (F t) := by
    intro t
    induction t with
    | zero => intro _; rw [hrun.1]; exact .zero
    | succ t ih =>
      intro ht
      have htL : t ≤ R.last := by omega
      rw [(hrun.2 t (by omega)).2]
      exact .step (ih (by omega)) _ _ (hs t htL).2.2.1 (g t) (hLip t htL) (hHeight t htL)
  have hretain (t : ℕ) (ht : t ≤ R.last) (a : ℕ) (ha : a ∈ R.inclusive t) (hat : a < t) :
      F (t+1) (p a).1 = F t (p a).1 ∧ F (t+1) (p a).2 = F t (p a).2 := by
    have hab : a ∈ before R t := Finset.mem_filter.mpr ⟨ha,hat⟩
    have h1 : (p a).1 ∈ occupied (before R t) p :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,hab,rfl⟩)
    have h2 : (p a).2 ∈ occupied (before R t) p :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,hab,rfl⟩)
    have hei (r : ι) (hr : r ∈ occupied (before R t) p) : r ≠ (p t).1 ∧ r ≠ (p t).2 := by
      constructor
      · intro he; exact (hs t ht).1 (he ▸ hr)
      · intro he; exact (hs t ht).2.1 (he ▸ hr)
    rw [(hrun.2 t (by omega)).2]
    constructor <;> funext x
    · exact functionPairUpdate_other _ _ _ _ (hei _ h1).1 (hei _ h1).2 _ x
    · exact functionPairUpdate_other _ _ _ _ (hei _ h2).1 (hei _ h2).2 _ x
  refine ⟨F,p,hrun,hreach,?_,?_⟩
  · intro t ht
    refine ⟨(hs t ht).2.2.1,?_⟩
    have hc : (1 : ℝ) ≤ Fintype.card ι := by
      have hh : 1 ≤ Fintype.card ι := by omega
      exact_mod_cast hh
    have hM : 0 < H * ((Fintype.card ι : ℝ)-1) + 2*Δ := by
      have hh := mul_nonneg hH.le (sub_nonneg.mpr hc)
      linarith
    have hb (s : ℕ) (hsl : s ≤ R.last+1) : ∀ r x,
        |F s r x| ≤ H * ((Fintype.card ι : ℝ)-1) + 2*Δ := by
      intro r x
      have hh := function_particles_height_bound hH (hreach s hsl) r x
      linarith
    rw [(hrun.2 t (by omega)).2]
    apply particleTrace_update _ hM _ _ _ (hs t ht).2.2.1 _ _ (hs t ht).2.2.2
      (hvanish t ht) (hb t (by omega))
    rw [← (hrun.2 t (by omega)).2]
    exact hb (t+1) (by omega)
  · intro t
    induction t with
    | zero =>
      intro ht a ha
      have ha0 : a = 0 := by
        simpa [ReservationPath.inclusive,ht] using (Finset.mem_filter.mp
          (show a ∈ (Finset.range 1).filter (fun a => 0 ≤ R.finish a) by
            simpa [ReservationPath.inclusive,ht] using ha)).1
      subst a
      exact ⟨rfl,rfl⟩
    | succ t ih =>
      intro ht a ha
      have hmem : a ≤ t+1 ∧ t+1 ≤ R.finish a := by
        simpa [ReservationPath.inclusive,ht,Nat.lt_succ_iff] using ha
      by_cases he : a = t+1
      · subst a; exact ⟨rfl,rfl⟩
      · have hat : a < t+1 := by omega
        have ht' : t ≤ R.last := by omega
        have ha' : a ∈ R.inclusive t := by
          simp [ReservationPath.inclusive,ht']
          omega
        have hh := hretain (t+1) ht a ha hat
        exact ⟨hh.1.trans (ih ht' a ha').1,hh.2.trans (ih ht' a ha').2⟩
end BoundedTreewidthL1.ParticleSchedule

namespace BoundedTreewidthL1.ParticleSchedule
open MeasureTheory
variable {V ι Ω : Type*} [Fintype V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma measurable_weak_order
    {V : Type treewidthLevel1} {Ω : Type treewidthLevel2} [Fintype V] [MeasurableSpace Ω]
    (P : Finset V) (F H : Ω → V → ℝ)
    (hF : ∀ v, Measurable (fun ω => F ω v))
    (hH : ∀ v, Measurable (fun ω => H ω v)) :
    MeasurableSet {ω | CommonWeakOrder P (F ω) (H ω)} := by
  classical
  simp only [CommonWeakOrder, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro e
  have hmono (A : Ω → V → ℝ) (hA : ∀ v, Measurable (fun ω => A ω v)) :
      MeasurableSet {ω | Monotone (fun i : Fin P.card => A ω (e i))} := by
    simp only [Monotone, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_le (hA _) (hA _)
  exact (hmono F hF).inter (hmono H hH)

noncomputable def selectEligible (Q : ι × ι → Prop) : ι × ι := by
  classical
  exact if h : ∃ p, Q p then h.choose else
    (Classical.choice inferInstance, Classical.choice inferInstance)

lemma measurable_selectEligible
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] : Measurable (selectEligible (ι := ι)) :=
  measurable_of_finite _

lemma measurable_eligibility
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} {Ω : Type treewidthLevel3} [Fintype V]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (P : Finset V) (C : Ω → Finset ι) (F : Ω → ι → V → ℝ)
    (hC : Measurable C) (hF : ∀ i v, Measurable (fun ω => F ω i v)) :
    Measurable (fun ω => fun p : ι × ι =>
      p.1 ∉ C ω ∧ p.2 ∉ C ω ∧ p.1 ≠ p.2 ∧
        CommonWeakOrder P (F ω p.1) (F ω p.2)) := by
  classical
  apply measurable_pi_iff.mpr
  intro p
  apply measurableSet_setOfPred.mp
  have hmem (i : ι) : MeasurableSet {ω | i ∈ C ω} :=
    measurableSet_setOfPred.mpr ((measurable_finset_mem i).comp hC)
  have hneq : MeasurableSet {ω : Ω | p.1 ≠ p.2} := by
    by_cases h : p.1 = p.2 <;> simp [h]
  exact (hmem p.1).compl.inter ((hmem p.2).compl.inter
    (hneq.inter (measurable_weak_order P _ _ (hF p.1) (hF p.2))))

lemma pickPair_eq_selectEligible
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Finset V) (C : Finset ι) (F : ι → V → ℝ) :
    pickPair P C F = selectEligible (fun p : ι × ι =>
      p.1 ∉ C ∧ p.2 ∉ C ∧ p.1 ≠ p.2 ∧ CommonWeakOrder P (F p.1) (F p.2)) := by
  classical
  unfold pickPair selectEligible
  split_ifs <;> rfl

lemma measurable_pickPair (P : Finset V) (C : Ω → Finset ι) (F : Ω → ι → V → ℝ)
    (hC : Measurable C) (hF : ∀ i v, Measurable (fun ω => F ω i v)) :
    Measurable (fun ω => pickPair P (C ω) (F ω)) := by
  simp_rw [pickPair_eq_selectEligible]
  exact measurable_selectEligible.comp (measurable_eligibility P C F hC hF)

lemma measurable_occupied
    {ι : Type treewidthLevel1} {Ω : Type treewidthLevel2} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (C : Finset ℕ) (p : Ω → ℕ → ι × ι)
    (hp : ∀ a ∈ C, Measurable (fun ω => p ω a)) :
    Measurable (fun ω => occupied C (p ω)) := by
  classical
  apply measurable_finset_iff.mpr
  intro i
  apply measurableSet_setOfPred.mp
  simp only [occupied, Finset.mem_union, Finset.mem_image, Set.ofPred_or,
    Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  all_goals
    apply MeasurableSet.iUnion
    intro a
    by_cases ha : a ∈ C
    · simp only [ha, Set.ofPred_true, Set.univ_inter]
      first | exact measurableSet_eq_fun (hp a ha).fst measurable_const
            | exact measurableSet_eq_fun (hp a ha).snd measurable_const
    · simp [ha]

lemma measurable_selected
    {ι : Type treewidthLevel1} {Ω : Type treewidthLevel2} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (F : Ω → ι → ℝ) (q : Ω → ι)
    (hF : ∀ i, Measurable (fun ω => F ω i)) (hq : Measurable q) :
    Measurable (fun ω => F ω (q ω)) := by
  classical
  have heq : (fun ω => F ω (q ω)) =
      (fun ω => ∑ i : ι, if q ω = i then F ω i else 0) := by
    funext ω
    simp
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact (hF i).ite (measurableSet_eq_fun hq measurable_const) measurable_const

lemma measurable_pairUpdate
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} {Ω : Type treewidthLevel3} [Fintype V]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (F : Ω → ι → V → ℝ) (p : Ω → ι × ι)
    (g : Ω → V → ℝ) (hF : ∀ i v, Measurable (fun ω => F ω i v))
    (hp : Measurable p) (hg : ∀ v, Measurable (fun ω => g ω v)) (i : ι) (v : V) :
    Measurable (fun ω => functionPairUpdate (F ω) (p ω).1 (p ω).2 (g ω) i v) := by
  classical
  have hleft := measurable_selected (fun ω j => F ω j v) (fun ω => (p ω).1)
    (fun j => hF j v) hp.fst
  have hright := measurable_selected (fun ω j => F ω j v) (fun ω => (p ω).2)
    (fun j => hF j v) hp.snd
  have hmean := (hleft.add hright).div_const 2
  dsimp only [functionPairUpdate, pairUpdate]
  exact ((hF i v).add (((hmean.add (hg v)).sub hleft).ite
    (measurableSet_eq_fun measurable_const hp.fst) measurable_const)).add
    (((hmean.sub (hg v)).sub hright).ite
      (measurableSet_eq_fun measurable_const hp.snd) measurable_const)

/-- Measurability follows from the deterministic causal equations, for EVERY
pointwise realization. There is no assertion that an arbitrary choice operator
on an infinite real-valued space is measurable. -/
lemma run_measurable (R : ReservationPath) (P : ℕ → Finset V)
    (g : Ω → ℕ → V → ℝ) (hg : ∀ t v, Measurable (fun ω => g ω t v)) (n : ℕ)
    (F : Ω → ℕ → ι → V → ℝ) (p : Ω → ℕ → ι × ι)
    (hrun : ∀ ω, RunEquations R P (g ω) n (F ω) (p ω)) :
    (∀ t ≤ n, ∀ i v, Measurable (fun ω => F ω t i v)) ∧
    (∀ t < n, Measurable (fun ω => p ω t)) := by
  classical
  have hi : ∀ t ≤ n,
      (∀ i v, Measurable (fun ω => F ω t i v)) ∧
      (∀ a < t, Measurable (fun ω => p ω a)) := by
    intro t
    induction t with
    | zero =>
      intro _
      constructor
      · intro i v
        have heq : (fun ω => F ω 0 i v) = (fun _ => 0) := by
          funext ω
          rw [(hrun ω).1]
        rw [heq]
        exact measurable_const
      · intro a ha
        omega
    | succ t ih =>
      intro ht
      obtain ⟨hF, hp⟩ := ih (by omega)
      have htn : t < n := by omega
      have hcurrent : Measurable (fun ω => p ω t) := by
        have heq : (fun ω => p ω t) =
            (fun ω => pickPair (P t) (occupied (before R t) (p ω)) (F ω t)) := by
          funext ω
          exact ((hrun ω).2 t htn).1
        rw [heq]
        apply measurable_pickPair _ _ _ _ hF
        apply measurable_occupied
        intro a ha
        exact hp a (Finset.mem_filter.mp ha).2
      constructor
      · intro i v
        have heq : (fun ω => F ω (t+1) i v) =
            (fun ω => functionPairUpdate (F ω t) (p ω t).1 (p ω t).2 (g ω t) i v) := by
          funext ω
          rw [((hrun ω).2 t htn).2]
        rw [heq]
        exact measurable_pairUpdate _ _ _ hF hcurrent (hg t) i v
      · intro a ha
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ha) with h | h
        · exact hp a h
        · simpa [h] using hcurrent
  exact ⟨fun t ht => (hi t ht).1, fun t ht => (hi n le_rfl).2 t ht⟩

theorem measurable_particle_run (R : ReservationPath) (P : ℕ → Finset V)
    (g : Ω → ℕ → V → ℝ) (hg : ∀ t v, Measurable (fun ω => g ω t v)) (n : ℕ) :
    ∃ F : Ω → ℕ → ι → V → ℝ, ∃ p : Ω → ℕ → ι × ι,
      (∀ ω, RunEquations R P (g ω) n (F ω) (p ω)) ∧
      (∀ t ≤ n, ∀ i v, Measurable (fun ω => F ω t i v)) ∧
      (∀ t < n, Measurable (fun ω => p ω t)) := by
  classical
  choose F p hrun using (fun ω => finite_run (ι := ι) R P (g ω) n)
  exact ⟨F, p, hrun, run_measurable R P g hg n F p hrun⟩
end BoundedTreewidthL1.ParticleSchedule

namespace BoundedTreewidthL1.ParticleSchedule
open MeasureTheory Set
variable {V ι Ω : Type*} [Fintype V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma measurable_threshold_joint
    {V : Type treewidthLevel1} {Ω : Type treewidthLevel2} [Fintype V] [MeasurableSpace Ω]
    (F : Ω → V → ℝ)
    (hF : ∀ v, Measurable (fun ω => F ω v)) :
    Measurable (fun z : Ω × ℝ => thresholdLabels (F z.1) z.2) := by
  classical
  apply measurable_pi_iff.mpr
  intro v
  have h : Measurable (fun z : Ω × ℝ => if z.2 < F z.1 v then true else false) :=
    measurable_const.ite (measurableSet_lt measurable_snd ((hF v).comp measurable_fst))
      measurable_const
  convert h using 1
  ext z
  simp [thresholdLabels]

lemma measurable_sweep_real (M : ℝ) (F : Ω → V → ℝ)
    (hF : ∀ v, Measurable (fun ω => F ω v)) (S : Set (V → Bool)) :
    Measurable (fun ω => (sweep M (F ω)).real S) := by
  have hs := (measurable_threshold_joint F hF) ((Set.toFinite S).measurableSet)
  have hm := measurable_measure_prodMk_left
    (ν := volume.restrict (Icc (-M) M)) hs
  convert hm.ennreal_toReal using 1
  funext ω
  rw [sweep, map_measureReal_apply (measurable_thresholdLabels _) (Set.toFinite S).measurableSet]
  rfl

lemma measurable_symmetrize_sweep_real (M : ℝ) (F : Ω → V → ℝ)
    (hF : ∀ v, Measurable (fun ω => F ω v)) (S : Set (V → Bool)) :
    Measurable (fun ω => (symmetrizeCut (sweep M (F ω))).real S) := by
  have heq (ω : Ω) : (symmetrizeCut (sweep M (F ω))).real S =
      (1/2 : ℝ) * ((sweep M (F ω)).real S +
        (sweep M (F ω)).real (complementCut ⁻¹' S)) := by
    rw [symmetrizeCut, measureReal_ennreal_smul_apply,
      measureReal_add_apply (by finiteness) (by finiteness),
      map_measureReal_apply measurable_complementCut (Set.toFinite S).measurableSet]
    norm_num
  simp_rw [heq]
  exact ((measurable_sweep_real M F hF S).add
    (measurable_sweep_real M F hF _)).const_mul _

instance finite_cutTrace (μ : Measure (V → Bool)) [IsFiniteMeasure μ] (P : Finset V) :
    IsFiniteMeasure (cutTrace μ P) := by
  unfold cutTrace
  infer_instance

instance finite_particleTrace (M : ℝ) (F : ι → V → ℝ) (P : Finset V) :
    IsFiniteMeasure (particleTrace M F P) := by
  unfold particleTrace cutTrace
  infer_instance

lemma particle_real_sum
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    {A : Type*} [MeasurableSpace A] (μ : ι → Measure A)
    [∀ i, IsFiniteMeasure (μ i)] (S : Set A) :
    (∑ i, μ i).real S = ∑ i, (μ i).real S := by
  simp only [measureReal_def, Measure.finsetSum_apply]
  exact ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)

lemma measurable_particleTrace_real (M : ℝ) (F : Ω → ι → V → ℝ)
    (hF : ∀ i v, Measurable (fun ω => F ω i v))
    (P : Finset V) (S : Set (P → Bool)) :
    Measurable (fun ω => (particleTrace M (F ω) P).real S) := by
  have heq (ω : Ω) : (particleTrace M (F ω) P).real S =
      ∑ i, (symmetrizeCut (sweep M (F ω i))).real
        ((fun a : V → Bool => fun v : P => a v) ⁻¹' S) := by
    rw [particleTrace, particle_real_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact map_measureReal_apply (measurable_of_finite _) (Set.toFinite S).measurableSet
  simp_rw [heq]
  apply Finset.measurable_sum
  intro i hi
  exact measurable_symmetrize_sweep_real M (fun ω => F ω i) (hF i) _

lemma symmetrize_sweep_mass (M : ℝ) (hM : 0 ≤ M) (F : V → ℝ) :
    (symmetrizeCut (sweep M F)).real univ = 2*M := by
  rw [symmetrizeCut, measureReal_ennreal_smul_apply,
    measureReal_add_apply (by finiteness) (by finiteness),
    map_measureReal_apply measurable_complementCut MeasurableSet.univ]
  simp only [preimage_univ, sweep_total_mass M hM]
  norm_num
  ring

lemma particleTrace_mass (M : ℝ) (hM : 0 ≤ M) (F : ι → V → ℝ) (P : Finset V) :
    (particleTrace M F P).real univ = 2*(Fintype.card ι : ℝ)*M := by
  rw [particleTrace, particle_real_sum]
  have heq (i : ι) : (cutTrace (symmetrizeCut (sweep M (F i))) P).real univ = 2*M := by
    rw [cutTrace, map_measureReal_apply (measurable_of_finite _) MeasurableSet.univ]
    simpa only [preimage_univ] using symmetrize_sweep_mass M hM (F i)
  simp_rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma integrable_particleTrace_real (M : ℝ) (hM : 0 ≤ M) (F : Ω → ι → V → ℝ)
    (hF : ∀ i v, Measurable (fun ω => F ω i v))
    (P : Finset V) (S : Set (P → Bool)) (ν : Measure Ω) [IsFiniteMeasure ν] :
    Integrable (fun ω => (particleTrace M (F ω) P).real S) ν := by
  apply (integrable_const (2*(Fintype.card ι : ℝ)*M)).mono'
    (measurable_particleTrace_real M F hF P S).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
  exact (measureReal_mono (subset_univ S)).trans_eq (particleTrace_mass M hM (F ω) P)

theorem measurable_branch_cut_laws (R : ReservationPath) (P : ℕ → Finset V)
    (g : Ω → ℕ → V → ℝ) (hg : ∀ t v, Measurable (fun ω => g ω t v)) (n : ℕ)
    (M : ℝ) (hM : 0 ≤ M) (ν : Measure Ω) [IsFiniteMeasure ν] :
    ∃ F : Ω → ℕ → ι → V → ℝ, ∃ p : Ω → ℕ → ι × ι,
      (∀ ω, RunEquations R P (g ω) n (F ω) (p ω)) ∧
      (∀ t ≤ n, ∀ B : Finset V, ∀ b : B → Bool,
        Measurable (fun ω => (particleTrace M (F ω t) B).real {b}) ∧
        Integrable (fun ω => (particleTrace M (F ω t) B).real {b}) ν) ∧
      (∀ ω t, (particleTrace M (F ω t) (P t)).real Set.univ =
        2*(Fintype.card ι : ℝ)*M) := by
  obtain ⟨F,p,hrun,hF,hp⟩ := measurable_particle_run (ι := ι) R P g hg n
  refine ⟨F,p,hrun,?_,?_⟩
  · intro t ht B b
    exact ⟨measurable_particleTrace_real M (fun ω => F ω t) (hF t ht) B {b},
      integrable_particleTrace_real M hM (fun ω => F ω t) (hF t ht) B {b} ν⟩
  · intro ω t
    exact particleTrace_mass M hM (F ω t) (P t)
end BoundedTreewidthL1.ParticleSchedule

namespace BoundedTreewidthL1.ParticleSchedule
open MeasureTheory
open scoped ENNReal
variable {V ι Ω : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [MeasurableSpace Ω]

/-- Literal restriction of a bag assignment to a smaller bag. -/
def restrictBagCut (P Q : Finset V) (h : Q ⊆ P) (a : P → Bool) : Q → Bool :=
  fun x => a ⟨x,h x.property⟩

lemma particleTrace_restrict
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [DecidableEq V] [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    (M : ℝ) (F : ι → V → ℝ)
    (P Q : Finset V) (h : Q ⊆ P) :
    (particleTrace M F P).map (restrictBagCut P Q h) = particleTrace M F Q := by
  classical
  rw [particleTrace, Measure.map_finset_sum' (measurable_of_finite _).aemeasurable]
  unfold particleTrace
  apply Finset.sum_congr rfl
  intro i _
  rw [cutTrace, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

theorem compatible_measurable_branch (R : ReservationPath)
    (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : ℕ → Finset V) (hP : ∀ t ≤ R.last, (P t).card ≤ k)
    (hsize : ∀ t, (R.inclusive t).card ≤ q)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : Ω → ℕ → V → ℝ) (hg : ∀ t v, Measurable (fun ω => g ω t v))
    (hLip : ∀ ω t, t ≤ R.last → ∀ u v, |g ω t u - g ω t v| ≤ L * d u v)
    (hHeight : ∀ ω t, t ≤ R.last → ∀ v, |g ω t v| ≤ H)
    (hvanish : ∀ ω t, t ≤ R.last → ∀ v ∈ P t, g ω t v = 0)
    (ν : Measure Ω) [IsFiniteMeasure ν] :
    let M := H * ((Fintype.card ι : ℝ)-1) + 2*Δ
    ∃ F : Ω → ℕ → ι → V → ℝ, ∃ p : Ω → ℕ → ι × ι,
      (∀ ω, RunEquations R P (g ω) (R.last+1) (F ω) (p ω)) ∧
      (∀ ω t, t ≤ R.last+1 → FunctionParticleReachable d L H (F ω t)) ∧
      (∀ t ≤ R.last, ∀ b : P t → Bool,
        Measurable (fun ω => (particleTrace M (F ω (t+1)) (P t)).real {b}) ∧
        Integrable (fun ω => (particleTrace M (F ω (t+1)) (P t)).real {b}) ν) ∧
      (∀ ω t, (particleTrace M (F ω (t+1)) (P t)).real Set.univ =
        2*(Fintype.card ι : ℝ)*M) ∧
      (∀ ω t, t < R.last →
        (particleTrace M (F ω (t+1)) (P t)).map
          (restrictBagCut (P t) (P t ∩ P (t+1)) Finset.inter_subset_left) =
        (particleTrace M (F ω (t+2)) (P (t+1))).map
          (restrictBagCut (P (t+1)) (P t ∩ P (t+1)) Finset.inter_subset_right)) ∧
      (∀ ω t, t ≤ R.last → ∀ a ∈ R.inclusive t,
        F ω (t+1) (p ω a).1 = F ω (a+1) (p ω a).1 ∧
        F ω (t+1) (p ω a).2 = F ω (a+1) (p ω a).2) := by
  classical
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  dsimp only
  choose F p hrun hreach htrace hretain using
    fun ω => scheduled_particle_realization (ι := ι) R k q hN P hP hsize d L H Δ hH hΔ
      (g ω) (hLip ω) (hHeight ω) (hvanish ω)
  have hmeas := (run_measurable R P g hg (R.last+1) F p hrun).1
  have hc : (1 : ℝ) ≤ Fintype.card ι := by
    have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
    exact_mod_cast hn
  have hM : 0 ≤ H * ((Fintype.card ι : ℝ)-1) + 2*Δ := by
    positivity
  refine ⟨F,p,hrun,hreach,?_,?_,?_,hretain⟩
  · intro t ht b
    exact ⟨measurable_particleTrace_real _ (fun ω => F ω (t+1))
        (hmeas (t+1) (by omega)) (P t) {b},
      integrable_particleTrace_real _ hM (fun ω => F ω (t+1))
        (hmeas (t+1) (by omega)) (P t) {b} ν⟩
  · intro ω t
    exact particleTrace_mass _ hM _ _
  · intro ω t ht
    rw [particleTrace_restrict, particleTrace_restrict]
    have heq := congrArg (fun μ => μ.map (restrictBagCut (P (t+1))
      (P t ∩ P (t+1)) Finset.inter_subset_right))
      (htrace ω (t+1) (by omega)).2
    simpa only [particleTrace_restrict, Nat.add_assoc] using heq
end BoundedTreewidthL1.ParticleSchedule

namespace BoundedTreewidthL1.ParticleBatch
open MeasureTheory ParticleSchedule
variable {V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]

noncomputable def usedPairs (C : Finset J) (p : J → ι × ι) : Finset ι :=
  (C.image (fun a => (p a).1)) ∪ (C.image (fun a => (p a).2))

/-- Launch all new active keys at one interface, reserving a pair immediately
before proceeding to the next key. Retained keys are supplied in C. -/
noncomputable def launchBatch (P : Finset V) : (l : List J) → (C : Finset J) →
    (F : ι → V → ℝ) → (p : J → ι × ι) → (g : J → V → ℝ) →
    (ι → V → ℝ) × (J → ι × ι)
  | [], _, F, p, _ => (F,p)
  | a :: l, C, F, p, g =>
    let z := pickPair P (usedPairs C p) F
    launchBatch P l (insert a C) (functionPairUpdate F z.1 z.2 (g a))
      (Function.update p a z) g

lemma usedPairs_card
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [DecidableEq J]
    (C : Finset J) (p : J → ι × ι) :
    (usedPairs C p).card ≤ 2*C.card := by
  unfold usedPairs
  have h := Finset.card_union_le (C.image (fun a => (p a).1)) (C.image (fun a => (p a).2))
  have h₁ := Finset.card_image_le (s := C) (f := fun a => (p a).1)
  have h₂ := Finset.card_image_le (s := C) (f := fun a => (p a).2)
  omega

lemma usedPairs_mono
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [DecidableEq J]
    {C D : Finset J} (h : C ⊆ D) (p : J → ι × ι) :
    usedPairs C p ⊆ usedPairs D p :=
  Finset.union_subset_union (Finset.image_subset_image h) (Finset.image_subset_image h)

lemma usedPairs_update
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [DecidableEq J]
    {C : Finset J} {a : J} (ha : a ∉ C)
    (p : J → ι × ι) (z : ι × ι) : usedPairs C (Function.update p a z) = usedPairs C p := by
  unfold usedPairs
  congr 1 <;> apply Finset.image_congr <;> intro b hb <;>
    simp only [Function.update_of_ne (show b ≠ a from fun h => ha (h ▸ hb))]

lemma first_mem_used
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [DecidableEq J]
    {C : Finset J} {a : J} (ha : a ∈ C) (p : J → ι × ι) :
    (p a).1 ∈ usedPairs C p :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
lemma second_mem_used
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [DecidableEq J]
    {C : Finset J} {a : J} (ha : a ∈ C) (p : J → ι × ι) :
    (p a).2 ∈ usedPairs C p :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)

/-- The reservation-preserving finite batch required by the co-bag active-scale
construction. No bound on the total number of updates is imposed. -/
theorem launchBatch_correct (k q : ℕ)
    (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : Finset V) (hP : P.card ≤ k) (l : List J) (C : Finset J)
    (hl : l.Nodup) (hfresh : ∀ a ∈ l, a ∉ C)
    (hcount : (C ∪ l.toFinset).card ≤ q)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (F : ι → V → ℝ) (p : J → ι × ι)
    (hF : FunctionParticleReachable d L H F) (g : J → V → ℝ)
    (hLip : ∀ a ∈ l, ∀ u v, |g a u - g a v| ≤ L*d u v)
    (hHeight : ∀ a ∈ l, ∀ v, |g a v| ≤ H)
    (hzero : ∀ a ∈ l, ∀ v ∈ P, g a v = 0) :
    let out := launchBatch P l C F p g
    let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
    FunctionParticleReachable d L H out.1 ∧
    particleTrace M out.1 P = particleTrace M F P ∧
    (∀ a ∈ C, out.2 a = p a) ∧
    (∀ i ∈ usedPairs C p, out.1 i = F i) ∧
    (∀ a ∈ l, (out.2 a).1 ≠ (out.2 a).2 ∧
      ∀ v, out.1 (out.2 a).1 v - out.1 (out.2 a).2 v = 2*g a v) := by
  classical
  induction l generalizing C F p with
  | nil =>
    simpa [launchBatch] using hF
  | cons a l ih =>
    have haC : a ∉ C := hfresh a (by simp)
    let z := pickPair P (usedPairs C p) F
    let F₁ := functionPairUpdate F z.1 z.2 (g a)
    let p₁ := Function.update p a z
    have hC : C.card ≤ q := (Finset.card_le_card Finset.subset_union_left).trans hcount
    have hz : z.1 ∉ usedPairs C p ∧ z.2 ∉ usedPairs C p ∧ z.1 ≠ z.2 ∧
        CommonWeakOrder P (F z.1) (F z.2) :=
      pickPair_spec k q hN P hP _ ((usedPairs_card C p).trans (by omega)) F
    have hF₁ : FunctionParticleReachable d L H F₁ :=
      FunctionParticleReachable.step hF z.1 z.2 hz.2.2.1 (g a)
        (hLip a (by simp)) (hHeight a (by simp))
    have hnewCount : (insert a C ∪ l.toFinset).card ≤ q := by
      simpa only [List.toFinset_cons, Finset.insert_union, Finset.union_insert] using hcount
    have hnewFresh : ∀ b ∈ l, b ∉ insert a C := by
      intro b hb h
      rcases Finset.mem_insert.mp h with h | h
      · subst b
        exact (List.nodup_cons.mp hl).1 hb
      · exact hfresh b (by simp [hb]) h
    have hresult := ih (insert a C) hl.of_cons hnewFresh hnewCount F₁ p₁ hF₁
      (fun b hb => hLip b (by simp [hb])) (fun b hb => hHeight b (by simp [hb]))
      (fun b hb => hzero b (by simp [hb]))
    dsimp only at hresult ⊢
    change _ ∧ _ ∧ _ ∧ _ ∧ _
    dsimp only [launchBatch]
    change FunctionParticleReachable d L H (launchBatch P l (insert a C) F₁ p₁ g).1 ∧
      particleTrace (H*((Fintype.card ι : ℝ)-1)+2*Δ)
        (launchBatch P l (insert a C) F₁ p₁ g).1 P = particleTrace
        (H*((Fintype.card ι : ℝ)-1)+2*Δ) F P ∧
      (∀ b ∈ C, (launchBatch P l (insert a C) F₁ p₁ g).2 b = p b) ∧
      (∀ i ∈ usedPairs C p, (launchBatch P l (insert a C) F₁ p₁ g).1 i = F i) ∧
      (∀ b ∈ a :: l,
        ((launchBatch P l (insert a C) F₁ p₁ g).2 b).1 ≠
          ((launchBatch P l (insert a C) F₁ p₁ g).2 b).2 ∧
        ∀ v, (launchBatch P l (insert a C) F₁ p₁ g).1
          ((launchBatch P l (insert a C) F₁ p₁ g).2 b).1 v -
          (launchBatch P l (insert a C) F₁ p₁ g).1
          ((launchBatch P l (insert a C) F₁ p₁ g).2 b).2 v = 2*g b v)
    refine ⟨hresult.1, ?_, ?_, ?_, ?_⟩
    · have hc : (1:ℝ) ≤ Fintype.card ι := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
      have hM : 0 < H*((Fintype.card ι : ℝ)-1)+2*Δ := by
        have := mul_nonneg hH.le (sub_nonneg.mpr hc)
        linarith
      have htrace := particleTrace_update _ hM F z.1 z.2 hz.2.2.1 (g a) P hz.2.2.2
        (hzero a (by simp))
        (fun i v => (function_particles_height_bound hH hF i v).trans (by linarith))
        (fun i v => (function_particles_height_bound hH hF₁ i v).trans (by linarith))
      exact hresult.2.1.trans htrace.symm
    · intro b hb
      rw [hresult.2.2.1 b (Finset.mem_insert_of_mem hb)]
      exact Function.update_of_ne (show b ≠ a from fun h => haC (h ▸ hb)) _ _
    · intro i hi
      have hi₁ : i ∈ usedPairs (insert a C) p₁ := by
        apply usedPairs_mono (Finset.subset_insert a C) p₁
        rwa [usedPairs_update haC]
      rw [hresult.2.2.2.1 i hi₁]
      funext v
      exact functionPairUpdate_other F z.1 z.2 i
        (fun h => hz.1 (h ▸ hi)) (fun h => hz.2.1 (h ▸ hi)) (g a) v
    · intro b hb
      rcases List.mem_cons.mp hb with h | hb
      · subst b
        have hpz : (launchBatch P l (insert a C) F₁ p₁ g).2 a = z := by
          simpa [p₁] using hresult.2.2.1 a (Finset.mem_insert_self a C)
        change ((launchBatch P l (insert a C) F₁ p₁ g).2 a).1 ≠ _ ∧ _
        rw [hpz]
        refine ⟨hz.2.2.1, ?_⟩
        intro v
        have hz₁ : z.1 ∈ usedPairs (insert a C) p₁ := by
          simpa [p₁] using first_mem_used (Finset.mem_insert_self a C) p₁
        have hz₂ : z.2 ∈ usedPairs (insert a C) p₁ := by
          simpa [p₁] using second_mem_used (Finset.mem_insert_self a C) p₁
        rw [hresult.2.2.2.1 z.1 hz₁, hresult.2.2.2.1 z.2 hz₂]
        dsimp [F₁]
        rw [functionPairUpdate_left F z.1 z.2 hz.2.2.1,
          functionPairUpdate_right F z.1 z.2 hz.2.2.1]
        ring
      · exact hresult.2.2.2.2 b hb
end BoundedTreewidthL1.ParticleBatch

namespace BoundedTreewidthL1.ParticleBatch
open MeasureTheory ParticleSchedule
variable {V ι J Ω : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J] [Fintype J]
  [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma measurable_usedPairs
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} {Ω : Type treewidthLevel3} [Fintype ι]
    [Nonempty ι] [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (C : Finset J) (p : Ω → J → ι × ι)
    (hp : ∀ a, Measurable (fun ω => p ω a)) :
    Measurable (fun ω => usedPairs C (p ω)) := by
  have hp' : Measurable p := measurable_pi_iff.mpr hp
  exact (measurable_of_finite (fun p : J → ι × ι => usedPairs C p)).comp hp'

/-- The exact finite multi-launch scheduler is measurable; all pair choice is
finite deterministic selection, not choice on the real sample space. -/
theorem measurable_launchBatch (P : Finset V) (l : List J) (C : Finset J)
    (F : Ω → ι → V → ℝ) (p : Ω → J → ι × ι) (g : Ω → J → V → ℝ)
    (hF : ∀ i v, Measurable (fun ω => F ω i v))
    (hp : ∀ a, Measurable (fun ω => p ω a))
    (hg : ∀ a v, Measurable (fun ω => g ω a v)) :
    Measurable (fun ω => launchBatch P l C (F ω) (p ω) (g ω)) := by
  classical
  induction l generalizing C F p with
  | nil =>
    exact (measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr (hF i)).prodMk
      (measurable_pi_iff.mpr hp)
  | cons a l ih =>
    let z : Ω → ι × ι := fun ω => pickPair P (usedPairs C (p ω)) (F ω)
    have hz : Measurable z := measurable_pickPair P _ F (measurable_usedPairs C p hp) hF
    have hF₁ : ∀ i v, Measurable (fun ω =>
        functionPairUpdate (F ω) (z ω).1 (z ω).2 (g ω a) i v) :=
      measurable_pairUpdate F z (fun ω => g ω a) hF hz (hg a)
    have hp₁ : ∀ b, Measurable (fun ω => Function.update (p ω) a (z ω) b) := by
      intro b
      by_cases h : b = a
      · subst b
        simpa only [Function.update_self] using hz
      · simpa only [Function.update_of_ne h] using hp b
    exact ih (insert a C) _ _ hF₁ hp₁
end BoundedTreewidthL1.ParticleBatch

end OAI
