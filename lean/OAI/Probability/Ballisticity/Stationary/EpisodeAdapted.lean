import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeInjection
import OAI.Probability.Ballisticity.Stationary.EpisodeCharts

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def episodeInitialChart {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor) (t : ℕ) : EpisodeChart (k:=k) e f r where
  height := t+1
  scale := sfloor
  profile := fun ω => (episodeInitial (k:=k) e f hef r sfloor hR t ω).profile
  measurable_profile := by
    apply Measurable.subtype_mk
    have hm := measurable_subtype_coe.comp
      ((BoundedInjection.injectionProfile_measurable (k:=k) e f hef (r sfloor) hR t).comp
        (globalTupleProfile_measurable_below (k:=k) e t))
    exact hm.mono (rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < ((t+1:ℕ):ℝ)
      exact hx.trans_le (by exact_mod_cast Nat.le_add_right t 1))) le_rfl
  event := Set.univ
  measurable_event := MeasurableSet.univ

noncomputable def episodeInitialAtlas {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor) (t : ℕ) :
    EpisodeAtlas (episodeInitial (k:=k) e f hef r sfloor hR t) where
  Label := Unit
  countable := inferInstance
  chart := fun _ => episodeInitialChart e f hef r sfloor hR t
  cover := fun _ => ⟨(),Set.mem_univ _⟩
  correct := fun _ _ _ => rfl

noncomputable def episodeFinalAtlas {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ) :
    EpisodeAtlas (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t) :=
  (episodeInitialAtlas (k:=k) e f hef r sfloor hR t).run hef fexp g χ b sfloor N N

lemma episodeFinal_height_event {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t m : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      {ω | (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height=m} :=
  (episodeFinalAtlas (k:=k) e f hef r fexp g χ b sfloor hR N t).height_event m

lemma episodeBoundary_height_event {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N i m : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      {ω | episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i=m} := by
  induction i generalizing m with
  | zero =>
    change MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)] {_ω : Environment d | (0:ℕ)=m}
    exact MeasurableSet.const _
  | succ i ih =>
    let T := fun ω => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let U := fun t ω => (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height
    have he : {ω | episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω (i+1)=m} =
        ({ω | T ω=m} ∩ {ω | N ≤ m}) ∪
        ⋃ t : {t : ℕ // t < N ∧ t < m}, {ω | T ω=t} ∩ {ω | U t ω=m} := by
      ext ω
      simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_inter_iff,Set.mem_iUnion]
      constructor
      · intro hh
        change (if T ω<N then U (T ω) ω else T ω)=m at hh
        split at hh
        · rename_i ht
          have htm : T ω< m := by rw [←hh]; exact episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N (T ω) ω
          exact Or.inr ⟨⟨T ω,ht,htm⟩,rfl,hh⟩
        · rename_i ht
          exact Or.inl ⟨hh,by omega⟩
      · rintro (⟨hh,hN⟩ | ⟨t,ht,hU⟩)
        · change (if T ω<N then U (T ω) ω else T ω)=m
          rw [hh,ite_eq_right (by omega)]
        · change (if T ω<N then U (T ω) ω else T ω)=m
          rw [ht,ite_eq_left t.property.1]
          exact hU
    rw [he]
    apply MeasurableSet.union
    · exact (ih m).inter (MeasurableSet.const _)
    · apply MeasurableSet.iUnion
      intro t
      have hle : rowSigma (BelowHeight (realPosition (step e)) (t.val:ℝ)) ≤
          rowSigma (BelowHeight (realPosition (step e)) (m:ℝ)) :=
        rowSigma_mono (by
          intro x hx
          change dot (realPosition x) (realPosition (step e)) < (t.val:ℝ) at hx
          change dot (realPosition x) (realPosition (step e)) < (m:ℝ)
          exact hx.trans_le (by exact_mod_cast t.property.2.le))
      exact (hle _ (ih t.val)).inter (episodeFinal_height_event (k:=k) e f hef r fexp g χ b sfloor hR N t m)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

lemma branch_unique (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (l m : Option (ℕ×Bool))
    (hl : ω∈(c.branch hef fexp g χ b sfloor N l).event)
    (hm : ω∈(c.branch hef fexp g χ b sfloor N m).event) : l=m := by
  cases l with
  | none =>
    cases m with
    | none => rfl
    | some m => exact False.elim (hl.2 ⟨hm.2.1,hm.2.2.1⟩)
  | some l =>
    cases m with
    | none => exact False.elim (hm.2 ⟨hl.2.1,hl.2.2.1⟩)
    | some m =>
      have hj : l.1=m.1 := hl.2.2.2.1.symm.trans hm.2.2.2.1
      have hg := hl.2.2.2.2
      rw [hj] at hg
      have hb : (l.2=true) ↔ (m.2=true) := hg.symm.trans hm.2.2.2.2
      have hbool : l.2=m.2 := by
        cases h₁ : l.2 <;> cases h₂ : m.2 <;> simp_all only [Bool.false_eq_true,iff_false,
          iff_true,not_true_eq_false,iff_self]
      exact congrArg some (Prod.ext hj hbool)

end EpisodeChart
namespace EpisodeAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r}

def IsPartition (A : EpisodeAtlas q) : Prop :=
  ∀ l m ω, ω∈(A.chart l).event → ω∈(A.chart m).event → l=m

lemma advance_partition (A : EpisodeAtlas q) (hA : A.IsPartition) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) :
    (A.advance hef fexp g χ b sfloor N).IsPartition := by
  rintro ⟨l,j⟩ ⟨m,h⟩ ω hl hm
  have hl₀ := ((A.chart l).branch_state hef fexp g χ b sfloor N ω j hl).1
  have hm₀ := ((A.chart m).branch_state hef fexp g χ b sfloor N ω h hm).1
  have he := hA l m ω hl₀ hm₀
  subst m
  exact Prod.ext rfl ((A.chart l).branch_unique hef fexp g χ b sfloor N ω j h hl hm)

lemma run_partition (A : EpisodeAtlas q) (hA : A.IsPartition) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N n : ℕ) :
    (A.run hef fexp g χ b sfloor N n).IsPartition := by
  induction n with
  | zero => exact hA
  | succ n ih => exact advance_partition _ ih hef fexp g χ b sfloor N

lemma chart_disjoint (A : EpisodeAtlas q) (hA : A.IsPartition) :
    Pairwise (fun l m => Disjoint (A.chart l).event (A.chart m).event) := by
  intro l m hne
  exact Set.disjoint_left.mpr (fun ω hl hm => hne (hA l m ω hl hm))

end EpisodeAtlas

lemma episodeInitialAtlas_partition {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor) (t : ℕ) :
    (episodeInitialAtlas (k:=k) e f hef r sfloor hR t).IsPartition :=
  by
    intro l m _ _ _
    change Unit at l m
    exact Subsingleton.elim l m

lemma episodeFinalAtlas_partition {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ) :
    (episodeFinalAtlas (k:=k) e f hef r fexp g χ b sfloor hR N t).IsPartition :=
  (episodeInitialAtlas (k:=k) e f hef r sfloor hR t).run_partition
    (episodeInitialAtlas_partition e f hef r sfloor hR t) hef fexp g χ b sfloor N N

end DirectionalTransience

end

end OAI
