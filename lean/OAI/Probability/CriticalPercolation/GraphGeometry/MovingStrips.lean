import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.StripCompactness
import OAI.Probability.CriticalPercolation.Gluing.StripMoves

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def parallelCoordinate (u v : V → ℝ) (a b : ℝ) (x : V) : ℝ := a*u x+b*v x
def normalCoordinate (u v : V → ℝ) (a b : ℝ) (x : V) : ℝ := -b*u x+a*v x

def longStripExit (u v : V → ℝ) (A : Set V) (W L a b : ℝ) : Set (Set E) :=
  G.restrictedSeed A
    ({x | |normalCoordinate u v a b x|≤W}∩{x | L≤|parallelCoordinate u v a b x|})
    (G.inducedEdges {x | |normalCoordinate u v a b x|≤W})

lemma unit_pair_bounds {a b : ℝ} (h : a^2+b^2=1) :
    -1≤a ∧ a≤1 ∧ -1≤b ∧ b≤1 := by
  have ha : a^2≤1 := by nlinarith [sq_nonneg b]
  have hb : b^2≤1 := by nlinarith [sq_nonneg a]
  constructor
  · nlinarith [sq_nonneg (a+1)]
  constructor
  · nlinarith [sq_nonneg (a-1)]
  constructor <;> nlinarith [sq_nonneg (b+1),sq_nonneg (b-1)]

theorem uniform_long_strip_exits [Countable V] [Countable E]
    (hl : G.LocallyFinite) (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (u v : V → ℝ) (A : Set V) (hA : A.Finite) (W r : ℝ)
    (hW : 0<W) (hr : 0<r)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 →
      μ (G.stripPercolates (normalCoordinate u v a b) (2*W))=0) :
    ∃ N : ℕ, ∀ L : ℝ, (N : ℝ)≤L → ∀ a b : ℝ, a^2+b^2=1 →
      μ.real (G.longStripExit u v A W L a b)<r := by
  by_contra hn
  push Not at hn
  choose L hL a b hab hprob using hn
  have hseq : ∀ n, (a n,b n)∈Set.Icc ((-1 : ℝ),(-1 : ℝ)) (1,1) := by
    intro n
    have h := unit_pair_bounds (hab n)
    exact ⟨⟨h.1,h.2.2.1⟩,h.2.1,h.2.2.2⟩
  obtain ⟨c,_hc,φ,hφ,hc⟩ := isCompact_Icc.tendsto_subseq hseq
  have ha : Tendsto (fun n => a (φ n)) atTop (𝓝 c.1) := (continuous_fst.tendsto c).comp hc
  have hb : Tendsto (fun n => b (φ n)) atTop (𝓝 c.2) := (continuous_snd.tendsto c).comp hc
  have hunit : c.1^2+c.2^2=1 := by
    apply tendsto_nhds_unique ((ha.pow 2).add (hb.pow 2))
    simpa only [hab] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hpar : ∀ x, Tendsto (fun n => parallelCoordinate u v (a (φ n)) (b (φ n)) x)
      atTop (𝓝 (parallelCoordinate u v c.1 c.2 x)) := fun x =>
    (ha.mul_const (u x)).add (hb.mul_const (v x))
  have hnorm : ∀ x, Tendsto (fun n => normalCoordinate u v (a (φ n)) (b (φ n)) x)
      atTop (𝓝 (normalCoordinate u v c.1 c.2 x)) := fun x =>
    (hb.neg.mul_const (u x)).add (ha.mul_const (v x))
  have hLtop : Tendsto (fun n => L (φ n)) atTop atTop :=
    tendsto_atTop_mono (fun n => hL (φ n))
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  let Sj := fun n => {x | |normalCoordinate u v (a (φ n)) (b (φ n)) x|≤W}
  let Tj := fun n => {x | L (φ n)≤|parallelCoordinate u v (a (φ n)) (b (φ n)) x|}
  let S := {x | |normalCoordinate u v c.1 c.2 x|≤2*W}
  have hlocal : ∀ K : Set V, K.Finite → ∀ᶠ n in atTop, Sj n∩K⊆S := by
    intro K hK
    have he : ∀ᶠ n in atTop, ∀ x∈K,
        |normalCoordinate u v (a (φ n)) (b (φ n)) x|≤W → x∈S := by
      apply hK.eventually_all.mpr
      intro x _hx
      by_cases hx : x∈S
      · exact Eventually.of_forall (fun _ _ => hx)
      · have hh : W < |normalCoordinate u v c.1 c.2 x| := by
          change ¬|normalCoordinate u v c.1 c.2 x|≤2*W at hx
          linarith
        filter_upwards [(hnorm x).abs.eventually (lt_mem_nhds hh)] with n hn
        exact fun hnx => False.elim (not_lt_of_ge hnx hn)
    exact he.mono fun n hn x hx => hn x hx.2 hx.1
  have hescape : ∀ K : Set V, K.Finite → ∀ᶠ n in atTop, Disjoint (Tj n) K := by
    intro K hK
    have he : ∀ᶠ n in atTop, ∀ x∈K,
        |parallelCoordinate u v (a (φ n)) (b (φ n)) x|<L (φ n) := by
      apply hK.eventually_all.mpr
      intro x _hx
      let M := |parallelCoordinate u v c.1 c.2 x|+1
      have hm : |parallelCoordinate u v c.1 c.2 x|<M := by dsimp [M]; linarith
      filter_upwards [(hpar x).abs.eventually (gt_mem_nhds hm),
        (tendsto_atTop.mp hLtop M)] with n hn hn'
      exact hn.trans_le hn'
    exact he.mono fun n hn => Set.disjoint_left.mpr (fun x hx hk =>
      not_lt_of_ge hx (hn x hk))
  have hmass := G.local_domain_exit_compactness hl μ A S hA Sj Tj r hlocal hescape
    (fun n => hprob (φ n))
  have hf : μ (G.seedDomainInfinite A S)=0 := measure_mono_null
    (fun ω hω => by obtain ⟨x,_hx,hx⟩ := hω; exact ⟨x,hx⟩) (hnull c.1 c.2 hunit)
  rw [measureReal_def,hf,ENNReal.toReal_zero] at hmass
  exact not_le_of_gt hr hmass

end CriticalPercolation.BondGraph
end
end
end

end OAI
