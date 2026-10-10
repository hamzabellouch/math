import Mathlib
import OAI.Probability.Perceptron.Variational.FiniteFieldModel

namespace OAI

noncomputable section

namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

theorem exists_finiteFieldModel_strict (f : Time → ℝ) (hf : Measurable f)
    (hfin : (Set.range f).Finite) : ∃ M : FiniteFieldModel f, StrictMono M.value := by
  classical
  let S := hfin.toFinset
  let T := S.filter (fun r => 0 < timeLaw.real (f ⁻¹' {r}))
  have hae : ∀ᵐ u ∂timeLaw, f u ∈ T := by
    have hnull : ∀ r ∈ S, ∀ᵐ u ∂timeLaw, f u=r → 0 < timeLaw.real (f ⁻¹' {r}) := by
      intro r _hr
      by_cases hp : 0 < timeLaw.real (f ⁻¹' {r})
      · exact ae_of_all _ (fun _ _ => hp)
      · have hz : timeLaw (f ⁻¹' {r})=0 := by
          have hz : (timeLaw (f ⁻¹' {r})).toReal=0 := le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
          have hp := (ENNReal.toReal_eq_zero_iff _).mp hz
          rcases hp with hp | hp
          · exact hp
          · exact (measure_ne_top _ _ hp).elim
        have hnot : ∀ᵐ u ∂timeLaw, f u ≠ r := by
          apply ae_iff.mpr
          simpa only [Set.preimage,Set.mem_singleton_iff,not_not] using hz
        filter_upwards [hnot] with u hu
        exact fun h => (hu h).elim
    have hall := (S.eventually_all).mpr hnull
    filter_upwards [hall] with u hu
    have hmem : f u ∈ S := hfin.mem_toFinset.mpr (mem_range_self u)
    exact Finset.mem_filter.mpr ⟨hmem,hu (f u) hmem rfl⟩
  have hT : T.Nonempty := by
    obtain ⟨u,hu⟩ := hae.exists
    exact ⟨f u,hu⟩
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hT)
  let e := T.orderIsoOfFin hd
  let v : Fin (d+1) → ℝ := fun i => e i
  have hv : StrictMono v := fun i j hij => e.strictMono hij
  have hve : MeasurableEmbedding v := ⟨hv.injective,measurable_of_finite _,fun _ _ => (Set.toFinite _).measurableSet⟩
  let a : Time → Fin (d+1) := fun u => hve.invFun (f u)
  have hag : (fun u => v (a u)) =ᵐ[timeLaw] f := by
    filter_upwards [hae] with u hu
    have hx : f u=v (e.symm ⟨f u,hu⟩) := congrArg Subtype.val (e.apply_symm_apply ⟨f u,hu⟩) |>.symm
    dsimp only [a]
    rw [hx,hve.leftInverse_invFun]
  refine ⟨⟨d,v,a,hve.measurable_invFun.comp hf,?_,hv.monotone,hag⟩,hv⟩
  intro i
  have he : a ⁻¹' {i}=ᵐ[timeLaw] f ⁻¹' {v i} := by
    filter_upwards [hag] with u hu
    apply propext
    change (a u=i) ↔ f u=v i
    rw [← hu]
    exact hv.injective.eq_iff.symm
  change 0 < (timeLaw (a ⁻¹' {i})).toReal
  rw [measure_congr he]
  exact (Finset.mem_filter.mp (e i).2).2

def finiteMonotoneExtension {k : ℕ} (q a : Fin (k+1)→ℝ) (r : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => if q i≤r then a i else a 0)

lemma finiteMonotoneExtension_mono {k : ℕ} (q a : Fin (k+1)→ℝ) (_ha : Monotone a) :
    Monotone (finiteMonotoneExtension q a) := by
  intro r s hrs
  apply Finset.sup'_le
  intro i hi
  by_cases hqi : q i≤r
  · simp only [ite_eq_left hqi]
    have h := Finset.le_sup' (s:=Finset.univ) (f:=fun j=>if q j≤ s then a j else a 0) hi
    simpa only [ite_eq_left (hqi.trans hrs),finiteMonotoneExtension] using h
  · simp only [ite_eq_right hqi]
    have h0 := Finset.le_sup' (s:=Finset.univ) (f:=fun j=>if q j≤ s then a j else a 0) (Finset.mem_univ 0)
    simpa only [finiteMonotoneExtension,ite_self] using h0

lemma finiteMonotoneExtension_value {k : ℕ} (q a : Fin (k+1)→ℝ)
    (hq : StrictMono q) (ha : Monotone a) (j : Fin (k+1)) :
    finiteMonotoneExtension q a (q j)=a j := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _hi
    split_ifs with h
    · exact ha (hq.le_iff_le.mp h)
    · exact ha (Fin.zero_le j)
  · have h := Finset.le_sup' (s:=Finset.univ) (f:=fun i=>if q i≤q j then a i else a 0) (Finset.mem_univ j)
    simpa only [finiteMonotoneExtension,le_refl,ite_true] using h

lemma finiteMonotoneExtension_bounds {k : ℕ} (q a : Fin (k+1)→ℝ) (C : ℝ)
    (ha : ∀ i,0≤a i) (hb : ∀ i,a i≤C) (r : ℝ) :
    0≤finiteMonotoneExtension q a r ∧ finiteMonotoneExtension q a r≤C := by
  constructor
  · have h := Finset.le_sup' (s:=Finset.univ) (f:=fun i=>if q i≤r then a i else a 0) (Finset.mem_univ 0)
    exact (ha 0).trans (by simpa only [finiteMonotoneExtension,ite_self] using h)
  · apply Finset.sup'_le
    intro i _hi
    split_ifs <;> apply hb

lemma monotone_tendsto_of_rat_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, Monotone (f n)) (hr : ∀ q : ℚ,
      Tendsto (fun n => f n q) atTop (𝓝 (g q)))
    {x : ℝ} (hg : ContinuousAt g x) :
    Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have he : ∀ᶠ y in 𝓝 x, a < g y := hg (eventually_gt_nhds ha)
    obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he
    obtain ⟨r,hr₁,hr₂⟩ := exists_rat_btwn (show x-δ<x by linarith)
    have har : a<g (r : ℝ) := hd (by rw [Real.dist_eq,abs_of_neg (by linarith)]; linarith)
    filter_upwards [(hr r).eventually (eventually_gt_nhds har)] with n hn
    exact hn.trans_le (hf n hr₂.le)
  · intro b hb
    have he : ∀ᶠ y in 𝓝 x, g y < b := hg (eventually_lt_nhds hb)
    obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he
    obtain ⟨r,hr₁,hr₂⟩ := exists_rat_btwn (show x<x+δ by linarith)
    have hbr : g (r : ℝ)<b := hd (by rw [Real.dist_eq,abs_of_pos (by linarith)]; linarith)
    filter_upwards [(hr r).eventually (eventually_lt_nhds hbr)] with n hn
    exact (hf n hr₁.le).trans_lt hn

 theorem bounded_monotone_helly (f : ℕ → ℝ → ℝ) (C : ℝ)
    (hf : ∀ n, Monotone (f n)) (hb : ∀ n x, 0≤f n x ∧ f n x≤C) :
    ∃ (s : ℕ → ℕ) (g : ℝ → ℝ), StrictMono s ∧ Monotone g ∧
      (∀ x,0≤g x ∧ g x≤C) ∧ ∀ x,Tendsto (fun n => f (s n) x) atTop (𝓝 (g x)) := by
  classical
  let Z : ℕ → ℚ → Icc (0 : ℝ) C := fun n r => ⟨f n r,hb n r⟩
  obtain ⟨l,-,s,hs,hl⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (Z n))
  have hr (q : ℚ) : Tendsto (fun n => f (s n) q) atTop (𝓝 (l q).val) :=
    continuous_subtype_val.tendsto _ |>.comp ((continuous_apply q).tendsto l |>.comp hl)
  let g : ℝ → ℝ := fun x => limsup (fun n => f (s n) x) atTop
  have gm : Monotone g := by
    intro x y hxy
    exact limsup_le_limsup (Eventually.of_forall (fun n => hf (s n) hxy))
      ((isBoundedUnder_of ⟨0,fun n => (hb (s n) x).1⟩).isCobounded_flip)
      (isBoundedUnder_of ⟨C,fun n => (hb (s n) y).2⟩)
  have hgq (q : ℚ) : g q=(l q).val := (hr q).limsup_eq
  have hgc (x : ℝ) (hx : ContinuousAt g x) :
      Tendsto (fun n => f (s n) x) atTop (𝓝 (g x)) :=
    monotone_tendsto_of_rat_tendsto (fun n => hf (s n)) (fun q => by rw [hgq]; exact hr q) hx
  let D := {x | ¬ContinuousAt g x}
  have hD : D.Countable := gm.countable_not_continuousAt
  let : Countable D := hD.to_subtype
  let W : ℕ → D → Icc (0 : ℝ) C := fun n x => ⟨f (s n) x,hb (s n) x⟩
  obtain ⟨v,-,t,ht,hv⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (W n))
  let a : ℝ → ℝ := fun x => if hx : x∈D then (v ⟨x,hx⟩).val else g x
  have ha (x : ℝ) : Tendsto (fun n => f (s (t n)) x) atTop (𝓝 (a x)) := by
    by_cases hx : x∈D
    · dsimp only [a]
      rw [dite_eq_left hx]
      exact continuous_subtype_val.tendsto _ |>.comp
        ((continuous_apply (⟨x,hx⟩ : D)).tendsto v |>.comp hv)
    · dsimp only [a]
      rw [dite_eq_right hx]
      exact (hgc x (not_not.mp hx)).comp ht.tendsto_atTop
  refine ⟨s ∘ t,a,hs.comp ht,?_,?_,ha⟩
  · intro x y hxy
    exact le_of_tendsto_of_tendsto (ha x) (ha y)
      (Eventually.of_forall (fun n => hf (s (t n)) hxy))
  · intro x
    exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds (ha x) (Eventually.of_forall (fun n => (hb (s (t n)) x).1)),
      le_of_tendsto_of_tendsto (ha x) tendsto_const_nhds (Eventually.of_forall (fun n => (hb (s (t n)) x).2))⟩

end SphericalPerceptronFreeEnergy

end

end OAI
