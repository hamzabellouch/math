import OAI.Combinatorics.TreewidthL1.CobagScales

namespace OAI

namespace BoundedTreewidthL1
open MeasureTheory Metric TreeParticles LaunchNoise CobagScales
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable

theorem cobag_embedding :
    ∀ k : ℕ, 2 ≤ k → ∃ U c : ℝ, 0 < U ∧ 0 < c ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) (_ : G.Connected)
      (ℓ : G.edgeSet → ℝ) (_ : ∀ e, 0 < ℓ e)
      (m : ℕ) (T : SimpleGraph (Fin m)) (_ : T.IsTree) (_ : Fin m)
      (B : Fin m → Finset V),
      (∀ v, ∃ i, v ∈ B i) →
      (∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i) →
      (∀ v, (T.induce {i | v ∈ B i}).Connected) →
      (∀ i, (B i).card ≤ k) →
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        (∀ u v, ‖Φ u - Φ v‖ ≤ U*shortestPathDistance G ℓ u v) ∧
        ∀ i u v, u ∈ B i → v ∈ B i →
          c*shortestPathDistance G ℓ u v ≤ ‖Φ u - Φ v‖ := by
  classical
  intro k hk
  obtain ⟨α,π,hα,hα8,hπ,hπ1,hsampler⟩ := graph_cobag_sampler k hk
  let q := 4*k.choose 2
  let N := 2*q + k.factorial + 2
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hNm : 0 < (N:ℝ)-1 := by linarith
  refine ⟨(N:ℝ)*((N:ℝ)-1),π*α/64,mul_pos (by linarith) hNm,by positivity,?_⟩
  intro V _ _ _ G hG ℓ hℓ m T hT root B hcover hedge hrun hbag
  let : MetricSpace V := weightedMetricSpace G ℓ hG hℓ
  let R := RootedTree.forest T hT root
  let K : Finset ℤ := Finset.univ.biUnion (fun i => active dist (B i))
  let J := ↥K
  let A : Fin m → Finset J := fun i => (active dist (B i)).subtype (fun j => j ∈ K)
  have hA : ∀ i, (A i).card ≤ q := by
    intro i
    calc
      (A i).card ≤ (active dist (B i)).card := by
        rw [Finset.card_subtype]
        exact Finset.card_filter_le _ _
      _ ≤ 4*(B i).card.choose 2 := active_card _ _
      _ ≤ q := Nat.mul_le_mul_left 4 (Nat.choose_le_choose 2 (hbag i))
  have hdec : HasTreeDecomposition G k := ⟨m,T,B,hT,hcover,hedge,hrun,hbag⟩
  have hs (p : Fin m × J) := hsampler V G hG hdec ℓ hℓ
    (interface R B p.1 : Set V) ((2:ℝ)^p.2.val/16) (by positivity)
  choose ν f hprob hf hprop hsep using hs
  let (p : Fin m × J) : IsProbabilityMeasure (ν p) := hprob p
  let Ω := (Fin m × J) → FiniteSampleSpace V
  let law : Measure Ω := Measure.pi ν
  let g : Ω → Fin m → J → V → ℝ := fun ω i a => f (i,a) (ω (i,a))
  let H : ℝ := 1 + ∑ a : J, (2:ℝ)^a.val
  have hH : 0 < H := by
    have hh : 0 ≤ ∑ a : J, (2:ℝ)^a.val := Finset.sum_nonneg (fun a _ => (zpow_pos (by norm_num) _).le)
    dsimp [H]; linarith
  have hh (a : J) : (2:ℝ)^a.val/16 ≤ H := by
    have hh := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset J)) =>
      (zpow_pos (by norm_num : (0:ℝ)<2) b.val).le) (Finset.mem_univ a)
    have hp := zpow_pos (by norm_num : (0:ℝ)<2) a.val
    dsimp [H]
    linarith
  have hg : ∀ i a v, Measurable (fun ω : Ω => g ω i a v) := by
    intro i a v
    exact ((measurable_pi_apply v).comp (hf (i,a))).comp (measurable_pi_apply (i,a))
  have hLip : ∀ ω i a, ∀ u v, |g ω i a u-g ω i a v| ≤ 1*shortestPathDistance G ℓ u v := by
    intro ω i a u v
    change |f (i,a) (ω (i,a)) u-f (i,a) (ω (i,a)) v| ≤ 1*dist u v
    exact (hprop (i,a) (ω (i,a))).1.dist_le_mul u v
  have hHeight : ∀ ω i a v, |g ω i a v| ≤ H := by
    intro ω i a v
    rw [abs_of_nonneg ((hprop (i,a) (ω (i,a))).2.1 v).1]
    exact ((hprop (i,a) (ω (i,a))).2.1 v).2.trans (hh a)
  have hz : ∀ ω i a, ∀ v ∈ interface R B i, g ω i a v = 0 := by
    intro ω i a v hv
    exact (hprop (i,a) (ω (i,a))).2.2 v hv
  obtain ⟨n,Φ,hup,hlo⟩ := averaged_origin_realization (ι := Fin N) G hG ℓ hℓ T hT root B
    hcover hedge (fun v => (hrun v).preconnected) A k q hbag hA (by simp [N])
    law 1 H 1 (by norm_num) hH (by norm_num) g hg hLip hHeight hz
  refine ⟨n,Φ,?_,?_⟩
  · simpa only [Fintype.card_fin,mul_one] using hup
  · intro i u v hu hv
    by_cases huv : u = v
    · subst v
      simp only [shortestPathDistance_self G ℓ hG (fun e => (hℓ e).le),mul_zero,sub_self,norm_zero,le_refl]
    let j := bandIndex 1 (dist u v)
    have hb : 0 < (2:ℝ)^j ∧ (2:ℝ)^j ≤ dist u v ∧ dist u v < 2*(2:ℝ)^j := by
      simpa only [bandLower,one_mul] using band_bounds 1 (dist u v) (by norm_num) (dist_pos.mpr huv)
    have haj : j ∈ active dist (B i) := small_scale_active (B i) u v hu hv huv
    let a : J := ⟨j,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,haj⟩⟩
    have ha : a ∈ A i := Finset.mem_subtype.mpr haj
    let o := origin R A root i a
    have hof : a ∈ fresh R A o := origin_fresh R A root i a ha
    have hge (x y : V) (hxy : (2:ℝ)^j/16 < dist x y)
        (hcap : (interface R B o : Set V).Nonempty →
          α*((2:ℝ)^j/16) ≤ infDist x (interface R B o : Set V)) :
        π*α*((2:ℝ)^j/16)/4 ≤ ∫ ω : Ω, |g ω o a x-g ω o a y| ∂law := by
      have heq := integral_comp_eval (μ := ν) (i := (o,a))
        (((measurable_pi_apply x).comp (hf (o,a))).sub
          ((measurable_pi_apply y).comp (hf (o,a)))).abs.aestronglyMeasurable
      change (∫ ω : Ω, |g ω o a x-g ω o a y| ∂law) = _ at heq
      rw [heq]
      exact hsep (o,a) x y hxy hcap
    have hgap : π*α*((2:ℝ)^j/16)/4 ≤ ∫ ω : Ω, |g ω o a u-g ω o a v| ∂law := by
      have hsmall : (2:ℝ)^j/16 < dist u v := by linarith [hb.1,hb.2.1]
      have hscale : α*((2:ℝ)^j/16) ≤ (2:ℝ)^j/8 := by nlinarith [hb.1]
      cases hp : R.parent o with
      | none =>
        apply hge u v hsmall
        simp only [interface,hp,Option.elim_none,Finset.coe_empty,Set.not_nonempty_empty,IsEmpty.forall_iff]
      | some p =>
        have hn : j ∉ active dist (B p) := by
          intro hj
          have hap : a ∈ A p := Finset.mem_subtype.mpr hj
          exact (Finset.mem_sdiff.mp hof).2 (by
            simpa only [retained,hp,Option.elim_some,Finset.mem_inter] using
              And.intro (Finset.mem_sdiff.mp hof).1 hap)
        by_cases hne : (B p : Set V).Nonempty
        · rcases inactive_far (B p) j u v hn hb.2.1 hb.2.2 hne with hfar | hfar
          · apply hge u v hsmall
            intro _
            simpa only [interface,hp,Option.elim_some] using hscale.trans hfar
          · have he := hge v u (by simpa only [dist_comm] using hsmall) (by
              intro _
              simpa only [interface,hp,Option.elim_some] using hscale.trans hfar)
            apply he.trans_eq
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun ω => abs_sub_comm _ _)
        · apply hge u v hsmall
          simpa only [interface,hp,Option.elim_some] using (fun h => False.elim (hne h))
    have hl := hlo i a ha ⟨u,hu⟩ ⟨v,hv⟩
    have hpos : 0 < π*α := mul_pos hπ hα
    change 2*(∫ ω : Ω, |g ω o a u-g ω o a v| ∂law) ≤ ‖Φ u-Φ v‖ at hl
    change π*α/64*dist u v ≤ ‖Φ u-Φ v‖
    nlinarith [hb.2.2]
end BoundedTreewidthL1

end OAI
