import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Encounter.Counts

namespace OAI

/-! Critical limits and zero encounter intensity. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph Filter Topology
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem branchCount_three (H : SimpleGraph V) (S : Finset V) (x a b c : V)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hab : ¬(cutVertex H x).Reachable a b)
    (hac : ¬(cutVertex H x).Reachable a c)
    (hbc : ¬(cutVertex H x).Reachable b c) : 3 ≤ branchCount H S x := by
  let f := (cutVertex H x).connectedComponentMk
  have hab' : f a ≠ f b := fun h => hab (ConnectedComponent.exact h)
  have hac' : f a ≠ f c := fun h => hac (ConnectedComponent.exact h)
  have hbc' : f b ≠ f c := fun h => hbc (ConnectedComponent.exact h)
  have hs : ({f a,f b,f c}:Finset _) ⊆ (S.erase x).image f := by
    intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨a,Finset.mem_erase.mpr ⟨hax,ha⟩,rfl⟩
    · exact Finset.mem_image.mpr ⟨b,Finset.mem_erase.mpr ⟨hbx,hb⟩,rfl⟩
    · exact Finset.mem_image.mpr ⟨c,Finset.mem_erase.mpr ⟨hcx,hc⟩,rfl⟩
  have hh := Finset.card_le_card hs
  have hcard : ({f a,f b,f c}:Finset _).card = 3 := by simp [hab',hac',hbc']
  rw [hcard] at hh
  exact hh

theorem eventually_conn_of_limit (G : BondGraph V E) (l : E → unitInterval)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hq : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) (hne : ∀ e, l e ≠ p)
    {x y : V} (hxy : Conn G (openEdges l p) x y) :
    ∀ᶠ n in atTop, Conn G (openEdges l (q n)) x y := by
  rw [openEdges_eq_iUnion_of_tendsto l p hne q hq hlim,conn_iUnion_iff G _
    (fun m n hmn => openEdges_mono l (hmono hmn))] at hxy
  obtain ⟨n,hn⟩ := hxy
  exact eventually_atTop.mpr ⟨n,fun m hm => conn_mono G (openEdges_mono l (hmono hm)) hn⟩

theorem eventually_encounterCount_three (G : BondGraph V E) (l : E → unitInterval)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hq : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) (hne : ∀ e, l e ≠ p)
    (hfin : ∀ n x, (cluster G (openEdges l (q n)) x).Finite)
    (hbranch : ∀ x, IsEncounter G (openEdges l p) x → ∀ a,
      Conn G (openEdges l p) x a → (cluster G (cutConfig G (openEdges l p) x) a).Infinite →
      ∃ z ∈ cluster G (cutConfig G (openEdges l p) x) a, z ≠ x ∧ IsEncounter G (openEdges l p) z)
    (x : V) (hx : IsEncounter G (openEdges l p) x) :
    ∀ᶠ n in atTop, 3 ≤ encounterCount G (openEdges l p) (openEdges l (q n)) x := by
  obtain ⟨a,b,c,hxa,hxb,hxc,ha,hb,hc,hab,hac,hbc⟩ := hx
  obtain ⟨a',haa',hax,ha'⟩ := hbranch x ⟨a,b,c,hxa,hxb,hxc,ha,hb,hc,hab,hac,hbc⟩ a hxa ha
  obtain ⟨b',hbb',hbx,hb'⟩ := hbranch x ⟨a,b,c,hxa,hxb,hxc,ha,hb,hc,hab,hac,hbc⟩ b hxb hb
  obtain ⟨c',hcc',hcx,hc'⟩ := hbranch x ⟨a,b,c,hxa,hxb,hxc,ha,hb,hc,hab,hac,hbc⟩ c hxc hc
  have hx' : IsEncounter G (openEdges l p) x := ⟨a,b,c,hxa,hxb,hxc,ha,hb,hc,hab,hac,hbc⟩
  have hac' : Conn G (openEdges l p) x a' := conn_trans G _ hxa (conn_mono G (fun _ h => h.1) haa')
  have hbc' : Conn G (openEdges l p) x b' := conn_trans G _ hxb (conn_mono G (fun _ h => h.1) hbb')
  have hxc' : Conn G (openEdges l p) x c' := conn_trans G _ hxc (conn_mono G (fun _ h => h.1) hcc')
  filter_upwards [eventually_conn_of_limit G l p q hmono hq hlim hne hac',
    eventually_conn_of_limit G l p q hmono hq hlim hne hbc',
    eventually_conn_of_limit G l p q hmono hq hlim hne hxc'] with n han hbn hcn
  rw [encounterCount,ite_eq_left hx']
  have hm (z : V) (hz : Conn G (openEdges l (q n)) x z) (he : IsEncounter G (openEdges l p) z) :
      z ∈ markedCluster G (openEdges l p) (openEdges l (q n)) x := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,he⟩
    have ht : z ∈ cluster G (openEdges l (q n)) x := hz
    rwa [←clusterFinset_coe G _ x (hfin n x)] at ht
  apply branchCount_three _ _ x a' b' c' (hm _ han ha') (hm _ hbn hb') (hm _ hcn hc') hax hbx hcx
  · intro ht
    rw [cutVertex_open] at ht
    exact hab (conn_trans G _ haa' (conn_trans G _ ((conn_iff_reachable G _ a' b').mpr ht) (conn_symm G _ hbb')))
  · intro ht
    rw [cutVertex_open] at ht
    exact hac (conn_trans G _ haa' (conn_trans G _ ((conn_iff_reachable G _ a' c').mpr ht) (conn_symm G _ hcc')))
  · intro ht
    rw [cutVertex_open] at ht
    exact hbc (conn_trans G _ hbb' (conn_trans G _ ((conn_iff_reachable G _ b' c').mpr ht) (conn_symm G _ hcc')))

end Percolation

namespace Percolation
open MeasureTheory SimpleGraph Filter Topology
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Fintype ι]

theorem critical_encounter_density_zero
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hp : 0 < pc G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l,
      (if IsEncounter G (openEdges l (pc G)) (root i) then 1 else 0) ∂labelLaw) = 0 := by
  obtain ⟨q,hmono,hq,hlim⟩ := exists_seq_strictMono_tendsto' hp
  let d (l : E → unitInterval) : ℝ≥0∞ := ∑ i, ENNReal.ofReal (weight i) *
    if IsEncounter G (openEdges l (pc G)) (root i) then 1 else 0
  let f (n : ℕ) (l : E → unitInterval) : ℝ≥0∞ := ∑ i, ENNReal.ofReal (weight i) *
    (encounterCount G (openEdges l (pc G)) (openEdges l (q n)) (root i) : ℝ≥0∞)
  have hd : Measurable d := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (Measurable.ite ((measurableSet_isEncounter G (root i)).preimage
      (measurable_openEdges (pc G))) measurable_const measurable_const)
  have hf n : Measurable (f n) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
      (measurable_encounterCount G (pc G) (q n) (root i)))
  have hdint : (∫⁻ l, d l ∂labelLaw) = ∑ i, ENNReal.ofReal (weight i) * ∫⁻ l,
      (if IsEncounter G (openEdges l (pc G)) (root i) then 1 else 0) ∂labelLaw := by
    rw [show d = _ from rfl,lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    · intro i _
      exact measurable_const.mul (Measurable.ite ((measurableSet_isEncounter G (root i)).preimage
        (measurable_openEdges (pc G))) measurable_const measurable_const)
  have hbound n : (∫⁻ l, f n l ∂labelLaw) ≤ 2 * ∫⁻ l, d l ∂labelLaw := by
    rw [hdint,show f n = _ from rfl,lintegral_finsetSum]
    · simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact expected_encounterCount_le G hconn hloc root weight htr (fun i => (hw i).le)
        (pc G) (q n) (hq n).2.le (fun x => subcritical_cluster_finite_ae G (q n) (hq n).2 x)
    · intro i _
      exact measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
        (measurable_encounterCount G (pc G) (q n) (root i)))
  have hfl : ∀ᵐ l ∂labelLaw, ∀ n x, (cluster G (openEdges l (q n)) x).Finite :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun x => label_cluster_finite_ae_subcritical G (q n) (hq n).2 x
  have hbl : ∀ᵐ l ∂labelLaw, ∀ x, IsEncounter G (openEdges l (pc G)) x → ∀ a,
      Conn G (openEdges l (pc G)) x a → (cluster G (cutConfig G (openEdges l (pc G)) x) a).Infinite →
      ∃ z ∈ cluster G (cutConfig G (openEdges l (pc G)) x) a, z ≠ x ∧ IsEncounter G (openEdges l (pc G)) z := by
    apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
      (p := fun ω : Set E => ∀ x, IsEncounter G ω x → ∀ a,
        Conn G ω x a → (cluster G (cutConfig G ω x) a).Infinite →
        ∃ z ∈ cluster G (cutConfig G ω x) a, z ≠ x ∧ IsEncounter G ω z)
      (measurable_openEdges (pc G)).aemeasurable
    rw [map_openEdges]
    exact encounter_branches_ae G hconn hloc root weight htr hw hw1 hcov (pc G)
  have hlow : ∀ᵐ l ∂labelLaw, 3 * d l ≤ liminf (fun n => f n l) atTop := by
    filter_upwards [hfl,hbl,ae_labels_ne (E := E) (pc G)] with l hl hb hn
    refine le_liminf_of_le (by isBoundedDefault) ?_
    have he (i : ι) : ∀ᶠ n in atTop,
        (3:ℝ≥0∞) * (if IsEncounter G (openEdges l (pc G)) (root i) then 1 else 0) ≤
        (encounterCount G (openEdges l (pc G)) (openEdges l (q n)) (root i) : ℝ≥0∞) := by
      by_cases hi : IsEncounter G (openEdges l (pc G)) (root i)
      · filter_upwards [eventually_encounterCount_three G l (pc G) q hmono.monotone
          (fun n => (hq n).2.le) hlim hn hl hb (root i) hi] with n hnc
        simpa only [ite_eq_left hi,mul_one] using (show (3:ℝ≥0∞) ≤ (encounterCount G (openEdges l (pc G)) (openEdges l (q n)) (root i):ℝ≥0∞) from by exact_mod_cast hnc)
      · filter_upwards [] with n
        simp only [ite_eq_right hi,mul_zero,zero_le]
    filter_upwards [(eventually_all_finset (Finset.univ : Finset ι)).mpr (fun i _ => he i)] with n hnn
    dsimp [d,f]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [←mul_assoc,mul_comm (3:ℝ≥0∞),mul_assoc]
    exact mul_le_mul_right (hnn i hi) _
  have hineq : 3 * (∫⁻ l, d l ∂labelLaw) ≤ 2 * ∫⁻ l, d l ∂labelLaw := by
    calc
      _ = ∫⁻ l, 3 * d l ∂labelLaw := (lintegral_const_mul' _ _ ENNReal.ofNat_ne_top).symm
      _ ≤ ∫⁻ l, liminf (fun n => f n l) atTop ∂labelLaw := lintegral_mono_ae hlow
      _ ≤ liminf (fun n => ∫⁻ l, f n l ∂labelLaw) atTop := lintegral_liminf_le hf
      _ ≤ _ := by
        refine liminf_le_of_le (by isBoundedDefault) ?_
        intro b hb
        obtain ⟨n,hn⟩ := hb.exists
        exact hn.trans (hbound n)
  have hdle (l : E → unitInterval) : d l ≤ 1 := by
    calc
      _ ≤ ∑ i, ENNReal.ofReal (weight i) * 1 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_right
        split_ifs <;> simp
      _ = 1 := by
        simp only [mul_one,←ENNReal.ofReal_sum_of_nonneg (fun i _ => (hw i).le),hw1,ENNReal.ofReal_one]
  have hdf : (∫⁻ l, d l ∂labelLaw) ≠ ⊤ := by
    have he : (∫⁻ l, d l ∂labelLaw) ≤ 1 := (lintegral_mono hdle).trans_eq (by simp)
    exact ne_of_lt (he.trans_lt ENNReal.one_lt_top)
  rw [←hdint]
  by_contra hne
  exact (not_lt_of_ge hineq) (ENNReal.mul_lt_mul_left hne hdf (by norm_num))

theorem critical_encounter_root_zero
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hp : 0 < pc G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) (i : ι) :
    law (pc G) {ω | IsEncounter G ω (root i)} = 0 := by
  have hd := critical_encounter_density_zero G hconn hloc hp root weight htr hw hw1 hcov
  have hi : ENNReal.ofReal (weight i) * ∫⁻ l,
      (if IsEncounter G (openEdges l (pc G)) (root i) then (1:ℝ≥0∞) else 0) ∂labelLaw = 0 := by
    exact (Finset.sum_eq_zero_iff.mp hd) i (Finset.mem_univ i)
  have hz : (∫⁻ l, (if IsEncounter G (openEdges l (pc G)) (root i) then (1:ℝ≥0∞) else 0) ∂labelLaw) = 0 :=
    (mul_eq_zero.mp hi).resolve_left ((ENNReal.ofReal_pos.mpr (hw i)).ne')
  rw [←map_openEdges (pc G),Measure.map_apply (measurable_openEdges (pc G))
    (measurableSet_isEncounter G (root i))]
  have he : (fun l : E → unitInterval => if IsEncounter G (openEdges l (pc G)) (root i) then (1:ℝ≥0∞) else 0) =
      ((fun l : E → unitInterval => openEdges l (pc G)) ⁻¹' {ω | IsEncounter G ω (root i)}).indicator (fun _ => 1) := rfl
  rw [he,lintegral_indicator ((measurableSet_isEncounter G (root i)).preimage (measurable_openEdges (pc G)))] at hz
  simpa only [lintegral_const,Measure.restrict_apply_univ,one_mul] using hz

theorem critical_encounter_zero
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hp : 0 < pc G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) (x : V) :
    law (pc G) {ω | IsEncounter G ω x} = 0 := by
  obtain ⟨i,a,⟨b,hab⟩,rfl⟩ := hcov x
  have he : {ω | IsEncounter G ω (a (root i))} =
      (fun ω : Set E => b ⁻¹' ω) ⁻¹' {ω | IsEncounter G ω (root i)} := by
    ext ω
    exact (isEncounter_aut_iff G a b hab ω (root i)).symm
  rw [he,←Measure.map_apply (measurable_set_preimage b) (measurableSet_isEncounter G (root i)),
    law_map_preimage_equiv]
  exact critical_encounter_root_zero G hconn hloc hp root weight htr hw hw1 hcov i

end Percolation

end OAI
