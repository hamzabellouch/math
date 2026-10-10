import OAI.Combinatorics.TreewidthL1.NoiseCube

namespace OAI

universe treewidthLevel1 treewidthLevel2 treewidthLevel3

namespace BoundedTreewidthL1.TreeCache
open _root_.OAI.BoundedTreewidthL1.RootedTree AnchorCache ParticleBatch
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} [Fintype ι] [Nonempty ι] (T : SimpleGraph I) (hT : T.IsTree) (root : I)
  (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (X : I)
  (S : I → (ι → V → ℝ) × (I → ι × ι))
  (hpairs : ∀ i p, (forest T hT root).parent i = some p →
      ∀ a ∈ active T hT root B D k d J i ∩ active T hT root B D k d J p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2)
lemma index_transport
    {I : Type treewidthLevel1} {V : Type treewidthLevel2} {ι : Type treewidthLevel3} [Fintype ι]
    [Nonempty ι] (T : SimpleGraph I) (hT : T.IsTree) (root : I) (B : I → Finset V) (D : I → V → ℝ)
    (k : ℕ) (d : V → V → ℝ) (J : ℝ) (X : I) (S : I → (ι → V → ℝ) × (I → ι × ι))
    (hpairs : ∀ (i p : I), (BoundedTreewidthL1.RootedTree.forest T hT root).parent i = some p → ∀ a
      ∈ BoundedTreewidthL1.TreeCache.active T hT root B D k d J i ∩
      BoundedTreewidthL1.TreeCache.active T hT root B D k d J p, (S i).2 a = (S p).2 a ∧ (S i).1 ((S
      i).2 a).1 = (S p).1 ((S p).2 a).1 ∧ (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2)
    (e a b : ℕ) (he : e ≤ (forest T hT root).depth X)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hab : a ≤ b) (hbe : b ≤ e) (u : Bool) :
    let v := (downPath T hT root X).getVert
    pairIndex (S (v b)).2 (v a) u = pairIndex (S (v a)).2 (v a) u ∧
    (S (v b)).1 (pairIndex (S (v a)).2 (v a) u) = (S (v a)).1 (pairIndex (S (v a)).2 (v a) u) := by
  dsimp only
  obtain ⟨h₁,h₂,h₃⟩ := pair_transport T hT root B D k d J X S hpairs e a b he ha hab hbe
  constructor
  · simp only [pairIndex,h₁]
  · cases u
    · simpa only [pairIndex,Bool.false_eq_true,ite_false,h₁] using h₂
    · simpa only [pairIndex,ite_true,h₁] using h₃
include hpairs
lemma index_retained (e a b : ℕ) (he : e ≤ (forest T hT root).depth X)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hab : a ≤ b) (hbe : b < e) (u : Bool) :
    let v := (downPath T hT root X).getVert
    pairIndex (S (v a)).2 (v a) u ∈ usedPairs
      (AnchorTreeParticles.retained (forest T hT root) (active T hT root B D k d J) (v (b+1))) (S (v (b+1))).2 := by
  dsimp only
  rw [← (index_transport T hT root B D k d J X S hpairs e a (b+1) he ha (by omega) (by omega) u).1]
  apply pairIndex_mem
  rw [AnchorTreeParticles.retained,parent_getVert T hT root X b (by omega)]
  exact Finset.mem_inter.mpr ⟨active_on_path T hT root B D k d J X e a (b+1) he ha (by omega) (by omega),
    active_on_path T hT root B D k d J X e a b he ha hab hbe.le⟩
lemma index_avoids (huniq : ∀ i, PairUnique (active T hT root B D k d J i) (S i).2)
    (e a b : ℕ) (he : e ≤ (forest T hT root).depth X)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hab : a < b) (hbe : b ≤ e) (u w : Bool) :
    let v := (downPath T hT root X).getVert
    pairIndex (S (v a)).2 (v a) u ≠ pairIndex (S (v b)).2 (v b) w := by
  dsimp only
  rw [← (index_transport T hT root B D k d J X S hpairs e a b he ha hab.le hbe u).1]
  intro hh
  have hn := (huniq _ _ (active_on_path T hT root B D k d J X e a b he ha hab.le hbe)
    _ (active_self T hT root B D k d J _) u w hh).1
  exact path_ne T hT root X a b (by omega) (by omega) (by omega) hn
end BoundedTreewidthL1.TreeCache

namespace BoundedTreewidthL1.CachedEnsemble
open _root_.OAI.BoundedTreewidthL1.RootedTree TreeCache AnchorCache ParticleBatch ExpandedConstruction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} [Fintype I] [Fintype V] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (T : SimpleGraph I) (hT : T.IsTree) (root : I) (B : I → Finset V)
  (cover : ∀ v, ∃ i, v ∈ B i) (run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
  (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
  (S : I → (ι → V → ℝ) × (I → ι × ι)) (M : ℝ)
  (hpairs : ∀ i p, (forest T hT root).parent i = some p →
      ∀ a ∈ active T hT root B D k d J i ∩ active T hT root B D k d J p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2)
  (htrace : ∀ i p, (forest T hT root).parent i = some p →
      particleTrace M (S i).1 (B i) = particleTrace M (S p).1 (B i))
noncomputable def data : TreeData (V := V) (ι := ι) T M where
  parent := (forest T hT root).parent
  orient := fun _ _ h => edge_orientation T hT root h
  anti := ExpandedAnchor.parent_antisymm (forest T hT root)
  F := fun i => (S i).1
  B := B
  cover := cover
  run := run
  fresh₁ := fun i => ((S i).2 i).1
  fresh₂ := fun i => ((S i).2 i).2
  C := fun i => usedPairs (AnchorTreeParticles.retained (forest T hT root) (active T hT root B D k d J) i) (S i).2
  retained := ExpandedAnchor.retained_functions _ _ S hpairs
  trace := fun _ _ hi => (htrace _ _ hi).symm

include hpairs htrace
lemma height (hM : 0 < M)
    (huniq : ∀ i, PairUnique (active T hT root B D k d J i) (S i).2)
    (X Y : I) (y z : V) (hy : y ∈ B Y) (s e l a t : ℕ)
    (he : e ≤ (forest T hT root).depth X) (hst : s ≤ t) (hte : t < e) (hat : a < t)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hz : z ∈ B ((downPath T hT root X).getVert e))
    (hlen : (forest T hT Y).depth ((downPath T hT root X).getVert e) = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e →
      (downPath T hT Y ((downPath T hT root X).getVert e)).getVert (l+(b-s)) = (downPath T hT root X).getVert b)
    (u : Bool) (ε : ℝ)
    (hF : ∀ v, |(S ((downPath T hT root X).getVert a)).1
      (pairIndex (S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a) u) v| ≤ M)
    (hlo : ε ≤ (S ((downPath T hT root X).getVert a)).1
      (pairIndex (S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a) u) z+M)
    (hhi : ε ≤ M-(S ((downPath T hT root X).getVert a)).1
      (pairIndex (S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a) u) z)
    (hgap : ∀ x ∈ B ((downPath T hT root X).getVert t), ε ≤
      |(S ((downPath T hT root X).getVert a)).1
        (pairIndex (S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a) u) z-
       (S ((downPath T hT root X).getVert a)).1
        (pairIndex (S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a) u) x|) :
    ε/2 ≤ (data T hT root B cover run D k d J S M hpairs htrace).dist y z := by
  let v := (downPath T hT root X).getVert
  let r := pairIndex (S (v a)).2 (v a) u
  have hf (b : ℕ) (hab : a ≤ b) (hbe : b ≤ e) : (S (v b)).1 r = (S (v a)).1 r :=
    (index_transport T hT root B D k d J X S hpairs e a b he ha hab hbe u).2
  refine (data T hT root B cover run D k d J S M hpairs htrace).height_segment hT hM Fintype.card_pos
    Y (v e) y z hy hz v s e l t hst hte hlen hpath ?_ r ?_ ?_ ?_ ε ?_ ?_ ?_
  · intro b htb hbe
    exact parent_getVert T hT root X b (by omega)
  · intro b htb hbe
    exact (hf b (by omega) hbe).trans (hf t hat.le hte.le).symm
  · intro b htb hbe
    refine ⟨index_retained T hT root B D k d J X S hpairs e a b he ha (by omega) hbe u, ?_, ?_⟩
    · exact index_avoids T hT root B D k d J X S hpairs huniq e a b he ha (by omega) hbe.le u false
    · exact index_avoids T hT root B D k d J X S hpairs huniq e a b he ha (by omega) hbe.le u true
  · change ∀ x, -M ≤ (S (v t)).1 r x ∧ (S (v t)).1 r x ≤ M
    rw [hf t hat.le hte.le]; exact fun x => abs_le.mp (hF x)
  · change ε ≤ (S (v t)).1 r z+M
    rw [hf t hat.le hte.le]; exact hlo
  · change ε ≤ M-(S (v t)).1 r z
    rw [hf t hat.le hte.le]; exact hhi
  · change ∀ x ∈ B (v t), ε ≤ |(S (v t)).1 r z-(S (v t)).1 r x|
    rw [hf t hat.le hte.le]; exact hgap

lemma launch (hM : 0 < M)
    (huniq : ∀ i, PairUnique (active T hT root B D k d J i) (S i).2)
    (X Y : I) (y z : V) (hy : y ∈ B Y) (s e l a : ℕ)
    (he : e ≤ (forest T hT root).depth X) (hsa : s ≤ a) (hae : a < e)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hz : z ∈ B ((downPath T hT root X).getVert e))
    (hlen : (forest T hT Y).depth ((downPath T hT root X).getVert e) = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e →
      (downPath T hT Y ((downPath T hT root X).getVert e)).getVert (l+(b-s)) = (downPath T hT root X).getVert b)
    (hbag : ∀ x ∈ B ((downPath T hT root X).getVert a),
      (S ((downPath T hT root X).getVert a)).1 ((S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a)).1 x =
      (S ((downPath T hT root X).getVert a)).1 ((S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a)).2 x)
    (hF : ∀ i r x, |(S i).1 r x| ≤ M) :
    |(S ((downPath T hT root X).getVert a)).1 ((S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a)).1 z-
      (S ((downPath T hT root X).getVert a)).1 ((S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a)).2 z|/2 ≤
    (data T hT root B cover run D k d J S M hpairs htrace).dist y z := by
  let v := (downPath T hT root X).getVert
  have hiu : ((S (v a)).2 (v a)).1 ≠ ((S (v a)).2 (v a)).2 := by
    intro hh
    have hb := (huniq (v a) _ (active_self T hT root B D k d J _) _
      (active_self T hT root B D k d J _) false true hh).2
    cases hb
  have hr (r : ι) (hr : r ∈ ({((S (v a)).2 (v a)).1,((S (v a)).2 (v a)).2} : Finset ι)) :
      ∃ u, r = pairIndex (S (v a)).2 (v a) u := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  apply (data T hT root B cover run D k d J S M hpairs htrace).launch_segment hT hM Fintype.card_pos
    Y (v e) y z hy hz v s e l a hsa hae hlen hpath
  · intro b hab hbe; exact parent_getVert T hT root X b (by omega)
  · exact hiu
  · exact hbag
  · intro r hmem b hab hbe
    obtain ⟨u,rfl⟩ := hr r hmem
    exact (index_transport T hT root B D k d J X S hpairs e a b he ha hab hbe u).2
  · exact ⟨index_retained T hT root B D k d J X S hpairs e a a he ha le_rfl hae false,
      index_retained T hT root B D k d J X S hpairs e a a he ha le_rfl hae true⟩
  · intro r hmem b hab hbe
    obtain ⟨u,rfl⟩ := hr r hmem
    exact ⟨index_retained T hT root B D k d J X S hpairs e a b he ha (by omega) hbe u,
      index_avoids T hT root B D k d J X S hpairs huniq e a b he ha (by omega) hbe.le u false,
      index_avoids T hT root B D k d J X S hpairs huniq e a b he ha (by omega) hbe.le u true⟩
  · intro r _ x; exact abs_le.mp (hF _ r x)
end BoundedTreewidthL1.CachedEnsemble

namespace BoundedTreewidthL1.NoiseCube
open MeasureTheory Set LaunchNoise
open scoped unitInterval ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
lemma OrdinarySeed.good_location {V : Type*} [MetricSpace V] {h : V → ℝ} {α π η : ℝ}
    (seed : OrdinarySeed h α π η) (x : V) (hx : 0 < h x) :
    ENNReal.ofReal (π/2) ≤ locationLaw seed.mass {a | GoodBump h α η (seed.bump a) x} := by
  have hh := seed.good x hx
  have he := Measure.map_apply (μ := noiseLaw seed.m seed.mass)
    (measurable_fst.comp measurable_snd) (MeasurableSet.of_discrete (s := {a | GoodBump h α η (seed.bump a) x}))
  change (Measure.map (fun ω : NoiseSpace seed.n seed.m => ω.2.1) (noiseLaw seed.m seed.mass)) _ = _ at he
  rw [noise_locationLaw] at he
  exact he.symm ▸ hh

lemma node_gap {V : Type*} [MetricSpace V] [Fintype V] {n : ℕ}
    (h : Fin (n+1) → V → ℝ) (α π η : ℝ)
    (seed : (i : Fin (n+1)) → OrdinarySeed (h i) α π η)
    (a : Fin (n+1)) (x : V) (B : Finset V)
    (F : ((i : Fin (n+1)) → NoiseSpace (seed i).n (seed i).m) → V → ℝ)
    (hF : ∀ v, Measurable (fun ω => F ω v))
    (haff : ∀ rest : (j : Fin n) → NoiseSpace (seed (a.succAbove j)).n (seed (a.succAbove j)).m,
      ∃ f : V → ℝ, ∀ u v, F (Fin.insertNth a u rest) v = f v + noiseG (h a) (seed a).bump u v)
    (t β γ : ℝ) (ht : 0 ≤ t) (hβ : 0 < β) (hγ : 0 < γ) (hπ : 0 ≤ π) (hx : 0 < h a x)
    (hamp : ∀ loc, GoodBump (h a) α η ((seed a).bump loc) x → ∀ s ∈ B,
      β ≤ |h a x-h a s| ∨ ∃ j, γ ≤ |(seed a).bump loc j x-(seed a).bump loc j s|)
    (hbudget : (B.card : ℝ)*(2*t/β+2*t/γ) ≤ 1/2) :
    ENNReal.ofReal (π/4) ≤ (Measure.pi (fun i => noiseLaw (seed i).m (seed i).mass))
      {ω | ∀ s ∈ B, t ≤ |F ω x-F ω s|} := by
  let (i : Fin (n+1)) := (seed i).probability
  apply pi_conditioned _ a _
  · simp_rw [ofPred_forall]
    exact MeasurableSet.iInter (fun s => MeasurableSet.iInter (fun _ => measurableSet_le measurable_const ((hF x).sub (hF s)).abs))
  · intro rest
    obtain ⟨f,hf⟩ := haff rest
    have he : {u | ∀ s ∈ B, t ≤ |F (Fin.insertNth a u rest) x-F (Fin.insertNth a u rest) s|} =
        {u | ∀ s : B, t ≤ |(f x-f s)+(h a x-h a s)*noiseXi u+
          ∑ j, (u.2.2 j : ℝ)*((seed a).bump u.2.1 j x-(seed a).bump u.2.1 j s)|} := by
      ext u
      simp only [mem_ofPred_eq,hf]
      have hab (s : V) : f x+noiseG (h a) (seed a).bump u x-(f s+noiseG (h a) (seed a).bump u s) =
          (f x-f s)+(h a x-h a s)*noiseXi u+
          ∑ j, (u.2.2 j : ℝ)*((seed a).bump u.2.1 j x-(seed a).bump u.2.1 j s) := by
        simp only [noiseG,noiseV,Finset.sum_sub_distrib,mul_sub]
        ring
      simp_rw [hab]
      constructor
      · intro h s; exact h s s.property
      · intro h s hs; exact h ⟨s,hs⟩
    change ENNReal.ofReal (π/4) ≤ (noiseLaw (seed a).m (seed a).mass) {u | ∀ s ∈ B, t ≤ |F (Fin.insertNth a u rest) x-F (Fin.insertNth a u rest) s|}
    rw [he]
    have hh := conditioned_gap (seed a).mass (seed a).mass_nonneg (seed a).mass_total
      (fun s : B => f x-f s) (fun s : B => h a x-h a s)
      (fun loc (s : B) j => (seed a).bump loc j x-(seed a).bump loc j s)
      {loc | GoodBump (h a) α η ((seed a).bump loc) x} t β γ (π/2) ht hβ hγ (by positivity)
      (OrdinarySeed.good_location (seed a) x hx) (fun loc hl s => hamp loc hl s s.property)
      (by simpa only [Fintype.card_coe] using hbudget)
    convert hh using 1 ; congr 1 ; ring
end BoundedTreewidthL1.NoiseCube

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
lemma event_lower_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (hf0 : ∀ ω, 0 ≤ f ω)
    (E : Set Ω) (hE : MeasurableSet E) (p t : ℝ) (hp : 0 ≤ p)
    (hprob : ENNReal.ofReal p ≤ μ E) (hlower : ∀ ω ∈ E, t ≤ f ω) :
    p*t ≤ ∫ ω, f ω ∂μ := by
  by_cases ht : 0 ≤ t
  · have hd : Integrable (E.indicator (fun _ => t)) μ := (integrable_const t).indicator hE
    have hi := integral_mono hd hf (fun ω => by
      by_cases hω : ω ∈ E
      · simpa only [Set.indicator_of_mem hω] using hlower ω hω
      · simpa only [Set.indicator_of_notMem hω] using hf0 ω)
    have hpr : p ≤ μ.real E := by
      rw [measureReal_def]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ E)).mp hprob
    rw [integral_indicator hE, setIntegral_const,smul_eq_mul] at hi
    exact (mul_le_mul_of_nonneg_right hpr ht).trans hi
  · exact (mul_nonpos_of_nonneg_of_nonpos hp (le_of_not_ge ht)).trans (integral_nonneg hf0)

lemma gap_proxy {V : Type*} (d : V → V → ℝ) (F : V → ℝ) (x z : V) (B : Finset V)
    (L ε : ℝ) (hL : |F x-F z| ≤ L*d x z)
    (hgap : ∀ s ∈ B, ε ≤ |F x-F s|) :
    ∀ s ∈ B, ε-L*d x z ≤ |F z-F s| := by
  intro s hs
  have hh := abs_sub_le (F x) (F z) (F s)
  linarith [hgap s hs]

lemma gap_budget (k : ℕ) (β γ δ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (_ : 0 ≤ δ) (hδβ : δ ≤ β) (hδγ : δ ≤ γ) :
    (k:ℝ)*(2*(δ/(8*((k:ℝ)+1)))/β+2*(δ/(8*((k:ℝ)+1)))/γ) ≤ 1/2 := by
  have hk : 0 < (k:ℝ)+1 := by positivity
  have h₁ : 2*(δ/(8*((k:ℝ)+1)))/β ≤ 1/(4*((k:ℝ)+1)) := by
    apply (div_le_iff₀ hβ).mpr
    have hh := mul_le_mul_of_nonneg_left hδβ (show 0 ≤ 1/(4*((k:ℝ)+1)) by positivity)
    convert hh using 1 ; field_simp ; ring
  have h₂ : 2*(δ/(8*((k:ℝ)+1)))/γ ≤ 1/(4*((k:ℝ)+1)) := by
    apply (div_le_iff₀ hγ).mpr
    have hh := mul_le_mul_of_nonneg_left hδγ (show 0 ≤ 1/(4*((k:ℝ)+1)) by positivity)
    convert hh using 1 ; field_simp ; ring
  have h := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  apply h.trans
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  field_simp
  nlinarith
end BoundedTreewidthL1

namespace BoundedTreewidthL1.AnchorTreeParticles
open ParticleBatch ParticleSchedule
attribute [local instance 2000] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
noncomputable def positive {I : Type*} (R : RootedForest I) (B : I → Finset V) (A : I → Finset I)
    (g : I → I → V → ℝ) (a : I) : V → ℝ :=
  (state (ι := ι) R B A g a).1 ((state (ι := ι) R B A g a).2 a).1
lemma positive_affine {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, Nonempty (Ω i)]
    (R : RootedForest (Fin (n+1))) (B : Fin (n+1) → Finset V) (A : Fin (n+1) → Finset (Fin (n+1)))
    (H : (i : Fin (n+1)) → Ω i → V → ℝ) (a : Fin (n+1)) (hfresh : fresh R A a = {a})
    (hdistinct : ∀ ω : ∀ i, Ω i,
      ((state (ι := ι) R B A (fun i _ => H i (ω i)) a).2 a).1 ≠
      ((state (ι := ι) R B A (fun i _ => H i (ω i)) a).2 a).2) :
    ∀ rest : ∀ j : Fin n, Ω (a.succAbove j), ∃ f : V → ℝ,
      ∀ u v, positive (ι := ι) R B A (fun i _ => H i ((Fin.insertNth a u rest) i)) a v = f v+H a u v := by
  intro rest
  let u₀ : Ω a := Classical.choice inferInstance
  let ω₀ := Fin.insertNth a u₀ rest
  let pre := (R.parent a).elim (seed (ι := ι) (V := V) (J := Fin (n+1)))
    (state R B A (fun i _ => H i (ω₀ i)))
  let p := pickPair (B a) (usedPairs (retained R A a) pre.2) pre.1
  refine ⟨fun v => (pre.1 p.1 v+pre.1 p.2 v)/2,?_⟩
  intro u v
  have hpre := predecessor_congr_depth (ι := ι) R B A
    (fun i _ => H i ((Fin.insertNth a u rest) i)) (fun i _ => H i (ω₀ i)) a (by
      intro j hj
      have hja : j ≠ a := by intro hh; subst j; exact (lt_irrefl _ hj)
      obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq hja
      subst j
      simp only [ω₀,Fin.insertNth_apply_succAbove])
  have hp := congrFun (singleton_positive (ι := ι) R B A
    (fun i _ => H i ((Fin.insertNth a u rest) i)) a a (by convert! hfresh using 1) (hdistinct _)) v
  rw [hpre] at hp
  simpa only [positive,Fin.insertNth_apply_same] using hp

lemma measurable_positive {I Ω : Type*} [Fintype I] [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (R : RootedForest I) (B : I → Finset V) (A : I → Finset I)
    (g : Ω → I → I → V → ℝ) (hg : ∀ i a v, Measurable (fun ω => g ω i a v)) (a : I) (v : V) :
    Measurable (fun ω => positive (ι := ι) R B A (g ω) a v) := by
  have hs := measurable_state (ι := ι) R B A g hg a
  have hf (r : ι) : Measurable (fun ω => (state (ι := ι) R B A (g ω) a).1 r v) :=
    (measurable_pi_apply v).comp ((measurable_pi_apply r).comp hs.fst)
  have hi : Measurable (fun ω => ((state (ι := ι) R B A (g ω) a).2 a).1) :=
    ((measurable_pi_apply a).comp hs.snd).fst
  exact measurable_selected (fun ω r => (state (ι := ι) R B A (g ω) a).1 r v)
    (fun ω => ((state (ι := ι) R B A (g ω) a).2 a).1) hf hi
end BoundedTreewidthL1.AnchorTreeParticles

end OAI
