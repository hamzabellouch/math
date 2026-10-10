import OAI.Analysis.LienardCycles.PeriodicOval

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology
namespace QuinticLienard
lemma stable_positive_arc {P : Type uP} [TopologicalSpace P] {p : P}
    {f g : P × ℝ → ℝ}
    (hd : ∀ q t, HasDerivAt (fun s=>f (q,s)) (g (q,t)) t)
    (hc : ∀ t ∈ Ioo (0:ℝ) 1, ContinuousAt f (p,t))
    (hg0 : ContinuousAt g (p,0)) (hg1 : ContinuousAt g (p,1))
    (hf0 : ∀ᶠ q in 𝓝 p, f (q,0)=0) (hf1 : ∀ᶠ q in 𝓝 p, f (q,1)=0)
    (hpos : ∀ t ∈ Ioo (0:ℝ) 1, 0<f (p,t))
    (h0 : 0<g (p,0)) (h1 : g (p,1)<0) :
    ∀ᶠ q in 𝓝 p, ∀ t ∈ Ioo (0:ℝ) 1, 0<f (q,t) := by
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp (hg0.eventually (eventually_gt_nhds h0))
  obtain ⟨C,hC,D,hD,hCD⟩ := mem_nhds_prod_iff.mp (hg1.eventually (eventually_lt_nhds h1))
  obtain ⟨e,he,heB⟩ := Metric.mem_nhds_iff.mp hB
  obtain ⟨d,hdp,hdD⟩ := Metric.mem_nhds_iff.mp hD
  let δ := min (min e d) 1 / 4
  have hδ : 0<δ := div_pos (lt_min (lt_min he hdp) zero_lt_one) (by norm_num)
  have hδe : δ<e := by dsimp [δ]; have h:=min_le_left (min e d) 1; have h':=min_le_left e d; linarith
  have hδd : δ<d := by dsimp [δ]; have h:=min_le_left (min e d) 1; have h':=min_le_right e d; linarith
  have hδ1 : δ<1/2 := by dsimp [δ]; have h:=min_le_right (min e d) 1; linarith
  have hmid : ∀ᶠ q in 𝓝 p, ∀ t ∈ Icc δ (1-δ), 0<f (q,t) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have ht' : t ∈ Ioo (0:ℝ) 1 := ⟨hδ.trans_le ht.1,by linarith [ht.2]⟩
    exact (hc t ht').eventually (eventually_gt_nhds (hpos t ht'))
  filter_upwards [hA,hC,hf0,hf1,hmid] with q hqA hqC hq0 hq1 hqm
  intro t ht
  by_cases htl : t≤δ
  · have hm : StrictMonoOn (fun s=>f (q,s)) (Icc 0 δ) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 δ)
        (fun s _=>(hd q s).continuousAt.continuousWithinAt)
      intro s hs
      rw [(hd q s).deriv]
      apply hAB ⟨hqA,heB ?_⟩
      have hs' := interior_subset hs
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hs'.1]
      exact hs'.2.trans_lt hδe
    have h:=hm ⟨le_rfl,hδ.le⟩ ⟨ht.1.le,htl⟩ ht.1
    simpa only [hq0] using h
  · by_cases htr : 1-δ≤t
    · have hm : StrictAntiOn (fun s=>f (q,s)) (Icc (1-δ) 1) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc (1-δ) 1)
          (fun s _=>(hd q s).continuousAt.continuousWithinAt)
        intro s hs
        rw [(hd q s).deriv]
        apply hCD ⟨hqC,hdD ?_⟩
        have hs' := interior_subset hs
        rw [Metric.mem_ball,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hs'.2)]
        linarith [hs'.1]
      have h:=hm ⟨htr,ht.2.le⟩ ⟨by linarith,le_rfl⟩ ht.2
      simpa only [hq1] using h
    · exact hqm t ⟨(lt_of_not_ge htl).le,(lt_of_not_ge htr).le⟩
lemma stable_positive_between {P : Type uP} [TopologicalSpace P] {p : P}
    {f g : P × ℝ → ℝ} {α β : P → ℝ}
    (hd : ∀ q t, HasDerivAt (fun s=>f (q,s)) (g (q,t)) t)
    (hc : Continuous f) (hg : Continuous g)
    (hα : ContinuousAt α p) (hβ : ContinuousAt β p)
    (hf0 : ∀ᶠ q in 𝓝 p,f (q,α q)=0) (hf1 : ∀ᶠ q in 𝓝 p,f (q,β q)=0)
    (hlt : α p<β p) (hpos : ∀ t ∈ Ioo (α p) (β p),0<f (p,t))
    (h0 : 0<g (p,α p)) (h1 : g (p,β p)<0) :
    ∀ᶠ q in 𝓝 p,α q<β q ∧ ∀ t ∈ Ioo (α q) (β q),0<f (q,t) := by
  let θ : P × ℝ → ℝ := fun q=>α q.1+(β q.1-α q.1)*q.2
  have hα' (t : ℝ) : ContinuousAt (fun q : P × ℝ=>α q.1) (p,t) := hα.comp continuousAt_fst
  have hβ' (t : ℝ) : ContinuousAt (fun q : P × ℝ=>β q.1) (p,t) := hβ.comp continuousAt_fst
  have hθ (t : ℝ) : ContinuousAt θ (p,t) :=
    (hα' t).add (((hβ' t).sub (hα' t)).mul continuousAt_snd)
  have hf : ∀ t,ContinuousAt (fun q : P × ℝ=>f (q.1,θ q)) (p,t) :=
    fun t=>hc.continuousAt.comp (continuousAt_fst.prodMk (hθ t))
  have hgg : ∀ t,ContinuousAt (fun q : P × ℝ=>(β q.1-α q.1)*g (q.1,θ q)) (p,t) :=
    fun t=>((hβ' t).sub (hα' t)).mul (hg.continuousAt.comp (continuousAt_fst.prodMk (hθ t)))
  have hdd (q : P) (t : ℝ) : HasDerivAt (fun s=>f (q,θ (q,s))) ((β q-α q)*g (q,θ (q,t))) t := by
    convert! (hd q (θ (q,t))).scomp t (((hasDerivAt_id t).const_mul (β q-α q)).const_add (α q)) using 1
    ring
  have hne := stable_positive_arc hdd (fun t _=>hf t) (hgg 0) (hgg 1)
    (by simpa [θ] using hf0) (by simpa [θ] using hf1)
    (fun t ht=>hpos _ ⟨by dsimp [θ];nlinarith [mul_pos (sub_pos.mpr hlt) ht.1],by dsimp [θ];nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr ht.2)]⟩)
    (by simpa [θ] using mul_pos (sub_pos.mpr hlt) h0)
    (by simpa [θ] using mul_neg_of_pos_of_neg (sub_pos.mpr hlt) h1)
  filter_upwards [hne,(hα.prodMk hβ).eventually (isOpen_lt continuous_fst continuous_snd |>.mem_nhds hlt)] with q hq hlq
  refine ⟨hlq,?_⟩
  intro t ht
  have hl : 0<β q-α q := sub_pos.mpr hlq
  have hu : (t-α q)/(β q-α q) ∈ Ioo (0:ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr ht.1) hl,(div_lt_one hl).mpr (sub_lt_sub_right ht.2 _)⟩
  have he : θ (q,(t-α q)/(β q-α q))=t := by dsimp [θ];field_simp;ring
  simpa only [he] using hq _ hu
end QuinticLienard

end OAI
