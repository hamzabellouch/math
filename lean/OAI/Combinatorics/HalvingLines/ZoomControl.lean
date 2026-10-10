import OAI.Combinatorics.HalvingLines.LocalZoom

namespace OAI

open Filter Topology

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma detPair_zero_parallel {u v : Point} (hv : v ≠ 0) (h : detPair u v=0) :
    ∃ a : ℝ, u=a • v := by
  by_cases h₁ : v.1=0
  · have h₂ : v.2≠0 := by intro hh; exact hv (Prod.ext h₁ hh)
    refine ⟨u.2/v.2,Prod.ext ?_ ?_⟩
    · change u.1=u.2/v.2*v.1
      rw [h₁,mul_zero]
      have he : u.1*v.2=0 := by simpa [detPair,h₁] using h
      exact (mul_eq_zero.mp he).resolve_right h₂
    · change u.2=u.2/v.2*v.2
      field_simp
  · refine ⟨u.1/v.1,Prod.ext ?_ ?_⟩
    · change u.1=u.1/v.1*v.1
      field_simp
    · change u.2=u.1/v.1*v.2
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff h₁).mpr
      dsimp [detPair] at h
      nlinarith

lemma map_eq_column (A : Point →L[ℝ] Point) (x : Point) :
    A x=x.1 • A (1,0)+x.2 • A (0,1) := by
  have hx : x=x.1 • ((1,0):Point)+x.2 • ((0,1):Point) := by ext <;> simp
  conv_lhs => rw [hx,map_add,map_smul,map_smul]

lemma detPair_map (A : Point →L[ℝ] Point) (u v : Point) :
    detPair (A u) (A v)=detPair (A (1,0)) (A (0,1))*detPair u v := by
  rw [map_eq_column A u,map_eq_column A v]
  dsimp [detPair]; ring

lemma map_injective_of_det (A : Point →L[ℝ] Point)
    (h : detPair (A (1,0)) (A (0,1)) ≠ 0) : Function.Injective A := by
  have he : A= (columnEquiv (A (1,0)) (A (0,1)) h).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact map_eq_column A x
  rw [he]
  exact (columnEquiv _ _ h).injective

lemma map_zero_of_two (A : Point →L[ℝ] Point) {u v : Point} (h : detPair u v ≠ 0)
    (hu : A u=0) (hv : A v=0) : A=0 := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨a,b,he⟩ := plane_span u v h x
  rw [he,map_add,map_smul,map_smul,hu,hv,smul_zero,smul_zero,add_zero]
  rfl

lemma three_lines_injective (A : Point →L[ℝ] Point) (hA : A≠0)
    (u v : Fin 3 → Point)
    (hu : ∀ i j, i≠j → detPair (u i) (u j) ≠ 0)
    (hv : ∀ i j, i≠j → detPair (v i) (v j) ≠ 0)
    (hline : ∀ i, detPair (A (u i)) (v i)=0) : Function.Injective A := by
  have hv0 (i : Fin 3) : v i≠0 := by
    obtain ⟨j,hj⟩ := exists_ne i
    intro he
    have hh := hv i j hj.symm
    simp only [he,detPair,Prod.fst_zero,Prod.snd_zero,zero_mul,sub_self,ne_eq,not_true_eq_false] at hh
  choose c hc using fun i => detPair_zero_parallel (hv0 i) (hline i)
  apply map_injective_of_det
  intro hdet
  have hp (i j : Fin 3) (hij : i≠j) : c i=0 ∨ c j=0 := by
    have hh := detPair_map A (u i) (u j)
    rw [hdet,zero_mul,hc,hc,detPair_smul] at hh
    have hz : c i*c j=0 := (mul_eq_zero.mp hh).resolve_right (hv i j hij)
    exact mul_eq_zero.mp hz
  have hz (i j : Fin 3) (hij : i≠j) (hi : c i=0) (hj : c j=0) : False := by
    apply hA
    apply map_zero_of_two A (hu i j hij)
    · rw [hc,hi,zero_smul]
    · rw [hc,hj,zero_smul]
  rcases hp 0 1 (by decide) with h0 | h1
  · rcases hp 1 2 (by decide) with h1 | h2
    · exact hz 0 1 (by decide) h0 h1
    · exact hz 0 2 (by decide) h0 h2
  · rcases hp 0 2 (by decide) with h0 | h2
    · exact hz 0 1 (by decide) h0 h1
    · exact hz 1 2 (by decide) h1 h2

lemma three_lines_uniform_conorm (v : Fin 3 → Point)
    (hv : ∀ i j, i≠j → detPair (v i) (v j) ≠ 0) (δ : ℝ) (hδ : 0<δ) :
    ∃ ε : ℝ, 0<ε ∧ ∀ (A : Point →L[ℝ] Point), ‖A‖=1 →
      ∀ u : Fin 3 → Point, (∀ i, ‖u i‖=1) →
      (∀ i j, i≠j → δ ≤ |detPair (u i) (u j)|) →
      (∀ i, detPair (A (u i)) (v i)=0) →
      ∀ y : Point, ‖y‖=1 → ε ≤ ‖A y‖ := by
  by_contra! hn
  have hex (n : ℕ) : ∃ (A : Point →L[ℝ] Point) (u : Fin 3 → Point) (y : Point),
      ‖A‖=1 ∧ (∀ i, ‖u i‖=1) ∧ (∀ i j, i≠j → δ ≤ |detPair (u i) (u j)|) ∧
      (∀ i, detPair (A (u i)) (v i)=0) ∧ ‖y‖=1 ∧ ‖A y‖ < 1/(n+1:ℝ) := by
    obtain ⟨A,hA,u,hu,hsep,hl,y,hy,hsmall⟩ := hn (1/(n+1:ℝ)) (by positivity)
    exact ⟨A,u,y,hA,hu,hsep,hl,hy,hsmall⟩
  choose A u y hA hu hsep hl hy hsmall using hex
  let Z := ((Point →L[ℝ] Point) × (Fin 3 → Point)) × Point
  let z : ℕ → Z := fun n => ((A n,u n),y n)
  have hz (n : ℕ) : z n∈closedBall (0:Z) 1 := by
    rw [mem_closedBall_zero_iff]
    change max (max ‖A n‖ ‖u n‖) ‖y n‖ ≤ 1
    rw [hA,hy,max_le_iff,max_le_iff]
    refine ⟨⟨le_rfl,?_⟩,le_rfl⟩
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr (fun i => (hu n i).le)
  obtain ⟨z₀,hz₀,ρ,hρ,hlim⟩ := (isCompact_closedBall (0:Z) 1).tendsto_subseq hz
  let A₀ := z₀.1.1
  let u₀ := z₀.1.2
  let y₀ := z₀.2
  have hAL : Tendsto (fun n => A (ρ n)) atTop (𝓝 A₀) := by
    exact ((continuous_fst.comp continuous_fst).tendsto z₀).comp hlim
  have huL : Tendsto (fun n => u (ρ n)) atTop (𝓝 u₀) := by
    exact ((continuous_snd.comp continuous_fst).tendsto z₀).comp hlim
  have hyL : Tendsto (fun n => y (ρ n)) atTop (𝓝 y₀) := by
    exact (continuous_snd.tendsto z₀).comp hlim
  have hAn : ‖A₀‖=1 := tendsto_nhds_unique hAL.norm (by simp only [hA]; exact tendsto_const_nhds)
  have hu_n (i : Fin 3) : ‖u₀ i‖=1 := tendsto_nhds_unique ((tendsto_pi_nhds.mp huL i).norm)
    (by simp only [hu]; exact tendsto_const_nhds)
  have hyn : ‖y₀‖=1 := tendsto_nhds_unique hyL.norm (by simp only [hy]; exact tendsto_const_nhds)
  have hsep₀ (i j : Fin 3) (hij : i≠j) : detPair (u₀ i) (u₀ j) ≠ 0 := by
    have hi := tendsto_pi_nhds.mp huL i
    have hj := tendsto_pi_nhds.mp huL j
    have hd : Tendsto (fun n => |detPair (u (ρ n) i) (u (ρ n) j)|) atTop
        (𝓝 |detPair (u₀ i) (u₀ j)|) := ((hi.fst_nhds.mul hj.snd_nhds).sub (hi.snd_nhds.mul hj.fst_nhds)).abs
    have hb := ge_of_tendsto hd (Eventually.of_forall (fun n => hsep (ρ n) i j hij))
    exact abs_pos.mp (hδ.trans_le hb)
  have hl₀ (i : Fin 3) : detPair (A₀ (u₀ i)) (v i)=0 := by
    have ht := ((continuous_fst.clm_apply continuous_snd).tendsto (A₀,u₀ i)).comp
      (hAL.prodMk_nhds (tendsto_pi_nhds.mp huL i))
    have hd : Tendsto (fun n => detPair (A (ρ n) (u (ρ n) i)) (v i)) atTop
        (𝓝 (detPair (A₀ (u₀ i)) (v i))) := (ht.fst_nhds.mul_const _).sub (ht.snd_nhds.mul_const _)
    exact tendsto_nhds_unique hd (by simp only [hl]; exact tendsto_const_nhds)
  have hInj := three_lines_injective A₀ (by intro he; rw [he,norm_zero] at hAn; norm_num at hAn)
    u₀ v hsep₀ hv hl₀
  have hzero : ‖A₀ y₀‖=0 := by
    have ht := (((continuous_fst.clm_apply continuous_snd).tendsto (A₀,y₀)).comp (hAL.prodMk_nhds hyL)).norm
    have hnlim : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
    have hbound : Tendsto (fun n => ‖A (ρ n) (y (ρ n))‖) atTop (𝓝 0) :=
      squeeze_zero (fun n => norm_nonneg _) (fun n => (hsmall (ρ n)).le) (hnlim.comp hρ.tendsto_atTop)
    exact tendsto_nhds_unique ht hbound
  have hye : y₀=0 := hInj ((norm_eq_zero.mp hzero).trans (map_zero A₀).symm)
  rw [hye,norm_zero] at hyn
  norm_num at hyn

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma detPair_equiv_ne_zero (B : Point ≃L[ℝ] Point) {u v : Point}
    (h : detPair u v≠0) : detPair (B u) (B v)≠0 := by
  intro he
  have ht := detPair_map B.symm.toContinuousLinearMap (B u) (B v)
  apply h
  simpa only [ContinuousLinearEquiv.coe_coe,B.symm_apply_apply,he,mul_zero] using ht

lemma signed_simplex_ne_zero (z : ℝ) :
    RankLimits.reflectFirst (Directions.simplex z)≠0 := by
  intro he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp [RankLimits.reflectFirst,Directions.simplex] at h1 h2
  linarith

lemma unit_simplex_parallel_det_ne_zero (B : Point ≃L[ℝ] Point)
    {u v : Point} (hu : ‖u‖=1) (hv : ‖v‖=1) {z w : ℝ} (hzw : z≠w)
    (huz : detPair u (B (RankLimits.reflectFirst (Directions.simplex z)))=0)
    (hvw : detPair v (B (RankLimits.reflectFirst (Directions.simplex w)))=0) :
    detPair u v≠0 := by
  have hnon (r : ℝ) : B (RankLimits.reflectFirst (Directions.simplex r))≠0 := by
    intro he
    exact signed_simplex_ne_zero r (B.injective (he.trans (map_zero B).symm))
  obtain ⟨a,ha⟩ := detPair_zero_parallel (hnon z) huz
  obtain ⟨b,hb⟩ := detPair_zero_parallel (hnon w) hvw
  have ha0 : a≠0 := by intro he; rw [he,zero_smul] at ha; rw [ha,norm_zero] at hu; norm_num at hu
  have hb0 : b≠0 := by intro he; rw [he,zero_smul] at hb; rw [hb,norm_zero] at hv; norm_num at hv
  rw [ha,hb,detPair_smul]
  apply mul_ne_zero (mul_ne_zero ha0 hb0)
  apply detPair_equiv_ne_zero
  have ht : detPair (RankLimits.reflectFirst (Directions.simplex z))
      (RankLimits.reflectFirst (Directions.simplex w))=w-z := by
    dsimp [detPair,RankLimits.reflectFirst,Directions.simplex]; ring
  rw [ht]
  exact sub_ne_zero.mpr hzw.symm

lemma compact_allowed_separation (B : Point ≃L[ℝ] Point)
    (S T : Set ℝ) (hS : IsClosed S) (hT : IsClosed T)
    (hSb : S ⊆ Icc (0:ℝ) 1) (hTb : T ⊆ Icc (0:ℝ) 1) (hST : Disjoint S T) :
    ∃ δ : ℝ, 0<δ ∧ ∀ u v : Point, ‖u‖=1 → ‖v‖=1 →
      (∃ z∈S, detPair u (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      (∃ z∈T, detPair v (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      δ ≤ |detPair u v| := by
  let dir : ℝ → Point := fun z => B (RankLimits.reflectFirst (Directions.simplex z))
  have hdir : Continuous dir := by
    apply B.continuous.comp
    apply RankLimits.reflectFirst.continuous.comp
    exact (continuous_id.prodMk (continuous_const.sub continuous_id))
  let K : Set (Point × ℝ) := {x | ‖x.1‖=1 ∧ x.2∈S ∧ detPair x.1 (dir x.2)=0}
  let L : Set (Point × ℝ) := {x | ‖x.1‖=1 ∧ x.2∈T ∧ detPair x.1 (dir x.2)=0}
  have hdet : Continuous (fun x : Point × ℝ => detPair x.1 (dir x.2)) := by
    exact ((continuous_fst.fst.mul ((hdir.comp continuous_snd).snd)).sub
      (continuous_fst.snd.mul ((hdir.comp continuous_snd).fst)))
  have hKC : IsClosed K :=
    (isClosed_eq continuous_fst.norm continuous_const).inter
      ((hS.preimage continuous_snd).inter (isClosed_eq hdet continuous_const))
  have hLC : IsClosed L :=
    (isClosed_eq continuous_fst.norm continuous_const).inter
      ((hT.preimage continuous_snd).inter (isClosed_eq hdet continuous_const))
  have hK : IsCompact K := ((isCompact_closedBall (0:Point) 1).prod isCompact_Icc).of_isClosed_subset hKC
    (by intro x hx; exact ⟨by simp [hx.1],hSb hx.2.1⟩)
  have hL : IsCompact L := ((isCompact_closedBall (0:Point) 1).prod isCompact_Icc).of_isClosed_subset hLC
    (by intro x hx; exact ⟨by simp [hx.1],hTb hx.2.1⟩)
  let f : (Point × ℝ) × (Point × ℝ) → ℝ := fun x => |detPair x.1.1 x.2.1|
  have hf : Continuous f := by
    exact ((continuous_fst.fst.fst.mul continuous_snd.fst.snd).sub
      (continuous_fst.fst.snd.mul continuous_snd.fst.fst)).abs
  have hpos (x) (hx : x∈K ×ˢ L) : 0<f x := by
    apply abs_pos.mpr
    exact unit_simplex_parallel_det_ne_zero B hx.1.1 hx.2.1
      (by intro he; exact Set.disjoint_left.mp hST hx.1.2.1 (he ▸ hx.2.2.1)) hx.1.2.2 hx.2.2.2
  by_cases hne : (K ×ˢ L).Nonempty
  · obtain ⟨x,hx,hmin⟩ := (hK.prod hL).exists_isMinOn hne hf.continuousOn
    refine ⟨f x,hpos x hx,?_⟩
    intro u v hu hv ⟨z,hz,huz⟩ ⟨w,hw,hvw⟩
    exact hmin (show ((u,z),(v,w))∈K ×ˢ L from ⟨⟨hu,hz,huz⟩,⟨hv,hw,hvw⟩⟩)
  · refine ⟨1,by norm_num,?_⟩
    intro u v hu hv ⟨z,hz,huz⟩ ⟨w,hw,hvw⟩
    exact (hne ⟨((u,z),(v,w)),⟨hu,hz,huz⟩,⟨hv,hw,hvw⟩⟩).elim

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma triple_allowed_separation (B : Point ≃L[ℝ] Point)
    (S : Fin 3 → Set ℝ) (hS : ∀ i, IsClosed (S i))
    (hSb : ∀ i, S i ⊆ Icc (0:ℝ) 1) (hdis : ∀ i j, i≠j → Disjoint (S i) (S j)) :
    ∃ δ : ℝ, 0<δ ∧ ∀ u : Fin 3 → Point, (∀ i, ‖u i‖=1) →
      (∀ i, ∃ z∈S i, detPair (u i) (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      ∀ i j, i≠j → δ ≤ |detPair (u i) (u j)| := by
  have hex (ij : Fin 3 × Fin 3) : ∃ δ : ℝ, 0<δ ∧ ∀ u v : Point, ‖u‖=1 → ‖v‖=1 →
      (∃ z∈S ij.1, detPair u (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      (∃ z∈S ij.2, detPair v (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      ij.1≠ij.2 → δ ≤ |detPair u v| := by
    by_cases hij : ij.1=ij.2
    · exact ⟨1,by norm_num,fun _ _ _ _ _ _ h => (h hij).elim⟩
    · obtain ⟨δ,hδ,hd⟩ := compact_allowed_separation B (S ij.1) (S ij.2)
        (hS ij.1) (hS ij.2) (hSb ij.1) (hSb ij.2) (hdis _ _ hij)
      exact ⟨δ,hδ,fun u v hu hv hz hw _ => hd u v hu hv hz hw⟩
  choose δ hδ hd using hex
  obtain ⟨ij,_,hmin⟩ := isCompact_univ.exists_isMinOn (s:= (univ:Set (Fin 3 × Fin 3)))
    (by simp) (continuous_of_discreteTopology (f:=δ)).continuousOn
  refine ⟨δ ij,hδ ij,?_⟩
  intro u hu hz i j hij
  exact (hmin (show (i,j)∈(univ:Set (Fin 3 × Fin 3)) from mem_univ _)).trans
    (hd (i,j) (u i) (u j) (hu i) (hu j) (hz i) (hz j) hij)

lemma eventually_separated_of_allowed_clusters (B : Point ≃L[ℝ] Point)
    (S : Fin 3 → Set ℝ) (hS : ∀ i, IsClosed (S i))
    (hSb : ∀ i, S i ⊆ Icc (0:ℝ) 1) (hdis : ∀ i j, i≠j → Disjoint (S i) (S j))
    : ∃ δ : ℝ, 0<δ ∧ ∀ (u : ℕ → Fin 3 → Point), (∀ n i, ‖u n i‖=1) →
      (∀ ρ : ℕ → ℕ, StrictMono ρ → ∀ v : Fin 3 → Point,
        Tendsto (u ∘ ρ) atTop (𝓝 v) →
        ∀ i, ∃ z∈S i, detPair (v i) (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      ∀ᶠ n in atTop, ∀ i j, i≠j → δ ≤ |detPair (u n i) (u n j)| := by
  obtain ⟨δ,hδ,hsep⟩ := triple_allowed_separation B S hS hSb hdis
  refine ⟨δ/2,by positivity,?_⟩
  intro u hu hcluster
  by_contra hn
  obtain ⟨ρ,hρ,hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hn)
  have hb (n : ℕ) : u (ρ n)∈closedBall (0:Fin 3 → Point) 1 := by
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr (fun i => (hu _ i).le)
  obtain ⟨v,_,τ,hτ,hlim⟩ := (isCompact_closedBall (0:Fin 3 → Point) 1).tendsto_subseq hb
  have hv (i : Fin 3) : ‖v i‖=1 := tendsto_nhds_unique ((tendsto_pi_nhds.mp hlim i).norm)
    (by simp only [Function.comp_def,hu]; exact tendsto_const_nhds)
  have hd := hsep v hv (hcluster (ρ ∘ τ) (hρ.comp hτ) v hlim)
  have he : ∀ᶠ n in atTop, ∀ i j, i≠j → δ/2 ≤ |detPair (u (ρ (τ n)) i) (u (ρ (τ n)) j)| := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i=j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have hi := tendsto_pi_nhds.mp hlim i
      have hj := tendsto_pi_nhds.mp hlim j
      have ht : Tendsto (fun n => |detPair (u (ρ (τ n)) i) (u (ρ (τ n)) j)|) atTop
          (𝓝 |detPair (v i) (v j)|) :=
        ((hi.fst_nhds.mul hj.snd_nhds).sub (hi.snd_nhds.mul hj.fst_nhds)).abs
      have hlt : δ/2 < |detPair (v i) (v j)| := by linarith [hd i j hij]
      exact (ht.eventually (lt_mem_nhds hlt)).mono (fun _ hh _ => hh.le)
  obtain ⟨n,hn⟩ := he.exists
  exact hbad (τ n) hn

end PlanarHalving.Zoom

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma affine_rank_forward_limit {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (h q : ℕ → ℝ) (hh : ∀ n, 0<h n) (hq : ∀ n, 0<q n)
    (E : ℕ → Point ≃L[ℝ] Point) (B' : Point ≃L[ℝ] Point) (x₀ : ℕ → Point)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B)
    (x y : ℕ → Point) (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n)
    (hE : ∀ n, E n (y n-x n)=s n • (1,(F n).timeSlope t))
    (a b : Point) (hab : b-a≠0)
    (ha : Tendsto (fun n => affineZoom ((F n).rankChart hAB (hA n) (hB n))
      (E n) B' p (x₀ n) (q n) (h n) (hq n).ne' (hh n).ne' (x n)) atTop (𝓝 a))
    (hb : Tendsto (fun n => affineZoom ((F n).rankChart hAB (hA n) (hB n))
      (E n) B' p (x₀ n) (q n) (h n) (hq n).ne' (hh n).ne' (y n)) atTop (𝓝 b))
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R)) :
    ∃ z∈Directions.allowed reflectFirst D
      (fun i => (lower (C i):ℝ)) (fun i => (upper (C i):ℝ)) t,
      detPair (b-a) (B' (reflectFirst (Directions.simplex z)))=0 := by
  let X := fun n => x₀ n+q n • E n (x n)
  let Y := fun n => x₀ n+q n • E n (y n)
  have hXY (n : ℕ) : Y n=X n+(q n*s n) • (1,(F n).timeSlope t) := by
    have he := hE n
    have hy : E n (y n)=E n (x n)+s n • (1,(F n).timeSlope t) := by
      rw [map_sub] at he; exact eq_add_of_sub_eq' he
    dsimp only [X,Y]
    rw [hy,smul_add,smul_smul,add_assoc]
  have hxa : Tendsto (fun n => (h n)⁻¹ •
      ((F n).rankChart hAB (hA n) (hB n) (X n)-p)) atTop (𝓝 (B'.symm a)) := by
    simpa only [Function.comp_def,affineZoom_apply,B'.symm_apply_apply,X]
      using (B'.symm.continuous.tendsto a).comp ha
  have hyb : Tendsto (fun n => (h n)⁻¹ •
      ((F n).rankChart hAB (hA n) (hB n) (Y n)-p)) atTop (𝓝 (B'.symm b)) := by
    simpa only [Function.comp_def,affineZoom_apply,B'.symm_apply_apply,Y]
      using (B'.symm.continuous.tendsto b).comp hb
  have hne : B'.symm b-B'.symm a≠0 := by
    intro he; apply hab
    have hg := congrArg B' he
    simpa only [map_sub,B'.apply_symm_apply,map_zero] using hg
  obtain ⟨r,_,z,hz,he⟩ := actual_forward_limit F hAB hA hB C hC D c p h hh t htA htB
    X Y (fun n => q n*s n) (fun n => mul_nonneg (hq n).le (hs n)) hXY
    (B'.symm a) (B'.symm b) hxa hyb
    (fun i => jet_at_physical F hAB (hCB i) hA hB (hC i) (D i) (c i) p h hh (hj i) X _ hxa)
    (fun i => jet_at_physical F hAB (hCB i) hA hB (hC i) (D i) (c i) p h hh (hj i) Y _ hyb) hne
  refine ⟨z,hz,?_⟩
  have ht := congrArg B' he
  simp only [map_sub,map_smul,B'.apply_symm_apply] at ht
  rw [ht]
  dsimp [detPair]; ring

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

noncomputable def forwardUnit (F : Configuration) (E : Point ≃L[ℝ] Point) (t : I) : Point :=
  ‖E.symm (1,F.timeSlope t)‖⁻¹ • E.symm (1,F.timeSlope t)

lemma forwardUnit_norm (F : Configuration) (E : Point ≃L[ℝ] Point) (t : I) :
    ‖forwardUnit F E t‖=1 := by
  apply norm_smul_inv_norm
  intro he
  have hh := congrArg E he
  simp at hh

lemma forwardUnit_map (F : Configuration) (E : Point ≃L[ℝ] Point) (t : I) :
    E (forwardUnit F E t)=‖E.symm (1,F.timeSlope t)‖⁻¹ • (1,F.timeSlope t) := by
  simp only [forwardUnit,map_smul,E.apply_symm_apply]

lemma actual_forwardUnit_clusters {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (h q : ℕ → ℝ) (hh : ∀ n, 0<h n) (hq : ∀ n, 0<q n)
    (E : ℕ → Point ≃L[ℝ] Point) (B' : Point ≃L[ℝ] Point)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B)
    (sgn : ℝ) (hsgn : sgn=1 ∨ sgn=-1)
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R))
    (hunif : TendstoUniformlyOn
      (fun n => affineZoom ((F n).rankChart hAB (hA n) (hB n)) (E n) B' p
        (((F n).rankChart hAB (hA n) (hB n)).symm p) (q n) (h n) (hq n).ne' (hh n).ne')
      (fun x => sgn • x) atTop (closedBall 0 1))
    (ρ : ℕ → ℕ) (hρ : StrictMono ρ) (v : Point)
    (hvlim : Tendsto (fun n => forwardUnit (F (ρ n)) (E (ρ n)) t) atTop (𝓝 v)) :
    ∃ z∈Directions.allowed reflectFirst D
      (fun i => (lower (C i):ℝ)) (fun i => (upper (C i):ℝ)) t,
      detPair v (B' (reflectFirst (Directions.simplex z)))=0 := by
  let f := fun n => (F n).rankChart hAB (hA n) (hB n)
  let x₀ := fun n => (f n).symm p
  let Z := fun n => affineZoom (f n) (E n) B' p (x₀ n) (q n) (h n) (hq n).ne' (hh n).ne'
  have hpt (n : ℕ) : p∈(f n).target := by rw [(F n).rankChart_target]; exact hp
  have hz (n : ℕ) : Z n 0=0 := affineZoom_zero (f n) (E n) B' (hpt n) _ _ _ _
  have hvn : ‖v‖=1 := tendsto_nhds_unique hvlim.norm
    (by simp only [forwardUnit_norm]; exact tendsto_const_nhds)
  have hsgn0 : sgn≠0 := by rcases hsgn with rfl | rfl <;> norm_num
  have hne : sgn • v-0≠0 := by
    rw [sub_zero]
    exact smul_ne_zero hsgn0 (by intro he; rw [he,norm_zero] at hvn; norm_num at hvn)
  have hvwithin : Tendsto (fun n => forwardUnit (F (ρ n)) (E (ρ n)) t) atTop
      (𝓝[closedBall (0:Point) 1] v) := tendsto_nhdsWithin_iff.mpr ⟨hvlim,Eventually.of_forall
        (fun n => by simp [forwardUnit_norm])⟩
  have hyl : Tendsto (fun n => Z (ρ n) (forwardUnit (F (ρ n)) (E (ρ n)) t)) atTop (𝓝 (sgn • v)) :=
    (hunif.seq_tendstoUniformlyOn ρ hρ.tendsto_atTop).tendsto_comp
      ((continuous_const : Continuous (fun _ : Point => sgn)).smul continuous_id).continuousWithinAt hvwithin
  obtain ⟨z,hz',hdet⟩ := affine_rank_forward_limit (F ∘ ρ) hAB (fun n => hA (ρ n)) (fun n => hB (ρ n))
    C hCB (fun i => hρ.tendsto_atTop.eventually (hC i)) D c p (h ∘ ρ) (q ∘ ρ)
    (fun n => hh (ρ n)) (fun n => hq (ρ n)) (E ∘ ρ) B' (x₀ ∘ ρ) t htA htB
    (fun _ => 0) (fun n => forwardUnit (F (ρ n)) (E (ρ n)) t)
    (fun n => ‖(E (ρ n)).symm (1,(F (ρ n)).timeSlope t)‖⁻¹)
    (fun n => inv_nonneg.mpr (norm_nonneg _))
    (fun n => by rw [sub_zero]; exact forwardUnit_map _ _ _)
    0 (sgn • v) hne
    (by change Tendsto (fun n => Z (ρ n) 0) atTop (𝓝 0); simp only [hz]; exact tendsto_const_nhds) hyl
    (fun i R hR => (hj i R hR).seq_tendstoUniformlyOn ρ hρ.tendsto_atTop)
  refine ⟨z,hz',?_⟩
  rw [sub_zero] at hdet
  have he : detPair (sgn • v) (B' (reflectFirst (Directions.simplex z)))=
      sgn*detPair v (B' (reflectFirst (Directions.simplex z))) := by dsimp [detPair]; ring
  rw [he] at hdet
  exact (mul_eq_zero.mp hdet).resolve_left hsgn0

end PlanarHalving.RankLimits

end OAI
