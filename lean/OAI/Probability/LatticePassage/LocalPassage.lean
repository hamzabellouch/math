import OAI.Probability.LatticePassage.PassageRegularity

namespace OAI

namespace CompanionFPP
open MeasureTheory Finset Real

noncomputable def localCandidates (x : Vertex) (R : ℕ) :
    Finset (Σ y : Vertex, lattice.Walk x y) := by
  classical
  exact ((range R).biUnion fun n => startingWalks n x).filter
    fun q => q.2.IsPath ∧ q.2.length < R

lemma mem_localCandidates {x y : Vertex} {R : ℕ} (p : lattice.Walk x y)
    (hp : p.IsPath) (hl : p.length < R) :
    (⟨y,p⟩ : Σ y : Vertex, lattice.Walk x y) ∈ localCandidates x R := by
  classical
  apply mem_filter.mpr
  exact ⟨mem_biUnion.mpr ⟨p.length, mem_range.mpr hl, trail_mem_starting p hp.isTrail⟩,
    hp, hl⟩

noncomputable def localEdges (x : Vertex) (R : ℕ) : Finset Edge := by
  classical
  exact (localCandidates x R).biUnion fun q => (pathEdges q.2).toFinset

lemma pathCost_eq_of_agree (ω ω' : Environment) {x y : Vertex} (p : lattice.Walk x y)
    (h : ∀ e ∈ pathEdges p, ω e = ω' e) : pathCost ω p = pathCost ω' p := by
  rw [pathCost_eq_edgeList_sum, pathCost_eq_edgeList_sum]
  congr 1
  exact List.map_congr_left h

lemma local_pathCost_eq (ω ω' : Environment) {x y : Vertex} {R : ℕ}
    (h : ∀ e ∈ localEdges x R, ω e = ω' e)
    (p : lattice.Walk x y) (hp : p.IsPath) (hl : p.length < R) :
    pathCost ω p = pathCost ω' p := by
  classical
  apply pathCost_eq_of_agree
  intro e he
  apply h e
  exact mem_biUnion.mpr ⟨⟨y,p⟩, mem_localCandidates p hp hl, List.mem_toFinset.mpr he⟩

noncomputable def localPassageTime (ω : Environment) (x y : Vertex) (R : ℕ) : ℝ :=
  sInf {c : ℝ | ∃ p : lattice.Walk x y, p.IsPath ∧ p.length < R ∧ c = pathCost ω p}

lemma local_costs_finite (ω : Environment) (x y : Vertex) (R : ℕ) :
    {c : ℝ | ∃ p : lattice.Walk x y, p.IsPath ∧ p.length < R ∧ c = pathCost ω p}.Finite := by
  classical
  apply ((localCandidates x R).image (fun q => pathCost ω q.2)).finite_toSet.subset
  rintro c ⟨p,hp,hl,rfl⟩
  exact mem_image.mpr ⟨⟨y,p⟩, mem_localCandidates p hp hl, rfl⟩

@[fun_prop] theorem measurable_localPassageTime (x y : Vertex) (R : ℕ) :
    Measurable (fun ω : Environment => localPassageTime ω x y R) := by
  have he : (fun ω : Environment => localPassageTime ω x y R) =
      (fun ω : Environment => ⨅ p : {p : lattice.Walk x y // p.IsPath ∧ p.length < R},
        pathCost ω p.1) := by
    funext ω
    unfold localPassageTime iInf
    congr 1
    ext c
    constructor
    · rintro ⟨p,hp,hl,rfl⟩
      exact ⟨⟨p,hp,hl⟩,rfl⟩
    · rintro ⟨⟨p,hp,hl⟩,rfl⟩
      exact ⟨p,hp,hl,rfl⟩
  rw [he]
  exact Measurable.iInf (fun p => measurable_pathCost p.1)

theorem localPassageTime_eq_of_agree (ω ω' : Environment) (x y : Vertex) (R : ℕ)
    (h : ∀ e ∈ localEdges x R, ω e = ω' e) :
    localPassageTime ω x y R = localPassageTime ω' x y R := by
  unfold localPassageTime
  congr 1
  ext c
  constructor <;> rintro ⟨p,hp,hl,rfl⟩
  · exact ⟨p,hp,hl,local_pathCost_eq ω ω' h p hp hl⟩
  · exact ⟨p,hp,hl,(local_pathCost_eq ω ω' h p hp hl).symm⟩

theorem local_geodesic_exists (ω : Environment) (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) :
    ∃ p : lattice.Walk x y, p.IsPath ∧ p.length < R ∧
      pathCost ω p = localPassageTime ω x y R := by
  let C := {c : ℝ | ∃ p : lattice.Walk x y, p.IsPath ∧ p.length < R ∧ c = pathCost ω p}
  have hC : C.Finite := local_costs_finite ω x y R
  obtain ⟨q,hq,hl⟩ := coordinate_path x y
  have hne : C.Nonempty := ⟨pathCost ω q,q,hq,hl.trans_lt hR,rfl⟩
  obtain ⟨c,hc,hm⟩ := Set.exists_min_image C id hC hne
  obtain ⟨p,hp,hl,rfl⟩ := hc
  refine ⟨p,hp,hl,le_antisymm ?_ ?_⟩
  · exact le_csInf hne (fun c hc => hm c hc)
  · exact csInf_le hC.bddBelow ⟨p,hp,hl,rfl⟩

theorem localPassageTime_eq_of_short_geodesic (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    {x y : Vertex} {R : ℕ} (p : lattice.Walk x y) (hp : p.IsPath)
    (hl : p.length < R) (hc : pathCost ω p = passageTime ω x y) :
    localPassageTime ω x y R = passageTime ω x y := by
  apply le_antisymm
  · rw [← hc]
    exact csInf_le (local_costs_finite ω x y R).bddBelow ⟨p,hp,hl,rfl⟩
  · apply le_csInf (s := {c : ℝ | ∃ q : lattice.Walk x y,
        q.IsPath ∧ q.length < R ∧ c = pathCost ω q}) ⟨pathCost ω p,p,hp,hl,rfl⟩
    rintro c ⟨q,_,_,rfl⟩
    exact passageTime_le_pathCost ω hω q

theorem localPassageTime_failure_probability (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    environmentLaw.real {ω : Environment | localPassageTime ω x y R ≠ passageTime ω x y} ≤
      (11/3 : ℝ) * exp (-(log 2/40)*R) := by
  have hsub : environmentLaw {ω : Environment | localPassageTime ω x y R ≠ passageTime ω x y} ≤
      environmentLaw {ω : Environment | ∃ p : lattice.Walk x y,
        pathCost ω p = passageTime ω x y ∧ R ≤ p.length} := by
    apply measure_mono_ae
    filter_upwards [all_edge_weights_positive, geodesics_exist] with ω hω hg
    intro hne
    obtain ⟨p,hp,hc⟩ := hg x y
    refine ⟨p,hc, ?_⟩
    by_contra hl
    exact hne (localPassageTime_eq_of_short_geodesic ω (fun e => (hω e).le)
      p hp (lt_of_not_ge hl) hc)
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
    (geodesic_length_tail x y R hR hscale)

end CompanionFPP

end OAI
