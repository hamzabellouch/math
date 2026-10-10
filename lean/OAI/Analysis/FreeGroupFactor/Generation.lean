import OAI.Analysis.FreeGroupFactor.LocalAutomorphism

namespace OAI

noncomputable section

universe uA uB uC uG uH uI uK uP uX uY uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation

section
variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B] {ι : Type uι} {κ : Type uκ}

def mapTuple (Φ : A ≃⋆ₐ[ℂ] B) (U : ι → unitary A) : ι → unitary B :=
  fun j => ⟨Φ (U j : A), Unitary.map_mem Φ (U j).property⟩

@[simp] theorem mapTuple_coe (Φ : A ≃⋆ₐ[ℂ] B) (U : ι → unitary A) (j : ι) :
    (mapTuple Φ U j : B) = Φ (U j : A) := rfl

@[simp] theorem word_mapTuple (Φ : A ≃⋆ₐ[ℂ] B) (U : ι → unitary A) (g : FreeGroup ι) :
    word (mapTuple Φ U) g = Φ (word U g) := by
  induction g using FreeGroup.induction_on with
  | one => simp only [map_one]
  | of j => simp only [word_of,mapTuple_coe]
  | inv_of j ih => rw [word_inv,word_inv,ih,map_star]
  | mul g h hg hh => rw [map_mul,map_mul,map_mul,hg,hh]

@[simp] theorem poly_mapTuple (Φ : A ≃⋆ₐ[ℂ] B) (U : ι → unitary A) (p : FreeGroup ι →₀ ℂ) :
    poly (mapTuple Φ U) p = Φ (poly U p) := by
  classical
  simp only [poly,Finsupp.sum,map_sum,map_smul,word_mapTuple]

def substitute (w : κ → FreeGroup ι) : (FreeGroup κ →₀ ℂ) →ₗ[ℂ] FreeGroup ι →₀ ℂ :=
  Finsupp.lmapDomain ℂ ℂ (FreeGroup.lift w)

def wordTuple (U : ι → unitary A) (w : κ → FreeGroup ι) : κ → unitary A :=
  fun j => FreeGroup.lift U (w j)

@[simp] theorem word_wordTuple (U : ι → unitary A) (w : κ → FreeGroup ι) (g : FreeGroup κ) :
    word (wordTuple U w) g = word U (FreeGroup.lift w g) := by
  have he : word (wordTuple U w) = (word U).comp (FreeGroup.lift w) := by
    apply FreeGroup.ext_hom
    intro j
    simp only [word_of,MonoidHom.comp_apply,FreeGroup.lift_apply_of]
    rfl
  exact DFunLike.congr_fun he g

@[simp] theorem poly_substitute (U : ι → unitary A) (w : κ → FreeGroup ι) (p : FreeGroup κ →₀ ℂ) :
    poly U (substitute w p) = poly (wordTuple U w) p := by
  induction p using Finsupp.induction_linear with
  | zero => simp only [map_zero,poly_zero]
  | add p q hp hq => simp only [map_add,poly_add,hp,hq]
  | single g c =>
    simp only [substitute,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,poly_single,word_wordTuple]

instance unitary_isClosed (A : Type uA) [CStarAlgebra A] : IsClosed (unitary A : Set A) :=
  isClosed_unitary

instance unitary_completeSpace (A : Type uA) [CStarAlgebra A] : CompleteSpace (unitary A) := by
  change CompleteSpace ↥(unitary A : Set A)
  infer_instance

end

@[simp] theorem word_canonical {ι : Type uι} (g : FreeGroup ι) :
    word (generatorUnitary (ι := ι)) g = groupUnitary g := by
  have he : word (generatorUnitary (ι := ι)) =
      (unitary (groupVonNeumann (FreeGroup ι))).subtype.comp (groupUnitaryUHom (FreeGroup ι)) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [word_of,MonoidHom.comp_apply]
    rfl
  exact DFunLike.congr_fun he g

theorem canonical_poly_dense {ι : Type uι} (ξ : GroupHilbert (FreeGroup ι)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : FreeGroup ι →₀ ℂ, ‖groupL2 (poly generatorUnitary p)-ξ‖ < ε := by
  classical
  let K := Submodule.span ℂ (Set.range (fun g : FreeGroup ι => groupL2 (groupUnitary g)))
  have ht : ⊤ ≤ K.topologicalClosure := by
    apply group_single_total _ (Submodule.isClosed_topologicalClosure _)
    intro g
    rw [← groupL2_groupUnitary g]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g,rfl⟩)
  have hx : ξ ∈ closure (K : Set (GroupHilbert (FreeGroup ι))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact ht trivial
  obtain ⟨x,hx,hd⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨p,hp⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨p,?_⟩
  have he : groupL2 (poly generatorUnitary p) = x := by
    rw [poly,Finsupp.sum]
    simp only [map_sum,map_smul,word_canonical]
    exact hp
  rw [he,← dist_eq_norm,dist_comm]
  exact hd

theorem automorphism_poly_dense {ι : Type uι}
    (Φ : groupVonNeumann (FreeGroup ι) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup ι))
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T)
    (T : groupVonNeumann (FreeGroup ι)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : FreeGroup ι →₀ ℂ, twoNorm (poly (mapTuple Φ generatorUnitary) p-T) < ε := by
  obtain ⟨p,hp⟩ := canonical_poly_dense (groupL2 (Φ.symm T)) hε
  refine ⟨p,?_⟩
  rw [poly_mapTuple,← Φ.apply_symm_apply T,← map_sub,twoNorm_iso Φ ht]
  change ‖groupL2 (poly generatorUnitary p-Φ.symm T)‖ < ε
  rw [map_sub]
  exact hp

abbrev Ambient (n : ℕ) := groupVonNeumann (FreeGroup (Option (Fin n)))
abbrev Tuple (n : ℕ) := Fin n → unitary (Ambient n)
def initial (n : ℕ) : Tuple n := fun j => generatorUnitary (some j)

theorem word_initial (n : ℕ) (g : FreeGroup (Fin n)) :
    word (initial n) g = groupUnitary (FreeGroup.map Option.some g) := by
  have he : word (initial n) =
      (unitary (Ambient n)).subtype.comp
        ((groupUnitaryUHom (FreeGroup (Option (Fin n)))).comp (FreeGroup.map Option.some)) := by
    apply FreeGroup.ext_hom
    intro j
    simp only [word_of,MonoidHom.comp_apply,FreeGroup.map.of]
    rfl
  exact DFunLike.congr_fun he g

def orbit (n : ℕ) : Set (Tuple n) :=
  {U | ∃ Φ : Ambient n ≃⋆ₐ[ℂ] Ambient n,
    (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧ U = mapTuple Φ (initial n)}

theorem orbit_nonempty (n : ℕ) : (orbit n).Nonempty := by
  refine ⟨mapTuple (StarAlgEquiv.refl ℂ (Ambient n)) (initial n),StarAlgEquiv.refl ℂ (Ambient n),?_,rfl⟩
  intro T
  rfl

@[simp] theorem mapTuple_trans {A : Type uA} {B : Type uB} {C : Type uC} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    {ι : Type uι} (Φ : A ≃⋆ₐ[ℂ] B) (Ψ : B ≃⋆ₐ[ℂ] C) (U : ι → unitary A) :
    mapTuple (Φ.trans Ψ) U = mapTuple Ψ (mapTuple Φ U) := rfl

theorem orbit_step (n : ℕ) (hn : 3 ≤ n)
    (Φ : Ambient n ≃⋆ₐ[ℂ] Ambient n)
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) {θ : ℝ} (hθ : 0 < θ) :
    ∃ V ∈ orbit n, dist V (mapTuple Φ (initial n)) < θ ∧
      ∃ w : FreeGroup (Fin n), ∀ j : Option (Fin n),
        twoNorm ((wordTuple V (fun j => j.elim w FreeGroup.of) j : Ambient n) -
          (mapTuple Φ generatorUnitary j : Ambient n)) < θ := by
  obtain ⟨α,hαt,_hαn,w,hgen,hword⟩ := one_step n hn hθ
  let V : Tuple n := mapTuple (α.trans Φ) (initial n)
  have hdist : dist V (mapTuple Φ (initial n)) < θ := by
    apply (dist_pi_lt_iff hθ).mpr
    intro j
    change dist (Φ (α (groupUnitary (FreeGroup.of (some j))))) (Φ (groupUnitary (FreeGroup.of (some j)))) < θ
    have hnorm (T : Ambient n) : ‖Φ T‖ = ‖T‖ :=
      NonUnitalStarAlgHom.norm_map Φ.toStarAlgHom Φ.injective T
    rw [dist_eq_norm, ← map_sub, hnorm]
    exact hgen j
  refine ⟨V,⟨α.trans Φ,?_,rfl⟩,hdist,w,?_⟩
  · intro T
    simp only [StarAlgEquiv.trans_apply,ht,hαt]
  · intro j
    cases j with
    | none =>
      change twoNorm (word V w-Φ (groupUnitary (FreeGroup.of none))) < θ
      rw [show V = mapTuple (α.trans Φ) (initial n) from rfl,word_mapTuple,
        word_initial,StarAlgEquiv.trans_apply,← map_sub,twoNorm_iso Φ ht]
      exact hword
    | some j =>
      change twoNorm ((V j : Ambient n)-Φ (groupUnitary (FreeGroup.of (some j)))) < θ
      have hj := (dist_pi_lt_iff hθ).mp hdist j
      change dist (V j : Ambient n) (Φ (groupUnitary (FreeGroup.of (some j)))) < θ at hj
      rw [dist_eq_norm] at hj
      exact (twoNorm_le_norm _).trans_lt hj

theorem poly_groupL2_continuous (n : ℕ) (p : FreeGroup (Fin n) →₀ ℂ) :
    Continuous (fun U : Tuple n => groupL2 (poly U p)) :=
  (groupL2 (G := FreeGroup (Option (Fin n)))).continuous.comp (poly_continuous p)

theorem orbit_local_approximation (n : ℕ) (hn : 3 ≤ n)
    (U : Tuple n) (hU : U ∈ orbit n) (δ : ℝ) (hδ : 0 < δ)
    (g : FreeGroup (Option (Fin n))) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ orbit n, dist V U < δ ∧ ∃ p : FreeGroup (Fin n) →₀ ℂ,
      dist (groupL2 (poly V p)) (lp.single 2 g (1 : ℂ)) < ε := by
  classical
  obtain ⟨Φ,ht,rfl⟩ := hU
  obtain ⟨p,hp⟩ := automorphism_poly_dense Φ ht (groupUnitary g) (half_pos hε)
  obtain ⟨K,hK,hbound⟩ := poly_twoNorm_bound (G := FreeGroup (Option (Fin n))) p
  let θ := min δ (ε/(2*(K+1)))
  have hθ : 0 < θ := lt_min hδ (div_pos hε (by positivity))
  obtain ⟨V,hV,hd,w,hw⟩ := orbit_step n hn Φ ht hθ
  refine ⟨V,hV,hd.trans_le (min_le_left _ _),substitute (fun j => j.elim w FreeGroup.of) p,?_⟩
  have hb := hbound (wordTuple V (fun j => j.elim w FreeGroup.of)) (mapTuple Φ generatorUnitary)
    θ hθ.le (fun j => (hw j).le)
  have hθe : θ*(2*(K+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2*(K+1))).mp (min_le_right _ _)
  have hKe : K*θ < ε/2 := by nlinarith
  rw [dist_eq_norm,← groupL2_groupUnitary g,← map_sub]
  change twoNorm (poly V (substitute (fun j => j.elim w FreeGroup.of) p)-groupUnitary g) < ε
  rw [poly_substitute]
  have he : poly (wordTuple V (fun j => j.elim w FreeGroup.of)) p-groupUnitary g =
      (poly (wordTuple V (fun j => j.elim w FreeGroup.of)) p-poly (mapTuple Φ generatorUnitary) p)+
      (poly (mapTuple Φ generatorUnitary) p-groupUnitary g) := by abel
  rw [he]
  exact (twoNorm_add_le _ _).trans_lt (by linarith)

theorem orbit_trace (n : ℕ) (U : Tuple n) (hU : U ∈ orbit n) (g : FreeGroup (Fin n)) :
    canonicalTrace (word U g) = if g = 1 then 1 else 0 := by
  classical
  obtain ⟨Φ,ht,rfl⟩ := hU
  rw [word_mapTuple,ht,word_initial,canonicalTrace_groupUnitary]
  have hi : FreeGroup.map (Option.some : Fin n → Option (Fin n)) g = 1 ↔ g = 1 := by
    rw [← (FreeGroup.map Option.some).map_one]
    exact (FreeGroup.map_injective (Option.some_injective (Fin n))).eq_iff
  simp only [hi]

theorem closure_orbit_trace (n : ℕ) (U : Tuple n) (hU : U ∈ closure (orbit n)) (g : FreeGroup (Fin n)) :
    canonicalTrace (word U g) = if g = 1 then 1 else 0 := by
  classical
  have hc : Continuous (fun V : Tuple n => canonicalTrace (word V g)) :=
    (canonicalTraceCLM (G := FreeGroup (Option (Fin n)))).continuous.comp (word_continuous g)
  have hclosed : IsClosed {V : Tuple n | canonicalTrace (word V g) = if g = 1 then 1 else 0} :=
    isClosed_eq hc continuous_const
  exact (closure_minimal (fun V hV => orbit_trace n V hV g) hclosed) hU

theorem poly_l2_mem {G : Type uG} [Group G] {ι : Type uι}
    (U : ι → unitary (groupVonNeumann G)) (p : FreeGroup ι →₀ ℂ) :
    groupL2 (poly U p) ∈ Submodule.span ℂ (Set.range (fun g => groupL2 (word U g))) := by
  classical
  rw [poly,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro g _hg
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g,rfl⟩)

theorem total_of_poly_approx {G : Type uG} [Group G] [DecidableEq G] {ι : Type uι}
    (U : ι → unitary (groupVonNeumann G))
    (hU : ∀ g : G, ∀ ε : ℝ, 0 < ε → ∃ p : FreeGroup ι →₀ ℂ,
      dist (groupL2 (poly U p)) (lp.single 2 g (1 : ℂ)) < ε) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g)))).topologicalClosure := by
  classical
  apply group_single_total _ (Submodule.isClosed_topologicalClosure _)
  intro g
  change lp.single 2 g (1 : ℂ) ∈ closure (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g))) : Set (GroupHilbert G))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨p,hp⟩ := hU g ε hε
  exact ⟨groupL2 (poly U p),poly_l2_mem U p,by simpa only [dist_comm] using hp⟩

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain

theorem baire_local_approximation
    {X : Type uX} {Y : Type uY} {I : Type uI} {P : Type uP} [MetricSpace X] [CompleteSpace X] [MetricSpace Y] [Countable I]
    (S : Set X) (hS : S.Nonempty) (a : P → X → Y) (ha : ∀ p, Continuous (a p))
    (v : I → Y)
    (hlocal : ∀ x ∈ S, ∀ δ : ℝ, 0 < δ → ∀ i : I, ∀ ε : ℝ, 0 < ε →
      ∃ y ∈ S, dist y x < δ ∧ ∃ p, dist (a p y) (v i) < ε) :
    ∃ x ∈ closure S, ∀ i : I, ∀ ε : ℝ, 0 < ε → ∃ p, dist (a p x) (v i) < ε := by
  let T := closure S
  let : IsClosed T := isClosed_closure
  let : Nonempty T := by
    obtain ⟨x,hx⟩ := hS
    exact ⟨⟨x, subset_closure hx⟩⟩
  let O (ik : I × ℕ) : Set T := {x | ∃ p, dist (a p x) (v ik.1) < 1 / (ik.2 + 1 : ℝ)}
  have hopen (ik : I × ℕ) : IsOpen (O ik) := by
    simp only [O, Set.ofPred_exists]
    apply isOpen_iUnion
    intro p
    exact isOpen_lt (((ha p).comp continuous_subtype_val).dist continuous_const) continuous_const
  have hdense (ik : I × ℕ) : Dense (O ik) := by
    intro x
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp x.property (δ/2) (half_pos hδ)
    obtain ⟨z,hz,hzy,p,hp⟩ := hlocal y hy (δ/2) (half_pos hδ) ik.1
      (1/(ik.2+1:ℝ)) (by positivity)
    refine ⟨⟨z,subset_closure hz⟩, ⟨p,hp⟩, ?_⟩
    change dist (x : X) z < δ
    have htri := dist_triangle (x : X) y z
    rw [dist_comm y z] at htri
    linarith
  obtain ⟨x,hx⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  refine ⟨x,x.property,?_⟩
  intro i ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨p,hp⟩ := Set.mem_iInter.mp hx (i,k)
  exact ⟨p, hp.trans hk⟩

theorem normalTracialIso_of_groupEquiv {G : Type uG} {H : Type uH} [Group G] [Group H] (e : G ≃* H) :
    HasNormalTracialIso G H := by
  classical
  let ρ : G →* groupVonNeumann H := (groupUnitaryHom H).comp e.toMonoidHom
  apply normalTracialIso_of_haar_total ρ
  · intro g
    change star (groupUnitary (e g)) = groupUnitary (e g⁻¹)
    rw [map_inv]
    exact Subtype.ext (leftRegular_star (e g))
  · intro g
    change canonicalTrace (groupUnitary (e g)) = _
    rw [canonicalTrace_groupUnitary]
    simp only [e.map_eq_one_iff]
  · apply group_single_total _ (Submodule.isClosed_topologicalClosure _)
    intro h
    have hh : groupL2 (groupUnitary h) = ((ρ (e.symm h) : groupVonNeumann H) : GroupOperator H) deltaOne := by
      simp only [ρ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.apply_symm_apply]
      rfl
    rw [← groupL2_groupUnitary h,hh]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨e.symm h,rfl⟩)

theorem HasNormalTracialIso.trans {G : Type uG} {H : Type uH} {K : Type uK} [Group G] [Group H] [Group K]
    (hGH : HasNormalTracialIso G H) (hHK : HasNormalTracialIso H K) : HasNormalTracialIso G K := by
  obtain ⟨Φ,hΦt,hΦn⟩ := hGH
  obtain ⟨Ψ,hΨt,hΨn⟩ := hHK
  refine ⟨Φ.trans Ψ,?_,?_⟩
  · intro T
    simp only [StarAlgEquiv.trans_apply,hΨt,hΦt]
  · let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
    let : TopologicalSpace (groupVonNeumann H) := groupUltraweakTopology H
    let : TopologicalSpace (groupVonNeumann K) := groupUltraweakTopology K
    exact hΨn.comp hΦn

def optionRankEquiv (n : ℕ) : FreeGroup (Option (Fin n)) ≃* FreeGroupRank (n+1) :=
  FreeGroup.freeGroupCongr (finSuccEquiv n).symm

open Generation

theorem generating_haar_tuple (n : ℕ) (hn : 3 ≤ n) :
    ∃ U : Tuple n,
      (∀ g : FreeGroup (Fin n), canonicalTrace (word U g) = if g = 1 then 1 else 0) ∧
      ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g)))).topologicalClosure := by
  classical
  obtain ⟨U,hU,happrox⟩ := baire_local_approximation (orbit n) (orbit_nonempty n)
    (fun p U => groupL2 (poly U p)) (poly_groupL2_continuous n)
    (fun g : FreeGroup (Option (Fin n)) => lp.single 2 g (1 : ℂ))
    (orbit_local_approximation n hn)
  exact ⟨U,closure_orbit_trace n U hU,total_of_poly_approx U happrox⟩

theorem rank_step_option (n : ℕ) (hn : 3 ≤ n) :
    HasNormalTracialIso (FreeGroupRank n) (FreeGroup (Option (Fin n))) := by
  classical
  obtain ⟨U,htrace,htotal⟩ := generating_haar_tuple n hn
  apply normalTracialIso_of_haar_total (word U)
  · intro g
    exact (word_inv U g).symm
  · exact htrace
  · exact htotal

theorem rank_step (n : ℕ) (hn : 3 ≤ n) :
    HasNormalTracialIso (FreeGroupRank n) (FreeGroupRank (n+1)) :=
  (rank_step_option n hn).trans (normalTracialIso_of_groupEquiv (optionRankEquiv n))

end FreeGroupFactorMain

end

end OAI
