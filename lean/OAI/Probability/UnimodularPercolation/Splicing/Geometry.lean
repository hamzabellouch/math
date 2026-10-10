import Mathlib
import OAI.Probability.UnimodularPercolation.Exploration.Goodness
import OAI.Probability.UnimodularPercolation.Kernel.Spectral

namespace OAI

/-! Critical parameters and the geometry, selection and traces of splices. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section CriticalParameter
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem twoPoint_adj_lower [Countable E] (G : BondGraph V E) (p : unitInterval)
    (z x y : V) (hxy : Adj G x y) : (p:ℝ)*twoPoint G p z x ≤ twoPoint G p z y := by
  obtain ⟨e,he⟩ := hxy
  have h := association_finiteWitness p {ω : Set E | e ∈ ω} {ω | Conn G ω z x}
    (fun _ _ hω h => hω h) (fun _ _ hω h => conn_mono G hω h)
    (finiteWitness_edge e) (finiteWitness_conn G z x)
  have hp : (law p).real {ω : Set E | e ∈ ω} = (p:ℝ) := by
    simpa using finite_open_probability p {e}
  rw [hp] at h
  exact h.trans (measureReal_mono (fun ω hω =>
    conn_trans G ω hω.2 (Relation.ReflTransGen.single ⟨e,hω.1,he⟩)))

 
theorem walk_operator_apply (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, P (lp.single 2 y (1:ℂ)) x = (walkKernel G hloc a x y : ℂ))
    (f : Hilbert V) (x : V) :
    P f x = ∑ y ∈ insert x (neighbors G hloc x), (walkKernel G hloc a x y : ℂ)*f y := by
  have hz (y : V) (hy : y ∉ insert x (neighbors G hloc x)) : matrixCoeff P x y*f y = 0 := by
    have hxy : x ≠ y := by intro h; subst y; exact hy (Finset.mem_insert_self _ _)
    have hAdj : ¬Adj G x y := fun h => hy (Finset.mem_insert_of_mem ((mem_neighbors ..).mpr h))
    simp only [matrixCoeff,hP,walkKernel,ite_eq_right hxy,ite_eq_right hAdj,add_zero,Complex.ofReal_zero,zero_mul]
  have hsum := (operator_kernel_hasSum P f x).unique (hasSum_sum_of_ne_finset_zero hz)
  simpa only [matrixCoeff,hP] using hsum

 

theorem parameter_le_walk_norm [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, P (lp.single 2 y (1:ℂ)) x = (walkKernel G hloc a x y : ℂ))
    (p : unitInterval) (hp : OperatorBounded G p) : (p:ℝ) ≤ ‖P‖ := by
  obtain ⟨T,hT⟩ := hp
  let z := Classical.arbitrary V
  let f := T (lp.single 2 z (1:ℂ))
  have hf (x : V) : f x = (twoPoint G p x z : ℂ) := hT x z
  have hf0 : 0 < ‖f‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hval := congrArg (fun g : Hilbert V => g z) h
    simp [hf] at hval
  have hrow (x : V) : (p:ℝ)*twoPoint G p x z ≤
      ∑ y ∈ insert x (neighbors G hloc x), walkKernel G hloc a x y*twoPoint G p y z := by
    calc
      _ = ∑ y ∈ insert x (neighbors G hloc x), walkKernel G hloc a x y*((p:ℝ)*twoPoint G p x z) := by
        rw [← Finset.sum_mul,walkKernel_row_sum,one_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro y hy
        apply mul_le_mul_of_nonneg_left _ (walkKernel_nonneg G hloc D hD a ha haD x y)
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact mul_le_of_le_one_left (twoPoint_nonneg G p y z) p.2.2
        · simpa only [twoPoint_symm G p] using twoPoint_adj_lower G p z x y ((mem_neighbors ..).mp hy)
  have hpoint (x : V) : ‖((p:ℂ) • f) x‖ ≤ ‖P f x‖ := by
    rw [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hf,← Complex.ofReal_mul,
      Complex.norm_of_nonneg (mul_nonneg p.2.1 (twoPoint_nonneg G p x z)),
      walk_operator_apply G hloc a P hP]
    simp only [hf,← Complex.ofReal_mul,← Complex.ofReal_sum]
    rw [Complex.norm_of_nonneg (le_trans (mul_nonneg p.2.1 (twoPoint_nonneg G p x z)) (hrow x))]
    exact hrow x
  have hn := (lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) hpoint).trans (P.le_opNorm f)
  rw [norm_smul,Complex.norm_of_nonneg p.2.1] at hn
  exact (mul_le_mul_iff_left₀ hf0).mp hn

 
theorem pc_lt_one_of_nonamenable [Nonempty V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) : pc G < 1 := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  obtain ⟨D,P,hD0,hD,hPn,_,hP⟩ := exists_strict_walk_operator G hloc hqt hh
  have hDr : 0 < (D:ℝ) := by exact_mod_cast hD0
  let p : unitInterval := ⟨(‖P‖+1)/2,by constructor <;> linarith [norm_nonneg P]⟩
  have hp1 : p < 1 := by change (‖P‖+1)/2 < 1; linarith
  have ha : 0 ≤ (1:ℝ)/(2*D) := by positivity
  have haD : (1:ℝ)/(2*D)*D ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  apply lt_of_le_of_ne (show pc G ≤ 1 from (pc G).2.2)
  intro he
  have hb := operatorBounded_of_lt_pc G hloc hqt p (he ▸ hp1)
  have hle := parameter_le_walk_norm G hloc D hD _ ha haD P hP p hb
  change (‖P‖+1)/2 ≤ ‖P‖ at hle
  linarith

end CriticalParameter

section SpliceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

def exchangeOn (mask ω η : Set E) : Set E := (ω \ mask) ∪ (η ∩ mask)

@[simp] theorem mem_exchangeOn {mask ω η : Set E} {e : E} :
    e ∈ exchangeOn mask ω η ↔ if e ∈ mask then e ∈ η else e ∈ ω := by
  by_cases h : e ∈ mask <;> simp [exchangeOn,h]

theorem exchangeOn_involutive (mask ω η : Set E) :
    exchangeOn mask (exchangeOn mask ω η) (exchangeOn mask η ω) = ω := by
  ext e
  by_cases h : e ∈ mask <;> simp [h]

 

def spliceMask (G : BondGraph V E) (S B : Set V) (e : E) : Set E :=
  insert e {f | (∃ b ∈ B, b ∈ G f) ∧ f ∈ internalEdges G Sᶜ}

def spliceField (G : BondGraph V E) (S B : Set V) (e : E) (ω η : Set E) : Set E :=
  exchangeOn (spliceMask G S B e) ω η

theorem slit_cluster_subset (G : BondGraph V E) (S : Set V) (η : Set E)
    (y : V) (hy : y ∉ S) : cluster G (η ∩ internalEdges G Sᶜ) y ⊆ Sᶜ := by
  exact fun z hz => conn_internal_endpoint G Sᶜ hy hz

theorem spliceMask_not_internal (G : BondGraph V E) (S B : Set V) (e : E)
    (a b : V) (he : G e = s(a,b)) (hb : b ∉ S) {f : E}
    (hf : f ∈ internalEdges G S) : f ∉ spliceMask G S B e := by
  rintro (rfl | ⟨_,hout⟩)
  · exact hb (((mem_internalEdges_of_ends G S f a b he).mp hf).2)
  · exact (hout _ (Sym2.out_fst_mem _)) (hf _ (Sym2.out_fst_mem _))

theorem spliceMask_of_internal_piece (G : BondGraph V E) (S B : Set V) (e : E)
    (hB : B ⊆ Sᶜ) {f : E} (hf : f ∈ internalEdges G B) : f ∈ spliceMask G S B e := by
  right
  exact ⟨⟨(G f).out.1,hf _ (Sym2.out_fst_mem _),Sym2.out_fst_mem _⟩,
    fun v hv => hB (hf v hv)⟩

 
theorem splice_internal_fields (G : BondGraph V E) (S B : Set V) (e : E)
    (ω η : Set E) (a b : V) (he : G e = s(a,b)) (hb : b ∉ S) (hB : B ⊆ Sᶜ) :
    spliceField G S B e ω η ∩ internalEdges G S = ω ∩ internalEdges G S ∧
    spliceField G S B e ω η ∩ internalEdges G B = η ∩ internalEdges G B := by
  constructor
  · ext f
    by_cases hf : f ∈ internalEdges G S
    · simp only [Set.mem_inter_iff,hf,and_true,spliceField,mem_exchangeOn,
        ite_eq_right (spliceMask_not_internal G S B e a b he hb hf)]
    · simp only [Set.mem_inter_iff,hf,and_false]
  · ext f
    by_cases hf : f ∈ internalEdges G B
    · simp only [Set.mem_inter_iff,hf,and_true,spliceField,mem_exchangeOn,
        ite_eq_left (spliceMask_of_internal_piece G S B e hB hf)]
    · simp only [Set.mem_inter_iff,hf,and_false]

 
theorem splice_crossing_unique (G : BondGraph V E) (ω η : Set E) (x : V)
    (B : Set V) (e : E) {f : E} {a b : V}
    (hf : f ∈ spliceField G (cluster G ω x) B e ω η)
    (hab : G f = s(a,b)) (ha : a ∈ cluster G ω x) (hb : b ∉ cluster G ω x) : f = e := by
  have hno : f ∉ ω := fun h => hb ((edge_cluster_sides G ω x h hab).mp ha)
  have hm : f ∈ spliceMask G (cluster G ω x) B e := by
    by_contra h
    have hh := hf
    simp only [spliceField,mem_exchangeOn,ite_eq_right h] at hh
    exact hno hh
  rcases hm with rfl | ⟨_,hout⟩
  · rfl
  · exact ((((mem_internalEdges_of_ends G _ f a b hab).mp hout).1) ha).elim

 

theorem splice_cluster (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    cluster G (spliceField G S B e ω η) x = S ∪ B := by
  let S := cluster G ω x
  let ζ := η ∩ internalEdges G Sᶜ
  let B := cluster G ζ y
  let ω' := spliceField G S B e ω η
  change cluster G ω' x = S ∪ B
  have hB : B ⊆ Sᶜ := slit_cluster_subset G S η y hy
  have hbS : b ∉ S := hB hb
  have hfields := splice_internal_fields G S B e ω η a b he hbS hB
  have he' : e ∈ ω' := by
    change e ∈ exchangeOn (spliceMask G S B e) ω η
    rw [mem_exchangeOn,ite_eq_left (show e ∈ spliceMask G S B e from Set.mem_insert _ _)]
    exact heη
  have hSconn (z : V) (hz : z ∈ S) : Conn G ω' x z := by
    have h := conn_restrict_cluster G ω x (mem_cluster_self G ω x) hz
    apply conn_mono G _ h
    intro f hf
    exact (hfields.1.symm ▸ hf).1
  have hBconn (u v : V) (hu : u ∈ B) (hv : v ∈ B) : Conn G ω' u v := by
    have h := conn_restrict_cluster G ζ y hu (conn_trans G ζ (conn_symm G ζ hu) hv)
    apply conn_mono G _ h
    intro f hf
    exact (hfields.2.symm ▸ (show f ∈ η ∩ internalEdges G B from ⟨hf.1.1,hf.2⟩)).1
  apply Set.Subset.antisymm
  · intro z hz
    induction hz with
    | refl => exact Or.inl (mem_cluster_self G ω x)
    | @tail u v hxu huv ih =>
      obtain ⟨f,hf,hfv⟩ := huv
      by_cases hvS : v ∈ S
      · exact Or.inl hvS
      · rcases ih with huS | huB
        · have hfe := splice_crossing_unique G ω η x B e hf hfv huS hvS
          subst f
          have hends := Sym2.eq_iff.mp (he.symm.trans hfv)
          rcases hends with ⟨hau,hbv⟩ | ⟨hav,hbu⟩
          · exact Or.inr (hbv ▸ hb)
          · exact (hvS (hav ▸ ha)).elim
        · have huS : u ∉ S := hB huB
          have hm : f ∈ spliceMask G S B e := by
            right
            exact ⟨⟨u,huB,by simp [hfv]⟩,(mem_internalEdges_of_ends G _ f u v hfv).mpr ⟨huS,hvS⟩⟩
          have hfη : f ∈ η := by
            change f ∈ exchangeOn (spliceMask G S B e) ω η at hf
            rwa [mem_exchangeOn,ite_eq_left hm] at hf
          exact Or.inr ((edge_cluster_sides G ζ y
            ⟨hfη,(mem_internalEdges_of_ends G _ f u v hfv).mpr ⟨huS,hvS⟩⟩ hfv).mp huB)
  · intro z hz
    rcases hz with hz | hz
    · exact hSconn z hz
    · exact ((hSconn a ha).tail ⟨e,he',he⟩).trans (hBconn b z hb hz)

 
theorem splice_seam_pivotal (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y)
    (z : V) (hz : z ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    OpenMarkedPivotal G (spliceField G S B e ω η) {z} x e := by
  let S := cluster G ω x
  let B := cluster G (η ∩ internalEdges G Sᶜ) y
  let ω' := spliceField G S B e ω η
  have hB := slit_cluster_subset G S η y hy
  have hC := splice_cluster G ω η x y hy e a b he heη ha hb
  change cluster G ω' x = S ∪ B at hC
  refine ⟨?_,⟨z,Set.mem_singleton z,by change z ∈ cluster G ω' x; rw [hC]; exact Or.inr hz⟩,?_⟩
  · change e ∈ exchangeOn (spliceMask G S B e) ω η
    rw [mem_exchangeOn,ite_eq_left (show e ∈ spliceMask G S B e from Set.mem_insert _ _)]
    exact heη
  · rintro ⟨v,hv,hxv⟩
    have hvz : v = z := Set.mem_singleton_iff.mp hv
    subst v
    have hsub : cluster G (ω' \ {e}) x ⊆ S := by
      intro v hxv
      induction hxv with
      | refl => exact mem_cluster_self G ω x
      | @tail u v hxu huv ih =>
        obtain ⟨f,hf,hfv⟩ := huv
        by_contra hvS
        have hfe := splice_crossing_unique G ω η x B e hf.1 hfv ih hvS
        exact hf.2 (by simpa only [Set.mem_singleton_iff] using hfe)
    exact hB hz (hsub hxv)

end SpliceGeometry

section SpliceInverse
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem splice_close_seam_cluster (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (_heη : e ∈ η) (_ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    cluster G (spliceField G S B e ω η \ {e}) x = S := by
  let S := cluster G ω x
  let B := cluster G (η ∩ internalEdges G Sᶜ) y
  let ω' := spliceField G S B e ω η
  have hB := slit_cluster_subset G S η y hy
  have hf := (splice_internal_fields G S B e ω η a b he (hB hb) hB).1
  apply Set.Subset.antisymm
  · intro v hxv
    induction hxv with
    | refl => exact mem_cluster_self G ω x
    | @tail u v _ huv ih =>
      obtain ⟨f,hf,hfv⟩ := huv
      by_contra hvS
      have hfe := splice_crossing_unique G ω η x B e hf.1 hfv ih hvS
      exact hf.2 (Set.mem_singleton_iff.mpr hfe)
  · intro z hz
    have hc := conn_restrict_cluster G ω x (mem_cluster_self G ω x) hz
    apply conn_mono G _ hc
    intro f hfin
    refine ⟨(hf.symm ▸ hfin).1,?_⟩
    intro hfe
    have hfe' := Set.mem_singleton_iff.mp hfe
    subst f
    exact hB hb (((mem_internalEdges_of_ends G S e a b he).mp hfin.2).2)

 
theorem splice_recover_piece (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    let ω' := spliceField G S B e ω η
    cluster G ω' x \ cluster G (ω' \ {e}) x = B := by
  dsimp only
  rw [splice_cluster G ω η x y hy e a b he heη ha hb,
    splice_close_seam_cluster G ω η x y hy e a b he heη ha hb]
  have hB := slit_cluster_subset G (cluster G ω x) η y hy
  ext z
  constructor
  · rintro ⟨hz,hzS⟩
    exact hz.resolve_left hzS
  · intro hz
    exact ⟨Or.inr hz,hB hz⟩

 
def recoveredMask (G : BondGraph V E) (ω' : Set E) (x : V) (e : E) : Set E :=
  spliceMask G (cluster G (ω' \ {e}) x)
    (cluster G ω' x \ cluster G (ω' \ {e}) x) e

theorem recoveredMask_splice (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    recoveredMask G (spliceField G S B e ω η) x e = spliceMask G S B e := by
  unfold recoveredMask
  dsimp only
  rw [splice_recover_piece G ω η x y hy e a b he heη ha hb,
    splice_close_seam_cluster G ω η x y hy e a b he heη ha hb]

 
def undoSplice (G : BondGraph V E) (x : V) (e : E) (ω' η' : Set E) : Set E × Set E :=
  let M := recoveredMask G ω' x e
  (exchangeOn M ω' η',exchangeOn M η' ω')

 
theorem undoSplice_of_valid (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    let M := spliceMask G S B e
    undoSplice G x e (exchangeOn M ω η) (exchangeOn M η ω) = (ω,η) := by
  dsimp only [undoSplice]
  rw [show recoveredMask G (exchangeOn
      (spliceMask G (cluster G ω x) (cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) e) ω η) x e =
      spliceMask G (cluster G ω x) (cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) e from
    recoveredMask_splice G ω η x y hy e a b he heη ha hb]
  rw [exchangeOn_involutive,exchangeOn_involutive]

 
theorem spliceMask_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (S B : Set V) (hB : B.Finite) (e : E) : (spliceMask G S B e).Finite := by
  apply Set.Finite.insert
  apply (hB.biUnion (fun b _ => hloc b)).subset
  rintro f ⟨⟨b,hb,hbf⟩,_⟩
  exact Set.mem_iUnion₂.mpr ⟨b,hb,hbf⟩

end SpliceInverse

section FiniteExchange
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteExchange (M ω η : Finset E) : Finset E := (ω \ M) ∪ (η ∩ M)

@[simp] theorem coe_finiteExchange (M ω η : Finset E) :
    (finiteExchange M ω η : Set E) = exchangeOn (M:Set E) (ω:Set E) (η:Set E) := by
  simp only [finiteExchange,exchangeOn,Finset.coe_union,Finset.coe_sdiff,Finset.coe_inter]

theorem finiteExchange_card (M ω η : Finset E) :
    (finiteExchange M ω η).card = (ω \ M).card+(η ∩ M).card := by
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_left.mpr fun e he he' => (Finset.mem_sdiff.mp he).2 (Finset.mem_inter.mp he').2

theorem finiteExchange_card_sum (M ω η : Finset E) :
    (finiteExchange M ω η).card+(finiteExchange M η ω).card = ω.card+η.card := by
  rw [finiteExchange_card,finiteExchange_card]
  have hω := Finset.card_sdiff_add_card_inter ω M
  have hη := Finset.card_sdiff_add_card_inter η M
  omega

theorem finiteExchange_subset (M Q ω η : Finset E) (hω : ω ⊆ Q) (hη : η ⊆ Q) :
    finiteExchange M ω η ⊆ Q := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hω (Finset.mem_sdiff.mp he).1
  · exact hη (Finset.mem_inter.mp he).1

 
theorem bernoulliWeight_exchange (M Q ω η : Finset E) (hω : ω ⊆ Q) (hη : η ⊆ Q)
    (p : ℝ) :
    bernoulliWeight Q (finiteExchange M ω η) p * bernoulliWeight Q (finiteExchange M η ω) p =
      bernoulliWeight Q ω p * bernoulliWeight Q η p := by
  have hc := finiteExchange_card_sum M ω η
  have hcω := Finset.card_le_card hω
  have hcη := Finset.card_le_card hη
  have hcω' := Finset.card_le_card (finiteExchange_subset M Q ω η hω hη)
  have hcη' := Finset.card_le_card (finiteExchange_subset M Q η ω hη hω)
  have hd : (Q.card-(finiteExchange M ω η).card)+(Q.card-(finiteExchange M η ω).card) =
      (Q.card-ω.card)+(Q.card-η.card) := by omega
  unfold bernoulliWeight
  calc
    _ = p^((finiteExchange M ω η).card+(finiteExchange M η ω).card) *
      (1-p)^((Q.card-(finiteExchange M ω η).card)+(Q.card-(finiteExchange M η ω).card)) := by
        rw [pow_add,pow_add]; ring
    _ = p^(ω.card+η.card)*(1-p)^((Q.card-ω.card)+(Q.card-η.card)) := by rw [hc,hd]
    _ = _ := by rw [pow_add,pow_add]; ring

end FiniteExchange

section DeletionGoodness
attribute [local instance] Classical.propDecidable Classical.decEq

 
def deletionContacts (G : BondGraph V E) (ω : Set E) (A B : Set V) : Set E :=
  {e | e ∈ ω ∧ ∃ a ∈ B, ∃ b ∈ A, G e = s(a,b)}

 

def DeletionGoodForScale (G : BondGraph V E) (ω : Set E) (x : V) (L : ℝ) : Prop :=
  ∀ A ⊆ cluster G ω x, ∀ y ∈ cluster G ω x \ A,
    let B := cluster G (ω ∩ internalEdges G Aᶜ) y
    0 < (deletionContacts G ω A B).ncard →
    ∀ a ∈ B, ∀ b ∈ B,
      (pivotalDistance G (ω ∩ internalEdges G B) a b : ℝ) ≤
        (deletionContacts G ω A B).ncard*L

theorem deleted_cluster_subset (G : BondGraph V E) (ω : Set E) (x y : V)
    (A : Set V) (hy : y ∈ cluster G ω x \ A) :
    cluster G (ω ∩ internalEdges G Aᶜ) y ⊆ cluster G ω x \ A := by
  intro z hz
  exact ⟨conn_trans G ω hy.1 (conn_mono G Set.inter_subset_left hz),
    conn_internal_endpoint G Aᶜ hy.2 hz⟩

theorem contactSet_deleted_cluster (G : BondGraph V E) (ω : Set E) (A : Set V)
    (y : V) (hy : y ∉ A) :
    let B := cluster G (ω ∩ internalEdges G Aᶜ) y
    contactSet G ω B = deletionContacts G ω A B := by
  let ζ := ω ∩ internalEdges G Aᶜ
  let B := cluster G ζ y
  have hB : B ⊆ Aᶜ := slit_cluster_subset G A ω y hy
  ext e
  constructor
  · rintro ⟨he,a,b,hab,ha,hb⟩
    refine ⟨he,a,ha,b,?_,hab⟩
    by_contra hbA
    have heζ : e ∈ ζ := ⟨he,(mem_internalEdges_of_ends G Aᶜ e a b hab).mpr ⟨hB ha,hbA⟩⟩
    exact hb ((edge_cluster_sides G ζ y heζ hab).mp ha)
  · rintro ⟨he,a,ha,b,hb,hab⟩
    exact ⟨he,a,b,hab,ha,fun hh => hB hh hb⟩

 

theorem goodForScale_iff_deletion (G : BondGraph V E) (ω : Set E) (x : V) (L : ℝ)
    (hC : (cluster G ω x).Finite) :
    GoodForScale G ω x L ↔ DeletionGoodForScale G ω x L := by
  constructor
  · intro h A _ y hy
    let ζ := ω ∩ internalEdges G Aᶜ
    let B := cluster G ζ y
    have hBC := deleted_cluster_subset G ω x y A hy
    have hfin : B.Finite := hC.subset (fun _ hz => (hBC hz).1)
    let W := hfin.toFinset
    have hW : (W : Set V) = B := hfin.coe_toFinset
    have hsub : (W : Set V) ⊆ cluster G ω x := by rw [hW]; exact fun _ hz => (hBC hz).1
    have hi (a : V) (ha : a ∈ W) (b : V) (hb : b ∈ W) :
        Conn G (ω ∩ internalEdges G (W : Set V)) a b := by
      have ha' : a ∈ B := hW ▸ ha
      have hb' : b ∈ B := hW ▸ hb
      have hc := conn_restrict_cluster G ζ y ha' (conn_trans G ζ (conn_symm G ζ ha') hb')
      rw [hW]
      apply conn_mono G ?_ hc
      intro e he
      exact ⟨he.1.1,he.2⟩
    have hh := h W hsub hi
    rw [hW,contactSet_deleted_cluster G ω A y hy.2] at hh
    dsimp only
    intro hK a ha b hb
    exact hh hK a (by change a ∈ (W : Set V); rw [hW]; exact ha) b
      (by change b ∈ (W : Set V); rw [hW]; exact hb)
  · intro h W hW hconn hK a ha b hb
    let C := cluster G ω x
    let A := C \ (W : Set V)
    have haA : a ∈ C \ A := ⟨hW ha,fun hh => hh.2 ha⟩
    have hWA : (W : Set V) ⊆ Aᶜ := fun _ hz hh => hh.2 hz
    have heq : cluster G (ω ∩ internalEdges G Aᶜ) a = (W : Set V) := by
      apply Set.Subset.antisymm
      · intro z hz
        have hzC := deleted_cluster_subset G ω x a A haA hz
        by_contra hzW
        exact hzC.2 ⟨hzC.1,hzW⟩
      · intro z hz
        apply conn_mono G ?_ (hconn a ha z hz)
        intro e he
        exact ⟨he.1,fun v hv => hWA (he.2 v hv)⟩
    have hh := h A Set.sdiff_subset a haA
    dsimp only at hh
    have hc := contactSet_deleted_cluster G ω A a haA.2
    dsimp only at hc
    rw [heq] at hh hc
    rw [← hc] at hh
    exact hh hK a ha b hb

 
theorem capped_good_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L) ↔
      ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧
        (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ M ∧
          GoodForScale G (ω ∩ (Q : Set E)) x L) := by
  have hc := capped_cluster_local G hloc x M ω
  have hb := cappedBadGoodness_local G hloc x M L ω
  unfold CappedBadGoodness at hb
  dsimp only at hc hb ⊢
  constructor
  · rintro ⟨hf,hM,hg⟩
    obtain ⟨hf',hM'⟩ := hc.mp ⟨hf,hM⟩
    refine ⟨hf',hM',?_⟩
    by_contra hng
    exact (hb.mpr ⟨hf',hM',hng⟩).2.2 hg
  · rintro ⟨hf,hM,hg⟩
    obtain ⟨hf',hM'⟩ := hc.mpr ⟨hf,hM⟩
    refine ⟨hf',hM',?_⟩
    by_contra hng
    exact (hb.mp ⟨hf',hM',hng⟩).2.2 hg

theorem measurableSet_capped_good (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) :
    MeasurableSet {ω : Set E | (cluster G ω x).Finite ∧
      (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  have he : {ω : Set E | (cluster G ω x).Finite ∧
      (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L} =
    {ω : Set E | (cluster G (ω ∩ (Q : Set E)) x).Finite ∧
      (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ M ∧ GoodForScale G (ω ∩ (Q : Set E)) x L} := by
    ext ω
    exact capped_good_local G hloc x M L ω
  rw [he]
  exact measurableSet_finite_restriction Q {η : Set E | (cluster G η x).Finite ∧
      (cluster G η x).ncard ≤ M ∧ GoodForScale G η x L}

end DeletionGoodness

section SpliceSelection
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_maximal_splice_index (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V)
    (k j : ℕ) (hj : j ≤ k)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (S : Set V) (hyj : y j ∈ S) (hyk : y k ∉ S) :
    ∃ i ∈ Finset.Icc (j+1) k,
      ((cluster G (η i) (y i)) ∩ S).Nonempty ∧ y i ∉ S ∧
      ∀ l, i < l → l ≤ k → Disjoint (cluster G (η l) (y l)) S := by
  have hjk : j < k := by
    by_contra h
    have hEq : j = k := by omega
    exact hyk (hEq ▸ hyj)
  let T := (Finset.Icc (j+1) k).filter fun i => ((cluster G (η i) (y i)) ∩ S).Nonempty
  have hT : T.Nonempty := by
    refine ⟨j+1,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩,?_⟩⟩
    refine ⟨y j,?_,hyj⟩
    simpa only [Nat.add_sub_cancel,cluster,Set.mem_ofPred_eq] using hchain (j+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  let i := T.max' hT
  have hi : i ∈ T := Finset.max'_mem T hT
  obtain ⟨hiI,hiS⟩ := Finset.mem_filter.mp hi
  have hiU := (Finset.mem_Icc.mp hiI).2
  have hiL := (Finset.mem_Icc.mp hiI).1
  have hl (l : ℕ) (hil : i < l) (hlk : l ≤ k) : Disjoint (cluster G (η l) (y l)) S := by
    apply Set.disjoint_left.mpr
    intro z hz hzS
    have hlT : l ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega,hlk⟩,⟨z,hz,hzS⟩⟩
    have hli : l ≤ i := Finset.le_max' T l hlT
    omega
  refine ⟨i,hiI,hiS,?_,hl⟩
  intro hyi
  by_cases hik : i = k
  · exact hyk (hik ▸ hyi)
  · have hic : y i ∈ cluster G (η (i+1)) (y (i+1)) := by
      simpa only [Nat.add_sub_cancel,cluster,Set.mem_ofPred_eq] using hchain (i+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    exact Set.disjoint_left.mp (hl (i+1) (by omega) (by omega)) hic hyi

 

theorem exists_splice_contact (G : BondGraph V E) (η : Set E) (S : Set V) (y : V)
    (hy : y ∉ S) (hmeet : (cluster G η y ∩ S).Nonempty) :
    ∃ e a b, e ∈ η ∧ G e = s(a,b) ∧ a ∈ S ∧
      b ∈ cluster G (η ∩ internalEdges G Sᶜ) y := by
  obtain ⟨v,hv,hvS⟩ := hmeet
  obtain ⟨b,a,e,_,ha,he,hab,hb⟩ := conn_first_entry G S η hy hvS hv
  exact ⟨e,a,b,he,hab.trans (Sym2.eq_swap),ha,hb⟩

 
theorem splice_cluster_cap (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y)
    (N M : ℕ) (hS : (cluster G ω x).Finite) (hN : (cluster G ω x).ncard ≤ N)
    (hC : (cluster G η y).Finite) (hM : (cluster G η y).ncard ≤ M) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    (cluster G (spliceField G S B e ω η) x).Finite ∧
      (cluster G (spliceField G S B e ω η) x).ncard ≤ N+M := by
  let S := cluster G ω x
  let B := cluster G (η ∩ internalEdges G Sᶜ) y
  have hBC : B ⊆ cluster G η y := fun _ hz => conn_mono G Set.inter_subset_left hz
  have hB : B.Finite := hC.subset hBC
  dsimp only
  rw [splice_cluster G ω η x y hy e a b he heη ha hb]
  refine ⟨hS.union hB,?_⟩
  exact (Set.ncard_union_le _ _).trans (Nat.add_le_add hN ((Set.ncard_le_ncard hBC hC).trans hM))

 

theorem cluster_eq_of_incident_agreement (G : BondGraph V E) (ω η : Set E) (x : V)
    (he : ∀ e, (∃ v ∈ cluster G ω x, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    cluster G η x = cluster G ω x := by
  have hforward : cluster G ω x ⊆ cluster G η x := by
    intro y hy
    induction hy with
    | refl => exact conn_refl G _ _
    | @tail a b hxa hab ih =>
      obtain ⟨e,heω,hab⟩ := hab
      exact ih.tail ⟨e,(he e ⟨a,hxa,by simp [hab]⟩).mp heω,hab⟩
  apply Set.Subset.antisymm _ hforward
  intro y hy
  induction hy with
  | refl => exact conn_refl G _ _
  | @tail a b _ hab ih =>
    obtain ⟨e,heη,hab⟩ := hab
    exact ih.tail ⟨e,(he e ⟨a,ih,by simp [hab]⟩).mpr heη,hab⟩

 

theorem spliceMask_avoids_prefix (G : BondGraph V E) (S B R : Set V) (hRS : R ⊆ S)
    (e : E) (a b : V) (hab : G e = s(a,b)) (ha : a ∉ R) (hb : b ∉ S)
    {f : E} (hf : ∃ v ∈ R, v ∈ G f) : f ∉ spliceMask G S B e := by
  rintro (rfl | ⟨_,hfo⟩)
  · obtain ⟨v,hv,hvf⟩ := hf
    rw [hab] at hvf
    rcases Sym2.mem_iff.mp hvf with rfl | rfl
    · exact ha hv
    · exact hb (hRS hv)
  · obtain ⟨v,hv,hvf⟩ := hf
    exact hfo v hvf (hRS hv)

 

theorem splice_preserves_prefix_cut (G : BondGraph V E) (ω η : Set E) (x : V)
    (B : Set V) (e f : E) (a b : V) (hab : G e = s(a,b))
    (ha : a ∉ cluster G (ω \ {f}) x) (hb : b ∉ cluster G ω x) :
    cluster G ((spliceField G (cluster G ω x) B e ω η) \ {f}) x =
      cluster G (ω \ {f}) x := by
  apply cluster_eq_of_incident_agreement
  intro g hg
  have hRS : cluster G (ω \ {f}) x ⊆ cluster G ω x := fun _ h => conn_mono G Set.sdiff_subset h
  have hno := spliceMask_avoids_prefix G _ B _ hRS e a b hab ha hb hg
  simp only [Set.mem_sdiff,spliceField,mem_exchangeOn,ite_eq_right hno]

end SpliceSelection

section SpliceTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 

inductive SpliceTrace (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) (k : ℕ) :
    ℕ → Set E → List (ℕ × E) → Set E → Prop
  | stop (j : ℕ) (ω : Set E) (hstop : y k ∈ cluster G ω x) :
      SpliceTrace G x η y k j ω [] ω
  | step (j i : ℕ) (ω : Set E) (e : E) (a b : V) (rest : List (ℕ × E)) (ωf : Set E)
      (hnot : y k ∉ cluster G ω x) (hji : j < i) (hik : i ≤ k)
      (hmax : ∀ l, i < l → l ≤ k → Disjoint (cluster G (η l) (y l)) (cluster G ω x))
      (hy : y i ∉ cluster G ω x) (he : e ∈ η i) (hab : G e = s(a,b))
      (ha : a ∈ cluster G ω x)
      (hb : b ∈ cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i))
      (htail : SpliceTrace G x η y k i
        (spliceField G (cluster G ω x)
          (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e ω (η i)) rest ωf) :
      SpliceTrace G x η y k j ω ((i,e)::rest) ωf

 

theorem exists_spliceTrace (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (k M : ℕ)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (N : ℕ) (hfin : (cluster G ω x).Finite) (hN : (cluster G ω x).ncard ≤ N) :
    ∃ steps ωf, SpliceTrace G x η y k j ω steps ωf ∧ steps.length ≤ k-j ∧
      y k ∈ cluster G ωf x ∧ (cluster G ωf x).Finite ∧
        (cluster G ωf x).ncard ≤ N+(k-j)*M := by
  generalize hn : k-j = n
  induction n using Nat.strong_induction_on generalizing j ω N with
  | h n ih =>
    by_cases hz : y k ∈ cluster G ω x
    · refine ⟨[],ω,SpliceTrace.stop j ω hz,by simp,hz,hfin,?_⟩
      exact hN.trans (Nat.le_add_right ..)
    · obtain ⟨i,hiI,hmeet,hyi,hmax⟩ :=
        exists_maximal_splice_index G η y k j hj hchain (cluster G ω x) hyj hz
      obtain ⟨hji,hik⟩ := Finset.mem_Icc.mp hiI
      obtain ⟨e,a,b,he,hab,ha,hb⟩ := exists_splice_contact G (η i) (cluster G ω x) (y i) hyi hmeet
      let B := cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)
      let ω' := spliceField G (cluster G ω x) B e ω (η i)
      have hi1 : i ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega,hik⟩
      have hcap := splice_cluster_cap G ω (η i) x (y i) hyi e a b hab he ha hb N M hfin hN
        (hcaps i hi1).1 (hcaps i hi1).2
      have hyt : y i ∈ cluster G ω' x := by
        change y i ∈ cluster G (spliceField G (cluster G ω x) B e ω (η i)) x
        rw [splice_cluster G ω (η i) x (y i) hyi e a b hab he ha hb]
        exact Or.inr (mem_cluster_self G _ _)
      have hlt : k-i < n := by omega
      obtain ⟨steps,ωf,htrace,hlen,hconn,hf,hs⟩ :=
        ih (k-i) hlt i hik ω' hyt (N+M) hcap.1 hcap.2 rfl
      refine ⟨(i,e)::steps,ωf,
        SpliceTrace.step j i ω e a b steps ωf hz (by omega) hik hmax hyi he hab ha hb htrace,
        ?_,hconn,hf,?_⟩
      · simp only [List.length_cons]
        omega
      · have hm : (k-i+1)*M ≤ (k-j)*M := Nat.mul_le_mul_right M (by omega)
        rw [Nat.add_mul,one_mul] at hm
        calc
          _ ≤ (N+M)+(k-i)*M := hs
          _ ≤ N+(k-j)*M := by omega
          _ = N+n*M := by rw [hn]

 
theorem SpliceTrace.cluster_subset (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) : cluster G ω x ⊆ cluster G ωf x := by
  induction h with
  | stop => exact Set.Subset.rfl
  | @step j i ω e a b rest ωf _ _ _ _ hy he hab ha hb ht ih =>
    apply Set.Subset.trans _ ih
    rw [splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb]
    exact Set.subset_union_left

 

theorem SpliceTrace.preserve_cut (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) (f : E)
    (havoid : ∀ l, j < l → l ≤ k →
      Disjoint (cluster G (η l) (y l)) (cluster G (ω \ {f}) x)) :
    cluster G (ωf \ {f}) x = cluster G (ω \ {f}) x := by
  induction h with
  | stop => rfl
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    have hBC : b ∈ cluster G (η i) (y i) := conn_mono G Set.inter_subset_left hb
    have haC : a ∈ cluster G (η i) (y i) := (edge_cluster_sides G (η i) (y i) he hab).mpr hBC
    have haR : a ∉ cluster G (ω \ {f}) x := fun hh => Set.disjoint_left.mp (havoid i hji hik) haC hh
    have hbS : b ∉ cluster G ω x := slit_cluster_subset G _ (η i) (y i) hy hb
    have heq := splice_preserves_prefix_cut G ω (η i) x
      (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e f a b hab haR hbS
    rw [ih]
    · exact heq
    · intro l hil hlk
      rw [heq]
      exact havoid l (hji.trans hil) hlk

 
theorem SpliceTrace.endpoint (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) : y k ∈ cluster G ωf x := by
  induction h with
  | stop _ _ hs => exact hs
  | step => assumption

 

theorem SpliceTrace.seams_pivotal (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ q ∈ steps, OpenMarkedPivotal G ωf {y k} x q.2 := by
  induction h with
  | stop => simp
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · let S := cluster G ω x
      let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
      let ω' := spliceField G S B e ω (η i)
      have hcut : cluster G (ω' \ {e}) x = S :=
        splice_close_seam_cluster G ω (η i) x (y i) hy e a b hab he ha hb
      have hfinal : cluster G (ωf \ {e}) x = S := by
        rw [SpliceTrace.preserve_cut G x η y k i ω' ωf rest ht e]
        · exact hcut
        · intro l hil hlk
          rw [hcut]
          exact hmax l hil hlk
      have hconn := SpliceTrace.endpoint G x η y k i ω' ωf rest ht
      have hno : ¬Conn G (ωf \ {e}) x (y k) := by
        intro hc
        have : y k ∈ cluster G (ωf \ {e}) x := hc
        rw [hfinal] at this
        exact hn this
      have heω : e ∈ ωf := by
        by_contra heω
        have heq : ωf \ {e} = ωf := by
          ext f
          constructor
          · exact fun hh => hh.1
          · intro hh
            exact ⟨hh,fun hfe => heω ((Set.mem_singleton_iff.mp hfe) ▸ hh)⟩
        exact hno (heq.symm ▸ hconn)
      exact ⟨heω,⟨y k,rfl,hconn⟩,by simpa only [MarkedEvent,Set.mem_singleton_iff,exists_eq_left] using hno⟩
    · exact ih q hq

end SpliceTrace

end Percolation

end OAI
