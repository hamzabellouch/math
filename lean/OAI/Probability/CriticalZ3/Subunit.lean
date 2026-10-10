import OAI.Probability.CriticalZ3.ExplorationSurvival

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace BlockPercolation
open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PlanarBoundary
variable {E : Type}

def active (J : Point → Finset E) (ω : E → Bool) (v : Point) : Prop :=
  ∀ e ∈ J v, ω e = true

def Bad (J : Point → Finset E) (v : Point) : Set (E → Bool) :=
  {ω | ¬active J ω v}

def Adj (J : Point → Finset E) (ω : E → Bool) (x y : Point) : Prop :=
  (∃ d : Direction, y = x+outward d) ∧ active J ω x ∧ active J ω y

def cluster (J : Point → Finset E) (ω : E → Bool) : Set Point :=
  {v | active J ω (0,0) ∧ Relation.ReflTransGen (Adj J ω) (0,0) v}

theorem root_mem_iff (J : Point → Finset E) (ω : E → Bool) :
    (0,0) ∈ cluster J ω ↔ active J ω (0,0) :=
  ⟨And.left,fun h => ⟨h,.refl⟩⟩

theorem cluster_active {J : Point → Finset E} {ω : E → Bool} {v : Point}
    (hv : v ∈ cluster J ω) : active J ω v := by
  obtain ⟨h,hv⟩ := hv
  induction hv with
  | refl => exact h
  | tail _ hab _ => exact hab.2.2

theorem outside_bad (J : Point → Finset E) (ω : E → Bool) (x : Point)
    (hx : x ∈ cluster J ω) (d : Direction) (hy : x+outward d ∉ cluster J ω) :
    ω ∈ Bad J (x+outward d) := by
  intro ha
  exact hy ⟨hx.1,hx.2.tail ⟨⟨d,rfl⟩,cluster_active hx,ha⟩⟩

theorem bad_determined (J : Point → Finset E) (v : Point) :
    ProductCylinder.DeterminedBy (F := Prop) (J v) (fun ω => ω ∈ Bad J v) := by
  intro ω ω' h
  dsimp [Bad,active]
  congr 1
  apply propext
  constructor <;> intro hh e he
  · rw [←h e he]; exact hh e he
  · rw [h e he]; exact hh e he

theorem measurableSet_bad (J : Point → Finset E) (v : Point) : MeasurableSet (Bad J v) :=
  ProductCylinder.measurableSet_determined (J v) _
    (fun ω ω' h => eq_iff_iff.mp (bad_determined J v ω ω' h))

theorem single_closed_probability (p : Set.Icc (0 : ℝ) 1) (e : E) :
    (ProductCylinder.law (fun _ : E => p)).real {ω | ω e = false} = 1-(p : ℝ) := by
  have h := Measure.infinitePi_map_eval (fun _ : E => bernoulliMeasure true false p) e
  have hm : Measurable (fun ω : E → Bool => ω e) := measurable_pi_apply e
  have he : {ω : E → Bool | ω e = false} = (fun ω => ω e) ⁻¹' {false} := rfl
  rw [he,Measure.real_def,←Measure.map_apply hm (measurableSet_singleton _)]
  change ((Measure.infinitePi (fun _ : E => bernoulliMeasure true false p)).map
    (fun ω => ω e) {false}).toReal = _
  rw [h]
  change (bernoulliMeasure true false p).real {false} = _
  rw [bernoulliMeasure_real_apply p (measurableSet_singleton _)]
  simp [unitInterval.coe_symm_eq]

theorem bad_probability_le (p : Set.Icc (0 : ℝ) 1) (J : Point → Finset E) (v : Point) :
    (ProductCylinder.law (fun _ : E => p)).real (Bad J v) ≤ (J v).card*(1-(p : ℝ)) := by
  have he : Bad J v = ⋃ e : J v, {ω | ω e.1 = false} := by
    ext ω
    simp only [Bad,active,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h
      push Not at h
      obtain ⟨e,he,hω⟩ := h
      exact ⟨⟨e,he⟩,Bool.eq_false_iff.mpr hω⟩
    · rintro ⟨e,he⟩ h
      have := h e.1 e.2
      simp_all
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  simp only [single_closed_probability,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,le_refl]

/-- Peierls survival for independent finite blocks of at most two bits. -/
theorem survival (p : Set.Icc (0 : ℝ) 1) (J : Point → Finset E)
    (hJ : Pairwise (fun u v => Disjoint (J u) (J v))) (hcard : ∀ v, (J v).card ≤ 2)
    (hp : 2*(1-(p : ℝ)) ≤ CriticalScales.contourError)
    (A : Set (E → Bool))
    (hA : ∀ ω, (cluster J ω).Infinite → ω ∈ A) :
    0 < ProductCylinder.law (fun _ : E => p) A := by
  let μ := ProductCylinder.law (fun _ : E => p)
  have hb (v : Point) : μ.real (Bad J v) ≤ CriticalScales.contourError := by
    apply (bad_probability_le p J v).trans
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard v) (sub_nonneg.mpr p.2.2)).trans hp
  have hbad (s : Finset Point) : μ.real {ω | ∀ v ∈ s, ω ∈ Bad J v} ≤
      CriticalScales.contourError^s.card := by
    rw [InfiniteConditioning.disjoint_blocks_probability (fun _ : E => p) J hJ (Bad J) (bad_determined J) s]
    calc
      _ ≤ ∏ _v ∈ s, CriticalScales.contourError :=
        Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg) (fun v _ => hb v)
      _ = _ := by simp
  have hf := PlanarBoundary.finite_good_bound μ (cluster J) (Bad J)
    (fun ω _ x hx d hy => outside_bad J ω x hx d hy) hbad
  have hroot : 1-CriticalScales.contourError ≤ μ.real {ω | active J ω (0,0)} := by
    have he : {ω | active J ω (0,0)} = (Bad J (0,0))ᶜ := by ext ω; simp [Bad]
    rw [he,measureReal_compl (measurableSet_bad J (0,0)),probReal_univ]
    linarith [hb (0,0)]
  have hcover : {ω | active J ω (0,0)} ⊆
      {ω | (cluster J ω).Finite ∧ (0,0) ∈ cluster J ω} ∪ A := by
    intro ω hω
    by_cases hfinite : (cluster J ω).Finite
    · exact Or.inl ⟨hfinite,(root_mem_iff J ω).mpr hω⟩
    · exact Or.inr (hA ω hfinite)
  have hle := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le _ _)
  have hpos : 0 < μ.real A := by
    have hh := CriticalScales.contourError_lt_half
    linarith
  exact ENNReal.toReal_pos_iff.mp hpos |>.1

end BlockPercolation

namespace CriticalZ3
open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PlanarBoundary

/-- The planar sublattice used only for the elementary strict upper threshold. -/
def planarEmbed (v : Point) : Vertex := ![v.1,v.2,0]

theorem planarEmbed_injective : Function.Injective planarEmbed := by
  intro u v h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  exact Prod.ext (by simpa [planarEmbed] using h0) (by simpa [planarEmbed] using h1)

@[simp] theorem planarEmbed_zero : planarEmbed (0,0) = 0 := by
  funext i; fin_cases i <;> rfl

def planarSiteBlock (v : Point) : Finset Vertex := {planarEmbed v}

def planarBondBlock (v : Point) : Finset Bond := {(planarEmbed v,0),(planarEmbed v,1)}

theorem planarSiteBlock_disjoint : Pairwise (fun u v => Disjoint (planarSiteBlock u) (planarSiteBlock v)) := by
  intro u v huv
  simp only [planarSiteBlock,Finset.disjoint_singleton]
  exact fun h => huv (planarEmbed_injective h)

theorem planarBondBlock_disjoint : Pairwise (fun u v => Disjoint (planarBondBlock u) (planarBondBlock v)) := by
  intro u v huv
  rw [Finset.disjoint_left]
  intro e he he'
  have hleft (w : Point) (he : e ∈ planarBondBlock w) : e.1 = planarEmbed w := by
    simp only [planarBondBlock,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> rfl
  exact huv (planarEmbed_injective ((hleft u he).symm.trans (hleft v he')))

theorem planarSiteBlock_card (v : Point) : (planarSiteBlock v).card ≤ 2 := by simp [planarSiteBlock]
theorem planarBondBlock_card (v : Point) : (planarBondBlock v).card ≤ 2 := by
  simp [planarBondBlock]

theorem planar_neighbor (v : Point) (d : Direction) :
    NearestNeighbor (planarEmbed v) (planarEmbed (v+outward d)) := by
  fin_cases d
  · refine ⟨1,Or.inr ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine ⟨0,Or.inl ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine ⟨1,Or.inl ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine ⟨0,Or.inr ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]

theorem planar_site_open {ω : SiteConfig} {u v : Point}
    (h : BlockPercolation.Adj planarSiteBlock ω u v) :
    SiteOpen ω (planarEmbed u) (planarEmbed v) := by
  obtain ⟨⟨d,rfl⟩,hu,hv⟩ := h
  exact ⟨planar_neighbor u d,hu _ (Finset.mem_singleton_self _),hv _ (Finset.mem_singleton_self _)⟩

theorem planar_bond_open {ω : BondConfig} {u v : Point}
    (h : BlockPercolation.Adj planarBondBlock ω u v) :
    BondOpen ω (planarEmbed u) (planarEmbed v) := by
  obtain ⟨⟨d,rfl⟩,hu,hv⟩ := h
  have hu0 : ω (planarEmbed u,0) = true := hu _ (Finset.mem_insert_self _ _)
  have hu1 : ω (planarEmbed u,1) = true := hu _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hv0 : ω (planarEmbed (u+outward d),0) = true := hv _ (Finset.mem_insert_self _ _)
  have hv1 : ω (planarEmbed (u+outward d),1) = true := hv _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  fin_cases d
  · refine Or.inr ⟨1,?_,hv1⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine Or.inl ⟨0,?_,hu0⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine Or.inl ⟨1,?_,hu1⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine Or.inr ⟨0,?_,hv0⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]

theorem planar_bond_infinite {ω : BondConfig}
    (h : (BlockPercolation.cluster planarBondBlock ω).Infinite) : ω ∈ bondInfiniteAt 0 := by
  apply (h.image planarEmbed_injective.injOn).mono
  rintro _ ⟨v,hv,rfl⟩
  have hc := hv.2.lift planarEmbed (fun _ _ h => planar_bond_open h)
  change Relation.ReflTransGen (BondOpen ω) (planarEmbed (0,0)) (planarEmbed v) at hc
  rw [planarEmbed_zero] at hc
  exact hc

theorem planar_site_infinite {ω : SiteConfig}
    (h : (BlockPercolation.cluster planarSiteBlock ω).Infinite) : ω ∈ siteInfiniteAt 0 := by
  apply (h.image planarEmbed_injective.injOn).mono
  rintro _ ⟨v,hv,rfl⟩
  have hc := hv.2.lift planarEmbed (fun _ _ h => planar_site_open h)
  change Relation.ReflTransGen (SiteOpen ω) (planarEmbed (0,0)) (planarEmbed v) at hc
  refine ⟨?_,by simpa only [planarEmbed_zero] using hc⟩
  have ho := hv.1 (planarEmbed (0,0)) (Finset.mem_singleton_self _)
  simpa only [planarEmbed_zero] using ho

noncomputable def subunitParameter : Set.Icc (0 : ℝ) 1 :=
  ⟨1-CriticalScales.contourError/4,by
    have hf0 := CriticalScales.contourError_pos
    have hf1 := CriticalScales.contourError_lt_half
    constructor <;> linarith⟩

theorem subunitParameter_lt_one : (subunitParameter : ℝ) < 1 := by
  dsimp [subunitParameter]
  linarith [CriticalScales.contourError_pos]

theorem subunit_bond_positive : 0 < bondLaw subunitParameter (bondInfiniteAt 0) := by
  have he : parameter subunitParameter = subunitParameter := Subtype.ext (parameter_coe subunitParameter.2)
  have h := BlockPercolation.survival subunitParameter planarBondBlock
    planarBondBlock_disjoint planarBondBlock_card (by
      change 2*(1-(1-CriticalScales.contourError/4)) ≤ CriticalScales.contourError
      linarith [CriticalScales.contourError_pos]) (bondInfiniteAt 0) (fun _ => planar_bond_infinite)
  simpa only [bondLaw,he,ProductCylinder.law] using h

theorem subunit_site_positive : 0 < siteLaw subunitParameter (siteInfiniteAt 0) := by
  have he : parameter subunitParameter = subunitParameter := Subtype.ext (parameter_coe subunitParameter.2)
  have h := BlockPercolation.survival subunitParameter planarSiteBlock
    planarSiteBlock_disjoint planarSiteBlock_card (by
      change 2*(1-(1-CriticalScales.contourError/4)) ≤ CriticalScales.contourError
      linarith [CriticalScales.contourError_pos]) (siteInfiniteAt 0) (fun _ => planar_site_infinite)
  simpa only [siteLaw,he,ProductCylinder.law] using h

theorem bondCritical_lt_one : bondCritical < 1 := by
  apply lt_of_le_of_lt (csInf_le (show BddBelow {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧
      0 < bondLaw p (bondInfiniteAt 0)} from ⟨0,fun _ h => h.1.1⟩)
    ⟨subunitParameter.2,subunit_bond_positive⟩) subunitParameter_lt_one

theorem siteCritical_lt_one : siteCritical < 1 := by
  apply lt_of_le_of_lt (csInf_le (show BddBelow {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧
      0 < siteLaw p (siteInfiniteAt 0)} from ⟨0,fun _ h => h.1.1⟩)
    ⟨subunitParameter.2,subunit_site_positive⟩) subunitParameter_lt_one

end CriticalZ3

end OAI
