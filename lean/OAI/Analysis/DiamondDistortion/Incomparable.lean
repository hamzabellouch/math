import OAI.Analysis.DiamondDistortion.CoordinateDual

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace IncomparableModel
open Forest
/-- Every node of one admissible segment is incomparable with every node of
    another. This is strictly more restrictive than disjointness. -/
def Incomparable (F : forestSegments.Family) : Prop :=
  Pairwise (fun i j => ∀ u ∈ F.seg i,∀ v ∈ F.seg j,
    ¬ ForestAncestor u v ∧ ¬ ForestAncestor v u)
def Family := {F : forestSegments.Family // Incomparable F}
instance : Nonempty Family := ⟨⟨{
  n := 0
  seg := Fin.elim0
  allowed := fun i => Fin.elim0 i
  disjoint := by intro i; exact Fin.elim0 i },by intro i; exact Fin.elim0 i⟩⟩
lemma families_bddAbove : BddAbove (Set.range (fun F : Family => F.val.seminorm)) := by
  rw [Seminorm.bddAbove_range_iff]
  intro p
  exact ⟨forestSegments.primalSeminorm p,by rintro _ ⟨F,rfl⟩; exact forestSegments.test_le_primal F.val p⟩
/-- The exact incomparable-segment primal norm, not its disjoint-segment analogue. -/
def primalSeminorm : Seminorm ℝ (ForestNode →₀ ℝ) := ⨆ F : Family,F.val.seminorm
lemma test_le_primal (F : Family) (p : ForestNode →₀ ℝ) : ‖F.val.test p‖ ≤ primalSeminorm p := by
  rw [primalSeminorm,Seminorm.iSup_apply families_bddAbove]
  exact le_ciSup (⟨forestSegments.primalSeminorm p,by
    rintro _ ⟨G,rfl⟩; exact forestSegments.test_le_primal G.val p⟩ :
      BddAbove (Set.range (fun G : Family => G.val.seminorm p))) F
lemma primal_le_disjoint (p : ForestNode →₀ ℝ) : primalSeminorm p ≤ forestSegments.primalSeminorm p := by
  rw [primalSeminorm,Seminorm.iSup_apply families_bddAbove]
  exact ciSup_le (fun F => forestSegments.test_le_primal F.val p)
def singletonFamily (i : ForestNode) : Family :=
  ⟨forestSegments.singletonFamily i,by
    intro j k h
    have he : j=k := @Subsingleton.elim (Fin 1) inferInstance j k
    exact False.elim (h he)⟩
lemma coordinate_le_primal (p : ForestNode →₀ ℝ) (i : ForestNode) : |p i| ≤ primalSeminorm p := by
  have hh := test_le_primal (singletonFamily i) p
  rw [EuclideanSpace.norm_eq] at hh
  change Real.sqrt (∑ _ : Fin 1,‖∑ j ∈ ({i} : Finset ForestNode),p j‖^2) ≤ _ at hh
  simpa [Real.sqrt_sq_eq_abs] using hh

def primalData : CoordinateCompletion.Data ForestNode where
  seminorm := primalSeminorm
  coordinate_bound i := ⟨1,fun p => by simpa only [one_mul] using coordinate_le_primal p i⟩
abbrev PrimalSpace := primalData.Space
/-- The full Banach dual of the incomparable-segment primal completion. -/
abbrev Space := StrongDual ℝ PrimalSpace

lemma family_energy (F : Family) (p : ForestNode →₀ ℝ) :
    (∑ i,(∑ j ∈ F.val.seg i,p j)^2) ≤ (primalSeminorm p)^2 := by
  have hh := (sq_le_sq₀ (norm_nonneg _) (apply_nonneg _ _)).mpr (test_le_primal F p)
  rw [EuclideanSpace.norm_sq_eq] at hh
  simpa only [SegmentSystem.Family.test_apply,Real.norm_eq_abs,sq_abs] using hh
lemma primal_sq_le (p : ForestNode →₀ ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ F : Family,(∑ i,(∑ j ∈ F.val.seg i,p j)^2) ≤ M) :
    (primalSeminorm p)^2 ≤ M := by
  have hb : primalSeminorm p ≤ Real.sqrt M := by
    rw [primalSeminorm,Seminorm.iSup_apply families_bddAbove]
    apply ciSup_le
    intro F
    have hh := hF F
    have he : ‖F.val.test p‖^2=(∑ i,(∑ j ∈ F.val.seg i,p j)^2) := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [SegmentSystem.Family.test_apply,Real.norm_eq_abs,sq_abs]
    rw [← he,← Real.sq_sqrt hM] at hh
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hh
  have hh := (sq_le_sq₀ (apply_nonneg _ _) (Real.sqrt_nonneg _)).mpr hb
  rwa [Real.sq_sqrt hM] at hh

def familyOfFintype {κ : Type*} [Fintype κ] (S : κ → Finset ForestNode)
    (hS : ∀ i,forestSegments.IsSegment (S i))
    (hi : Pairwise (fun i j => ∀ u ∈ S i,∀ v ∈ S j,¬ ForestAncestor u v ∧ ¬ ForestAncestor v u)) : Family := by
  have hd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (hi hij v hv v hw).1 ⟨rfl,List.prefix_refl _⟩
  refine ⟨forestSegments.familyOfFintype S hS hd,?_⟩
  intro i j hij
  exact hi (fun he => hij ((Fintype.equivFin κ).symm.injective he))
lemma test_energy {κ : Type*} [Fintype κ] (S : κ → Finset ForestNode)
    (hS : ∀ i,forestSegments.IsSegment (S i))
    (hi : Pairwise (fun i j => ∀ u ∈ S i,∀ v ∈ S j,¬ ForestAncestor u v ∧ ¬ ForestAncestor v u))
    (p : ForestNode →₀ ℝ) : (∑ i,(∑ j ∈ S i,p j)^2) ≤ (primalSeminorm p)^2 := by
  have hh := family_energy (familyOfFintype S hS hi) p
  change (∑ i : Fin (Fintype.card κ),(∑ j ∈ S ((Fintype.equivFin κ).symm i),p j)^2) ≤ _ at hh
  rwa [(Fintype.equivFin κ).symm.sum_comp (fun i : κ => (∑ j ∈ S i,p j)^2)] at hh

lemma block_square (p q : ForestNode →₀ ℝ)
    (hd : Disjoint (p.support.image component) (q.support.image component)) :
    (primalSeminorm (p+q))^2 ≤ (primalSeminorm p)^2+(primalSeminorm q)^2 := by
  apply primal_sq_le _ (by positivity)
  intro F
  have hz (i : Fin F.val.n) : (∑ v ∈ F.val.seg i,p v)*(∑ v ∈ F.val.seg i,q v)=0 := by
    by_cases hp : (∑ v ∈ F.val.seg i,p v)=0
    · rw [hp,zero_mul]
    by_cases hq : (∑ v ∈ F.val.seg i,q v)=0
    · rw [hq,mul_zero]
    obtain ⟨u,hu,hpu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    obtain ⟨v,hv,hqv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    have he := same_component _ (F.val.allowed i) u hu v hv
    exact False.elim (Finset.disjoint_left.mp hd
      (Finset.mem_image.mpr ⟨u,Finsupp.mem_support_iff.mpr hpu,rfl⟩)
      (Finset.mem_image.mpr ⟨v,Finsupp.mem_support_iff.mpr hqv,he.symm⟩))
  have he (i : Fin F.val.n) : (∑ v ∈ F.val.seg i,(p+q) v)^2=
      (∑ v ∈ F.val.seg i,p v)^2+(∑ v ∈ F.val.seg i,q v)^2 := by
    simp only [Finsupp.add_apply,Finset.sum_add_distrib]
    nlinarith [hz i]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  exact add_le_add (family_energy F p) (family_energy F q)

lemma block_filter (p : ForestNode →₀ ℝ) (C : Set ℕ) :
    primalSeminorm (p.filter (fun i => component i ∈ C)) ≤ primalSeminorm p := by
  apply (sq_le_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  apply primal_sq_le _ (sq_nonneg _)
  intro F
  apply le_trans _ (family_energy F p)
  apply Finset.sum_le_sum
  intro i _
  by_cases hc : ∃ u ∈ F.val.seg i,component u ∈ C
  · obtain ⟨u,hu,hcu⟩ := hc
    have he : (∑ v ∈ F.val.seg i,(p.filter (fun j => component j ∈ C)) v)=∑ v ∈ F.val.seg i,p v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finsupp.filter_apply,ite_eq_left]
      rwa [← same_component _ (F.val.allowed i) u hu v hv]
    rw [he]
  · have he : (∑ v ∈ F.val.seg i,(p.filter (fun j => component j ∈ C)) v)=0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [Finsupp.filter_apply,ite_eq_right (fun hh => hc ⟨v,hv,hh⟩)]
    rw [he,zero_pow (by decide : 2 ≠ 0)]
    positivity

lemma singleton_test (j : ℕ) (p : ForestNode →₀ ℝ) :
    (∑ v ∈ p.support.filter (fun v => v.val.2.length=j),p v^2) ≤ (primalSeminorm p)^2 := by
  let S := p.support.filter (fun v => v.val.2.length=j)
  have hh := test_energy (fun v : S => ({v.val} : Finset ForestNode))
    (fun v => forestSegments.singleton v.val) (by
      intro u v huv a ha b hb
      simp only [Finset.mem_singleton] at ha hb
      subst a
      subst b
      have hu : u.val.val.2.length=j := (Finset.mem_filter.mp u.property).2
      have hv : v.val.val.2.length=j := (Finset.mem_filter.mp v.property).2
      constructor
      · intro hab
        have he : u.val=v.val := Subtype.ext (Prod.ext hab.1 (hab.2.eq_of_length (hu.trans hv.symm)))
        exact huv (Subtype.ext he)
      · intro hab
        have he : v.val=u.val := Subtype.ext (Prod.ext hab.1 (hab.2.eq_of_length (hv.trans hu.symm)))
        exact huv (Subtype.ext he.symm)) p
  simp only [Finset.sum_singleton] at hh
  have he := Finset.sum_coe_sort S (fun v => p v^2)
  rw [he] at hh
  exact hh

lemma local_lower (C : Finset ℕ) (p : ForestNode →₀ ℝ)
    (hp : ∀ v ∈ p.support,component v ∈ C) :
    (∑ v ∈ p.support,p v^2) ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*(primalSeminorm p)^2 := by
  have hm : ∀ v ∈ p.support,v.val.2.length ∈ Finset.range (C.sup (id : ℕ → ℕ)+1) := by
    intro v hv
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (v.property.2.trans (Finset.le_sup (f := id) (hp v hv))))
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun v => p v^2)]
  calc
    _ ≤ ∑ _j ∈ Finset.range (C.sup (id : ℕ → ℕ)+1),(primalSeminorm p)^2 :=
      Finset.sum_le_sum (fun j _ => singleton_test j p)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

lemma blocks : primalData.HilbertBlocks component where
  orthogonal p q hd := block_square p q (by
    simpa only [Finset.disjoint_left,Finset.mem_image] using hd)
  contractive := block_filter
  upper C := ⟨((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1,by positivity,fun p hp =>
    ((sq_le_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mpr (primal_le_disjoint p)).trans
      (primal_sq_bounded_components C p hp)⟩
  lower C := ⟨((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1,by positivity,fun p hp => local_lower C p hp⟩

def Head := {H : Finset ForestNode // Ancestry.Ancestral (A := forestAncestry) (H : Set ForestNode)}

def heads : Midpoint.Heads Head Space where
  projection H := primalData.dualProjection H.val
  idempotent H := primalData.dualProjection_idempotent H.val
  finite H := primalData.dualProjection_finite H.val
  approximation x η hη := by
    obtain ⟨v,hv⟩ := primalData.dual_approximation component blocks x hη
    obtain ⟨H,hH,hanc⟩ := forest_finite_heads v.support
    exact ⟨⟨H,hanc⟩,primalData.dualEmbedding v,primalData.dualProjection_fixed v hH,hv⟩

theorem graph (hinput : heads.RadialInput PathApplications.incomparableK)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → Space) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (1-(D⁻¹/PathApplications.incomparableK)^2)^k :=
  PathApplications.incomparable_segments heads hinput k f hf

end IncomparableModel

end DiamondDistortion

end

end OAI
